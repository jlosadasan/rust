// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::panic;
use std::path::PathBuf;

use errors::{Diagnostic, DiagnosticBuilder, FatalError, Level};

use proc_macro::{Delimiter, LexError, LineColumn, LiteralKind, Spacing};
use proc_macro::bridge::{Expand1, Expand2, FrontendInterface, ThreadRef, TokenNode};

use rustc_data_structures::sync::Lrc;
use syntax_pos::{SyntaxContext, FileMap, FileName, MultiSpan, Pos, DUMMY_SP, Span};
use syntax_pos::hygiene::Mark;
use syntax_pos::symbol::Symbol;
use syntax::ast;
use syntax::ext::base::{self, ExtCtxt, ProcMacro};
use syntax::parse::{self, token, ParseSess};
use syntax::tokenstream::{self, TokenStream};

pub struct AttrProcMacro {
    pub inner: Expand2,
}

impl base::AttrProcMacro for AttrProcMacro {
    fn expand<'cx>(&self,
                   ecx: &'cx mut ExtCtxt,
                   span: Span,
                   annotation: TokenStream,
                   annotated: TokenStream)
                   -> TokenStream {
        let res = panic::catch_unwind(panic::AssertUnwindSafe(|| {
            self.inner.run(Frontend::new(ecx), annotation, annotated)
        }));

        match res {
            Ok(stream) => stream,
            Err(e) => {
                let msg = "custom attribute panicked";
                let mut err = ecx.struct_span_fatal(span, msg);
                if let Some(s) = e.downcast_ref::<String>() {
                    err.help(&format!("message: {}", s));
                }
                if let Some(s) = e.downcast_ref::<&'static str>() {
                    err.help(&format!("message: {}", s));
                }

                err.emit();
                FatalError.raise();
            }
        }
    }
}

pub struct BangProcMacro {
    pub inner: Expand1,
}

impl ProcMacro for BangProcMacro {
    fn expand<'cx>(&self,
                   ecx: &'cx mut ExtCtxt,
                   span: Span,
                   input: TokenStream)
                   -> TokenStream {
        let res = panic::catch_unwind(panic::AssertUnwindSafe(|| {
            self.inner.run(Frontend::new(ecx), input)
        }));

        match res {
            Ok(stream) => stream,
            Err(e) => {
                let msg = "proc macro panicked";
                let mut err = ecx.struct_span_fatal(span, msg);
                if let Some(s) = e.downcast_ref::<String>() {
                    err.help(&format!("message: {}", s));
                }
                if let Some(s) = e.downcast_ref::<&'static str>() {
                    err.help(&format!("message: {}", s));
                }

                err.emit();
                FatalError.raise();
            }
        }
    }
}

pub struct Quoter;

impl ProcMacro for Quoter {
    fn expand<'cx>(&self, cx: &'cx mut ExtCtxt,
                   _: Span,
                   stream: TokenStream)
                   -> TokenStream {
        let expand_quoter = Expand1::new(&::proc_macro::quote_token_stream);

        let mut info = cx.current_expansion.mark.expn_info().unwrap();
        info.callee.allow_internal_unstable = true;
        cx.current_expansion.mark.set_expn_info(info);

        expand_quoter.run(Frontend::new(cx), stream)
    }
}

trait FromInternal<T> {
    fn from_internal(x: T) -> Self;
}

trait ToInternal<T> {
    fn to_internal(self) -> T;
}

impl ToInternal<Level> for ::proc_macro::Level {
    fn to_internal(self) -> Level {
        match self {
            ::proc_macro::Level::Error => Level::Error,
            ::proc_macro::Level::Warning => Level::Warning,
            ::proc_macro::Level::Note => Level::Note,
            ::proc_macro::Level::Help => Level::Help,
            ::proc_macro::Level::__Nonexhaustive => unreachable!("Level::__Nonexhaustive")
        }
    }
}

impl FromInternal<token::DelimToken> for Delimiter {
    fn from_internal(delim: token::DelimToken) -> Delimiter {
        match delim {
            token::Paren => Delimiter::Parenthesis,
            token::Brace => Delimiter::Brace,
            token::Bracket => Delimiter::Bracket,
            token::NoDelim => Delimiter::None,
        }
    }
}

impl ToInternal<token::DelimToken> for Delimiter {
    fn to_internal(self) -> token::DelimToken {
        match self {
            Delimiter::Parenthesis => token::Paren,
            Delimiter::Brace => token::Brace,
            Delimiter::Bracket => token::Bracket,
            Delimiter::None => token::NoDelim,
        }
    }
}

macro_rules! literals {
    ($($i:ident),*; $($raw:ident),*) => {
        impl FromInternal<token::Token> for (LiteralKind, Symbol, Option<Symbol>) {
            fn from_internal(token: token::Token) -> Self {
                let (lit, suffix) = match token {
                    token::Literal(lit, suffix) => (lit, suffix),
                    token::DocComment(contents) => {
                        return (LiteralKind::DocComment, contents, None);
                    }
                    _ => panic!("unsupported literal {:?}", token),
                };

                let (kind, contents) = match lit {
                    $(token::Lit::$i(contents) => (LiteralKind::$i, contents),)*
                    $(token::Lit::$raw(contents, n) => (LiteralKind::$raw(n), contents),)*
                };

                (kind, contents, suffix)
            }
        }

        impl ToInternal<token::Token> for (LiteralKind, Symbol, Option<Symbol>) {
            fn to_internal(self) -> token::Token {
                let (kind, contents, suffix) = self;
                match kind {
                    LiteralKind::DocComment => {
                        assert_eq!(suffix, None);
                        token::DocComment(contents)
                    }
                    $(LiteralKind::$i => {
                        token::Literal(token::Lit::$i(contents), suffix)
                    })*
                    $(LiteralKind::$raw(n) => {
                        token::Literal(token::Lit::$raw(contents, n), suffix)
                    })*
                }
            }
        }
    }
}

literals!(Byte, Char, Float, Str_, Integer, ByteStr; StrRaw, ByteStrRaw);

pub(crate) struct Frontend<'a> {
    sess: &'a ParseSess,
    mark: Mark,
}

impl<'a> Frontend<'a> {
    pub fn new(cx: &'a ExtCtxt) -> Self {
        Frontend {
            sess: cx.parse_sess,
            mark: cx.current_expansion.mark
        }
    }
}

impl<'a> FrontendInterface for Frontend<'a> {
    type TokenStream = TokenStream;
    type TokenStreamBuilder = tokenstream::TokenStreamBuilder;
    type TokenCursor = tokenstream::Cursor;
    type SourceFile = Lrc<FileMap>;
    type Diagnostic = Diagnostic;
    type Span = Span;
    type Term = Symbol;

    type TokenNode = TokenNode<Self>;

    fn token_stream_empty(&self) -> Self::TokenStream {
        TokenStream::empty()
    }
    fn token_stream_is_empty(&self, stream: &Self::TokenStream) -> bool {
        stream.is_empty()
    }
    fn token_stream_from_str(&self, src: &str) -> Result<Self::TokenStream, LexError> {
        let src = src.to_string();
        let name = FileName::ProcMacroSourceCode;
        let expn_info = self.mark.expn_info().unwrap();
        let call_site = expn_info.call_site;
        // notify the expansion info that it is unhygienic
        let mark = Mark::fresh(self.mark);
        mark.set_expn_info(expn_info);
        let span = call_site.with_ctxt(SyntaxContext::empty().apply_mark(mark));
        Ok(parse::parse_stream_from_source_str(name, src, self.sess, Some(span)))
    }
    fn token_stream_from_token_tree(&self, node: Self::TokenNode, span: Self::Span)
                                    -> Self::TokenStream {
        use syntax::parse::token::*;
        use syntax::tokenstream::TokenTree;

        let (op, kind) = match node {
            TokenNode::Op(op, kind) => (op, kind),
            TokenNode::Group(delimiter, delimed) => {
                return tokenstream::TokenTree::Delimited(span, tokenstream::Delimited {
                    delim: delimiter.to_internal(),
                    tts: delimed.into(),
                }).into();
            }
            TokenNode::Term(symbol) => {
                let ident = ast::Ident { name: symbol, ctxt: span.ctxt() };
                let token = if symbol.as_str().starts_with("'") {
                    Lifetime(ident)
                } else {
                    Ident(ident)
                };
                return TokenTree::Token(span, token).into();
            }
            TokenNode::Literal(kind, contents, suffix) => {
                return TokenTree::Token(span, (kind, contents, suffix).to_internal()).into()
            }
        };

        let token = match op {
            '=' => Eq,
            '<' => Lt,
            '>' => Gt,
            '!' => Not,
            '~' => Tilde,
            '+' => BinOp(Plus),
            '-' => BinOp(Minus),
            '*' => BinOp(Star),
            '/' => BinOp(Slash),
            '%' => BinOp(Percent),
            '^' => BinOp(Caret),
            '&' => BinOp(And),
            '|' => BinOp(Or),
            '@' => At,
            '.' => Dot,
            ',' => Comma,
            ';' => Semi,
            ':' => Colon,
            '#' => Pound,
            '$' => Dollar,
            '?' => Question,
            _ => panic!("unsupported character {}", op),
        };

        let tree = TokenTree::Token(span, token);
        match kind {
            Spacing::Alone => tree.into(),
            Spacing::Joint => tree.joint(),
        }
    }
    fn token_stream_to_token_tree(&self, stream: Self::TokenStream)
                                  -> ((Self::Span, Self::TokenNode),
                                      Option<Self::TokenStream>) {
        use syntax::parse::token::*;

        let mut next = None;

        let (tree, is_joint) = stream.as_tree();
        let (mut span, token) = match tree {
            tokenstream::TokenTree::Delimited(span, delimed) => {
                let delimiter = Delimiter::from_internal(delimed.delim);
                return ((span, TokenNode::Group(delimiter, delimed.tts.into())), next);
            }
            tokenstream::TokenTree::Token(span, token) => (span, token),
        };

        let op_kind = if is_joint { Spacing::Joint } else { Spacing::Alone };
        macro_rules! op {
            ($op:expr) => { TokenNode::Op($op, op_kind) }
        }

        macro_rules! joint {
            ($first:expr, $rest:expr) => {
                joint($first, $rest, is_joint, &mut span, &mut next)
            }
        }

        fn joint<'a>(first: char, rest: Token, is_joint: bool, span: &mut Span,
                     next: &mut Option<TokenStream>)
                     -> TokenNode<Frontend<'a>> {
            let (first_span, rest_span) = (*span, *span);
            *span = first_span;
            let tree = tokenstream::TokenTree::Token(rest_span, rest);
            *next = Some(if is_joint { tree.joint() } else { tree.into() });
            TokenNode::Op(first, Spacing::Joint)
        }

        let kind = match token {
            Eq => op!('='),
            Lt => op!('<'),
            Le => joint!('<', Eq),
            EqEq => joint!('=', Eq),
            Ne => joint!('!', Eq),
            Ge => joint!('>', Eq),
            Gt => op!('>'),
            AndAnd => joint!('&', BinOp(And)),
            OrOr => joint!('|', BinOp(Or)),
            Not => op!('!'),
            Tilde => op!('~'),
            BinOp(Plus) => op!('+'),
            BinOp(Minus) => op!('-'),
            BinOp(Star) => op!('*'),
            BinOp(Slash) => op!('/'),
            BinOp(Percent) => op!('%'),
            BinOp(Caret) => op!('^'),
            BinOp(And) => op!('&'),
            BinOp(Or) => op!('|'),
            BinOp(Shl) => joint!('<', Lt),
            BinOp(Shr) => joint!('>', Gt),
            BinOpEq(Plus) => joint!('+', Eq),
            BinOpEq(Minus) => joint!('-', Eq),
            BinOpEq(Star) => joint!('*', Eq),
            BinOpEq(Slash) => joint!('/', Eq),
            BinOpEq(Percent) => joint!('%', Eq),
            BinOpEq(Caret) => joint!('^', Eq),
            BinOpEq(And) => joint!('&', Eq),
            BinOpEq(Or) => joint!('|', Eq),
            BinOpEq(Shl) => joint!('<', Le),
            BinOpEq(Shr) => joint!('>', Ge),
            At => op!('@'),
            Dot => op!('.'),
            DotDot => joint!('.', Dot),
            DotDotDot => joint!('.', DotDot),
            DotDotEq => joint!('.', DotEq),
            Comma => op!(','),
            Semi => op!(';'),
            Colon => op!(':'),
            ModSep => joint!(':', Colon),
            RArrow => joint!('-', Gt),
            LArrow => joint!('<', BinOp(Minus)),
            FatArrow => joint!('=', Gt),
            Pound => op!('#'),
            Dollar => op!('$'),
            Question => op!('?'),

            Ident(ident) | Lifetime(ident) => TokenNode::Term(ident.name),
            Literal(..) | DocComment(..) => {
                let (kind, contents, suffix) = FromInternal::from_internal(token);
                TokenNode::Literal(kind, contents, suffix)
            }

            Interpolated(_) => {
                let tts = token.interpolated_to_tokenstream(self.sess, span);
                TokenNode::Group(Delimiter::None, tts)
            }

            DotEq => joint!('.', Eq),
            OpenDelim(..) | CloseDelim(..) => unreachable!(),
            Whitespace | Comment | Shebang(..) | Eof => unreachable!(),
        };

        ((span, kind), next)
    }
    fn token_stream_trees(&self, stream: Self::TokenStream) -> Self::TokenCursor {
        stream.trees()
    }

    fn token_stream_builder_new(&self) -> Self::TokenStreamBuilder {
        tokenstream::TokenStreamBuilder::new()
    }
    fn token_stream_builder_push(&self, builder: &mut Self::TokenStreamBuilder,
                                 stream: Self::TokenStream) {
        builder.push(stream);
    }
    fn token_stream_builder_build(&self, builder: Self::TokenStreamBuilder)
                                  -> Self::TokenStream {
        builder.build()
    }

    fn token_cursor_next(&self, cursor: &mut Self::TokenCursor) -> Option<Self::TokenStream> {
        while let Some(stream) = cursor.next_as_stream() {
            let (tree, _) = stream.clone().as_tree();
            let span = tree.span();
            if span != DUMMY_SP {
                return Some(stream);
            }
            let nested_stream = match tree {
                tokenstream::TokenTree::Delimited(_, tokenstream::Delimited {
                    delim: token::NoDelim,
                    tts
                }) => tts.into(),
                tokenstream::TokenTree::Token(_, token @ token::Interpolated(_)) => {
                    token.interpolated_to_tokenstream(self.sess, span)
                }
                _ => return Some(stream)
            };
            cursor.insert(nested_stream);
        }
        None
    }

    fn source_file_eq(&self, file1: &Self::SourceFile, file2: &Self::SourceFile) -> bool {
        Lrc::ptr_eq(file1, file2)
    }
    fn source_file_path(&self, file: &Self::SourceFile) -> PathBuf {
        match file.name {
            FileName::Real(ref path) => path.clone(),
            _ => PathBuf::from(file.name.to_string())
        }
    }
    fn source_file_is_real(&self, file: &Self::SourceFile) -> bool {
        file.is_real_file()
    }

    fn diagnostic_new(&self, level: ::proc_macro::Level, msg: &str, span: Option<Self::Span>)
                      -> Self::Diagnostic {
        let mut diagnostic = Diagnostic::new(level.to_internal(), msg);

        if let Some(span) = span {
            diagnostic.set_span(span);
        }

        diagnostic

    }
    fn diagnostic_sub(&self, diagnostic: &mut Self::Diagnostic,
                      level: ::proc_macro::Level, msg: &str, span: Option<Self::Span>) {
        let span = span.map(|s| s.into()).unwrap_or(MultiSpan::new());
        diagnostic.sub(level.to_internal(), msg, span, None);
    }
    fn diagnostic_emit(&self, diagnostic: Self::Diagnostic) {
        DiagnosticBuilder::new_diagnostic(&self.sess.span_diagnostic, diagnostic).emit()
    }

    fn span_def_site(&self) -> Self::Span {
        self.span_call_site()
            .with_ctxt(SyntaxContext::empty().apply_mark(self.mark))
    }
    fn span_call_site(&self) -> Self::Span {
        self.mark.expn_info().unwrap().call_site
    }
    fn span_source_file(&self, span: Self::Span) -> Self::SourceFile {
        self.sess.codemap().lookup_char_pos(span.lo()).file
    }
    fn span_parent(&self, span: Self::Span) -> Option<Self::Span> {
        span.ctxt().outer().expn_info().map(|i| i.call_site)
    }
    fn span_source(&self, span: Self::Span) -> Self::Span {
        span.source_callsite()
    }
    fn span_start(&self, span: Self::Span) -> LineColumn {
        let loc = self.sess.codemap().lookup_char_pos(span.lo());
        LineColumn {
            line: loc.line,
            column: loc.col.to_usize()
        }
    }
    fn span_end(&self, span: Self::Span) -> LineColumn {
        let loc = self.sess.codemap().lookup_char_pos(span.hi());
        LineColumn {
            line: loc.line,
            column: loc.col.to_usize()
        }
    }
    fn span_join(&self, first: Self::Span, second: Self::Span) -> Option<Self::Span> {
        let self_loc = self.sess.codemap().lookup_char_pos(first.lo());
        let other_loc = self.sess.codemap().lookup_char_pos(second.lo());

        if self_loc.file.name != other_loc.file.name { return None }

        Some(first.to(second))
    }
    fn span_resolved_at(&self, span: Self::Span, at: Self::Span) -> Self::Span {
        span.with_ctxt(at.ctxt())
    }

    fn term_intern(&self, string: &str) -> Self::Term {
        Symbol::intern(string)
    }
    fn term_as_str(&self, term: Self::Term) -> ThreadRef<str> {
        ThreadRef::new(unsafe { &*(&*term.as_str() as *const str) })
    }
}
