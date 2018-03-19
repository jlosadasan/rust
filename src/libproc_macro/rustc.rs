// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use {Delimiter, Literal, LiteralKind, Spacing, Term, TokenNode};

use rustc_data_structures::sync::Lrc;
use rustc_errors::{Diagnostic, DiagnosticBuilder, Level};
use std::path::PathBuf;
use syntax_pos::{self, SyntaxContext, FileMap, FileName, MultiSpan, Pos, DUMMY_SP};
use syntax_pos::hygiene::Mark;
use syntax::ast;
use syntax::ext::base::{ExtCtxt, ProcMacro};
use syntax::parse::{self, token, ParseSess};
use syntax::tokenstream;

pub struct Quoter;

impl ProcMacro for Quoter {
    fn expand<'cx>(&self, cx: &'cx mut ExtCtxt,
                _: syntax_pos::Span,
                stream: tokenstream::TokenStream)
                -> tokenstream::TokenStream {
        let expand_quoter = ::bridge::Expand1::new(&::quote_token_stream);

        let mut info = cx.current_expansion.mark.expn_info().unwrap();
        info.callee.allow_internal_unstable = true;
        cx.current_expansion.mark.set_expn_info(info);

        expand_quoter.run(Rustc::new(cx), stream)
    }
}

impl ::Level {
    fn to_internal(self) -> Level {
        match self {
            ::Level::Error => Level::Error,
            ::Level::Warning => Level::Warning,
            ::Level::Note => Level::Note,
            ::Level::Help => Level::Help,
            ::Level::__Nonexhaustive => unreachable!("Level::__Nonexhaustive")
        }
    }
}

impl Delimiter {
    fn from_internal(delim: token::DelimToken) -> Delimiter {
        match delim {
            token::Paren => Delimiter::Parenthesis,
            token::Brace => Delimiter::Brace,
            token::Bracket => Delimiter::Bracket,
            token::NoDelim => Delimiter::None,
        }
    }

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
        impl Literal {
            fn from_internal(token: token::Token) -> Self {
                let (lit, suffix) = match token {
                    token::Literal(lit, suffix) => (lit, suffix),
                    token::DocComment(contents) => {
                        return Literal {
                            kind: LiteralKind::DocComment,
                            contents: Term(contents),
                            suffix: None
                        };
                    }
                    _ => panic!("unsupported literal {:?}", token),
                };

                let (kind, contents) = match lit {
                    $(token::Lit::$i(contents) => (LiteralKind::$i, contents),)*
                    $(token::Lit::$raw(contents, n) => (LiteralKind::$raw(n), contents),)*
                };

                Literal {
                    kind,
                    contents: Term(contents),
                    suffix: suffix.map(Term)
                }
            }

            fn to_internal(self) -> token::Token {
                let contents = self.contents.0;
                let suffix = self.suffix.map(|t| t.0);
                match self.kind {
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

pub struct Rustc<'a> {
    sess: &'a ParseSess,
    mark: Mark,
}

impl<'a> Rustc<'a> {
    pub fn new(cx: &'a ExtCtxt) -> Self {
        Rustc {
            sess: cx.parse_sess,
            mark: cx.current_expansion.mark
        }
    }
}

impl<'a> ::bridge::FrontendInterface for Rustc<'a> {
    type TokenStream = tokenstream::TokenStream;
    type TokenStreamBuilder = tokenstream::TokenStreamBuilder;
    type TokenCursor = tokenstream::Cursor;
    type SourceFile = Lrc<FileMap>;
    type Diagnostic = Diagnostic;
    type Span = syntax_pos::Span;

    fn token_stream_empty(&self) -> Self::TokenStream {
        tokenstream::TokenStream::empty()
    }
    fn token_stream_is_empty(&self, stream: &Self::TokenStream) -> bool {
        stream.is_empty()
    }
    fn token_stream_from_str(&self, src: &str) -> Result<Self::TokenStream, ::LexError> {
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
    fn token_stream_delimited(&self, span: Self::Span,
                              delimiter: ::Delimiter,
                              delimed: Self::TokenStream)
                              -> Self::TokenStream {
        tokenstream::TokenTree::Delimited(span, tokenstream::Delimited {
            delim: delimiter.to_internal(),
            tts: delimed.into(),
        }).into()
    }
    fn token_stream_from_token_tree(&self, node: ::TokenNode, span: Self::Span)
                                    -> Self::TokenStream {
        use syntax::parse::token::*;
        use syntax::tokenstream::TokenTree;

        let (op, kind) = match node {
            TokenNode::Op(op, kind) => (op, kind),
            TokenNode::Group(..) => unreachable!(),
            TokenNode::Term(symbol) => {
                let ident = ast::Ident { name: symbol.0, ctxt: span.ctxt() };
                let token = if symbol.0.as_str().starts_with("'") {
                    Lifetime(ident)
                } else {
                    Ident(ident)
                };
                return TokenTree::Token(span, token).into();
            }
            TokenNode::Literal(literal) => {
                return TokenTree::Token(span, literal.to_internal()).into()
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
                                  -> (Self::Span,
                                      Result<(::TokenNode, Option<Self::TokenStream>),
                                             (::Delimiter, Self::TokenStream)>) {
        use syntax::parse::token::*;

        let mut next = None;

        let (tree, is_joint) = stream.as_tree();
        let (mut span, token) = match tree {
            tokenstream::TokenTree::Delimited(span, delimed) => {
                let delimiter = Delimiter::from_internal(delimed.delim);
                return (span, Err((delimiter, delimed.tts.into())));
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

        fn joint(first: char, rest: Token, is_joint: bool, span: &mut syntax_pos::Span,
                next: &mut Option<tokenstream::TokenStream>)
                -> TokenNode {
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

            Ident(ident) | Lifetime(ident) => TokenNode::Term(Term(ident.name)),
            Literal(..) | DocComment(..) => {
                TokenNode::Literal(::Literal::from_internal(token))
            }

            Interpolated(_) => {
                let tts = token.interpolated_to_tokenstream(self.sess, span);
                return (span, Err((Delimiter::None, tts)));
            }

            DotEq => joint!('.', Eq),
            OpenDelim(..) | CloseDelim(..) => unreachable!(),
            Whitespace | Comment | Shebang(..) | Eof => unreachable!(),
        };

        (span, Ok((kind, next)))
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

    fn diagnostic_new(&self, level: ::Level, msg: &str, span: Option<Self::Span>)
                      -> Self::Diagnostic {
        let mut diagnostic = Diagnostic::new(level.to_internal(), msg);

        if let Some(span) = span {
            diagnostic.set_span(span);
        }

        diagnostic

    }
    fn diagnostic_sub(&self, diagnostic: &mut Self::Diagnostic,
                      level: ::Level, msg: &str, span: Option<Self::Span>) {
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
    fn span_start(&self, span: Self::Span) -> ::LineColumn {
        let loc = self.sess.codemap().lookup_char_pos(span.lo());
        ::LineColumn {
            line: loc.line,
            column: loc.col.to_usize()
        }
    }
    fn span_end(&self, span: Self::Span) -> ::LineColumn {
        let loc = self.sess.codemap().lookup_char_pos(span.hi());
        ::LineColumn {
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
}
