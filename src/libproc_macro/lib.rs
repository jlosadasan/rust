// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A support library for macro authors when defining new macros.
//!
//! This library, provided by the standard distribution, provides the types
//! consumed in the interfaces of procedurally defined macro definitions.
//! Currently the primary use of this crate is to provide the ability to define
//! new custom derive modes through `#[proc_macro_derive]`.
//!
//! Note that this crate is intentionally very bare-bones currently. The main
//! type, `TokenStream`, only supports `fmt::Display` and `FromStr`
//! implementations, indicating that it can only go to and come from a string.
//! This functionality is intended to be expanded over time as more surface
//! area for macro authors is stabilized.
//!
//! See [the book](../book/first-edition/procedural-macros.html) for more.

#![stable(feature = "proc_macro_lib", since = "1.15.0")]
#![deny(warnings)]
#![deny(missing_docs)]
#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk-v2.png",
       html_favicon_url = "https://doc.rust-lang.org/favicon.ico",
       html_root_url = "https://doc.rust-lang.org/nightly/",
       html_playground_url = "https://play.rust-lang.org/",
       issue_tracker_base_url = "https://github.com/rust-lang/rust/issues/",
       test(no_crate_inject, attr(deny(warnings))),
       test(attr(allow(dead_code, deprecated, unused_variables, unused_mut))))]

#![feature(i128_type)]
#![feature(rustc_private)]
#![feature(staged_api)]
#![feature(lang_items)]
#![feature(optin_builtin_traits)]
#![feature(box_into_raw_non_null)]
#![feature(nonnull_cast)]

#[macro_use]
extern crate syntax;
extern crate syntax_pos;
extern crate rustc_errors;
extern crate rustc_data_structures;

#[unstable(feature = "proc_macro_internals", issue = "27812")]
#[doc(hidden)]
pub mod bridge;

use bridge::{Frontend, FrontendInterface};

#[unstable(feature = "proc_macro_internals", issue = "27812")]
#[doc(hidden)]
pub mod rustc;

mod diagnostic;

#[unstable(feature = "proc_macro", issue = "38356")]
pub use diagnostic::{Diagnostic, Level};

use std::{ascii, fmt, iter};
use std::path::PathBuf;
use std::str::FromStr;

use syntax::symbol::Symbol;

/// The main type provided by this crate, representing an abstract stream of
/// tokens.
///
/// This is both the input and output of `#[proc_macro_derive]` definitions.
/// Currently it's required to be a list of valid Rust items, but this
/// restriction may be lifted in the future.
///
/// The API of this type is intentionally bare-bones, but it'll be expanded over
/// time!
#[stable(feature = "proc_macro_lib", since = "1.15.0")]
#[derive(Clone, Debug)]
pub struct TokenStream(bridge::TokenStream);

/// Error returned from `TokenStream::from_str`.
#[stable(feature = "proc_macro_lib", since = "1.15.0")]
#[derive(Debug)]
pub struct LexError {
    _inner: (),
}

#[stable(feature = "proc_macro_lib", since = "1.15.0")]
impl FromStr for TokenStream {
    type Err = LexError;

    fn from_str(src: &str) -> Result<TokenStream, LexError> {
        Frontend.token_stream_from_str(src).map(TokenStream)
    }
}

#[stable(feature = "proc_macro_lib", since = "1.15.0")]
impl fmt::Display for TokenStream {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// `quote!(..)` accepts arbitrary tokens and expands into a `TokenStream` describing the input.
/// For example, `quote!(a + b)` will produce a expression, that, when evaluated, constructs
/// the `TokenStream` `[Word("a"), Op('+', Alone), Word("b")]`.
///
/// Unquoting is done with `$`, and works by taking the single next ident as the unquoted term.
/// To quote `$` itself, use `$$`.
#[unstable(feature = "proc_macro", issue = "38356")]
#[macro_export]
macro_rules! quote { () => {} }

#[unstable(feature = "proc_macro_internals", issue = "27812")]
#[doc(hidden)]
mod quote;

/// Quote a `TokenStream` into a `TokenStream`.
/// This is needed to implement a custom quoter.
#[unstable(feature = "proc_macro", issue = "38356")]
pub fn quote_token_stream(stream: TokenStream) -> TokenStream {
    quote::Quote::quote(stream)
}

#[unstable(feature = "proc_macro", issue = "38356")]
impl From<TokenTree> for TokenStream {
    fn from(tree: TokenTree) -> TokenStream {
        TokenStream(match tree.kind {
            TokenNode::Group(delimiter, tokens) => {
                Frontend.token_stream_delimited(tree.span.0, delimiter, tokens.0)
            }
            _ => Frontend.token_stream_from_token_tree(tree.kind, tree.span.0)
        })
    }
}

#[unstable(feature = "proc_macro", issue = "38356")]
impl From<TokenNode> for TokenStream {
    fn from(kind: TokenNode) -> TokenStream {
        TokenTree::from(kind).into()
    }
}

#[unstable(feature = "proc_macro", issue = "38356")]
impl<T: Into<TokenStream>> iter::FromIterator<T> for TokenStream {
    fn from_iter<I: IntoIterator<Item = T>>(streams: I) -> Self {
        let mut builder = Frontend.token_stream_builder_new();
        for stream in streams {
            Frontend.token_stream_builder_push(&mut builder, stream.into().0);
        }
        TokenStream(Frontend.token_stream_builder_build(builder))
    }
}

#[unstable(feature = "proc_macro", issue = "38356")]
impl IntoIterator for TokenStream {
    type Item = TokenTree;
    type IntoIter = TokenTreeIter;

    fn into_iter(self) -> TokenTreeIter {
        TokenTreeIter {
            cursor: Frontend.token_stream_trees(self.0),
            next: None,
        }
    }
}

impl TokenStream {
    /// Returns an empty `TokenStream`.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn empty() -> TokenStream {
        TokenStream(Frontend.token_stream_empty())
    }

    /// Checks if this `TokenStream` is empty.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn is_empty(&self) -> bool {
        Frontend.token_stream_is_empty(&self.0)
    }
}

/// A region of source code, along with macro expansion information.
#[unstable(feature = "proc_macro", issue = "38356")]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Span(bridge::Span);

/// Quote a `Span` into a `TokenStream`.
/// This is needed to implement a custom quoter.
#[unstable(feature = "proc_macro", issue = "38356")]
pub fn quote_span(span: Span) -> TokenStream {
    quote::Quote::quote(span)
}

macro_rules! diagnostic_method {
    ($name:ident, $level:expr) => (
        /// Create a new `Diagnostic` with the given `message` at the span
        /// `self`.
        #[unstable(feature = "proc_macro", issue = "38356")]
        pub fn $name<T: Into<String>>(self, message: T) -> Diagnostic {
            Diagnostic::spanned(self, $level, message)
        }
    )
}

impl Span {
    /// A span that resolves at the macro definition site.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn def_site() -> Span {
        Span(Frontend.span_def_site())
    }

    /// The span of the invocation of the current procedural macro.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn call_site() -> Span {
        Span(Frontend.span_call_site())
    }

    /// The original source file into which this span points.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn source_file(&self) -> SourceFile {
        SourceFile(Frontend.span_source_file(self.0))
    }

    /// The `Span` for the tokens in the previous macro expansion from which
    /// `self` was generated from, if any.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn parent(&self) -> Option<Span> {
        Frontend.span_parent(self.0).map(Span)
    }

    /// The span for the origin source code that `self` was generated from. If
    /// this `Span` wasn't generated from other macro expansions then the return
    /// value is the same as `*self`.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn source(&self) -> Span {
        Span(Frontend.span_source(self.0))
    }

    /// Get the starting line/column in the source file for this span.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn start(&self) -> LineColumn {
        Frontend.span_start(self.0)
    }

    /// Get the ending line/column in the source file for this span.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn end(&self) -> LineColumn {
        Frontend.span_end(self.0)
    }

    /// Create a new span encompassing `self` and `other`.
    ///
    /// Returns `None` if `self` and `other` are from different files.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn join(&self, other: Span) -> Option<Span> {
        Frontend.span_join(self.0, other.0).map(Span)
    }

    /// Creates a new span with the same line/column information as `self` but
    /// that resolves symbols as though it were at `other`.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn resolved_at(&self, other: Span) -> Span {
        Span(Frontend.span_resolved_at(self.0, other.0))
    }

    /// Creates a new span with the same name resolution behavior as `self` but
    /// with the line/column information of `other`.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn located_at(&self, other: Span) -> Span {
        other.resolved_at(*self)
    }

    diagnostic_method!(error, Level::Error);
    diagnostic_method!(warning, Level::Warning);
    diagnostic_method!(note, Level::Note);
    diagnostic_method!(help, Level::Help);
}

/// A line-column pair representing the start or end of a `Span`.
#[unstable(feature = "proc_macro", issue = "38356")]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LineColumn {
    /// The 1-indexed line in the source file on which the span starts or ends (inclusive).
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub line: usize,
    /// The 0-indexed column (in UTF-8 characters) in the source file on which
    /// the span starts or ends (inclusive).
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub column: usize
}

/// The source file of a given `Span`.
#[unstable(feature = "proc_macro", issue = "38356")]
#[derive(Clone)]
pub struct SourceFile(bridge::SourceFile);

impl SourceFile {
    /// Get the path to this source file.
    ///
    /// ### Note
    /// If the code span associated with this `SourceFile` was generated by an external macro, this
    /// may not be an actual path on the filesystem. Use [`is_real`] to check.
    ///
    /// Also note that even if `is_real` returns `true`, if `--remap-path-prefix` was passed on
    /// the command line, the path as given may not actually be valid.
    ///
    /// [`is_real`]: #method.is_real
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn path(&self) -> PathBuf {
        Frontend.source_file_path(&self.0)
    }

    /// Returns `true` if this source file is a real source file, and not generated by an external
    /// macro's expansion.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn is_real(&self) -> bool {
        // This is a hack until intercrate spans are implemented and we can have real source files
        // for spans generated in external macros.
        // https://github.com/rust-lang/rust/pull/43604#issuecomment-333334368
        Frontend.source_file_is_real(&self.0)
    }
}


#[unstable(feature = "proc_macro", issue = "38356")]
impl fmt::Debug for SourceFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("SourceFile")
            .field("path", &self.path())
            .field("is_real", &self.is_real())
            .finish()
    }
}

#[unstable(feature = "proc_macro", issue = "38356")]
impl PartialEq for SourceFile {
    fn eq(&self, other: &Self) -> bool {
        Frontend.source_file_eq(&self.0, &other.0)
    }
}

#[unstable(feature = "proc_macro", issue = "38356")]
impl Eq for SourceFile {}

/// A single token or a delimited sequence of token trees (e.g. `[1, (), ..]`).
#[unstable(feature = "proc_macro", issue = "38356")]
#[derive(Clone, Debug)]
pub struct TokenTree {
    /// The `TokenTree`'s span
    pub span: Span,
    /// Description of the `TokenTree`
    pub kind: TokenNode,
}

#[unstable(feature = "proc_macro", issue = "38356")]
impl From<TokenNode> for TokenTree {
    fn from(kind: TokenNode) -> TokenTree {
        TokenTree { span: Span::def_site(), kind: kind }
    }
}

#[unstable(feature = "proc_macro", issue = "38356")]
impl fmt::Display for TokenTree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        TokenStream::from(self.clone()).fmt(f)
    }
}

/// Description of a `TokenTree`
#[derive(Clone, Debug)]
#[unstable(feature = "proc_macro", issue = "38356")]
pub enum TokenNode {
    /// A delimited tokenstream.
    Group(Delimiter, TokenStream),
    /// A unicode identifier.
    Term(Term),
    /// A punctuation character (`+`, `,`, `$`, etc.).
    Op(char, Spacing),
    /// A literal character (`'a'`), string (`"hello"`), or number (`2.3`).
    Literal(Literal),
}

/// Describes how a sequence of token trees is delimited.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[unstable(feature = "proc_macro", issue = "38356")]
pub enum Delimiter {
    /// `( ... )`
    Parenthesis,
    /// `{ ... }`
    Brace,
    /// `[ ... ]`
    Bracket,
    /// An implicit delimiter, e.g. `$var`, where $var is  `...`.
    None,
}

/// An interned string.
#[derive(Copy, Clone, Debug)]
#[unstable(feature = "proc_macro", issue = "38356")]
pub struct Term(Symbol);

impl Term {
    /// Intern a string into a `Term`.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn intern(string: &str) -> Term {
        Term(Symbol::intern(string))
    }

    /// Get a reference to the interned string.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn as_str(&self) -> &str {
        unsafe { &*(&*self.0.as_str() as *const str) }
    }
}

/// Whether an `Op` is either followed immediately by another `Op` or followed by whitespace.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[unstable(feature = "proc_macro", issue = "38356")]
pub enum Spacing {
    /// e.g. `+` is `Alone` in `+ =`.
    Alone,
    /// e.g. `+` is `Joint` in `+=`.
    Joint,
}

/// A literal character (`'a'`), string (`"hello"`), or number (`2.3`).
#[derive(Clone)]
#[unstable(feature = "proc_macro", issue = "38356")]
pub struct Literal {
    #[unstable(feature = "proc_macro_internals", issue = "27812")]
    #[doc(hidden)]
    pub kind: LiteralKind,

    #[unstable(feature = "proc_macro_internals", issue = "27812")]
    #[doc(hidden)]
    pub contents: Term,

    #[unstable(feature = "proc_macro_internals", issue = "27812")]
    #[doc(hidden)]
    pub suffix: Option<Term>,
}

#[unstable(feature = "proc_macro", issue = "38356")]
impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&TokenTree {
            kind: TokenNode::Literal(self.clone()),
            span: Span::def_site()
        }, f)
    }
}

#[unstable(feature = "proc_macro", issue = "38356")]
impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&TokenTree {
            kind: TokenNode::Literal(self.clone()),
            span: Span::def_site()
        }, f)
    }
}

macro_rules! int_literals {
    ($($int_kind:ident),*) => {$(
        /// Integer literal.
        #[unstable(feature = "proc_macro", issue = "38356")]
        pub fn $int_kind(n: $int_kind) -> Literal {
            Literal::typed_integer(n as i128, stringify!($int_kind))
        }
    )*}
}

impl Literal {
    /// Integer literal
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn integer(n: i128) -> Literal {
        Literal {
            kind: LiteralKind::Integer,
            contents: Term::intern(&n.to_string()),
            suffix: None,
        }
    }

    int_literals!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize);
    fn typed_integer(n: i128, kind: &'static str) -> Literal {
        Literal {
            kind: LiteralKind::Integer,
            contents: Term::intern(&n.to_string()),
            suffix: Some(Term::intern(kind)),
        }
    }

    /// Floating point literal.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn float(n: f64) -> Literal {
        if !n.is_finite() {
            panic!("Invalid float literal {}", n);
        }
        Literal {
            kind: LiteralKind::Float,
            contents: Term::intern(&n.to_string()),
            suffix: None,
        }
    }

    /// Floating point literal.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn f32(n: f32) -> Literal {
        if !n.is_finite() {
            panic!("Invalid f32 literal {}", n);
        }
        Literal {
            kind: LiteralKind::Float,
            contents: Term::intern(&n.to_string()),
            suffix: Some(Term::intern("f32")),
        }
    }

    /// Floating point literal.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn f64(n: f64) -> Literal {
        if !n.is_finite() {
            panic!("Invalid f64 literal {}", n);
        }
        Literal {
            kind: LiteralKind::Float,
            contents: Term::intern(&n.to_string()),
            suffix: Some(Term::intern("f64")),
        }
    }

    /// String literal.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn string(string: &str) -> Literal {
        let mut escaped = String::new();
        for ch in string.chars() {
            escaped.extend(ch.escape_debug());
        }
        Literal {
            kind: LiteralKind::Str_,
            contents: Term::intern(&escaped),
            suffix: None,
        }
    }

    /// Character literal.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn character(ch: char) -> Literal {
        let mut escaped = String::new();
        escaped.extend(ch.escape_unicode());
        Literal {
            kind: LiteralKind::Char,
            contents: Term::intern(&escaped),
            suffix: None,
        }
    }

    /// Byte string literal.
    #[unstable(feature = "proc_macro", issue = "38356")]
    pub fn byte_string(bytes: &[u8]) -> Literal {
        let string = bytes.iter().cloned().flat_map(ascii::escape_default)
            .map(Into::<char>::into).collect::<String>();
        Literal {
            kind: LiteralKind::ByteStr,
            contents: Term::intern(&string),
            suffix: None,
        }
    }
}

#[derive(Copy, Clone)]
#[unstable(feature = "proc_macro_internals", issue = "27812")]
#[doc(hidden)]
pub enum LiteralKind {
    DocComment,

    Byte,
    Char,
    Float,
    Str_,
    Integer,
    ByteStr,

    StrRaw(usize),
    ByteStrRaw(usize),
}

/// An iterator over `TokenTree`s.
#[derive(Clone)]
#[unstable(feature = "proc_macro", issue = "38356")]
pub struct TokenTreeIter {
    cursor: bridge::TokenCursor,
    next: Option<bridge::TokenStream>,
}

#[unstable(feature = "proc_macro", issue = "38356")]
impl Iterator for TokenTreeIter {
    type Item = TokenTree;

    fn next(&mut self) -> Option<TokenTree> {
        let next = unwrap_or!(self.next.take().or_else(|| {
            Frontend.token_cursor_next(&mut self.cursor)
        }), return None);
        let (span, kind) = match Frontend.token_stream_to_token_tree(next) {
            (span, Ok((kind, next))) => {
                self.next = next;
                (span, kind)
            }
            (span, Err((delimiter, delimed))) => {
                (span, TokenNode::Group(delimiter, TokenStream(delimed)))
            }
        };
        Some(TokenTree {
            span: Span(span),
            kind
        })
    }
}
