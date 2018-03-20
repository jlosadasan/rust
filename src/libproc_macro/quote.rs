// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! # Quasiquoter
//! This file contains the implementation internals of the quasiquoter provided by `quote!`.

//! This quasiquoter uses macros 2.0 hygiene to reliably access
//! items from `proc_macro`, to build a `proc_macro::TokenStream`.

use {Delimiter, Literal, LiteralKind, Spacing, Span, Term, TokenNode, TokenStream, TokenTree};

pub trait Quote {
    fn quote(self) -> TokenStream;
}

macro_rules! quote_tok {
    (,) => { TokenNode::Op(',', Spacing::Alone) };
    (.) => { TokenNode::Op('.', Spacing::Alone) };
    (:) => { TokenNode::Op(':', Spacing::Alone) };
    (::) => {
        [
            TokenNode::Op(':', Spacing::Joint),
            TokenNode::Op(':', Spacing::Alone)
        ].iter().cloned().collect::<TokenStream>()
    };
    (!) => { TokenNode::Op('!', Spacing::Alone) };
    (<) => { TokenNode::Op('<', Spacing::Alone) };
    (>) => { TokenNode::Op('>', Spacing::Alone) };
    (_) => { TokenNode::Op('_', Spacing::Alone) };
    (0) => { TokenNode::Literal(::Literal::integer(0)) };
    (&) => { TokenNode::Op('&', Spacing::Alone) };
    ($i:ident) => { TokenNode::Term(Term::intern(stringify!($i))) };
}

macro_rules! quote_tree {
    ((unquote $($t:tt)*)) => { $($t)* };
    ((quote $($t:tt)*)) => { ($($t)*).quote() };
    (($($t:tt)*)) => { TokenNode::Group(Delimiter::Parenthesis, quote!($($t)*)) };
    ([$($t:tt)*]) => { TokenNode::Group(Delimiter::Bracket, quote!($($t)*)) };
    ({$($t:tt)*}) => { TokenNode::Group(Delimiter::Brace, quote!($($t)*)) };
    ($t:tt) => { quote_tok!($t) };
}

macro_rules! quote {
    () => { TokenStream::empty() };
    ($($t:tt)*) => {
        [
            $(TokenStream::from(quote_tree!($t)),)*
        ].iter().cloned().collect::<TokenStream>()
    };
}

impl<T: Quote> Quote for Option<T> {
    fn quote(self) -> TokenStream {
        match self {
            Some(t) => quote!(Some((quote t))),
            None => quote!(None),
        }
    }
}

impl Quote for TokenStream {
    fn quote(self) -> TokenStream {
        if self.is_empty() {
            return quote!(::TokenStream::empty());
        }
        let mut after_dollar = false;
        let tokens = self.into_iter().filter_map(|tree| {
            if after_dollar {
                after_dollar = false;
                match tree.kind {
                    TokenNode::Term(_) => {
                        return Some(quote!(Into::<::TokenStream>::into(
                            Clone::clone(&(unquote tree))),));
                    }
                    TokenNode::Op('$', _) => {}
                    _ => panic!("`$` must be followed by an ident or `$` in `quote!`"),
                }
            } else if let TokenNode::Op('$', _) = tree.kind {
                after_dollar = true;
                return None;
            }

            Some(quote!(::TokenStream::from((quote tree)),))
        }).collect::<TokenStream>();

        if after_dollar {
            panic!("unexpected trailing `$` in `quote!`");
        }

        quote!([(unquote tokens)].iter().cloned().collect::<::TokenStream>())
    }
}

impl Quote for TokenTree {
    fn quote(self) -> TokenStream {
        quote!(::TokenTree { span: (quote self.span), kind: (quote self.kind) })
    }
}

impl Quote for TokenNode {
    fn quote(self) -> TokenStream {
        macro_rules! gen_match {
            ($($i:ident($($arg:ident),+)),*) => {
                match self {
                    $(TokenNode::$i($($arg),+) => quote! {
                        ::TokenNode::$i($((quote $arg)),+)
                    },)*
                }
            }
        }

        gen_match! { Op(op, kind), Group(delim, tokens), Term(term), Literal(lit) }
    }
}

impl Quote for char {
    fn quote(self) -> TokenStream {
        TokenNode::Literal(Literal::character(self)).into()
    }
}

impl<'a> Quote for &'a str {
    fn quote(self) -> TokenStream {
        TokenNode::Literal(Literal::string(self)).into()
    }
}

impl Quote for usize {
    fn quote(self) -> TokenStream {
        TokenNode::Literal(Literal::integer(self as i128)).into()
    }
}

impl Quote for Term {
    fn quote(self) -> TokenStream {
        quote!(::Term::intern((quote self.as_str())))
    }
}

impl Quote for Span {
    fn quote(self) -> TokenStream {
        quote!(::Span::def_site())
    }
}

impl Quote for LiteralKind {
    fn quote(self) -> TokenStream {
        macro_rules! gen_match {
            ($($i:ident),*; $($raw:ident),*) => {
                match self {
                    $(LiteralKind::$i => quote!(::LiteralKind::$i),)*
                    $(LiteralKind::$raw(n) => quote!(::LiteralKind::$raw((quote n))),)*
                }
            }
        }

        gen_match!(DocComment, Byte, Char, Float, Str_, Integer, ByteStr; StrRaw, ByteStrRaw)
    }
}


impl Quote for Literal {
    fn quote(self) -> TokenStream {
        quote!(::Literal {
            kind: (quote self.kind),
            contents: (quote self.contents),
            suffix: (quote self.suffix),
        })
    }
}

impl Quote for Delimiter {
    fn quote(self) -> TokenStream {
        macro_rules! gen_match {
            ($($i:ident),*) => {
                match self {
                    $(Delimiter::$i => { quote!(::Delimiter::$i) })*
                }
            }
        }

        gen_match!(Parenthesis, Brace, Bracket, None)
    }
}

impl Quote for Spacing {
    fn quote(self) -> TokenStream {
        macro_rules! gen_match {
            ($($i:ident),*) => {
                match self {
                    $(Spacing::$i => { quote!(::Spacing::$i) })*
                }
            }
        }

        gen_match!(Alone, Joint)
    }
}
