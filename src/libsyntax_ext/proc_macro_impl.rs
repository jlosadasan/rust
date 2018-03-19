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

use errors::FatalError;

use syntax::codemap::Span;
use syntax::ext::base::*;
use syntax::tokenstream::TokenStream;
use syntax::ext::base;

pub struct AttrProcMacro {
    pub inner: ::proc_macro::bridge::Expand2,
}

impl base::AttrProcMacro for AttrProcMacro {
    fn expand<'cx>(&self,
                   ecx: &'cx mut ExtCtxt,
                   span: Span,
                   annotation: TokenStream,
                   annotated: TokenStream)
                   -> TokenStream {
        let res = panic::catch_unwind(panic::AssertUnwindSafe(|| {
            self.inner.run(::proc_macro::rustc::Rustc::new(ecx), annotation, annotated)
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
    pub inner: ::proc_macro::bridge::Expand1,
}

impl base::ProcMacro for BangProcMacro {
    fn expand<'cx>(&self,
                   ecx: &'cx mut ExtCtxt,
                   span: Span,
                   input: TokenStream)
                   -> TokenStream {
        let res = panic::catch_unwind(panic::AssertUnwindSafe(|| {
            self.inner.run(::proc_macro::rustc::Rustc::new(ecx), input)
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
