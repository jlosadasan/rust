// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Internal interface for communicating with the front-end of a compiler.
//!
//! C ABI and "generation tagging" are employed to allow safely interfacing
//! between two copies of `proc_macro` built (from the same source by different
//! compilers with potentially mismatching Rust ABIs (e.g. during bootstrap).
//!
//! FIXME(eddyb) fully implement the ABI compatibility described above.
//! So far it wouldn't be needed unless beta and nightly differ in
//! type layout or function call ABI, and it's only relevant to
//! `stage1/bin/rustc` loading and invoking proc macros it built.

use std::cell::Cell;
use std::fmt;
use std::path::PathBuf;
use std::ptr::NonNull;

use self::storage::{FromConcrete, ToConcrete};

mod generation {
    use std::cell::Cell;

    #[repr(C)]
    #[derive(Copy, Clone, PartialEq, Eq, Debug)]
    pub(super) struct Generation(usize);

    impl !Send for Generation {}
    impl !Sync for Generation {}

    impl Generation {
        pub(super) extern "C" fn next() -> Self {
            thread_local!(static NEXT: Cell<usize> = Cell::new(0));
            NEXT.with(|next| {
                let gen = next.get();
                next.set(gen.checked_add(1).expect("Generation::next overflowed counter"));
                Generation(gen)
            })
        }
    }
}

#[macro_use]
mod storage {
    use std::marker::PhantomData;
    use std::mem;
    use std::ptr::NonNull;

    use super::generation::Generation;

    #[repr(C)]
    pub(super) struct Storage<S> {
        gen: Generation,
        _marker: PhantomData<S>,
    }

    impl<S> Storage<S> {
        pub(super) fn new(next_generation: extern "C" fn() -> Generation) -> Self {
            Storage {
                gen: next_generation(),
                _marker: PhantomData,
            }
        }
    }

    pub(super) trait Concrete<S> {
        type Concrete: 'static;
    }

    pub(super) trait FromConcrete<T, U> {
        fn from_concrete(&self, x: T) -> U;
    }

    pub(super) trait ToConcrete<T, U> {
        fn to_concrete(&self, x: T) -> U;
    }

    // FIXME(eddyb) achieve ABI compatibility for these types.
    impl<S, T1, T2, U1, U2> FromConcrete<(T1, T2), (U1, U2)> for S
        where S: FromConcrete<T1, U1> + FromConcrete<T2, U2>
    {
        fn from_concrete(&self, (a, b): (T1, T2)) -> (U1, U2) {
            (self.from_concrete(a), self.from_concrete(b))
        }
    }

    // FIXME(eddyb) achieve ABI compatibility for these types.
    impl<S: FromConcrete<T, U>, T, U> FromConcrete<Option<T>, Option<U>> for S {
        fn from_concrete(&self, x: Option<T>) -> Option<U> {
            x.map(|x| self.from_concrete(x))
        }
    }

    // FIXME(eddyb) achieve ABI compatibility for these types.
    impl<S, T1, T2, U1, U2> FromConcrete<Result<T1, T2>, Result<U1, U2>> for S
        where S: FromConcrete<T1, U1> + FromConcrete<T2, U2>
    {
        fn from_concrete(&self, r: Result<T1, T2>) -> Result<U1, U2> {
            r.map(|x| self.from_concrete(x)).map_err(|e| self.from_concrete(e))
        }
    }

    macro_rules! storage_concrete_passthrough {
        ($([$($generics:tt),*] $ty:ty),*) => {
            $(
                impl<$($generics,)* S> FromConcrete<$ty, $ty> for S {
                    fn from_concrete(&self, x: $ty) -> $ty { x }
                }
                impl<$($generics,)* S> ToConcrete<$ty, $ty> for S {
                    fn to_concrete(&self, x: $ty) -> $ty { x }
                }
            )*
        }
    }

    pub(super) trait Cleanup: Sized {
        fn cleanup_boxed(boxed: Boxed<Self>);
    }

    #[repr(C)]
    pub(super) struct Boxed<T: Cleanup> {
        ptr: NonNull<*mut ()>,
        gen: Generation,
        _marker: PhantomData<T>,
    }

    impl<T: Cleanup> !Send for Boxed<T> {}
    impl<T: Cleanup> !Sync for Boxed<T> {}

    impl<T: Cleanup> Drop for Boxed<T> {
        fn drop(&mut self) {
            T::cleanup_boxed(Boxed {
                ptr: self.ptr,
                gen: self.gen,
                _marker: PhantomData,
            });
        }
    }

    impl<S, T: Cleanup + Concrete<S>> FromConcrete<Box<T::Concrete>, Boxed<T>> for Storage<S> {
        fn from_concrete(&self, x: Box<T::Concrete>) -> Boxed<T> {
            Boxed {
                ptr: Box::into_raw_non_null(x).cast(),
                gen: self.gen,
                _marker: PhantomData,
            }
        }
    }

    impl<S, T: Cleanup + Concrete<S>> ToConcrete<Boxed<T>, Box<T::Concrete>> for Storage<S> {
        fn to_concrete(&self, x: Boxed<T>) -> Box<T::Concrete> {
            assert_eq!(x.gen, self.gen);
            let ptr = x.ptr.cast::<T::Concrete>();
            mem::forget(x);
            unsafe {
                Box::from_raw(ptr.as_ptr())
            }
        }
    }

    impl<'a, S, T: Cleanup + Concrete<S>> ToConcrete<&'a Boxed<T>, &'a T::Concrete> for Storage<S> {
        fn to_concrete(&self, x: &'a Boxed<T>) -> &'a T::Concrete {
            assert_eq!(x.gen, self.gen);
            unsafe {
                &*x.ptr.cast::<T::Concrete>().as_ptr()
            }
        }
    }

    impl<'a, S, T: Cleanup + Concrete<S>> ToConcrete<&'a mut Boxed<T>, &'a mut T::Concrete>
            for Storage<S> {
        fn to_concrete(&self, x: &'a mut Boxed<T>) -> &'a mut T::Concrete {
            assert_eq!(x.gen, self.gen);
            unsafe {
                &mut *x.ptr.cast::<T::Concrete>().as_ptr()
            }
        }
    }
}

storage_concrete_passthrough! {
    [] (),
    [] bool,
    ['a] &'a str,

    // FIXME(eddyb) achieve ABI compatibility for these types.
    [] ::TokenTree,
    [] ::Span,
    [] ::Delimiter,
    [] ::LexError,

    [] PathBuf,
    // NOTE(eddyb) this will need some `extern "C" fn write`.
    ['a, 'b] &'a mut fmt::Formatter<'b>,
    [] fmt::Error
}

macro_rules! each_frontend_method {
    ($meth:ident) => {
        $meth!(fn token_stream_cleanup(&self, _stream: Self::TokenStream) -> () {});
        $meth!(fn token_stream_clone(&self, stream: &Self::TokenStream) -> Self::TokenStream {
            stream.clone()
        });
        $meth!(fn token_stream_debug(&self, stream: &Self::TokenStream,
                                     f: &mut fmt::Formatter) -> fmt::Result {
            fmt::Debug::fmt(stream, f)
        });
        $meth!(fn token_stream_display(&self, stream: &Self::TokenStream,
                                       f: &mut fmt::Formatter) -> fmt::Result {
            fmt::Display::fmt(stream, f)
        });
        $meth!(fn token_stream_empty(&self) -> Self::TokenStream;);
        $meth!(fn token_stream_is_empty(&self, stream: &Self::TokenStream) -> bool;);
        $meth!(fn token_stream_from_str(&self, src: &str)
                                        -> Result<Self::TokenStream, ::LexError>;);
        $meth!(fn token_stream_delimited(&self, span: ::Span,
                                         delimiter: ::Delimiter,
                                         delimed: Self::TokenStream)
                                         -> Self::TokenStream;);
        $meth!(fn token_stream_from_token_tree(&self, tree: ::TokenTree)
                                               -> Self::TokenStream;);
        $meth!(fn token_stream_to_token_tree(&self, stream: Self::TokenStream)
                                             -> Result<(::TokenTree, Option<Self::TokenStream>),
                                                       (::Span, (::Delimiter,
                                                                 Self::TokenStream))>;);
        $meth!(fn token_stream_trees(&self, stream: Self::TokenStream) -> Self::TokenCursor;);

        $meth!(fn token_stream_builder_cleanup(&self, _builder: Self::TokenStreamBuilder) -> () {});
        $meth!(fn token_stream_builder_new(&self) -> Self::TokenStreamBuilder;);
        $meth!(fn token_stream_builder_push(&self, builder: &mut Self::TokenStreamBuilder,
                                            stream: Self::TokenStream) -> (););
        $meth!(fn token_stream_builder_build(&self, builder: Self::TokenStreamBuilder)
                                             -> Self::TokenStream;);

        $meth!(fn token_cursor_cleanup(&self, _cursor: Self::TokenCursor) -> () {});
        $meth!(fn token_cursor_clone(&self, cursor: &Self::TokenCursor) -> Self::TokenCursor {
            cursor.clone()
        });
        $meth!(fn token_cursor_next(&self, cursor: &mut Self::TokenCursor)
                                    -> Option<Self::TokenStream>;);

        $meth!(fn source_file_cleanup(&self, _file: Self::SourceFile) -> () {});
        $meth!(fn source_file_clone(&self, file: &Self::SourceFile) -> Self::SourceFile {
            file.clone()
        });
        $meth!(fn source_file_eq(&self, file1: &Self::SourceFile,
                                 file2: &Self::SourceFile) -> bool;);
        $meth!(fn source_file_path(&self, file: &Self::SourceFile) -> PathBuf;);
        $meth!(fn source_file_is_real(&self, file: &Self::SourceFile) -> bool;);

        $meth!(fn span_source_file(&self, span: ::Span) -> Self::SourceFile;);
    }
}

macro_rules! define_frontend_trait_method {
    ($($m:tt)*) => ($($m)*)
}
pub trait FrontendInterface {
    type TokenStream: 'static + Clone + fmt::Debug + fmt::Display;
    type TokenStreamBuilder: 'static;
    type TokenCursor: 'static + Clone;
    type SourceFile: 'static + Clone;
    each_frontend_method!(define_frontend_trait_method);
}

macro_rules! define_boxed {
    ($($name:ident { cleanup: $cleanup:ident }),*) => {
        $(
            #[repr(C)]
            pub(crate) struct $name(storage::Boxed<$name>);
            impl<F: FrontendInterface> storage::Concrete<F> for $name {
                type Concrete = F::$name;
            }
            impl storage::Cleanup for $name {
                fn cleanup_boxed(boxed: storage::Boxed<Self>) {
                    Frontend.$cleanup($name(boxed))
                }
            }
            impl<S, T: 'static> FromConcrete<T, $name> for storage::Storage<S>
                where $name: storage::Concrete<S, Concrete = T>
            {
                fn from_concrete(&self, x: T) -> $name {
                    $name(self.from_concrete(Box::new(x)))
                }
            }
            impl<S, T: 'static> ToConcrete<$name, T> for storage::Storage<S>
                where $name: storage::Concrete<S, Concrete = T>
            {
                fn to_concrete(&self, x: $name) -> T {
                    *self.to_concrete(x.0)
                }
            }
            impl<'a, S, T: 'static> ToConcrete<&'a $name, &'a T> for storage::Storage<S>
                where $name: storage::Concrete<S, Concrete = T>
            {
                fn to_concrete(&self, x: &'a $name) -> &'a T {
                    self.to_concrete(&x.0)
                }
            }
            impl<'a, S, T: 'static> ToConcrete<&'a mut $name, &'a mut T> for storage::Storage<S>
                where $name: storage::Concrete<S, Concrete = T>
            {
                fn to_concrete(&self, x: &'a mut $name) -> &'a mut T {
                    self.to_concrete(&mut x.0)
                }
            }
        )*
    }
}

define_boxed! {
    TokenStream {
        cleanup: token_stream_cleanup
    },
    TokenStreamBuilder {
        cleanup: token_stream_builder_cleanup
    },
    TokenCursor {
        cleanup: token_cursor_cleanup
    },
    SourceFile {
        cleanup: source_file_cleanup
    }
}

impl Clone for TokenStream {
    fn clone(&self) -> Self {
        Frontend.token_stream_clone(self)
    }
}

impl fmt::Debug for TokenStream {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Frontend.token_stream_debug(self, f)
    }
}

impl fmt::Display for TokenStream {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Frontend.token_stream_display(self, f)
    }
}

impl Clone for TokenCursor {
    fn clone(&self) -> Self {
        Frontend.token_cursor_clone(self)
    }
}

impl Clone for SourceFile {
    fn clone(&self) -> Self {
        Frontend.source_file_clone(self)
    }
}

pub(crate) struct Frontend;

macro_rules! define_frontend_current_method {
    (fn $name:ident(&$self:ident $(, $arg:ident: $arg_ty:ty)*) -> $ret_ty:ty
     $($body:block)* $(;)*) => {
        fn $name(&$self $(, $arg: $arg_ty)*) -> $ret_ty {
            with_current_frontend(|current| current.$name($($arg),*))
        }
    }
}
impl FrontendInterface for Frontend {
    type TokenStream = TokenStream;
    type TokenStreamBuilder = TokenStreamBuilder;
    type TokenCursor = TokenCursor;
    type SourceFile = SourceFile;
    each_frontend_method!(define_frontend_current_method);
}

// FIXME(eddyb) generate a manual C ABI vtable instead.
type CurrentFrontend<'a> = FrontendInterface<
    TokenStream = TokenStream,
    TokenStreamBuilder = TokenStreamBuilder,
    TokenCursor = TokenCursor,
    SourceFile = SourceFile,
> + 'a;

// Emulate scoped_thread_local!() here essentially
thread_local! {
    static CURRENT_FRONTEND: Cell<Option<NonNull<CurrentFrontend<'static>>>> = Cell::new(None);
}

pub fn has_current_frontend() -> bool {
    CURRENT_FRONTEND.with(|p| p.get().is_some())
}

fn with_current_frontend<F, R>(f: F) -> R
    where F: FnOnce(&CurrentFrontend) -> R
{
    let p = CURRENT_FRONTEND.with(|p| p.get());
    assert!(!p.is_none(), "proc_macro::bridge::with_current_frontend() called \
                           before set_current_frontend()!");
    f(unsafe { p.unwrap().as_ref() })
}

fn set_current_frontend<F, R>(frontend: &CurrentFrontend, f: F) -> R
    where F: FnOnce() -> R
{
    struct Reset { prev: Option<NonNull<CurrentFrontend<'static>>> }

    impl Drop for Reset {
        fn drop(&mut self) {
            CURRENT_FRONTEND.with(|p| p.set(self.prev));
        }
    }

    CURRENT_FRONTEND.with(|p| {
        let _reset = Reset { prev: p.get() };
        p.set(NonNull::new(frontend as *const _ as *mut _));
        f()
    })
}

fn erase_concrete_frontend<F, G, R>(ng: extern "C" fn() -> generation::Generation,
                                    frontend: F,
                                    f: G) -> R
    where F: FrontendInterface,
          G: FnOnce(&CurrentFrontend, &storage::Storage<F>) -> R
{
    struct EraseConcrete<F: FrontendInterface> {
        storage: storage::Storage<F>,
        concrete: F
    }

    macro_rules! define_frontend_erase_concrete_method {
        (fn $name:ident(&$self:ident $(, $arg:ident: $arg_ty:ty)*) -> $ret_ty:ty
        $($body:block)* $(;)*) => {
            fn $name(&$self $(, $arg: $arg_ty)*) -> $ret_ty {
                let r = $self.concrete.$name($($self.storage.to_concrete($arg)),*);
                $self.storage.from_concrete(r)
            }
        }
    }
    impl<F: FrontendInterface> FrontendInterface for EraseConcrete<F> {
        type TokenStream = TokenStream;
        type TokenStreamBuilder = TokenStreamBuilder;
        type TokenCursor = TokenCursor;
        type SourceFile = SourceFile;
        each_frontend_method!(define_frontend_erase_concrete_method);
    }

    let frontend = EraseConcrete {
        storage: storage::Storage::new(ng),
        concrete: frontend
    };
    f(&frontend, &frontend.storage)
}

/// A function taking one `TokenStream` and returning another,
/// which may be using a different `proc_macro` from the one
/// used by the frontend, but can be interacted with compatibly.
#[repr(C)]
pub struct Expand1 {
    next_generation: extern "C" fn() -> generation::Generation,
    data: *const (),
    run: unsafe extern "C" fn(*const (), &&CurrentFrontend, TokenStream)
                              -> TokenStream,
}

impl !Send for Expand1 {}
impl !Sync for Expand1 {}

impl Expand1 {
    pub fn new<F>(f: &'static F) -> Self
        where F: Fn(::TokenStream) -> ::TokenStream
    {
        unsafe extern "C" fn run<F>(f: *const (),
                                    frontend: &&CurrentFrontend,
                                    input: TokenStream) -> TokenStream
            where F: Fn(::TokenStream) -> ::TokenStream
        {
            let f = &*(f as *const F);
            set_current_frontend(*frontend, || {
                f(::TokenStream(input)).0
            })
        }
        Expand1 {
            next_generation: generation::Generation::next,
            data: f as *const _ as *const (),
            run: run::<F>
        }
    }

    pub fn run<F>(&self, frontend: F, input: F::TokenStream) -> F::TokenStream
        where F: FrontendInterface
    {
        erase_concrete_frontend(self.next_generation, frontend, |frontend, storage| {
            let input = storage.from_concrete(input);
            let output = unsafe {
                (self.run)(self.data, &frontend, input)
            };
            storage.to_concrete(output)
        })
    }
}

/// A function taking two `TokenStream`s and returning another,
/// which may be using a different `proc_macro` from the one
/// used by the frontend, but can be interacted with compatibly.
#[repr(C)]
pub struct Expand2 {
    next_generation: extern "C" fn() -> generation::Generation,
    data: *const (),
    run: unsafe extern "C" fn(*const (), &&CurrentFrontend, TokenStream, TokenStream)
                              -> TokenStream,
}

impl !Send for Expand2 {}
impl !Sync for Expand2 {}

impl Expand2 {
    pub fn new<F>(f: &'static F) -> Self
        where F: Fn(::TokenStream, ::TokenStream) -> ::TokenStream
    {
        unsafe extern "C" fn run<F>(f: *const (),
                                    frontend: &&CurrentFrontend,
                                    input: TokenStream,
                                    input2: TokenStream) -> TokenStream
            where F: Fn(::TokenStream, ::TokenStream) -> ::TokenStream
        {
            let f = &*(f as *const F);
            set_current_frontend(*frontend, || {
                f(::TokenStream(input), ::TokenStream(input2)).0
            })
        }
        Expand2 {
            next_generation: generation::Generation::next,
            data: f as *const _ as *const (),
            run: run::<F>
        }
    }

    pub fn run<F>(&self, frontend: F, input: F::TokenStream, input2: F::TokenStream)
                  -> F::TokenStream
        where F: FrontendInterface
    {
        erase_concrete_frontend(self.next_generation, frontend, |frontend, storage| {
            let input = storage.from_concrete(input);
            let input2 = storage.from_concrete(input2);
            let output = unsafe {
                (self.run)(self.data, &frontend, input, input2)
            };
            storage.to_concrete(output)
        })
    }
}

// FIXME(eddyb) use a C ABI wrapper instead of `&mut Registry` in the registrar.
pub trait Registry {
    fn register_custom_derive(&mut self,
                              trait_name: &str,
                              expand: Expand1,
                              attributes: &[&'static str]);

    fn register_attr_proc_macro(&mut self,
                                name: &str,
                                expand: Expand2);

    fn register_bang_proc_macro(&mut self,
                                name: &str,
                                expand: Expand1);
}
