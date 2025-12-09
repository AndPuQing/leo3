//! Procedural macros for Leo3 (Rust-Lean4 bindings).
//!
//! This crate provides the proc macro attributes for Leo3. The actual implementation
//! is in `leo3-macros-backend`.

use leo3_macros_backend::{
    build_lean_function,
    derive::{expand_from_lean, expand_into_lean},
    LeanFunctionOptions,
};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::parse_macro_input;

/// A proc macro used to expose Rust functions to Lean4.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
///
/// #[leanfn]
/// fn add(a: u64, b: u64) -> u64 {
///     a + b
/// }
/// ```
///
/// Functions annotated with `#[leanfn]` can also be annotated with the following options:
///
/// | Annotation | Description |
/// | :- | :- |
/// | `#[leo3(name = "...")]` | Defines the name of the function in Lean4. |
/// | `#[leo3(crate = "leo3")]` | Defines the path to Leo3 to use in generated code. |
///
/// # Name Override
///
/// By default, the Lean4 function name will match the Rust function name.
/// Use `#[leo3(name = "my_name")]` to override it.
#[proc_macro_attribute]
pub fn leanfn(attr: TokenStream, input: TokenStream) -> TokenStream {
    let mut ast = parse_macro_input!(input as syn::ItemFn);
    let options = parse_macro_input!(attr as LeanFunctionOptions);

    let expanded = build_lean_function(&mut ast, options).unwrap_or_compile_error();

    expanded.into()
}

/// Derive macro for automatic `IntoLean` trait implementation.
///
/// Automatically generates an implementation of the `IntoLean` trait for converting
/// Rust types into Lean constructors.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
///
/// #[derive(IntoLean)]
/// struct Point {
///     x: u64,
///     y: u64,
/// }
/// ```
///
/// This will generate an `IntoLean` implementation that converts the struct into
/// a Lean constructor with tag 0 and two fields.
///
/// # Supported Types
///
/// - Structs with named fields
/// - Structs with unnamed fields (tuple structs)
/// - Enums with unit variants
/// - Enums with tuple/struct variants
/// - Generic types (with appropriate trait bounds)
///
/// # Requirements
///
/// All field types must implement `IntoLean<'l>`.
///
/// # Attributes
///
/// The derive supports the following attributes:
/// - `#[lean(transparent)]` - For newtype wrappers, skips the constructor layer
/// - `#[lean(skip)]` - Excludes a field from conversion
/// - `#[lean(with = "path")]` - Uses a custom conversion function
/// - `#[lean(rename = "name")]` - Custom field name for error messages
/// - `#[lean(tag = n)]` - Explicit constructor tag for enum variants
#[proc_macro_derive(IntoLean, attributes(lean))]
pub fn derive_into_lean(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as syn::DeriveInput);
    expand_into_lean(ast).unwrap_or_compile_error().into()
}

/// Derive macro for automatic `FromLean` trait implementation.
///
/// Automatically generates an implementation of the `FromLean` trait for extracting
/// Rust types from Lean constructors.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
///
/// #[derive(FromLean)]
/// struct Point {
///     x: u64,
///     y: u64,
/// }
/// ```
///
/// This will generate a `FromLean` implementation that extracts the struct from
/// a Lean constructor with tag 0 and two fields.
///
/// # Supported Types
///
/// - Structs with named fields
/// - Structs with unnamed fields (tuple structs)
/// - Enums with unit variants
/// - Enums with tuple/struct variants
/// - Generic types (with appropriate trait bounds)
///
/// # Requirements
///
/// All field types must implement `FromLean<'l>`.
///
/// # Attributes
///
/// The derive supports the following attributes:
/// - `#[lean(transparent)]` - For newtype wrappers, extracts directly from inner type
/// - `#[lean(skip)]` - Excludes a field from extraction, uses Default::default()
/// - `#[lean(default)]` - Uses Default::default() if extraction fails
/// - `#[lean(with = "path")]` - Uses a custom extraction function
/// - `#[lean(rename = "name")]` - Custom field name for error messages
/// - `#[lean(tag = n)]` - Explicit constructor tag for enum variants
#[proc_macro_derive(FromLean, attributes(lean))]
pub fn derive_from_lean(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as syn::DeriveInput);
    expand_from_lean(ast).unwrap_or_compile_error().into()
}

/// A proc macro used to expose Rust structs as Lean4 classes.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
///
/// #[leanclass]
/// struct Point {
///     x: f64,
///     y: f64,
/// }
/// ```
///
/// This macro is planned for future implementation.
#[proc_macro_attribute]
pub fn leanclass(_attr: TokenStream, input: TokenStream) -> TokenStream {
    let input2: TokenStream2 = input.into();
    quote!(
        compile_error!("#[leanclass] is not yet implemented. Coming soon!");
        #input2
    )
    .into()
}

/// A proc macro used to create Lean4 modules.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
///
/// #[leanmodule]
/// fn my_module(m: &mut LeanModule) {
///     m.add_function(wrap_leanfn!(add))?;
/// }
/// ```
///
/// This macro is planned for future implementation.
#[proc_macro_attribute]
pub fn leanmodule(_attr: TokenStream, input: TokenStream) -> TokenStream {
    let input2: TokenStream2 = input.into();
    quote!(
        compile_error!("#[leanmodule] is not yet implemented. Coming soon!");
        #input2
    )
    .into()
}

trait UnwrapOrCompileError {
    fn unwrap_or_compile_error(self) -> TokenStream2;
}

impl UnwrapOrCompileError for syn::Result<TokenStream2> {
    fn unwrap_or_compile_error(self) -> TokenStream2 {
        self.unwrap_or_else(|e| e.into_compile_error())
    }
}
