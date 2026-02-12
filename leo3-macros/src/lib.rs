//! Procedural macros for Leo3 (Rust-Lean4 bindings).
//!
//! This crate provides the proc macro attributes for Leo3. The actual implementation
//! is in `leo3-macros-backend`.

use leo3_macros_backend::{build_lean_function, LeanFunctionOptions};
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
    leo3_macros_backend::derive::expand_into_lean(ast)
        .unwrap_or_compile_error()
        .into()
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
    leo3_macros_backend::derive::expand_from_lean(ast)
        .unwrap_or_compile_error()
        .into()
}

/// A proc macro used to expose Rust structs as Lean4 classes.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
///
/// #[leanclass]
/// struct Counter {
///     value: i32,
/// }
///
/// #[leanclass]
/// impl Counter {
///     fn new() -> Self {
///         Counter { value: 0 }
///     }
///
///     fn increment(&mut self) {
///         self.value += 1;
///     }
///
///     fn get(&self) -> i32 {
///         self.value
///     }
/// }
/// ```
///
/// This macro generates:
/// - An `ExternalClass` implementation for the struct
/// - FFI wrappers for each method
/// - Metadata for Lean code generation
#[proc_macro_attribute]
pub fn leanclass(attr: TokenStream, input: TokenStream) -> TokenStream {
    use leo3_macros_backend::LeanClassOptions;

    let options = parse_macro_input!(attr as LeanClassOptions);

    // Try to parse as struct first, then as impl
    if let Ok(mut item_struct) = syn::parse::<syn::ItemStruct>(input.clone()) {
        let expanded = leo3_macros_backend::build_lean_class_struct(&mut item_struct, options)
            .unwrap_or_compile_error();
        return expanded.into();
    }

    if let Ok(mut item_impl) = syn::parse::<syn::ItemImpl>(input.clone()) {
        let expanded = leo3_macros_backend::build_lean_class_impl(&mut item_impl, options)
            .unwrap_or_compile_error();
        return expanded.into();
    }

    // If neither struct nor impl, return error
    quote!(
        compile_error!("#[leanclass] can only be applied to structs or impl blocks");
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
/// #[leanmodule(name = "MyRustLib")]
/// mod my_module {
///     #[leanfn]
///     pub fn add(a: u64, b: u64) -> u64 {
///         a + b
///     }
/// }
/// ```
///
/// This generates a module initialization function `initialize_MyRustLib` that
/// can be called from Lean4 to initialize the module.
#[proc_macro_attribute]
pub fn leanmodule(attr: TokenStream, input: TokenStream) -> TokenStream {
    let item_mod = parse_macro_input!(input as syn::ItemMod);

    // Parse the module name from attributes
    let attr_str = attr.to_string();
    let module_name = if attr_str.contains("name") {
        // Extract name from `name = "..."`
        attr_str
            .split('"')
            .nth(1)
            .map(|s| s.to_string())
            .unwrap_or_else(|| item_mod.ident.to_string())
    } else if !attr_str.is_empty() {
        // Bare identifier
        attr_str.trim().to_string()
    } else {
        // Default to module name
        item_mod.ident.to_string()
    };

    let init_fn_name = syn::Ident::new(
        &format!("initialize_{}", module_name),
        proc_macro2::Span::call_site(),
    );

    let expanded = quote! {
        #item_mod

        /// Module initialization function for Lean4.
        ///
        /// This function is called by Lean when loading the module.
        #[no_mangle]
        pub unsafe extern "C" fn #init_fn_name(
            builtin: u8,
            _world: *mut ::std::ffi::c_void,
        ) -> *mut ::std::ffi::c_void {
            if builtin == 0 {
                ::leo3::ffi::lean_initialize_runtime_module();
                ::leo3::ffi::lean_initialize_thread();
            }

            // Return IO.ok ()
            let unit = ::leo3::ffi::lean_mk_unit();
            let io_ok = ::leo3::ffi::lean_except_ok(unit);
            io_ok as *mut ::std::ffi::c_void
        }
    };

    expanded.into()
}

/// A proc macro to implement Lean type classes for Rust types.
///
/// # Supported Type Classes
///
/// - `BEq` - Boolean equality (requires `fn beq(&self, other: &Self) -> bool`)
/// - `Hashable` - Hashing (requires `fn hash(&self) -> u64`)
/// - `Repr` - Representation (requires `fn repr(&self) -> String`)
/// - `ToString` - String conversion (requires `fn to_string(&self) -> String`)
/// - `Ord` - Ordering (requires `fn compare(&self, other: &Self) -> Ordering`)
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
///
/// struct Point { x: i32, y: i32 }
///
/// #[lean_instance(BEq)]
/// impl Point {
///     fn beq(&self, other: &Self) -> bool {
///         self.x == other.x && self.y == other.y
///     }
/// }
///
/// #[lean_instance(Hashable)]
/// impl Point {
///     fn hash(&self) -> u64 {
///         (self.x as u64) ^ (self.y as u64).wrapping_shl(32)
///     }
/// }
/// ```
///
/// This generates FFI functions that can be used as type class instances in Lean4.
#[proc_macro_attribute]
pub fn lean_instance(attr: TokenStream, input: TokenStream) -> TokenStream {
    use leo3_macros_backend::LeanInstanceOptions;

    let mut item_impl = parse_macro_input!(input as syn::ItemImpl);
    let options = parse_macro_input!(attr as LeanInstanceOptions);

    let expanded =
        leo3_macros_backend::build_lean_instance(&mut item_impl, options).unwrap_or_compile_error();

    expanded.into()
}

trait UnwrapOrCompileError {
    fn unwrap_or_compile_error(self) -> TokenStream2;
}

impl UnwrapOrCompileError for syn::Result<TokenStream2> {
    fn unwrap_or_compile_error(self) -> TokenStream2 {
        self.unwrap_or_else(|e| e.into_compile_error())
    }
}
