//! Implementation of the `#[leanfn]` macro.

use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::Parse;

use crate::{get_leo3_crate, CommonOptions};

/// Options for the `#[leanfn]` attribute
pub struct LeanFunctionOptions {
    pub common: CommonOptions,
}

impl Parse for LeanFunctionOptions {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Self {
            common: input.parse()?,
        })
    }
}

/// Build the implementation for a `#[leanfn]` annotated function.
///
/// This generates:
/// - A wrapper function that handles Lean FFI calling conventions
/// - Type conversions between Rust and Lean types
/// - Error handling
pub fn build_lean_function(
    func: &mut syn::ItemFn,
    options: LeanFunctionOptions,
) -> syn::Result<TokenStream> {
    let rust_name = &func.sig.ident;
    let lean_name = options
        .common
        .name
        .as_ref()
        .map(|s| s.value())
        .unwrap_or_else(|| rust_name.to_string());

    let leo3_crate = get_leo3_crate(options.common.krate.as_ref());

    // For now, generate a simple stub that will be expanded later
    // This demonstrates the structure without full implementation
    let wrapper_name = syn::Ident::new(&format!("__leo3_leanfn_{}", rust_name), rust_name.span());

    Ok(quote! {
        // Hidden module to hold metadata (similar to pyo3's pattern)
        mod #wrapper_name {
            use super::*;

            // TODO: Generate actual FFI wrapper
            // This will include:
            // - Converting lean_obj_arg parameters to Rust types
            // - Calling the original function
            // - Converting result back to lean_obj_res
            // - Error handling

            pub const LEAN_NAME: &str = #lean_name;

            #[doc(hidden)]
            pub fn __leo3_metadata() -> #leo3_crate::LeanFunctionMetadata {
                #leo3_crate::LeanFunctionMetadata {
                    name: LEAN_NAME,
                    // Additional metadata will go here
                }
            }
        }

        // Re-export for wrapping macros
        #[doc(hidden)]
        pub use #wrapper_name::__leo3_metadata;
    })
}
