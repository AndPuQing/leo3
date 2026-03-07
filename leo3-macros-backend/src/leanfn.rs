//! Implementation of the `#[leanfn]` macro.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
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

/// Information extracted from a function signature
struct FunctionInfo {
    rust_name: syn::Ident,
    lean_name: String,
    params: Vec<(syn::Ident, syn::Type)>,
    return_type: syn::Type,
    #[allow(unused)]
    vis: syn::Visibility,
}

/// Analyze a function signature and extract relevant information
fn analyze_function(
    func: &syn::ItemFn,
    options: &LeanFunctionOptions,
) -> syn::Result<FunctionInfo> {
    let rust_name = func.sig.ident.clone();
    let lean_name = options
        .common
        .name
        .as_ref()
        .map(|s| s.value())
        .unwrap_or_else(|| rust_name.to_string());

    // Extract parameters
    let mut params = Vec::new();
    for input in &func.sig.inputs {
        match input {
            syn::FnArg::Typed(pat_type) => {
                let name = match &*pat_type.pat {
                    syn::Pat::Ident(ident) => ident.ident.clone(),
                    _ => {
                        return Err(syn::Error::new_spanned(
                            pat_type,
                            "Only simple parameter patterns are supported",
                        ))
                    }
                };
                params.push((name, (*pat_type.ty).clone()));
            }
            syn::FnArg::Receiver(_) => {
                return Err(syn::Error::new_spanned(
                    input,
                    "Methods with `self` are not supported. Use standalone functions.",
                ))
            }
        }
    }

    // Extract return type
    let return_type = match &func.sig.output {
        syn::ReturnType::Default => syn::parse_quote! { () },
        syn::ReturnType::Type(_, ty) => (**ty).clone(),
    };

    // Check for generics
    if !func.sig.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &func.sig.generics,
            "Generic functions are not supported yet",
        ));
    }

    Ok(FunctionInfo {
        rust_name,
        lean_name,
        params,
        return_type,
        vis: func.vis.clone(),
    })
}

/// Generate parameter conversion code
fn generate_param_conversions(
    params: &[(syn::Ident, syn::Type)],
    leo3_crate: &TokenStream,
) -> Vec<TokenStream> {
    params
        .iter()
        .enumerate()
        .map(|(i, (name, ty))| {
            let arg_name = format_ident!("arg{}", i);
            quote! {
                let #name = {
                    let bound = #leo3_crate::LeanBound::<_>::from_owned_ptr(lean, #arg_name);
                    <#ty as #leo3_crate::conversion::FromLean>::from_lean(&bound)
                        .map_err(|e| #leo3_crate::LeanError::conversion(&format!(
                            "Failed to convert `{}` from Lean to Rust: {}",
                            stringify!(#name),
                            e
                        )))?
                };
            }
        })
        .collect()
}

/// Generate result conversion code
fn generate_result_conversion(return_type: &syn::Type, leo3_crate: &TokenStream) -> TokenStream {
    // Check if return type is unit ()
    if matches!(return_type, syn::Type::Tuple(t) if t.elems.is_empty()) {
        // For unit return type, return a unit Lean object (constructor 0 with 0 fields)
        quote! {
            Ok(unsafe {
                #leo3_crate::ffi::lean_alloc_ctor(0, 0, 0)
            })
        }
    } else {
        quote! {
            {
                let lean_result = <#return_type as #leo3_crate::conversion::IntoLean>::into_lean(result, lean)
                    .map_err(|e| #leo3_crate::LeanError::conversion(&format!(
                        "Failed to convert Rust result to Lean: {}",
                        e
                    )))?;
                Ok(lean_result.into_ptr())
            }
        }
    }
}

/// Generate the FFI wrapper function with panic boundary
fn generate_ffi_wrapper(info: &FunctionInfo, leo3_crate: &TokenStream) -> TokenStream {
    let lean_name = &info.lean_name;
    // Internal name to avoid conflicts with imported names
    let internal_ffi_name = format_ident!("__ffi_{}", lean_name);

    let param_count = info.params.len();
    let ffi_params: Vec<_> = (0..param_count)
        .map(|i| {
            let arg_name = format_ident!("arg{}", i);
            quote! { #arg_name: #leo3_crate::ffi::object::lean_obj_arg }
        })
        .collect();

    let wrapper_call_args: Vec<_> = (0..param_count)
        .map(|i| {
            let arg_name = format_ident!("arg{}", i);
            quote! { #arg_name }
        })
        .collect();

    quote! {
        #[no_mangle]
        #[export_name = #lean_name]
        pub unsafe extern "C" fn #internal_ffi_name(
            #(#ffi_params),*
        ) -> #leo3_crate::ffi::object::lean_obj_res {
            // Panic safety boundary - catch any panics and convert to Lean panic
            match ::std::panic::catch_unwind(::std::panic::AssertUnwindSafe(|| {
                __ffi_try_wrapper(#(#wrapper_call_args),*)
            })) {
                Ok(Ok(ptr)) => ptr,
                Ok(Err(err)) => {
                    let lean = #leo3_crate::Lean::assume_initialized();
                    #leo3_crate::__private::lean_panic_message(lean, &err.to_string())
                }
                Err(payload) => {
                    let lean = #leo3_crate::Lean::assume_initialized();
                    let message = #leo3_crate::__private::panic_payload_message(payload.as_ref());
                    #leo3_crate::__private::lean_panic_message(lean, &message)
                }
            }
        }
    }
}

/// Generate the conversion wrapper (separate for testing)
fn generate_conversion_wrapper(info: &FunctionInfo, leo3_crate: &TokenStream) -> TokenStream {
    let rust_name = &info.rust_name;
    let param_count = info.params.len();

    let ffi_params: Vec<_> = (0..param_count)
        .map(|i| {
            let arg_name = format_ident!("arg{}", i);
            quote! { #arg_name: #leo3_crate::ffi::object::lean_obj_arg }
        })
        .collect();

    let param_conversions = generate_param_conversions(&info.params, leo3_crate);
    let result_conversion = generate_result_conversion(&info.return_type, leo3_crate);

    let call_args: Vec<_> = info
        .params
        .iter()
        .map(|(name, _)| quote! { #name })
        .collect();

    // Check if return type is unit
    let call_and_return = if matches!(info.return_type, syn::Type::Tuple(ref t) if t.elems.is_empty())
    {
        quote! {
            #rust_name(#(#call_args),*);
            #result_conversion
        }
    } else {
        quote! {
            let result = #rust_name(#(#call_args),*);
            #result_conversion
        }
    };

    quote! {
        pub(crate) unsafe fn __ffi_try_wrapper(
            #(#ffi_params),*
        ) -> #leo3_crate::err::LeanResult<#leo3_crate::ffi::object::lean_obj_res> {
            // Get Lean token (proves runtime is initialized)
            let lean = #leo3_crate::Lean::assume_initialized();

            // Convert arguments from Lean to Rust
            #(#param_conversions)*

            // Call the original function and convert result
            #call_and_return
        }
    }
}

/// Generate metadata
fn generate_metadata(info: &FunctionInfo, leo3_crate: &TokenStream) -> TokenStream {
    let lean_name = &info.lean_name;

    quote! {
        pub const LEAN_NAME: &str = #lean_name;

        #[doc(hidden)]
        pub fn __leo3_metadata() -> #leo3_crate::LeanFunctionMetadata {
            #leo3_crate::LeanFunctionMetadata {
                name: LEAN_NAME,
            }
        }
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
    let info = analyze_function(func, &options)?;
    let leo3_crate = get_leo3_crate(options.common.krate.as_ref());

    let rust_name = &info.rust_name;
    let lean_name_ident = format_ident!("{}", &info.lean_name);
    let wrapper_module = format_ident!("__leo3_leanfn_{}", rust_name);
    let metadata_name = format_ident!("__leo3_metadata_{}", rust_name);

    // Generate wrapper components
    let ffi_wrapper = generate_ffi_wrapper(&info, &leo3_crate);
    let conversion_wrapper = generate_conversion_wrapper(&info, &leo3_crate);
    let metadata = generate_metadata(&info, &leo3_crate);

    // Only re-export FFI function if the lean name is different from rust name
    let internal_ffi_name = format_ident!("__ffi_{}", &info.lean_name);
    let ffi_reexport = if *rust_name != info.lean_name {
        quote! {
            // Re-export FFI function with its Lean name (for FFI calls)
            #[allow(non_snake_case)]
            pub use #wrapper_module::#internal_ffi_name as #lean_name_ident;
        }
    } else {
        quote! {}
    };

    // Remove ALL attributes from the function to ensure clean output
    func.attrs.clear();

    // Keep the original function as-is (without any attributes)
    Ok(quote! {
        // Original function stays at top level - unchanged
        #func

        // Hidden module to hold FFI wrappers and metadata (PyO3 pattern)
        #[allow(non_snake_case)]
        mod #wrapper_module {
            use super::*;

            // FFI entry point with panic boundary
            #ffi_wrapper

            // Conversion logic (testable separately)
            #conversion_wrapper

            // Metadata
            #metadata
        }

        // Re-export FFI function if name is different
        #ffi_reexport

        // Re-export metadata with unique name
        #[doc(hidden)]
        #[allow(non_snake_case)]
        pub use #wrapper_module::__leo3_metadata as #metadata_name;
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CommonOptions;

    #[test]
    fn generated_wrapper_avoids_expect_for_boundary_failures() {
        let mut func: syn::ItemFn = syn::parse_quote! {
            fn demo(x: u64) -> u64 {
                x
            }
        };

        let tokens = build_lean_function(
            &mut func,
            LeanFunctionOptions {
                common: CommonOptions::default(),
            },
        )
        .expect("leanfn expansion should succeed");

        let rendered = tokens.to_string();
        assert!(rendered.contains("__private :: lean_panic_message"));
        assert!(rendered.contains("__private :: panic_payload_message"));
        assert!(rendered.contains("Failed to convert"));
        assert!(rendered.contains("Failed to convert Rust result to Lean"));
        assert!(!rendered.contains(".expect("));
        assert!(!rendered.contains(". expect ("));
    }
}
