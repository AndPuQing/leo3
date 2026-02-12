//! Implementation of the `#[leanclass]` macro.
//!
//! This macro generates both Rust and Lean code for exposing Rust structs
//! as Lean external classes. In addition to the Rust FFI wrappers and
//! `ExternalClass` trait implementation, the macro produces string constants
//! containing the corresponding Lean source code (`opaque` type declarations
//! and `@[extern]`-annotated function signatures) that can be embedded into
//! `.lean` files.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::parse::Parse;

use crate::{get_leo3_crate, CommonOptions};

/// Options for the `#[leanclass]` attribute
pub struct LeanClassOptions {
    pub common: CommonOptions,
}

impl Parse for LeanClassOptions {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Self {
            common: input.parse()?,
        })
    }
}

/// Information about a struct
struct StructInfo {
    name: syn::Ident,
    generics: syn::Generics,
    _vis: syn::Visibility,
}

/// Information about a method
struct MethodInfo {
    name: syn::Ident,
    lean_name: String,
    receiver: MethodReceiver,
    params: Vec<(syn::Ident, syn::Type)>,
    return_type: syn::Type,
}

/// Type of method receiver
#[derive(Debug, Clone)]
enum MethodReceiver {
    None,   // Static method (no self)
    Ref,    // &self
    MutRef, // &mut self
    Owned,  // self
}

/// Build the #\[leanclass\] expansion for a struct
pub fn build_lean_class_struct(
    item: &mut syn::ItemStruct,
    options: LeanClassOptions,
) -> syn::Result<TokenStream> {
    let leo3_crate = get_leo3_crate(options.common.krate.as_ref());

    let struct_info = StructInfo {
        name: item.ident.clone(),
        generics: item.generics.clone(),
        _vis: item.vis.clone(),
    };

    // Check for generics
    if !struct_info.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &struct_info.generics,
            "#[leanclass] does not support generic types yet",
        ));
    }

    // Generate ExternalClass implementation
    let external_class_impl = generate_external_class_impl(&struct_info, &leo3_crate)?;

    // Generate Lean code metadata
    let lean_code_gen = generate_lean_code_metadata(&struct_info, &[], &leo3_crate);

    // Keep original struct
    let original_struct = quote! { #item };

    Ok(quote! {
        #original_struct
        #external_class_impl
        #lean_code_gen
    })
}

/// Build the #\[leanclass\] expansion for an impl block
pub fn build_lean_class_impl(
    item: &mut syn::ItemImpl,
    options: LeanClassOptions,
) -> syn::Result<TokenStream> {
    let leo3_crate = get_leo3_crate(options.common.krate.as_ref());

    // Extract the struct name from the impl
    let struct_name = match &*item.self_ty {
        syn::Type::Path(type_path) => {
            if let Some(segment) = type_path.path.segments.last() {
                segment.ident.clone()
            } else {
                return Err(syn::Error::new_spanned(
                    &item.self_ty,
                    "Could not extract struct name from impl",
                ));
            }
        }
        _ => {
            return Err(syn::Error::new_spanned(
                &item.self_ty,
                "#[leanclass] impl must be for a simple struct type",
            ));
        }
    };

    // Check for generics
    if !item.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &item.generics,
            "#[leanclass] does not support generic impl blocks yet",
        ));
    }

    // Extract methods
    let mut methods = Vec::new();
    for impl_item in &item.items {
        if let syn::ImplItem::Fn(method) = impl_item {
            let method_info = analyze_method(method, &struct_name)?;
            methods.push(method_info);
        }
    }

    // Generate FFI wrapper functions for each method
    let mut ffi_functions = Vec::new();
    for method in &methods {
        let ffi_fn = generate_method_ffi_wrapper(method, &struct_name, &leo3_crate)?;
        ffi_functions.push(ffi_fn);
    }

    // Generate Lean code metadata
    let lean_code_gen =
        generate_lean_code_metadata_for_methods(&struct_name, &methods, &leo3_crate);

    // Keep original impl
    let original_impl = quote! { #item };

    Ok(quote! {
        #original_impl
        #(#ffi_functions)*
        #lean_code_gen
    })
}

/// Analyze a method signature and extract relevant information
fn analyze_method(method: &syn::ImplItemFn, struct_name: &syn::Ident) -> syn::Result<MethodInfo> {
    let method_name = method.sig.ident.clone();

    // Determine lean name: StructName.method_name
    let lean_name = format!("{}.{}", struct_name, method_name);

    // Determine receiver type
    let mut receiver = MethodReceiver::None;
    let mut param_start_index = 0;

    if let Some(first_arg) = method.sig.inputs.first() {
        match first_arg {
            syn::FnArg::Receiver(recv) => {
                param_start_index = 1;
                receiver = if recv.mutability.is_some() {
                    MethodReceiver::MutRef
                } else if recv.reference.is_some() {
                    MethodReceiver::Ref
                } else {
                    MethodReceiver::Owned
                };
            }
            syn::FnArg::Typed(_) => {
                // No self, static method
                receiver = MethodReceiver::None;
            }
        }
    }

    // Extract parameters (excluding self)
    let mut params = Vec::new();
    for input in method.sig.inputs.iter().skip(param_start_index) {
        if let syn::FnArg::Typed(pat_type) = input {
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
    }

    // Extract return type
    let return_type = match &method.sig.output {
        syn::ReturnType::Default => syn::parse_quote! { () },
        syn::ReturnType::Type(_, ty) => (**ty).clone(),
    };

    // Check for generics
    if !method.sig.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &method.sig.generics,
            "Generic methods are not supported yet",
        ));
    }

    Ok(MethodInfo {
        name: method_name,
        lean_name,
        receiver,
        params,
        return_type,
    })
}

/// Generate the ExternalClass trait implementation
fn generate_external_class_impl(
    struct_info: &StructInfo,
    leo3_crate: &TokenStream,
) -> syn::Result<TokenStream> {
    let struct_name = &struct_info.name;
    let class_name_str = struct_name.to_string();

    Ok(quote! {
        impl #leo3_crate::external::ExternalClass for #struct_name {
            fn class_name() -> &'static str {
                #class_name_str
            }
        }
    })
}

/// Generate FFI wrapper for a method
fn generate_method_ffi_wrapper(
    method: &MethodInfo,
    struct_name: &syn::Ident,
    leo3_crate: &TokenStream,
) -> syn::Result<TokenStream> {
    let method_name = &method.name;
    let lean_name = &method.lean_name;
    let ffi_name = format_ident!("__lean_ffi_{}_{}", struct_name, method_name);

    match &method.receiver {
        MethodReceiver::None => {
            // Static method
            generate_static_method_wrapper(method, struct_name, &ffi_name, lean_name, leo3_crate)
        }
        MethodReceiver::Ref => {
            // &self method
            generate_ref_method_wrapper(method, struct_name, &ffi_name, lean_name, leo3_crate)
        }
        MethodReceiver::MutRef => {
            // &mut self method - needs special handling for Lean's pure functional semantics
            generate_mut_ref_method_wrapper(method, struct_name, &ffi_name, lean_name, leo3_crate)
        }
        MethodReceiver::Owned => {
            // self method (consuming)
            generate_owned_method_wrapper(method, struct_name, &ffi_name, lean_name, leo3_crate)
        }
    }
}

/// Generate wrapper for static methods (no self)
fn generate_static_method_wrapper(
    method: &MethodInfo,
    struct_name: &syn::Ident,
    ffi_name: &syn::Ident,
    lean_name: &str,
    leo3_crate: &TokenStream,
) -> syn::Result<TokenStream> {
    let method_name = &method.name;
    let params = &method.params;
    let return_type = &method.return_type;

    // Generate FFI parameters
    let param_count = params.len();
    let ffi_params: Vec<_> = (0..param_count)
        .map(|i| {
            let arg_name = format_ident!("arg{}", i);
            quote! { #arg_name: #leo3_crate::ffi::object::lean_obj_arg }
        })
        .collect();

    // Generate parameter conversions
    let param_conversions: Vec<_> = params
        .iter()
        .enumerate()
        .map(|(i, (name, ty))| {
            let arg_name = format_ident!("arg{}", i);
            quote! {
                let #name = {
                    let bound = #leo3_crate::LeanBound::<_>::from_owned_ptr(lean, #arg_name);
                    <#ty as #leo3_crate::conversion::FromLean>::from_lean(&bound)
                        .expect(&format!("Failed to convert {} from Lean to Rust", stringify!(#name)))
                };
            }
        })
        .collect();

    // Generate method call
    let param_names: Vec<_> = params.iter().map(|(name, _)| name).collect();

    // Generate result conversion
    let result_conversion = if is_self_return(return_type, struct_name) {
        // Returns Self - wrap in LeanExternal
        quote! {
            {
                let external = #leo3_crate::external::LeanExternal::new(lean, result)
                    .expect("Failed to create external object");
                external.into_ptr()
            }
        }
    } else if is_unit_type(return_type) {
        quote! {
            #leo3_crate::ffi::lean_alloc_ctor(0, 0, 0)
        }
    } else {
        quote! {
            {
                let lean_result = <#return_type as #leo3_crate::conversion::IntoLean>::into_lean(result, lean)
                    .expect("Failed to convert result from Rust to Lean");
                lean_result.into_ptr()
            }
        }
    };

    Ok(quote! {
        #[no_mangle]
        pub unsafe extern "C" fn #ffi_name(#(#ffi_params),*) -> #leo3_crate::ffi::object::lean_obj_res {
            let lean = #leo3_crate::Lean::assume_initialized();

            #(#param_conversions)*

            let result = #struct_name::#method_name(#(#param_names),*);

            #result_conversion
        }

        #[allow(non_upper_case_globals)]
        const _: () = {
            #[link_section = "__DATA,__lean_metadata"]
            #[used]
            static __LEAN_METADATA: #leo3_crate::LeanFunctionMetadata =
                #leo3_crate::LeanFunctionMetadata {
                    name: #lean_name,
                };
        };
    })
}

/// Generate wrapper for &self methods
fn generate_ref_method_wrapper(
    method: &MethodInfo,
    struct_name: &syn::Ident,
    ffi_name: &syn::Ident,
    lean_name: &str,
    leo3_crate: &TokenStream,
) -> syn::Result<TokenStream> {
    let method_name = &method.name;
    let params = &method.params;
    let return_type = &method.return_type;

    // First parameter is the external object
    let param_count = params.len() + 1;
    let ffi_params: Vec<_> = (0..param_count)
        .map(|i| {
            let arg_name = format_ident!("arg{}", i);
            quote! { #arg_name: #leo3_crate::ffi::object::lean_obj_arg }
        })
        .collect();

    // Convert self parameter
    let self_conversion = quote! {
        let self_obj = #leo3_crate::LeanBound::<#leo3_crate::external::LeanExternalType<#struct_name>>::from_owned_ptr(lean, arg0);
        let self_ref = self_obj.get_ref();
    };

    // Convert other parameters
    let param_conversions: Vec<_> = params
        .iter()
        .enumerate()
        .map(|(i, (name, ty))| {
            let arg_name = format_ident!("arg{}", i + 1);
            quote! {
                let #name = {
                    let bound = #leo3_crate::LeanBound::<_>::from_owned_ptr(lean, #arg_name);
                    <#ty as #leo3_crate::conversion::FromLean>::from_lean(&bound)
                        .expect(&format!("Failed to convert {} from Lean to Rust", stringify!(#name)))
                };
            }
        })
        .collect();

    // Generate method call
    let param_names: Vec<_> = params.iter().map(|(name, _)| name).collect();

    // Generate result conversion
    let result_conversion = if is_unit_type(return_type) {
        quote! {
            unsafe { #leo3_crate::ffi::lean_alloc_ctor(0, 0, 0) }
        }
    } else {
        quote! {
            {
                let lean_result = <#return_type as #leo3_crate::conversion::IntoLean>::into_lean(result, lean)
                    .expect("Failed to convert result from Rust to Lean");
                lean_result.into_ptr()
            }
        }
    };

    Ok(quote! {
        #[no_mangle]
        pub unsafe extern "C" fn #ffi_name(#(#ffi_params),*) -> #leo3_crate::ffi::object::lean_obj_res {
            let lean = #leo3_crate::Lean::assume_initialized();

            #self_conversion
            #(#param_conversions)*

            let result = self_ref.#method_name(#(#param_names),*);

            #result_conversion
        }

        #[allow(non_upper_case_globals)]
        const _: () = {
            #[link_section = "__DATA,__lean_metadata"]
            #[used]
            static __LEAN_METADATA: #leo3_crate::LeanFunctionMetadata =
                #leo3_crate::LeanFunctionMetadata {
                    name: #lean_name,
                };
        };
    })
}

/// Generate wrapper for &mut self methods
/// In Lean (pure functional), this must return a new instance
fn generate_mut_ref_method_wrapper(
    method: &MethodInfo,
    struct_name: &syn::Ident,
    ffi_name: &syn::Ident,
    lean_name: &str,
    leo3_crate: &TokenStream,
) -> syn::Result<TokenStream> {
    let method_name = &method.name;
    let params = &method.params;
    let return_type = &method.return_type;

    // First parameter is the external object
    let param_count = params.len() + 1;
    let ffi_params: Vec<_> = (0..param_count)
        .map(|i| {
            let arg_name = format_ident!("arg{}", i);
            quote! { #arg_name: #leo3_crate::ffi::object::lean_obj_arg }
        })
        .collect();

    // Convert self parameter with COW (copy-on-write) semantics.
    // If the object is shared (refcount > 1), clone the inner value into a
    // fresh external object so that mutation never affects other references.
    let self_conversion = quote! {
        let mut self_obj = if #leo3_crate::ffi::object::lean_is_exclusive(arg0) {
            // Exclusively owned — safe to mutate in place.
            #leo3_crate::LeanBound::<#leo3_crate::external::LeanExternalType<#struct_name>>::from_owned_ptr(lean, arg0)
        } else {
            // Shared — clone the inner value, release our reference to the
            // original, and wrap the clone in a new external object.
            let borrowed = #leo3_crate::LeanBound::<#leo3_crate::external::LeanExternalType<#struct_name>>::from_owned_ptr(lean, arg0);
            let cloned: #struct_name = borrowed.get_ref().clone();
            drop(borrowed);
            #leo3_crate::external::LeanExternal::new(lean, cloned)
                .expect("Failed to allocate COW copy of external object")
        };
        let self_mut = self_obj.get_mut();
    };

    // Convert other parameters
    let param_conversions: Vec<_> = params
        .iter()
        .enumerate()
        .map(|(i, (name, ty))| {
            let arg_name = format_ident!("arg{}", i + 1);
            quote! {
                let #name = {
                    let bound = #leo3_crate::LeanBound::<_>::from_owned_ptr(lean, #arg_name);
                    <#ty as #leo3_crate::conversion::FromLean>::from_lean(&bound)
                        .expect(&format!("Failed to convert {} from Lean to Rust", stringify!(#name)))
                };
            }
        })
        .collect();

    // Generate method call
    let param_names: Vec<_> = params.iter().map(|(name, _)| name).collect();

    // For &mut self methods, we return the modified object
    let result_conversion = if is_unit_type(return_type) {
        // Method returns (), so return the modified self
        quote! {
            self_obj.into_ptr()
        }
    } else {
        // Method returns some value and modifies self
        // We need to return both (as a tuple? or just the result?)
        // For now, return the result and discard the modified self
        quote! {
            {
                let lean_result = <#return_type as #leo3_crate::conversion::IntoLean>::into_lean(result, lean)
                    .expect("Failed to convert result from Rust to Lean");
                lean_result.into_ptr()
            }
        }
    };

    Ok(quote! {
        #[no_mangle]
        pub unsafe extern "C" fn #ffi_name(#(#ffi_params),*) -> #leo3_crate::ffi::object::lean_obj_res {
            let lean = #leo3_crate::Lean::assume_initialized();

            #self_conversion
            #(#param_conversions)*

            let result = self_mut.#method_name(#(#param_names),*);

            #result_conversion
        }

        #[allow(non_upper_case_globals)]
        const _: () = {
            #[link_section = "__DATA,__lean_metadata"]
            #[used]
            static __LEAN_METADATA: #leo3_crate::LeanFunctionMetadata =
                #leo3_crate::LeanFunctionMetadata {
                    name: #lean_name,
                };
        };
    })
}

/// Generate wrapper for self methods (consuming)
fn generate_owned_method_wrapper(
    method: &MethodInfo,
    struct_name: &syn::Ident,
    ffi_name: &syn::Ident,
    lean_name: &str,
    leo3_crate: &TokenStream,
) -> syn::Result<TokenStream> {
    let method_name = &method.name;
    let params = &method.params;
    let return_type = &method.return_type;

    // First parameter is the external object
    let param_count = params.len() + 1;
    let ffi_params: Vec<_> = (0..param_count)
        .map(|i| {
            let arg_name = format_ident!("arg{}", i);
            quote! { #arg_name: #leo3_crate::ffi::object::lean_obj_arg }
        })
        .collect();

    // Convert self parameter (consuming).
    // If exclusively owned, read the value and let the LeanBound drop handle
    // the deallocation. If shared, clone the inner value instead.
    let self_conversion = quote! {
        let self_obj = #leo3_crate::LeanBound::<#leo3_crate::external::LeanExternalType<#struct_name>>::from_owned_ptr(lean, arg0);
        let self_owned: #struct_name = self_obj.get_ref().clone();
    };

    // Convert other parameters
    let param_conversions: Vec<_> = params
        .iter()
        .enumerate()
        .map(|(i, (name, ty))| {
            let arg_name = format_ident!("arg{}", i + 1);
            quote! {
                let #name = {
                    let bound = #leo3_crate::LeanBound::<_>::from_owned_ptr(lean, #arg_name);
                    <#ty as #leo3_crate::conversion::FromLean>::from_lean(&bound)
                        .expect(&format!("Failed to convert {} from Lean to Rust", stringify!(#name)))
                };
            }
        })
        .collect();

    // Generate method call
    let param_names: Vec<_> = params.iter().map(|(name, _)| name).collect();

    // Generate result conversion
    let result_conversion = if is_unit_type(return_type) {
        quote! {
            unsafe { #leo3_crate::ffi::lean_alloc_ctor(0, 0, 0) }
        }
    } else {
        quote! {
            {
                let lean_result = <#return_type as #leo3_crate::conversion::IntoLean>::into_lean(result, lean)
                    .expect("Failed to convert result from Rust to Lean");
                lean_result.into_ptr()
            }
        }
    };

    Ok(quote! {
        #[no_mangle]
        pub unsafe extern "C" fn #ffi_name(#(#ffi_params),*) -> #leo3_crate::ffi::object::lean_obj_res {
            let lean = #leo3_crate::Lean::assume_initialized();

            #self_conversion
            #(#param_conversions)*

            let result = self_owned.#method_name(#(#param_names),*);

            #result_conversion
        }

        #[allow(non_upper_case_globals)]
        const _: () = {
            #[link_section = "__DATA,__lean_metadata"]
            #[used]
            static __LEAN_METADATA: #leo3_crate::LeanFunctionMetadata =
                #leo3_crate::LeanFunctionMetadata {
                    name: #lean_name,
                };
        };
    })
}

/// Generate a string constant containing the Lean `opaque` type declaration for the struct.
///
/// For a struct named `Foo`, this produces:
/// ```ignore
/// pub const FOO_LEAN_CLASS_DECL: &str = "opaque Foo : Type";
/// ```
fn generate_lean_code_metadata(
    struct_info: &StructInfo,
    _methods: &[MethodInfo],
    _leo3_crate: &TokenStream,
) -> TokenStream {
    let struct_name_str = struct_info.name.to_string();
    let const_name = format_ident!("{}_LEAN_CLASS_DECL", struct_name_str.to_uppercase());
    let lean_code = format!("opaque {} : Type", struct_name_str);

    quote! {
        pub const #const_name: &str = #lean_code;
    }
}

/// Generate a string constant containing Lean `@[extern]` declarations for each method.
///
/// For a struct `Foo` with a method `bar(&self, x: u32) -> u32`, this produces:
/// ```ignore
/// pub const FOO_LEAN_METHODS_DECL: &str = r#"@[extern "__lean_ffi_Foo_bar"] opaque Foo.bar : Foo → UInt32 → UInt32"#;
/// ```
///
/// Receiver types are mapped as follows:
/// - `&self` / `&mut self` / `self` → the struct type as the first parameter
/// - `&mut self` with `()` return → return type becomes the struct (modified-in-place semantics)
fn generate_lean_code_metadata_for_methods(
    struct_name: &syn::Ident,
    methods: &[MethodInfo],
    _leo3_crate: &TokenStream,
) -> TokenStream {
    let struct_name_str = struct_name.to_string();
    let const_name = format_ident!("{}_LEAN_METHODS_DECL", struct_name_str.to_uppercase());

    let mut lean_lines = Vec::new();

    for method in methods {
        let ffi_name = format!("__lean_ffi_{}_{}", struct_name, method.name);
        let lean_name = &method.lean_name;

        // Build the type signature parts
        let mut type_parts: Vec<String> = Vec::new();

        // Add self parameter if applicable
        match &method.receiver {
            MethodReceiver::Ref | MethodReceiver::MutRef | MethodReceiver::Owned => {
                type_parts.push(struct_name_str.clone());
            }
            MethodReceiver::None => {}
        }

        // Add regular parameters
        for (_name, ty) in &method.params {
            type_parts.push(rust_type_to_lean(ty, &struct_name_str));
        }

        // Determine return type
        // For &mut self with unit return, the FFI returns the modified struct
        let return_lean_type = match &method.receiver {
            MethodReceiver::MutRef if is_unit_type(&method.return_type) => struct_name_str.clone(),
            _ => rust_type_to_lean(&method.return_type, &struct_name_str),
        };
        type_parts.push(return_lean_type);

        let type_sig = type_parts.join(" \u{2192} ");

        lean_lines.push(format!(
            "@[extern \"{}\"] opaque {} : {}",
            ffi_name, lean_name, type_sig
        ));
    }

    let lean_code = lean_lines.join("\n");

    quote! {
        pub const #const_name: &str = #lean_code;
    }
}

/// Map a Rust type to its Lean equivalent string
fn rust_type_to_lean(ty: &syn::Type, struct_name: &str) -> String {
    match ty {
        syn::Type::Path(type_path) => {
            if let Some(segment) = type_path.path.segments.last() {
                match segment.ident.to_string().as_str() {
                    "i32" => "Int32".to_string(),
                    "i64" => "Int64".to_string(),
                    "u32" => "UInt32".to_string(),
                    "u64" => "UInt64".to_string(),
                    "f64" => "Float".to_string(),
                    "String" => "String".to_string(),
                    "bool" => "Bool".to_string(),
                    "Self" => struct_name.to_string(),
                    other if other == struct_name => struct_name.to_string(),
                    other => other.to_string(),
                }
            } else {
                "Unit".to_string()
            }
        }
        syn::Type::Tuple(tuple) if tuple.elems.is_empty() => "Unit".to_string(),
        _ => "Unit".to_string(),
    }
}

/// Check if a type is unit ()
fn is_unit_type(ty: &syn::Type) -> bool {
    matches!(ty, syn::Type::Tuple(t) if t.elems.is_empty())
}

/// Check if return type is Self
fn is_self_return(ty: &syn::Type, struct_name: &syn::Ident) -> bool {
    match ty {
        syn::Type::Path(type_path) => {
            if let Some(segment) = type_path.path.segments.last() {
                segment.ident == "Self" || segment.ident == *struct_name
            } else {
                false
            }
        }
        _ => false,
    }
}
