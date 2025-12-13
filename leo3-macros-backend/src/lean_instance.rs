//! Implementation of the `#[lean_instance]` macro.
//!
//! This macro generates FFI functions that implement Lean type classes for Rust types.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{parse::Parse, ImplItem, ItemImpl, Token};

use crate::get_leo3_crate;

/// Options for the `#[lean_instance]` macro.
pub struct LeanInstanceOptions {
    /// The type class to implement (BEq, Hashable, Repr, ToString, Ord).
    pub typeclass: syn::Ident,
    /// Path to the leo3 crate (for re-exports).
    pub krate: Option<syn::Path>,
}

impl Parse for LeanInstanceOptions {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let typeclass: syn::Ident = input.parse()?;

        // Optional: crate path
        let krate = if input.peek(Token![,]) {
            input.parse::<Token![,]>()?;
            if input.peek(syn::Ident) {
                let ident: syn::Ident = input.parse()?;
                if ident == "crate" {
                    input.parse::<Token![=]>()?;
                    Some(input.parse()?)
                } else {
                    return Err(syn::Error::new(ident.span(), "Expected `crate = path`"));
                }
            } else {
                None
            }
        } else {
            None
        };

        Ok(LeanInstanceOptions { typeclass, krate })
    }
}

/// Supported type classes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeClass {
    /// Boolean equality (BEq)
    BEq,
    /// Hashing (Hashable)
    Hashable,
    /// Representation (Repr)
    Repr,
    /// String conversion (ToString)
    ToString,
    /// Ordering comparison (Ord)
    Ord,
}

impl TypeClass {
    /// Parse from identifier.
    pub fn from_ident(ident: &syn::Ident) -> Option<Self> {
        match ident.to_string().as_str() {
            "BEq" => Some(TypeClass::BEq),
            "Hashable" => Some(TypeClass::Hashable),
            "Repr" => Some(TypeClass::Repr),
            "ToString" => Some(TypeClass::ToString),
            "Ord" => Some(TypeClass::Ord),
            _ => None,
        }
    }

    /// Get the required method name.
    pub fn method_name(&self) -> &'static str {
        match self {
            TypeClass::BEq => "beq",
            TypeClass::Hashable => "hash",
            TypeClass::Repr => "repr",
            TypeClass::ToString => "to_string",
            TypeClass::Ord => "compare",
        }
    }

    /// Get the FFI function prefix.
    pub fn ffi_prefix(&self) -> &'static str {
        match self {
            TypeClass::BEq => "__lean_beq",
            TypeClass::Hashable => "__lean_hash",
            TypeClass::Repr => "__lean_repr",
            TypeClass::ToString => "__lean_to_string",
            TypeClass::Ord => "__lean_compare",
        }
    }
}

/// Build the `#[lean_instance]` macro output.
pub fn build_lean_instance(
    item: &mut ItemImpl,
    options: LeanInstanceOptions,
) -> syn::Result<TokenStream> {
    let typeclass = TypeClass::from_ident(&options.typeclass).ok_or_else(|| {
        syn::Error::new(
            options.typeclass.span(),
            format!(
                "Unsupported type class '{}'. Supported: BEq, Hashable, Repr, ToString, Ord",
                options.typeclass
            ),
        )
    })?;

    // Extract the struct name from the impl block
    let struct_name = extract_struct_name(item)?;

    // Find the required method
    let method = find_method(item, typeclass.method_name())?;

    // Generate the FFI function
    let leo3_crate = get_leo3_crate(options.krate.as_ref());
    let ffi_fn = generate_ffi_function(&leo3_crate, &struct_name, typeclass, method)?;

    // Return original impl + generated FFI function
    Ok(quote! {
        #item

        #ffi_fn
    })
}

/// Extract the struct name from an impl block.
fn extract_struct_name(item: &ItemImpl) -> syn::Result<syn::Ident> {
    match &*item.self_ty {
        syn::Type::Path(type_path) => {
            if let Some(segment) = type_path.path.segments.last() {
                Ok(segment.ident.clone())
            } else {
                Err(syn::Error::new_spanned(
                    &item.self_ty,
                    "Cannot determine struct name from impl block",
                ))
            }
        }
        _ => Err(syn::Error::new_spanned(
            &item.self_ty,
            "Expected a path type in impl block",
        )),
    }
}

/// Find a method in an impl block.
fn find_method<'a>(item: &'a ItemImpl, name: &str) -> syn::Result<&'a syn::ImplItemFn> {
    for impl_item in &item.items {
        if let ImplItem::Fn(method) = impl_item {
            if method.sig.ident == name {
                return Ok(method);
            }
        }
    }

    Err(syn::Error::new_spanned(
        item,
        format!(
            "Method '{}' not found in impl block. This method is required for the type class.",
            name
        ),
    ))
}

/// Generate the FFI function for a type class.
fn generate_ffi_function(
    leo3_crate: &TokenStream,
    struct_name: &syn::Ident,
    typeclass: TypeClass,
    _method: &syn::ImplItemFn,
) -> syn::Result<TokenStream> {
    let ffi_name = format_ident!("{}_{}", typeclass.ffi_prefix(), struct_name);
    let method_ident = format_ident!("{}", typeclass.method_name());

    match typeclass {
        TypeClass::BEq => Ok(quote! {
            /// Auto-generated BEq instance implementation.
            #[no_mangle]
            pub unsafe extern "C" fn #ffi_name(
                a: *mut #leo3_crate::ffi::lean_object,
                b: *mut #leo3_crate::ffi::lean_object,
            ) -> *mut #leo3_crate::ffi::lean_object {
                let lean = #leo3_crate::Lean::assume_initialized();

                // Get references to the external objects
                let a_bound: #leo3_crate::LeanBound<'_, #leo3_crate::external::LeanExternalType<#struct_name>> =
                    #leo3_crate::LeanBound::from_owned_ptr(lean, a);
                let b_bound: #leo3_crate::LeanBound<'_, #leo3_crate::external::LeanExternalType<#struct_name>> =
                    #leo3_crate::LeanBound::from_owned_ptr(lean, b);

                // Call the beq method
                let result = a_bound.get_ref().#method_ident(b_bound.get_ref());

                // Return Lean Bool (boxed)
                #leo3_crate::ffi::inline::lean_box(result as usize)
            }
        }),

        TypeClass::Hashable => Ok(quote! {
            /// Auto-generated Hashable instance implementation.
            #[no_mangle]
            pub unsafe extern "C" fn #ffi_name(
                obj: *mut #leo3_crate::ffi::lean_object,
            ) -> u64 {
                let lean = #leo3_crate::Lean::assume_initialized();

                let obj_bound: #leo3_crate::LeanBound<'_, #leo3_crate::external::LeanExternalType<#struct_name>> =
                    #leo3_crate::LeanBound::from_owned_ptr(lean, obj);

                // Call the hash method
                obj_bound.get_ref().#method_ident()
            }
        }),

        TypeClass::Repr => Ok(quote! {
            /// Auto-generated Repr instance implementation.
            #[no_mangle]
            pub unsafe extern "C" fn #ffi_name(
                obj: *mut #leo3_crate::ffi::lean_object,
            ) -> *mut #leo3_crate::ffi::lean_object {
                let lean = #leo3_crate::Lean::assume_initialized();

                let obj_bound: #leo3_crate::LeanBound<'_, #leo3_crate::external::LeanExternalType<#struct_name>> =
                    #leo3_crate::LeanBound::from_owned_ptr(lean, obj);

                // Call the repr method
                let repr_str: String = obj_bound.get_ref().#method_ident();

                // Convert to Lean String
                match #leo3_crate::types::LeanString::mk(lean, &repr_str) {
                    Ok(s) => s.into_ptr(),
                    Err(_) => {
                        // Return empty string on error
                        #leo3_crate::ffi::string::lean_mk_string(b"\0".as_ptr() as *const _)
                    }
                }
            }
        }),

        TypeClass::ToString => Ok(quote! {
            /// Auto-generated ToString instance implementation.
            #[no_mangle]
            pub unsafe extern "C" fn #ffi_name(
                obj: *mut #leo3_crate::ffi::lean_object,
            ) -> *mut #leo3_crate::ffi::lean_object {
                let lean = #leo3_crate::Lean::assume_initialized();

                let obj_bound: #leo3_crate::LeanBound<'_, #leo3_crate::external::LeanExternalType<#struct_name>> =
                    #leo3_crate::LeanBound::from_owned_ptr(lean, obj);

                // Call the to_string method
                let s: String = obj_bound.get_ref().#method_ident();

                // Convert to Lean String
                match #leo3_crate::types::LeanString::mk(lean, &s) {
                    Ok(lean_str) => lean_str.into_ptr(),
                    Err(_) => {
                        #leo3_crate::ffi::string::lean_mk_string(b"\0".as_ptr() as *const _)
                    }
                }
            }
        }),

        TypeClass::Ord => Ok(quote! {
            /// Auto-generated Ord instance implementation.
            #[no_mangle]
            pub unsafe extern "C" fn #ffi_name(
                a: *mut #leo3_crate::ffi::lean_object,
                b: *mut #leo3_crate::ffi::lean_object,
            ) -> *mut #leo3_crate::ffi::lean_object {
                let lean = #leo3_crate::Lean::assume_initialized();

                let a_bound: #leo3_crate::LeanBound<'_, #leo3_crate::external::LeanExternalType<#struct_name>> =
                    #leo3_crate::LeanBound::from_owned_ptr(lean, a);
                let b_bound: #leo3_crate::LeanBound<'_, #leo3_crate::external::LeanExternalType<#struct_name>> =
                    #leo3_crate::LeanBound::from_owned_ptr(lean, b);

                // Call the compare method
                let ordering = a_bound.get_ref().#method_ident(b_bound.get_ref());

                // Convert Ordering to Lean representation
                // Lean Ordering: lt = 0, eq = 1, gt = 2
                let ord_val = match ordering {
                    std::cmp::Ordering::Less => 0usize,
                    std::cmp::Ordering::Equal => 1usize,
                    std::cmp::Ordering::Greater => 2usize,
                };

                #leo3_crate::ffi::inline::lean_box(ord_val)
            }
        }),
    }
}
