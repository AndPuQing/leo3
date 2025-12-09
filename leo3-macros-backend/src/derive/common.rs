//! Common utilities for derive macro implementations.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields, Generics, Ident, Type};

/// Information about a type being derived.
pub struct TypeInfo {
    pub name: Ident,
    pub generics: Generics,
    pub data: TypeData,
}

/// The data associated with a type (struct or enum).
pub enum TypeData {
    Struct(StructInfo),
    Enum(EnumInfo),
}

/// Information about a struct.
pub struct StructInfo {
    pub fields: Vec<Field>,
}

/// Information about an enum.
pub struct EnumInfo {
    pub variants: Vec<Variant>,
}

/// Information about a field in a struct or enum variant.
#[derive(Clone)]
pub struct Field {
    pub name: Option<Ident>,
    pub ty: Type,
    pub index: usize,
}

/// Information about an enum variant.
pub struct Variant {
    pub name: Ident,
    pub tag: usize,
    pub fields: Vec<Field>,
}

/// Analyze a DeriveInput and extract type information.
pub fn analyze_type(input: &DeriveInput) -> syn::Result<TypeInfo> {
    let name = input.ident.clone();
    let generics = input.generics.clone();

    let data = match &input.data {
        Data::Struct(data_struct) => {
            let fields = extract_fields(&data_struct.fields)?;
            TypeData::Struct(StructInfo { fields })
        }
        Data::Enum(data_enum) => {
            let variants = data_enum
                .variants
                .iter()
                .enumerate()
                .map(|(tag, variant)| {
                    let fields = extract_fields(&variant.fields)?;
                    Ok(Variant {
                        name: variant.ident.clone(),
                        tag,
                        fields,
                    })
                })
                .collect::<syn::Result<Vec<_>>>()?;

            if variants.is_empty() {
                return Err(syn::Error::new_spanned(
                    input,
                    "Cannot derive IntoLean/FromLean for empty enums",
                ));
            }

            TypeData::Enum(EnumInfo { variants })
        }
        Data::Union(_) => {
            return Err(syn::Error::new_spanned(
                input,
                "Cannot derive IntoLean/FromLean for unions",
            ))
        }
    };

    Ok(TypeInfo {
        name,
        generics,
        data,
    })
}

/// Extract fields from syn::Fields.
fn extract_fields(fields: &Fields) -> syn::Result<Vec<Field>> {
    match fields {
        Fields::Named(fields_named) => fields_named
            .named
            .iter()
            .enumerate()
            .map(|(index, field)| {
                Ok(Field {
                    name: field.ident.clone(),
                    ty: field.ty.clone(),
                    index,
                })
            })
            .collect(),
        Fields::Unnamed(fields_unnamed) => fields_unnamed
            .unnamed
            .iter()
            .enumerate()
            .map(|(index, field)| {
                Ok(Field {
                    name: None,
                    ty: field.ty.clone(),
                    index,
                })
            })
            .collect(),
        Fields::Unit => Ok(Vec::new()),
    }
}

/// Add trait bounds to generic parameters.
///
/// Returns two Generics: one for the impl block (includes 'l), and one for the type (original).
pub fn add_trait_bounds(generics: &Generics, trait_name: &str) -> (Generics, Generics) {
    let type_generics = generics.clone();
    let mut impl_generics = generics.clone();

    // Add the 'l lifetime parameter first to impl generics
    let lifetime = syn::Lifetime::new("'l", proc_macro2::Span::call_site());
    let lifetime_param = syn::LifetimeParam::new(lifetime);
    impl_generics
        .params
        .insert(0, syn::GenericParam::Lifetime(lifetime_param));

    // Add trait bounds for each type parameter
    for param in &mut impl_generics.params {
        if let syn::GenericParam::Type(type_param) = param {
            let trait_path: syn::Path =
                syn::parse_str(&format!("::leo3::conversion::{}", trait_name))
                    .expect("Failed to parse trait path");

            // Add the trait bound
            type_param.bounds.push(syn::parse_quote! {
                #trait_path<'l>
            });

            // Add 'l lifetime bound for the type parameter
            type_param.bounds.push(syn::parse_quote! {
                'l
            });
        }
    }

    (impl_generics, type_generics)
}

/// Get the leo3 crate path (handles re-exports).
pub fn get_leo3_crate() -> TokenStream {
    quote! { ::leo3 }
}

/// Generate a field name for unnamed fields.
pub fn field_name(field: &Field) -> TokenStream {
    if let Some(name) = &field.name {
        quote! { #name }
    } else {
        let index = syn::Index::from(field.index);
        quote! { #index }
    }
}

/// Generate a variable name for a field (used in pattern matching).
pub fn field_var_name(field: &Field) -> Ident {
    if let Some(name) = &field.name {
        name.clone()
    } else {
        Ident::new(&format!("v{}", field.index), proc_macro2::Span::call_site())
    }
}

/// Generate an error message prefix for a field.
pub fn field_error_prefix(field: &Field) -> String {
    if let Some(name) = &field.name {
        format!("Field '{}': ", name)
    } else {
        format!("Field {}: ", field.index)
    }
}
