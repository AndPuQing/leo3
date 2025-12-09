//! Common utilities for derive macro implementations.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields, Generics, Ident, Type};

/// Container-level attributes (applied to struct or enum).
#[derive(Default, Debug)]
pub struct ContainerAttrs {
    pub transparent: bool,
}

/// Field-level attributes (applied to struct fields).
#[derive(Default, Debug, Clone)]
pub struct FieldAttrs {
    pub skip: bool,
    pub default: bool,
    pub with: Option<syn::Path>,
    pub rename: Option<String>,
}

/// Variant-level attributes (applied to enum variants).
#[derive(Default, Debug)]
pub struct VariantAttrs {
    pub tag: Option<usize>,
}

/// Information about a type being derived.
pub struct TypeInfo {
    pub name: Ident,
    pub generics: Generics,
    pub data: TypeData,
    pub attrs: ContainerAttrs,
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
    pub attrs: FieldAttrs,
}

/// Information about an enum variant.
pub struct Variant {
    pub name: Ident,
    pub tag: usize,
    pub fields: Vec<Field>,
    pub attrs: VariantAttrs,
}

/// Analyze a DeriveInput and extract type information.
pub fn analyze_type(input: &DeriveInput) -> syn::Result<TypeInfo> {
    let name = input.ident.clone();
    let generics = input.generics.clone();

    // Parse container attributes
    let container_attrs = parse_container_attrs(&input.attrs)?;

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
                .map(|(default_tag, variant)| {
                    let variant_attrs = parse_variant_attrs(&variant.attrs)?;
                    let tag = variant_attrs.tag.unwrap_or(default_tag);
                    let fields = extract_fields(&variant.fields)?;
                    Ok(Variant {
                        name: variant.ident.clone(),
                        tag,
                        fields,
                        attrs: variant_attrs,
                    })
                })
                .collect::<syn::Result<Vec<_>>>()?;

            if variants.is_empty() {
                return Err(syn::Error::new_spanned(
                    input,
                    "Cannot derive IntoLean/FromLean for empty enums",
                ));
            }

            // Validate variant attributes
            validate_variant_attrs(&variants)?;

            TypeData::Enum(EnumInfo { variants })
        }
        Data::Union(_) => {
            return Err(syn::Error::new_spanned(
                input,
                "Cannot derive IntoLean/FromLean for unions",
            ))
        }
    };

    let type_info = TypeInfo {
        name,
        generics,
        data,
        attrs: container_attrs,
    };

    // Validate container attributes
    validate_container_attrs(&type_info, &type_info.attrs)?;

    Ok(type_info)
}

/// Extract fields from syn::Fields.
fn extract_fields(fields: &Fields) -> syn::Result<Vec<Field>> {
    match fields {
        Fields::Named(fields_named) => fields_named
            .named
            .iter()
            .enumerate()
            .map(|(index, field)| {
                let attrs = parse_field_attrs(&field.attrs)?;
                let f = Field {
                    name: field.ident.clone(),
                    ty: field.ty.clone(),
                    index,
                    attrs: attrs.clone(),
                };
                validate_field_attrs(&f, &attrs)?;
                Ok(f)
            })
            .collect(),
        Fields::Unnamed(fields_unnamed) => fields_unnamed
            .unnamed
            .iter()
            .enumerate()
            .map(|(index, field)| {
                let attrs = parse_field_attrs(&field.attrs)?;
                let f = Field {
                    name: None,
                    ty: field.ty.clone(),
                    index,
                    attrs: attrs.clone(),
                };
                validate_field_attrs(&f, &attrs)?;
                Ok(f)
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

/// Parse container-level attributes from #[lean(...)].
pub fn parse_container_attrs(attrs: &[syn::Attribute]) -> syn::Result<ContainerAttrs> {
    let mut result = ContainerAttrs::default();

    for attr in attrs {
        if !attr.path().is_ident("lean") {
            continue;
        }

        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("transparent") {
                result.transparent = true;
                Ok(())
            } else {
                Err(meta.error(format!(
                    "Unknown container attribute: {}",
                    meta.path
                        .get_ident()
                        .map(|i| i.to_string())
                        .unwrap_or_else(|| "?".to_string())
                )))
            }
        })?;
    }

    Ok(result)
}

/// Parse field-level attributes from #[lean(...)].
pub fn parse_field_attrs(attrs: &[syn::Attribute]) -> syn::Result<FieldAttrs> {
    let mut result = FieldAttrs::default();

    for attr in attrs {
        if !attr.path().is_ident("lean") {
            continue;
        }

        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("skip") {
                result.skip = true;
                Ok(())
            } else if meta.path.is_ident("default") {
                result.default = true;
                Ok(())
            } else if meta.path.is_ident("with") {
                let value = meta.value()?;
                let path: syn::Path = value.parse()?;
                result.with = Some(path);
                Ok(())
            } else if meta.path.is_ident("rename") {
                let value = meta.value()?;
                let lit: syn::LitStr = value.parse()?;
                result.rename = Some(lit.value());
                Ok(())
            } else {
                Err(meta.error(format!(
                    "Unknown field attribute: {}",
                    meta.path
                        .get_ident()
                        .map(|i| i.to_string())
                        .unwrap_or_else(|| "?".to_string())
                )))
            }
        })?;
    }

    Ok(result)
}

/// Parse variant-level attributes from #[lean(...)].
pub fn parse_variant_attrs(attrs: &[syn::Attribute]) -> syn::Result<VariantAttrs> {
    let mut result = VariantAttrs::default();

    for attr in attrs {
        if !attr.path().is_ident("lean") {
            continue;
        }

        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("tag") {
                let value = meta.value()?;
                let lit: syn::LitInt = value.parse()?;
                result.tag = Some(lit.base10_parse()?);
                Ok(())
            } else {
                Err(meta.error(format!(
                    "Unknown variant attribute: {}",
                    meta.path
                        .get_ident()
                        .map(|i| i.to_string())
                        .unwrap_or_else(|| "?".to_string())
                )))
            }
        })?;
    }

    Ok(result)
}

/// Validate container attributes.
pub fn validate_container_attrs(type_info: &TypeInfo, attrs: &ContainerAttrs) -> syn::Result<()> {
    if attrs.transparent {
        // Transparent only makes sense for newtype structs
        match &type_info.data {
            TypeData::Struct(info) => {
                if info.fields.len() != 1 {
                    return Err(syn::Error::new_spanned(
                        &type_info.name,
                        "transparent attribute can only be used on structs with exactly one field",
                    ));
                }
            }
            TypeData::Enum(_) => {
                return Err(syn::Error::new_spanned(
                    &type_info.name,
                    "transparent attribute cannot be used on enums",
                ));
            }
        }
    }
    Ok(())
}

/// Validate field attributes.
pub fn validate_field_attrs(field: &Field, attrs: &FieldAttrs) -> syn::Result<()> {
    // Can't have both skip and default
    if attrs.skip && attrs.default {
        return Err(syn::Error::new_spanned(
            &field.ty,
            "cannot use both 'skip' and 'default' attributes on the same field",
        ));
    }

    // Can't have both skip and with
    if attrs.skip && attrs.with.is_some() {
        return Err(syn::Error::new_spanned(
            &field.ty,
            "cannot use both 'skip' and 'with' attributes on the same field",
        ));
    }

    Ok(())
}

/// Validate variant attributes for an enum.
pub fn validate_variant_attrs(variants: &[Variant]) -> syn::Result<()> {
    let mut used_tags = std::collections::HashSet::new();

    for variant in variants {
        if let Some(tag) = variant.attrs.tag {
            if !used_tags.insert(tag) {
                return Err(syn::Error::new_spanned(
                    &variant.name,
                    format!("duplicate tag value: {}", tag),
                ));
            }
        }
    }

    Ok(())
}

/// Filter out skipped fields and recalculate indices.
pub fn active_fields(fields: &[Field]) -> Vec<Field> {
    fields
        .iter()
        .filter(|f| !f.attrs.skip)
        .enumerate()
        .map(|(new_index, f)| {
            let mut field = f.clone();
            field.index = new_index;
            field
        })
        .collect()
}
