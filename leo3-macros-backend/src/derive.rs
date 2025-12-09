//! Derive macro implementations for IntoLean and FromLean traits.
//!
//! This module provides automatic derive implementations for converting Rust types
//! to and from Lean constructors.

pub mod common;
pub mod from_lean;
pub mod into_lean;

use proc_macro2::TokenStream;
use syn::DeriveInput;

/// Expand `#[derive(IntoLean)]` for a Rust type.
///
/// Generates an implementation of the `IntoLean` trait that converts
/// the Rust type into a Lean constructor.
pub fn expand_into_lean(input: DeriveInput) -> syn::Result<TokenStream> {
    into_lean::expand(input)
}

/// Expand `#[derive(FromLean)]` for a Rust type.
///
/// Generates an implementation of the `FromLean` trait that extracts
/// a Rust value from a Lean constructor.
pub fn expand_from_lean(input: DeriveInput) -> syn::Result<TokenStream> {
    from_lean::expand(input)
}
