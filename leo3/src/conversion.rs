//! Traits for converting between Rust and Lean types.
//!
//! This module provides traits for converting between Rust values and Lean objects.

use crate::marker::Lean;
use crate::instance::LeanBound;
use crate::err::LeanResult;

/// Trait for types that can be converted from Rust to Lean.
///
/// # Example
///
/// ```rust,ignore
/// impl<'l> IntoLean<'l> for u64 {
///     type Target = LeanNat;
///
///     fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
///         Ok(LeanNat::from_u64(lean, self))
///     }
/// }
/// ```
pub trait IntoLean<'l> {
    /// The target Lean type
    type Target;

    /// Convert this value into a Lean object.
    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>>;
}

/// Trait for types that can be converted from Lean to Rust.
///
/// # Example
///
/// ```rust,ignore
/// impl<'l> FromLean<'l> for u64 {
///     fn from_lean(obj: &LeanBound<'l, LeanNat>) -> LeanResult<Self> {
///         obj.to_u64()
///     }
/// }
/// ```
pub trait FromLean<'l>: Sized {
    /// The source Lean type
    type Source;

    /// Extract a Rust value from a Lean object.
    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self>;
}

// Future: Add derive macros
// #[derive(IntoLean, FromLean)]
// for automatic conversion implementations
