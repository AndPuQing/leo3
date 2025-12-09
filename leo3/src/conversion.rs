//! Traits for converting between Rust and Lean types.
//!
//! This module provides traits for converting between Rust values and Lean objects.

use crate::err::LeanResult;
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;
use crate::types::{LeanArray, LeanBool, LeanNat, LeanString};

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

// =============================================================================
// Implementations for primitive types
// =============================================================================

// u64 ↔ LeanNat
impl<'l> IntoLean<'l> for u64 {
    type Target = LeanNat;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanNat::from_usize(lean, self as usize)
    }
}

impl<'l> FromLean<'l> for u64 {
    type Source = LeanNat;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanNat::to_usize(obj).map(|n| n as u64)
    }
}

// usize ↔ LeanNat
impl<'l> IntoLean<'l> for usize {
    type Target = LeanNat;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanNat::from_usize(lean, self)
    }
}

impl<'l> FromLean<'l> for usize {
    type Source = LeanNat;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanNat::to_usize(obj)
    }
}

// u32 ↔ LeanNat
impl<'l> IntoLean<'l> for u32 {
    type Target = LeanNat;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanNat::from_usize(lean, self as usize)
    }
}

impl<'l> FromLean<'l> for u32 {
    type Source = LeanNat;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanNat::to_usize(obj).and_then(|n| {
            u32::try_from(n).map_err(|_| crate::err::LeanError::conversion("Nat too large for u32"))
        })
    }
}

// u16 ↔ LeanNat
impl<'l> IntoLean<'l> for u16 {
    type Target = LeanNat;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanNat::from_usize(lean, self as usize)
    }
}

impl<'l> FromLean<'l> for u16 {
    type Source = LeanNat;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanNat::to_usize(obj).and_then(|n| {
            u16::try_from(n).map_err(|_| crate::err::LeanError::conversion("Nat too large for u16"))
        })
    }
}

// u8 ↔ LeanNat
impl<'l> IntoLean<'l> for u8 {
    type Target = LeanNat;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanNat::from_usize(lean, self as usize)
    }
}

impl<'l> FromLean<'l> for u8 {
    type Source = LeanNat;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanNat::to_usize(obj).and_then(|n| {
            u8::try_from(n).map_err(|_| crate::err::LeanError::conversion("Nat too large for u8"))
        })
    }
}

// bool ↔ LeanBool
impl<'l> IntoLean<'l> for bool {
    type Target = LeanBool;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanBool::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for bool {
    type Source = LeanBool;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanBool::toBool(obj))
    }
}

// String ↔ LeanString
impl<'l> IntoLean<'l> for String {
    type Target = LeanString;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanString::mk(lean, &self)
    }
}

impl<'l> FromLean<'l> for String {
    type Source = LeanString;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanString::cstr(obj).map(|s| s.to_string())
    }
}

// &str → LeanString (one-way conversion)
impl<'l> IntoLean<'l> for &str {
    type Target = LeanString;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanString::mk(lean, self)
    }
}

// Vec<T> ↔ LeanArray
impl<'l, T> IntoLean<'l> for Vec<T>
where
    T: IntoLean<'l> + 'l,
{
    type Target = LeanArray;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        let mut arr = LeanArray::empty(lean)?;

        for item in self {
            let lean_item = item.into_lean(lean)?;
            let any_item: LeanBound<'l, LeanAny> = lean_item.cast();
            arr = LeanArray::push(arr, any_item)?;
        }

        Ok(arr)
    }
}

impl<'l, T> FromLean<'l> for Vec<T>
where
    T: FromLean<'l> + 'l,
{
    type Source = LeanArray;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        let lean = obj.lean_token();
        let size = LeanArray::size(obj);
        let mut result = Vec::with_capacity(size);

        for i in 0..size {
            let elem = LeanArray::get(obj, lean, i)
                .ok_or_else(|| crate::err::LeanError::runtime("Index out of bounds"))?;
            let typed_elem: LeanBound<'l, T::Source> = elem.cast();
            let rust_item = T::from_lean(&typed_elem)?;
            result.push(rust_item);
        }

        Ok(result)
    }
}
