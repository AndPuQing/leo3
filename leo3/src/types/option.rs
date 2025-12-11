//! Lean option type wrapper.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;

/// A Lean option object.
///
/// Options in Lean4 are inductively defined:
/// ```lean
/// inductive Option (α : Type u) where
///   | none : Option α
///   | some (val : α) : Option α
/// ```
pub struct LeanOption {
    _private: (),
}

impl LeanOption {
    /// Create an Option with no value (none).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.none` or `none` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let opt = LeanOption::none(lean)?;
    ///     assert!(LeanOption::isNone(&opt));
    ///     Ok(())
    /// })
    /// ```
    pub fn none<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Option.none is constructor 0 with no fields
            let ptr = ffi::lean_alloc_ctor(0, 0, 0);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create an Option with a value (some).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.some` or `some` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let value = LeanNat::from_usize(lean, 42)?;
    /// let opt = LeanOption::some(value.unbind())?;
    /// assert!(LeanOption::isSome(&opt));
    /// ```
    pub fn some<'l>(value: LeanBound<'l, LeanAny>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = value.lean_token();
            // Option.some is constructor 1 with 1 field (val)
            let ptr = ffi::lean_alloc_ctor(1, 1, 0);
            ffi::lean_ctor_set(ptr, 0, value.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Check if the option is none.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.isNone` in Lean4.
    #[allow(non_snake_case)]
    pub fn isNone<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe {
            let tag = ffi::lean_obj_tag(obj.as_ptr());
            tag == 0 // none has tag 0
        }
    }

    /// Check if the option is some.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.isSome` in Lean4.
    #[allow(non_snake_case)]
    pub fn isSome<'l>(obj: &LeanBound<'l, Self>) -> bool {
        !Self::isNone(obj)
    }

    /// Get the value from the option if it's some.
    ///
    /// Returns `None` if the option is none.
    ///
    /// # Lean4 Reference
    /// Similar to pattern matching on `some val` in Lean4.
    pub fn get<'l>(obj: &LeanBound<'l, Self>) -> Option<LeanBound<'l, LeanAny>> {
        if Self::isNone(obj) {
            return None;
        }

        unsafe {
            let lean = obj.lean_token();
            let val_ptr = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;
            // Increment ref count since we're borrowing
            ffi::lean_inc(val_ptr);
            Some(LeanBound::from_owned_ptr(lean, val_ptr))
        }
    }

    /// Convert to Rust Option.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let opt = LeanOption::some(value)?;
    /// if let Some(val) = LeanOption::toRustOption(&opt) {
    ///     // use val
    /// }
    /// ```
    #[allow(non_snake_case)]
    pub fn toRustOption<'l>(obj: &LeanBound<'l, Self>) -> Option<LeanBound<'l, LeanAny>> {
        Self::get(obj)
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanOption> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if LeanOption::isNone(self) {
            write!(f, "LeanOption::none")
        } else {
            write!(f, "LeanOption::some(...)")
        }
    }
}
