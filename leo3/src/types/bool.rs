//! Lean boolean type wrapper.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;

/// A Lean boolean object.
///
/// Booleans in Lean4 are inductively defined:
/// ```lean
/// inductive Bool : Type where
///   | false : Bool
///   | true : Bool
/// ```
pub struct LeanBool {
    _private: (),
}

impl LeanBool {
    /// Create a Lean boolean from a Rust bool.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Bool.false` or `Bool.true` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let b = LeanBool::mk(lean, true)?;
    ///     assert_eq!(LeanBool::toBool(&b), true);
    ///     Ok(())
    /// })
    /// ```
    pub fn mk<'l>(lean: Lean<'l>, value: bool) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Bool.false = tag 0, Bool.true = tag 1 — both are scalars
            let ptr = ffi::lean_mk_bool(value);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert a Lean boolean to a Rust bool.
    ///
    /// # Lean4 Reference
    /// Pattern matching on `Bool.false` | `Bool.true`.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let b = LeanBool::mk(lean, true)?;
    /// assert_eq!(LeanBool::toBool(&b), true);
    /// ```
    #[allow(non_snake_case)]
    pub fn toBool<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe {
            let tag = ffi::lean_obj_tag(obj.as_ptr());
            tag == 1 // true has tag 1, false has tag 0
        }
    }

    /// Logical NOT operation.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Bool.not` or `!` operator in Lean4.
    pub fn not<'l>(obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let lean = obj.lean_token();
        let value = !Self::toBool(&obj);
        Self::mk(lean, value)
    }

    /// Logical AND operation.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Bool.and` or `&&` operator in Lean4.
    pub fn and<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        Self::toBool(a) && Self::toBool(b)
    }

    /// Logical OR operation.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Bool.or` or `||` operator in Lean4.
    pub fn or<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        Self::toBool(a) || Self::toBool(b)
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanBool> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanBool({})", LeanBool::toBool(self))
    }
}
