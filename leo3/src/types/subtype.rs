//! Lean subtype wrapper.
//!
//! The `Subtype` represents a value of type α that satisfies a predicate p.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};

/// A Lean subtype object.
///
/// Subtype in Lean4 is defined as a structure:
/// ```lean
/// structure Subtype {α : Sort u} (p : α → Prop) where
///   val : α
///   property : p val
/// ```
///
/// `Subtype p` (written `{ x : α // p x }` in Lean4) represents values of type `α`
/// that satisfy the predicate `p`. It pairs a value with a proof that the predicate
/// holds for that value.
///
/// # Runtime Representation
///
/// At runtime, only the value is stored - the proof is erased during compilation
/// since proofs don't affect computation. This means `Subtype p` has the exact same
/// runtime representation as the underlying type `α`.
///
/// The constructor has tag 0 with 1 object field containing just the value. The
/// `property` field (the proof) does not exist at runtime.
///
/// # Proof Erasure
///
/// Since proofs are erased, the FFI layer cannot enforce that values actually satisfy
/// their predicates. You must trust that any Lean code that constructed the subtype
/// correctly proved the property.
///
/// # Examples
///
/// In Lean4, subtypes are commonly used for:
/// - Non-empty lists: `{ xs : List α // xs ≠ [] }`
/// - Positive numbers: `{ n : Nat // n > 0 }`
/// - Valid indices: `{ i : Nat // i < xs.length }`
pub struct LeanSubtype {
    _private: (),
}

impl LeanSubtype {
    /// Create a subtype from a value.
    ///
    /// In Lean4, this would require a proof that the predicate holds for the value.
    /// Since proofs are erased at runtime, this FFI constructor only takes the value.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Subtype.mk` or `⟨val, proof⟩` in Lean4.
    ///
    /// # Safety
    ///
    /// This function assumes that the value was constructed by Lean code that proved
    /// the required predicate. There is no runtime verification.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     // In Lean: subtype of positive naturals { n : Nat // n > 0 }
    ///     let value = LeanNat::from_usize(lean, 42)?;
    ///     let subtype = LeanSubtype::mk(value.unbind())?;
    ///
    ///     // Extract the value
    ///     let extracted = LeanSubtype::val(&subtype);
    ///     Ok(())
    /// })
    /// ```
    pub fn mk<'l>(val: LeanBound<'l, LeanAny>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = val.lean_token();
            let ptr = ffi::lean_mk_wrapper(val.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Extract the value from a subtype.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Subtype.val` or `.val` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let subtype = LeanSubtype::mk(value)?;
    /// let extracted_value = LeanSubtype::val(&subtype);
    /// ```
    pub fn val<'l>(obj: &LeanBound<'l, Self>) -> LeanBound<'l, LeanAny> {
        unsafe {
            let lean = obj.lean_token();
            let val_ptr = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;
            // Increment ref count since we're borrowing
            ffi::lean_inc(val_ptr);
            LeanBound::from_owned_ptr(lean, val_ptr)
        }
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanSubtype> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanSubtype{{val: ...}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_subtype_size() {
        // Verify that LeanSubtype is zero-sized
        assert_eq!(std::mem::size_of::<LeanSubtype>(), 0);
    }
}
