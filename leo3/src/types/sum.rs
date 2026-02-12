//! Lean sum (disjoint union) type wrapper.
//!
//! The `Sum` type represents a discriminated union of two types, also called a disjoint union.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};

/// A Lean sum (disjoint union) object.
///
/// Sum in Lean4 is inductively defined:
/// ```lean
/// inductive Sum (α : Type u) (β : Type v)
///   | inl : α → Sum α β
///   | inr : β → Sum α β
/// ```
///
/// `Sum α β` (written `α ⊕ β` in Lean4) is a type that contains either a value of type `α`
/// (tagged as `inl`) or a value of type `β` (tagged as `inr`). It's also called a
/// discriminated union or tagged union.
///
/// # Runtime Representation
///
/// - `inl a`: Constructor with tag 0, containing one field (the left value)
/// - `inr b`: Constructor with tag 1, containing one field (the right value)
pub struct LeanSum {
    _private: (),
}

impl LeanSum {
    /// Create a Sum with a left value (inl).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Sum.inl` or `inl` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let value = LeanNat::from_usize(lean, 42)?;
    ///     let sum = LeanSum::inl(value.unbind())?;
    ///     assert!(LeanSum::isLeft(&sum));
    ///     Ok(())
    /// })
    /// ```
    pub fn inl<'l>(value: LeanBound<'l, LeanAny>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = value.lean_token();
            let ptr = ffi::lean_sum_inl(value.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a Sum with a right value (inr).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Sum.inr` or `inr` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let value = LeanString::from_str(lean, "hello")?;
    ///     let sum = LeanSum::inr(value.unbind())?;
    ///     assert!(LeanSum::isRight(&sum));
    ///     Ok(())
    /// })
    /// ```
    pub fn inr<'l>(value: LeanBound<'l, LeanAny>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = value.lean_token();
            let ptr = ffi::lean_sum_inr(value.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Check if the sum contains a left value (inl).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Sum.isLeft` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let sum = LeanSum::inl(value)?;
    /// assert!(LeanSum::isLeft(&sum));
    /// ```
    #[allow(non_snake_case)]
    pub fn isLeft<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe {
            let tag = ffi::lean_obj_tag(obj.as_ptr());
            tag == 0 // inl has tag 0
        }
    }

    /// Check if the sum contains a right value (inr).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Sum.isRight` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let sum = LeanSum::inr(value)?;
    /// assert!(LeanSum::isRight(&sum));
    /// ```
    #[allow(non_snake_case)]
    pub fn isRight<'l>(obj: &LeanBound<'l, Self>) -> bool {
        !Self::isLeft(obj)
    }

    /// Get the left value if the sum is inl, returns None if it's inr.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Sum.getLeft?` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let sum = LeanSum::inl(value)?;
    /// if let Some(left_val) = LeanSum::getLeft(&sum) {
    ///     // Use left_val
    /// }
    /// ```
    #[allow(non_snake_case)]
    pub fn getLeft<'l>(obj: &LeanBound<'l, Self>) -> Option<LeanBound<'l, LeanAny>> {
        if !Self::isLeft(obj) {
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

    /// Get the right value if the sum is inr, returns None if it's inl.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Sum.getRight?` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let sum = LeanSum::inr(value)?;
    /// if let Some(right_val) = LeanSum::getRight(&sum) {
    ///     // Use right_val
    /// }
    /// ```
    #[allow(non_snake_case)]
    pub fn getRight<'l>(obj: &LeanBound<'l, Self>) -> Option<LeanBound<'l, LeanAny>> {
        if !Self::isRight(obj) {
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

    /// Swap the left and right components of a sum.
    ///
    /// Maps `inl a` to `inr a` and `inr b` to `inl b`.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Sum.swap` in Lean4:
    /// ```lean
    /// def swap : α ⊕ β → β ⊕ α := Sum.elim inr inl
    /// ```
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let sum = LeanSum::inl(value)?;
    /// let swapped = LeanSum::swap(sum)?;
    /// assert!(LeanSum::isRight(&swapped));
    /// ```
    pub fn swap<'l>(obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = obj.lean_token();
            let tag = ffi::lean_obj_tag(obj.as_ptr());
            let val_ptr = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;

            // Increment ref count for the value we're extracting
            ffi::lean_inc(val_ptr);
            let value = LeanBound::from_owned_ptr(lean, val_ptr);

            // Drop the original object (decrement its refcount)
            drop(obj);

            // Create new sum with swapped tag
            if tag == 0 {
                // inl -> inr
                Self::inr(value)
            } else {
                // inr -> inl
                Self::inl(value)
            }
        }
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanSum> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if LeanSum::isLeft(self) {
            write!(f, "LeanSum::inl(...)")
        } else {
            write!(f, "LeanSum::inr(...)")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sum_size() {
        // Verify that LeanSum is zero-sized
        assert_eq!(std::mem::size_of::<LeanSum>(), 0);
    }
}
