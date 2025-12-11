//! Lean sigma (dependent pair) type wrapper.
//!
//! The `Sigma` type represents dependent pairs where the second element's type
//! depends on the value of the first element.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};

/// A Lean sigma (dependent pair) object.
///
/// Sigma in Lean4 is defined as a structure:
/// ```lean
/// structure Sigma {α : Type u} (β : α → Type v) where
///   mk :: fst : α | snd : β fst
/// ```
///
/// `Sigma β` (written `Σ a : α, β a` or `(a : α) × β a` in Lean4) is a dependent pair
/// where the type of the second component depends on the value of the first component.
///
/// # Runtime Representation
///
/// At runtime, Sigma is identical to Prod (a product/pair). The dependency between types
/// exists only at the type level and is erased during compilation. Like Prod, it's
/// represented as a constructor with tag 0 and two object fields (fst, snd).
///
/// # Difference from Prod
///
/// While `Prod α β` requires both types to be fixed, `Sigma β` allows the second type
/// to depend on the first value. This is useful for representing heterogeneous collections
/// or values paired with their type information.
pub struct LeanSigma {
    _private: (),
}

impl LeanSigma {
    /// Create a dependent pair (Sigma).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Sigma.mk` or `⟨fst, snd⟩` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let first = LeanNat::from_usize(lean, 42)?;
    ///     let second = LeanString::from_str(lean, "hello")?;
    ///     let sigma = LeanSigma::mk(first.unbind(), second.unbind())?;
    ///     Ok(())
    /// })
    /// ```
    pub fn mk<'l>(
        fst: LeanBound<'l, LeanAny>,
        snd: LeanBound<'l, LeanAny>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = fst.lean_token();
            // Sigma.mk is constructor 0 with 2 fields (fst, snd)
            // Identical to Prod at runtime
            let ptr = ffi::lean_alloc_ctor(0, 2, 0);
            ffi::lean_ctor_set(ptr, 0, fst.into_ptr());
            ffi::lean_ctor_set(ptr, 1, snd.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get the first element of the dependent pair.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Sigma.fst` or `.1` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let sigma = LeanSigma::mk(first, second)?;
    /// let fst_val = LeanSigma::fst(&sigma);
    /// ```
    pub fn fst<'l>(obj: &LeanBound<'l, Self>) -> LeanBound<'l, LeanAny> {
        unsafe {
            let lean = obj.lean_token();
            let fst_ptr = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;
            // Increment ref count since we're borrowing
            ffi::lean_inc(fst_ptr);
            LeanBound::from_owned_ptr(lean, fst_ptr)
        }
    }

    /// Get the second element of the dependent pair.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Sigma.snd` or `.2` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let sigma = LeanSigma::mk(first, second)?;
    /// let snd_val = LeanSigma::snd(&sigma);
    /// ```
    pub fn snd<'l>(obj: &LeanBound<'l, Self>) -> LeanBound<'l, LeanAny> {
        unsafe {
            let lean = obj.lean_token();
            let snd_ptr = ffi::lean_ctor_get(obj.as_ptr(), 1) as *mut ffi::lean_object;
            // Increment ref count since we're borrowing
            ffi::lean_inc(snd_ptr);
            LeanBound::from_owned_ptr(lean, snd_ptr)
        }
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanSigma> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanSigma(⟨..., ...⟩)")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sigma_size() {
        // Verify that LeanSigma is zero-sized
        assert_eq!(std::mem::size_of::<LeanSigma>(), 0);
    }
}
