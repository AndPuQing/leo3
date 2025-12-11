//! Lean product (pair) type wrapper.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};

/// A Lean product (pair) object.
///
/// Products in Lean4 are defined as a structure:
/// ```lean
/// structure Prod (α : Type u) (β : Type v) where
///   mk :: fst : α | snd : β
/// ```
pub struct LeanProd {
    _private: (),
}

impl LeanProd {
    /// Create a product (pair) from two values.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Prod.mk` or `(a, b)` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let a = LeanNat::from_usize(lean, 42)?;
    ///     let b = LeanNat::from_usize(lean, 100)?;
    ///     let pair = LeanProd::mk(a.unbind(), b.unbind())?;
    ///     Ok(())
    /// })
    /// ```
    pub fn mk<'l>(
        fst: LeanBound<'l, LeanAny>,
        snd: LeanBound<'l, LeanAny>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = fst.lean_token();
            // Prod.mk is constructor 0 with 2 fields (fst, snd)
            let ptr = ffi::lean_alloc_ctor(0, 2, 0);
            ffi::lean_ctor_set(ptr, 0, fst.into_ptr());
            ffi::lean_ctor_set(ptr, 1, snd.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get the first element of the pair.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Prod.fst` or `.1` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let pair = LeanProd::mk(a, b)?;
    /// let first = LeanProd::fst(&pair);
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

    /// Get the second element of the pair.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Prod.snd` or `.2` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let pair = LeanProd::mk(a, b)?;
    /// let second = LeanProd::snd(&pair);
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

    /// Swap the elements of a pair.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Prod.swap` in Lean4.
    pub fn swap<'l>(obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let fst = Self::fst(&obj);
        let snd = Self::snd(&obj);
        Self::mk(snd, fst)
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanProd> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanProd(..., ...)")
    }
}
