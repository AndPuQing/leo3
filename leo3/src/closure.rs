//! Safe wrapper for Lean closures.
//!
//! This module provides [`LeanClosure`], a safe wrapper around Lean's closure
//! objects that supports inspection and application.
//!
//! # Example
//!
//! ```rust,ignore
//! use leo3::prelude::*;
//! use leo3::closure::LeanClosure;
//!
//! fn example<'l>(lean: Lean<'l>, closure: LeanClosure<'l>) -> LeanResult<()> {
//!     // Check arity
//!     println!("Arity: {}", closure.arity());
//!     println!("Remaining: {}", closure.remaining_arity());
//!
//!     // Apply arguments
//!     let result = closure.apply(42u64)?;
//!     Ok(())
//! }
//! ```

use crate::conversion::{FromLean, IntoLean};
use crate::err::{LeanError, LeanResult};
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};

/// Marker type for Lean closure objects.
pub struct LeanClosureType {
    _private: (),
}

/// A safe wrapper around a Lean closure object.
///
/// `LeanClosure` provides:
/// - Inspection of closure arity and fixed arguments
/// - Safe application with type-checked arguments
/// - Partial application support
///
/// # Memory Management
///
/// Like other Lean objects, closures use reference counting. The `LeanClosure`
/// wrapper automatically manages reference counts through [`LeanBound`].
///
/// # Important: Closure Consumption
///
/// Lean's `lean_apply_*` functions consume the closure. This wrapper clones
/// the closure before application to allow multiple calls. For single-use
/// scenarios with better performance, use the `*_once` variants.
pub type LeanClosure<'l> = LeanBound<'l, LeanClosureType>;

impl<'l> LeanClosure<'l> {
    // ========================================================================
    // Type Checking
    // ========================================================================

    /// Check if a Lean object is a closure.
    ///
    /// Returns `true` if the object is a closure, `false` otherwise.
    #[inline]
    pub fn is_closure(obj: &LeanBound<'l, LeanAny>) -> bool {
        unsafe {
            let ptr = obj.as_ptr();
            !ffi::inline::lean_is_scalar(ptr) && ffi::inline::lean_is_closure(ptr)
        }
    }

    /// Try to convert a `LeanBound<LeanAny>` to a `LeanClosure`.
    ///
    /// Returns `Some(closure)` if the object is a closure, `None` otherwise.
    #[inline]
    pub fn try_from_any(obj: LeanBound<'l, LeanAny>) -> Option<Self> {
        if Self::is_closure(&obj) {
            Some(obj.cast())
        } else {
            None
        }
    }

    // ========================================================================
    // Inspection
    // ========================================================================

    /// Get the total arity of this closure.
    ///
    /// This is the total number of arguments the underlying function expects,
    /// regardless of how many have already been applied.
    #[inline]
    pub fn arity(&self) -> u16 {
        unsafe {
            let closure = self.as_ptr() as *const ffi::inline::lean_closure_object;
            (*closure).m_arity
        }
    }

    /// Get the number of arguments already applied to this closure.
    ///
    /// This represents how many arguments have been captured through
    /// partial application.
    #[inline]
    pub fn num_fixed(&self) -> u16 {
        unsafe {
            let closure = self.as_ptr() as *const ffi::inline::lean_closure_object;
            (*closure).m_num_fixed
        }
    }

    /// Get the number of arguments still needed to fully apply this closure.
    ///
    /// Returns `arity() - num_fixed()`.
    #[inline]
    pub fn remaining_arity(&self) -> u16 {
        self.arity().saturating_sub(self.num_fixed())
    }

    /// Check if this closure is fully saturated (ready to be called).
    ///
    /// A saturated closure has all its arguments applied and can be
    /// called with no additional arguments.
    #[inline]
    pub fn is_saturated(&self) -> bool {
        self.remaining_arity() == 0
    }

    // ========================================================================
    // Application (returns LeanAny - caller casts as needed)
    // ========================================================================

    /// Apply this closure to one argument, returning a new closure or result.
    ///
    /// If the closure needs more than one argument, this returns a new
    /// partially-applied closure. If this was the last argument needed,
    /// the closure is executed and the result is returned.
    ///
    /// # Note
    ///
    /// This clones the closure before application. For single-use scenarios,
    /// use [`apply_once`](Self::apply_once) for better performance.
    pub fn apply(&self, arg: LeanBound<'l, LeanAny>) -> LeanBound<'l, LeanAny> {
        let lean = self.lean_token();
        let closure_clone = self.clone();

        unsafe {
            let result = ffi::closure::lean_apply_1(closure_clone.into_ptr(), arg.into_ptr());
            LeanBound::from_owned_ptr(lean, result)
        }
    }

    /// Apply this closure to one argument, consuming the closure.
    ///
    /// This is more efficient than [`apply`](Self::apply) when you don't
    /// need to reuse the closure.
    pub fn apply_once(self, arg: LeanBound<'l, LeanAny>) -> LeanBound<'l, LeanAny> {
        let lean = self.lean_token();

        unsafe {
            let result = ffi::closure::lean_apply_1(self.into_ptr(), arg.into_ptr());
            LeanBound::from_owned_ptr(lean, result)
        }
    }

    /// Apply this closure to two arguments.
    pub fn apply2(
        &self,
        a: LeanBound<'l, LeanAny>,
        b: LeanBound<'l, LeanAny>,
    ) -> LeanBound<'l, LeanAny> {
        let lean = self.lean_token();
        let closure_clone = self.clone();

        unsafe {
            let result =
                ffi::closure::lean_apply_2(closure_clone.into_ptr(), a.into_ptr(), b.into_ptr());
            LeanBound::from_owned_ptr(lean, result)
        }
    }

    /// Apply this closure to three arguments.
    pub fn apply3(
        &self,
        a: LeanBound<'l, LeanAny>,
        b: LeanBound<'l, LeanAny>,
        c: LeanBound<'l, LeanAny>,
    ) -> LeanBound<'l, LeanAny> {
        let lean = self.lean_token();
        let closure_clone = self.clone();

        unsafe {
            let result = ffi::closure::lean_apply_3(
                closure_clone.into_ptr(),
                a.into_ptr(),
                b.into_ptr(),
                c.into_ptr(),
            );
            LeanBound::from_owned_ptr(lean, result)
        }
    }

    /// Apply this closure to four arguments.
    pub fn apply4(
        &self,
        a: LeanBound<'l, LeanAny>,
        b: LeanBound<'l, LeanAny>,
        c: LeanBound<'l, LeanAny>,
        d: LeanBound<'l, LeanAny>,
    ) -> LeanBound<'l, LeanAny> {
        let lean = self.lean_token();
        let closure_clone = self.clone();

        unsafe {
            let result = ffi::closure::lean_apply_4(
                closure_clone.into_ptr(),
                a.into_ptr(),
                b.into_ptr(),
                c.into_ptr(),
                d.into_ptr(),
            );
            LeanBound::from_owned_ptr(lean, result)
        }
    }

    /// Apply this closure to a dynamic number of arguments.
    ///
    /// The arguments are consumed.
    pub fn apply_n(&self, args: Vec<LeanBound<'l, LeanAny>>) -> LeanBound<'l, LeanAny> {
        let lean = self.lean_token();
        let closure_clone = self.clone();

        let mut arg_ptrs: Vec<*mut ffi::lean_object> =
            args.into_iter().map(|arg| arg.into_ptr()).collect();

        unsafe {
            let result = ffi::closure::lean_apply_n(
                closure_clone.into_ptr(),
                arg_ptrs.len() as libc::c_uint,
                arg_ptrs.as_mut_ptr(),
            );
            LeanBound::from_owned_ptr(lean, result)
        }
    }

    /// Apply this closure to a dynamic number of arguments, consuming the closure.
    pub fn apply_n_once(self, args: Vec<LeanBound<'l, LeanAny>>) -> LeanBound<'l, LeanAny> {
        let lean = self.lean_token();

        let mut arg_ptrs: Vec<*mut ffi::lean_object> =
            args.into_iter().map(|arg| arg.into_ptr()).collect();

        unsafe {
            let result = ffi::closure::lean_apply_n(
                self.into_ptr(),
                arg_ptrs.len() as libc::c_uint,
                arg_ptrs.as_mut_ptr(),
            );
            LeanBound::from_owned_ptr(lean, result)
        }
    }

    // ========================================================================
    // Type-Converting Call Methods
    // ========================================================================

    /// Call this closure with 1 argument, converting types automatically.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let result: u64 = closure.call1::<u64, u64>(42)?;
    /// ```
    pub fn call1<A, R>(&self, a: A) -> LeanResult<R>
    where
        A: IntoLean<'l> + 'l,
        R: FromLean<'l> + 'l,
    {
        let lean = self.lean_token();
        let a_obj = a.into_lean(lean)?.cast::<LeanAny>();
        let result = self.apply(a_obj);
        R::from_lean(&result.cast())
    }

    /// Call this closure with 2 arguments, converting types automatically.
    pub fn call2<A, B, R>(&self, a: A, b: B) -> LeanResult<R>
    where
        A: IntoLean<'l> + 'l,
        B: IntoLean<'l> + 'l,
        R: FromLean<'l> + 'l,
    {
        let lean = self.lean_token();
        let a_obj = a.into_lean(lean)?.cast::<LeanAny>();
        let b_obj = b.into_lean(lean)?.cast::<LeanAny>();
        let result = self.apply2(a_obj, b_obj);
        R::from_lean(&result.cast())
    }

    /// Call this closure with 3 arguments, converting types automatically.
    pub fn call3<A, B, C, R>(&self, a: A, b: B, c: C) -> LeanResult<R>
    where
        A: IntoLean<'l> + 'l,
        B: IntoLean<'l> + 'l,
        C: IntoLean<'l> + 'l,
        R: FromLean<'l> + 'l,
    {
        let lean = self.lean_token();
        let a_obj = a.into_lean(lean)?.cast::<LeanAny>();
        let b_obj = b.into_lean(lean)?.cast::<LeanAny>();
        let c_obj = c.into_lean(lean)?.cast::<LeanAny>();
        let result = self.apply3(a_obj, b_obj, c_obj);
        R::from_lean(&result.cast())
    }

    /// Call this closure with 4 arguments, converting types automatically.
    pub fn call4<A, B, C, D, R>(&self, a: A, b: B, c: C, d: D) -> LeanResult<R>
    where
        A: IntoLean<'l> + 'l,
        B: IntoLean<'l> + 'l,
        C: IntoLean<'l> + 'l,
        D: IntoLean<'l> + 'l,
        R: FromLean<'l> + 'l,
    {
        let lean = self.lean_token();
        let a_obj = a.into_lean(lean)?.cast::<LeanAny>();
        let b_obj = b.into_lean(lean)?.cast::<LeanAny>();
        let c_obj = c.into_lean(lean)?.cast::<LeanAny>();
        let d_obj = d.into_lean(lean)?.cast::<LeanAny>();
        let result = self.apply4(a_obj, b_obj, c_obj, d_obj);
        R::from_lean(&result.cast())
    }

    // ========================================================================
    // Helper Methods
    // ========================================================================

    /// Check that the closure can accept the given number of arguments.
    #[allow(dead_code)]
    fn check_arity(&self, n: usize) -> LeanResult<()> {
        let remaining = self.remaining_arity() as usize;
        if remaining != n {
            return Err(LeanError::Conversion(format!(
                "Closure expects {} arguments, got {}",
                remaining, n
            )));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_closure_type_size() {
        // LeanClosure should be pointer-sized (same as LeanBound)
        assert_eq!(
            std::mem::size_of::<LeanClosure>(),
            std::mem::size_of::<*mut ()>()
        );
    }
}
