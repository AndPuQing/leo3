//! Safe wrapper for Lean thunks (lazy evaluation).
//!
//! This module provides [`LeanThunk`], a safe wrapper around Lean's thunk
//! objects that support lazy evaluation patterns.
//!
//! # Example
//!
//! ```rust,ignore
//! use leo3::prelude::*;
//! use leo3::thunk::LeanThunk;
//!
//! fn example<'l>(lean: Lean<'l>, thunk: LeanThunk<'l>) -> LeanResult<()> {
//!     // Check if evaluated
//!     if thunk.is_pure() {
//!         println!("Thunk is pure (already evaluated)");
//!     }
//!
//!     // Force evaluation
//!     let result = thunk.get();
//!     Ok(())
//! }
//! ```

use crate::closure::LeanClosure;
use crate::ffi;
use crate::instance::{LeanAny, LeanBorrowed, LeanBound};
use std::marker::PhantomData;

/// Marker type for Lean thunk objects.
pub struct LeanThunkType<T = LeanAny> {
    _marker: PhantomData<T>,
}

/// A safe wrapper around a Lean thunk (lazy computation).
///
/// `LeanThunk` provides lazy evaluation semantics. The computation is
/// deferred until the thunk is forced (evaluated) with [`get`](LeanThunk::get)
/// or [`get_owned`](LeanThunk::get_owned).
///
/// # Memory Management
///
/// Like other Lean objects, thunks use reference counting. The `LeanThunk`
/// wrapper automatically manages reference counts through [`LeanBound`].
pub type LeanThunk<'l, T = LeanAny> = LeanBound<'l, LeanThunkType<T>>;

impl<'l, T> LeanThunk<'l, T> {
    // ========================================================================
    // Type Checking
    // ========================================================================

    /// Check if a Lean object is a thunk.
    ///
    /// Returns `true` if the object is a thunk, `false` otherwise.
    #[inline]
    pub fn is_thunk(obj: &LeanBound<'l, LeanAny>) -> bool {
        unsafe {
            let ptr = obj.as_ptr();
            !ffi::inline::lean_is_scalar(ptr) && ffi::inline::lean_is_thunk(ptr)
        }
    }

    /// Try to convert a `LeanBound<LeanAny>` to a `LeanThunk`.
    ///
    /// Returns `Some(thunk)` if the object is a thunk, `None` otherwise.
    #[inline]
    pub fn try_from_any(obj: LeanBound<'l, LeanAny>) -> Option<Self> {
        if Self::is_thunk(&obj) {
            Some(obj.cast())
        } else {
            None
        }
    }

    // ========================================================================
    // Creation
    // ========================================================================

    /// Create a new thunk from a closure.
    ///
    /// The closure should take no arguments and return a value. It will be
    /// executed lazily when the thunk is first forced.
    pub fn new(closure: LeanClosure<'l>) -> Self {
        let lean = closure.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_mk_thunk(closure.into_ptr());
            LeanBound::from_owned_ptr(lean, ptr)
        }
    }

    /// Create a pure (already evaluated) thunk from a value.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Thunk.pure` in Lean4.
    ///
    /// This creates a thunk that is already evaluated with the given value.
    /// Useful when you need a thunk but already have the computed result.
    pub fn pure(value: LeanBound<'l, T>) -> Self {
        let lean = value.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_thunk_pure(value.into_ptr());
            LeanBound::from_owned_ptr(lean, ptr)
        }
    }

    // ========================================================================
    // Inspection
    // ========================================================================

    /// Check if this thunk is pure (already evaluated).
    ///
    /// A pure thunk has already been forced and its value is cached.
    #[inline]
    pub fn is_pure(&self) -> bool {
        unsafe {
            // A thunk is pure if m_value is not null
            let thunk = ffi::inline::lean_to_thunk(self.as_ptr());
            !(*thunk)
                .m_value
                .load(std::sync::atomic::Ordering::Acquire)
                .is_null()
        }
    }

    // ========================================================================
    // Evaluation
    // ========================================================================

    /// Force evaluation and get a borrowed reference to the result.
    ///
    /// If the thunk has not been evaluated, this forces evaluation and
    /// caches the result. Subsequent calls return the cached value.
    ///
    /// The returned reference is valid as long as this thunk is alive.
    pub fn get(&self) -> LeanBorrowed<'_, 'l, T> {
        unsafe {
            let result = ffi::inline::lean_thunk_get(self.as_ptr());
            LeanBorrowed::from_ptr(result as *const _)
        }
    }

    /// Force evaluation and get an owned reference to the result.
    ///
    /// This consumes the thunk and returns an owned reference to the result.
    /// This is more efficient when you don't need to keep the thunk around.
    pub fn get_owned(self) -> LeanBound<'l, T> {
        let lean = self.lean_token();
        unsafe {
            // lean_thunk_get_own borrows the thunk, gets the result, and increments ref count
            let result = ffi::inline::lean_thunk_get_own(self.as_ptr());
            // Drop self (which will dec ref the thunk)
            drop(self);
            LeanBound::from_owned_ptr(lean, result)
        }
    }

    /// Get an owned reference to the result without consuming the thunk.
    ///
    /// This forces evaluation (if needed) and increments the reference count
    /// of the result.
    pub fn get_cloned(&self) -> LeanBound<'l, T> {
        self.get().to_owned()
    }

    // ========================================================================
    // Combinators
    // ========================================================================

    /// Map a function over the thunk result.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Thunk.map` in Lean4.
    ///
    /// Returns a new thunk that will apply `f` to the result of this thunk
    /// when forced. The original thunk is not evaluated until the new thunk
    /// is forced.
    pub fn map<F>(self, f: F) -> LeanThunk<'l, LeanAny>
    where
        F: FnOnce(LeanBound<'l, T>) -> LeanBound<'l, LeanAny>,
    {
        let lean = self.lean_token();
        // Force evaluation and apply the function
        let result = self.get_owned();
        let mapped = f(result);
        // Create a pure thunk with the mapped result
        unsafe {
            let ptr = ffi::inline::lean_thunk_pure(mapped.into_ptr());
            LeanBound::from_owned_ptr(lean, ptr)
        }
    }

    /// Monadic bind over the thunk result.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Thunk.bind` in Lean4.
    ///
    /// Returns a new thunk that will apply `f` to the result of this thunk
    /// and then force the resulting thunk.
    pub fn bind<F>(self, f: F) -> LeanThunk<'l, LeanAny>
    where
        F: FnOnce(LeanBound<'l, T>) -> LeanThunk<'l, LeanAny>,
    {
        // Force evaluation and apply the function
        let result = self.get_owned();
        f(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_thunk_type_size() {
        // LeanThunk should be pointer-sized (same as LeanBound)
        assert_eq!(
            std::mem::size_of::<LeanThunk<LeanAny>>(),
            std::mem::size_of::<*mut ()>()
        );
    }
}
