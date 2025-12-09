//! Lean array type wrapper.

use crate::err::{LeanError, LeanResult};
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;

/// A Lean array object.
///
/// Arrays in Lean4 are dynamic arrays of Lean objects.
pub struct LeanArray {
    _private: (),
}

impl LeanArray {
    /// Create an empty Lean array.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Array.empty` in Lean4.
    /// ```lean
    /// def Array.empty : Array α := emptyWithCapacity 0
    /// ```
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let arr = LeanArray::empty(lean)?;
    ///     assert!(LeanArray::isEmpty(&arr));
    ///     Ok(())
    /// })
    /// ```
    pub fn empty<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Create an empty array by converting from an empty list (nil)
            // In Lean, this is represented as constructor 0 with no fields
            let nil_ptr = ffi::lean_alloc_ctor(0, 0, 0);
            let ptr = ffi::array::lean_array_mk(nil_ptr);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get the size of the array.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let arr = LeanArray::empty(lean)?;
    /// assert_eq!(LeanArray::size(&arr), 0);
    /// ```
    pub fn size<'l>(obj: &LeanBound<'l, Self>) -> usize {
        unsafe { ffi::array::lean_array_size(obj.as_ptr()) }
    }

    /// Check if the array is empty.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Array.isEmpty` in Lean4.
    #[allow(non_snake_case)]
    pub fn isEmpty<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::size(obj) == 0
    }

    /// Push an element to the end of the array.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let arr = LeanArray::empty(lean)?;
    /// let elem = LeanNat::from_usize(lean, 42)?;
    /// let arr = LeanArray::push(arr, elem.unbind())?;
    /// assert_eq!(LeanArray::size(&arr), 1);
    /// ```
    pub fn push<'l>(
        arr: LeanBound<'l, Self>,
        elem: LeanBound<'l, LeanAny>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = arr.lean_token();
            let ptr = ffi::array::lean_array_push(arr.into_ptr(), elem.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get an element from the array at the given index.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let elem = LeanArray::get(&arr, lean, 0);
    /// ```
    pub fn get<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
        index: usize,
    ) -> Option<LeanBound<'l, LeanAny>> {
        if index >= Self::size(obj) {
            return None;
        }

        unsafe {
            let ptr = ffi::array::lean_array_uget(obj.as_ptr(), index);
            Some(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Set an element in the array at the given index.
    ///
    /// Returns the modified array. If the array is exclusive (RC == 1),
    /// it's modified in-place. Otherwise, a copy is made.
    ///
    /// # Errors
    ///
    /// Returns an error if index is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let new_elem = LeanNat::from_usize(lean, 100)?;
    /// let arr = LeanArray::set(arr, 0, new_elem.unbind())?;
    /// ```
    pub fn set<'l>(
        arr: LeanBound<'l, Self>,
        index: usize,
        value: LeanBound<'l, LeanAny>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        if index >= Self::size(&arr) {
            return Err(LeanError::runtime("Index out of bounds"));
        }

        unsafe {
            let lean = arr.lean_token();
            let ptr = ffi::array::lean_array_uset(arr.into_ptr(), index, value.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Pop the last element from the array.
    ///
    /// Returns the modified array with the last element removed.
    ///
    /// # Errors
    ///
    /// Returns an error if the array is empty.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let arr = LeanArray::pop(arr)?;
    /// ```
    pub fn pop<'l>(arr: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        if Self::isEmpty(&arr) {
            return Err(LeanError::runtime("Cannot pop from empty array"));
        }

        unsafe {
            let lean = arr.lean_token();
            let ptr = ffi::array::lean_array_pop(arr.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Swap two elements in the array.
    ///
    /// # Errors
    ///
    /// Returns an error if either index is out of bounds.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let arr = LeanArray::swap(arr, 0, 1)?;
    /// ```
    pub fn swap<'l>(
        arr: LeanBound<'l, Self>,
        i: usize,
        j: usize,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let size = Self::size(&arr);
        if i >= size || j >= size {
            return Err(LeanError::runtime("Index out of bounds"));
        }

        unsafe {
            let lean = arr.lean_token();
            let ptr = ffi::array::lean_array_uswap(arr.into_ptr(), i, j);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create an array from a Lean list.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Array.mk` in Lean4.
    /// ```lean
    /// structure Array (α : Type u) where
    ///   mk :: toList : List α
    /// ```
    ///
    /// # Safety
    ///
    /// The list object must be a valid Lean list.
    pub unsafe fn mk<'l>(
        lean: Lean<'l>,
        list: LeanBound<'l, LeanAny>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let ptr = ffi::array::lean_array_mk(list.into_ptr());
        Ok(LeanBound::from_owned_ptr(lean, ptr))
    }

    /// Convert the array to a Lean list.
    pub fn to_list<'l>(arr: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanAny>> {
        unsafe {
            let lean = arr.lean_token();
            let ptr = ffi::array::lean_array_to_list(arr.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanArray> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanArray(size: {})", LeanArray::size(self))
    }
}
