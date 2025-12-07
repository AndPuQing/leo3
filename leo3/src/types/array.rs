//! Lean array type wrapper.

use crate::ffi;
use crate::marker::Lean;
use crate::instance::{LeanBound, LeanAny};
use crate::err::LeanResult;

/// A Lean array object.
///
/// Arrays in Lean4 are dynamic arrays of Lean objects.
pub struct LeanArray {
    _private: (),
}

impl LeanArray {
    /// Create a new empty Lean array.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let arr = LeanArray::new(lean)?;
    ///     assert!(LeanArray::is_empty(&arr));
    ///     Ok(())
    /// })
    /// ```
    pub fn new<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
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
    /// let arr = LeanArray::new(lean)?;
    /// assert_eq!(LeanArray::size(&arr), 0);
    /// ```
    pub fn size<'l>(obj: &LeanBound<'l, Self>) -> usize {
        unsafe { ffi::array::lean_array_size(obj.as_ptr()) }
    }

    /// Check if the array is empty.
    pub fn is_empty<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::size(obj) == 0
    }

    /// Push an element to the end of the array.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let arr = LeanArray::new(lean)?;
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
    /// # Panics
    ///
    /// Panics if index is out of bounds.
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
        assert!(index < Self::size(&arr), "Index out of bounds");

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
    /// # Panics
    ///
    /// Panics if the array is empty.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let arr = LeanArray::pop(arr)?;
    /// ```
    pub fn pop<'l>(arr: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        assert!(!Self::is_empty(&arr), "Cannot pop from empty array");

        unsafe {
            let lean = arr.lean_token();
            let ptr = ffi::array::lean_array_pop(arr.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Swap two elements in the array.
    ///
    /// # Panics
    ///
    /// Panics if either index is out of bounds.
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
        assert!(i < size && j < size, "Index out of bounds");

        unsafe {
            let lean = arr.lean_token();
            let ptr = ffi::array::lean_array_uswap(arr.into_ptr(), i, j);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create an array from a Lean list.
    ///
    /// # Safety
    ///
    /// The list object must be a valid Lean list.
    pub unsafe fn from_list<'l>(
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
