//! Lean array type wrapper.

use crate::ffi;
use crate::marker::Lean;
use crate::instance::{LeanBound, LeanAny};
use crate::err::LeanResult;

/// A Lean array object.
pub struct LeanArray {
    _private: (),
}

impl LeanArray {
    /// Create a new empty Lean array.
    pub fn new<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::lean_alloc_array(0, std::mem::size_of::<*mut ffi::lean_object>());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get the size of the array.
    pub fn size<'l>(obj: &LeanBound<'l, Self>) -> usize {
        unsafe { ffi::lean_array_size(obj.as_ptr()) }
    }

    /// Get an element from the array.
    ///
    /// Returns `None` if the index is out of bounds.
    pub fn get<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
        index: usize,
    ) -> Option<LeanBound<'l, LeanAny>> {
        if index >= Self::size(obj) {
            return None;
        }

        unsafe {
            let ptr = ffi::lean_array_get(obj.as_ptr(), index);
            Some(LeanBound::from_borrowed_ptr(lean, ptr))
        }
    }

    /// Check if the array is empty.
    pub fn is_empty<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::size(obj) == 0
    }
}
