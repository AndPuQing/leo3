//! Lean list type wrapper.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;

/// A Lean list object.
///
/// Lists in Lean4 are inductively defined:
/// ```lean
/// inductive List (α : Type u) where
///   | nil : List α
///   | cons (head : α) (tail : List α) : List α
/// ```
pub struct LeanList {
    _private: (),
}

impl LeanList {
    /// Create an empty list (nil).
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.nil` or `[]` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let list = LeanList::nil(lean)?;
    ///     assert!(LeanList::isEmpty(&list));
    ///     Ok(())
    /// })
    /// ```
    pub fn nil<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // List.nil is constructor 0 with no fields
            let ptr = ffi::lean_alloc_ctor(0, 0, 0);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a list by prepending an element to an existing list (cons).
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.cons` or `::` operator in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let list = LeanList::nil(lean)?;
    /// let list = LeanList::cons(elem, list)?;
    /// ```
    pub fn cons<'l>(
        head: LeanBound<'l, LeanAny>,
        tail: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = head.lean_token();
            // List.cons is constructor 1 with 2 fields (head, tail)
            let ptr = ffi::lean_alloc_ctor(1, 2, 0);
            ffi::lean_ctor_set(ptr, 0, head.into_ptr());
            ffi::lean_ctor_set(ptr, 1, tail.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Check if the list is empty (nil).
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.isEmpty` in Lean4.
    #[allow(non_snake_case)]
    pub fn isEmpty<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe {
            let tag = ffi::lean_obj_tag(obj.as_ptr());
            tag == 0 // nil has tag 0
        }
    }

    /// Get the head of the list.
    ///
    /// Returns `None` if the list is empty.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.head?` in Lean4.
    pub fn head<'l>(obj: &LeanBound<'l, Self>) -> Option<LeanBound<'l, LeanAny>> {
        if Self::isEmpty(obj) {
            return None;
        }

        unsafe {
            let lean = obj.lean_token();
            let head_ptr = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;
            // Increment ref count since we're borrowing
            ffi::lean_inc(head_ptr);
            Some(LeanBound::from_owned_ptr(lean, head_ptr))
        }
    }

    /// Get the tail of the list.
    ///
    /// Returns `None` if the list is empty.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.tail?` in Lean4.
    pub fn tail<'l>(obj: &LeanBound<'l, Self>) -> Option<LeanBound<'l, Self>> {
        if Self::isEmpty(obj) {
            return None;
        }

        unsafe {
            let lean = obj.lean_token();
            let tail_ptr = ffi::lean_ctor_get(obj.as_ptr(), 1) as *mut ffi::lean_object;
            // Increment ref count since we're borrowing
            ffi::lean_inc(tail_ptr);
            Some(LeanBound::from_owned_ptr(lean, tail_ptr))
        }
    }

    /// Get the length of the list.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.length` in Lean4.
    pub fn length<'l>(obj: &LeanBound<'l, Self>) -> usize {
        let mut count = 0;
        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                count += 1;
                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        count
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanList> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanList(length: {})", LeanList::length(self))
    }
}
