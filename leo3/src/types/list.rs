//! Lean list type wrapper.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;
use crate::types::LeanOption;

/// A Lean list object.
///
/// Lists in Lean4 are inductively defined:
/// ```lean
/// inductive List (α : Type u) where
///   | nil : List α
///   | cons (head : α) (tail : List α) : List α
/// ```
///
/// # Lean4 Reference
/// Lists are linked lists with:
/// - O(1) prepend (cons)
/// - O(n) length, append, and indexed access
/// - Reference-counted memory management
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
            // List.nil is a scalar (lean_box(0)) — NOT a heap-allocated constructor.
            // The C++ runtime checks `is_scalar(raw())` to detect nil.
            let ptr = ffi::inline::lean_box(0);
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
            let ptr = ffi::lean_list_cons(head.into_ptr(), tail.into_ptr());
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

    /// Create a singleton list.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.singleton` in Lean4.
    pub fn singleton<'l>(elem: LeanBound<'l, LeanAny>) -> LeanResult<LeanBound<'l, Self>> {
        let lean = elem.lean_token();
        let nil = Self::nil(lean)?;
        Self::cons(elem, nil)
    }

    /// Append two lists.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.append` in Lean4 (also `++` operator).
    pub fn append<'l>(
        xs: LeanBound<'l, Self>,
        ys: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let lean = xs.lean_token();
        if Self::isEmpty(&xs) {
            return Ok(ys);
        }
        if Self::isEmpty(&ys) {
            return Ok(xs);
        }

        // Collect elements from xs in reverse order
        let mut elements = Vec::new();
        let mut current = unsafe {
            ffi::lean_inc(xs.as_ptr());
            xs.as_ptr()
        };

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                elements.push(head);
                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        // Build the result by prepending elements in reverse order to ys
        let mut result = ys;
        for elem_ptr in elements.into_iter().rev() {
            let elem = unsafe { LeanBound::from_owned_ptr(lean, elem_ptr) };
            result = Self::cons(elem, result)?;
        }

        Ok(result)
    }

    /// Reverse the list.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.reverse` in Lean4.
    pub fn reverse<'l>(obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let lean = obj.lean_token();
        let mut result = Self::nil(lean)?;

        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                let elem = LeanBound::from_owned_ptr(lean, head);
                result = Self::cons(elem, result)?;

                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        Ok(result)
    }

    /// Get head as an Option.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.head?` in Lean4.
    #[allow(non_snake_case)]
    pub fn headOpt<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanOption>> {
        let lean = obj.lean_token();
        match Self::head(obj) {
            Some(head) => LeanOption::some(head),
            None => LeanOption::none(lean),
        }
    }

    /// Get tail as an Option.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.tail?` in Lean4.
    #[allow(non_snake_case)]
    pub fn tailOpt<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanOption>> {
        let lean = obj.lean_token();
        match Self::tail(obj) {
            Some(tail) => {
                // Cast to LeanAny first
                unsafe {
                    let ptr = tail.as_ptr();
                    ffi::lean_inc(ptr);
                    LeanOption::some(LeanBound::from_owned_ptr(lean, ptr))
                }
            }
            None => LeanOption::none(lean),
        }
    }

    /// Get head with a default value.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.headD` in Lean4.
    #[allow(non_snake_case)]
    pub fn headD<'l>(
        obj: &LeanBound<'l, Self>,
        default: LeanBound<'l, LeanAny>,
    ) -> LeanBound<'l, LeanAny> {
        match Self::head(obj) {
            Some(head) => {
                unsafe {
                    ffi::lean_dec(default.into_ptr());
                }
                head
            }
            None => default,
        }
    }

    /// Get element at index.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.get?` in Lean4.
    pub fn get<'l>(obj: &LeanBound<'l, Self>, index: usize) -> Option<LeanBound<'l, LeanAny>> {
        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        let mut i = 0;
        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                if i == index {
                    let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                    ffi::lean_inc(head);
                    ffi::lean_dec(current);
                    return Some(LeanBound::from_owned_ptr(obj.lean_token(), head));
                }
                i += 1;
                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        None
    }

    /// Get element at index with a default.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.getD` in Lean4.
    #[allow(non_snake_case)]
    pub fn getD<'l>(
        obj: &LeanBound<'l, Self>,
        index: usize,
        default: LeanBound<'l, LeanAny>,
    ) -> LeanBound<'l, LeanAny> {
        match Self::get(obj, index) {
            Some(elem) => {
                unsafe {
                    ffi::lean_dec(default.into_ptr());
                }
                elem
            }
            None => default,
        }
    }

    /// Get the last element.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.getLast?` in Lean4.
    #[allow(non_snake_case)]
    pub fn getLast<'l>(obj: &LeanBound<'l, Self>) -> Option<LeanBound<'l, LeanAny>> {
        if Self::isEmpty(obj) {
            return None;
        }

        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        let mut last_head: Option<*mut ffi::lean_object> = None;

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                // Release previous last if any
                if let Some(prev) = last_head {
                    ffi::lean_dec(prev);
                }
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                last_head = Some(head);

                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        last_head.map(|ptr| unsafe { LeanBound::from_owned_ptr(obj.lean_token(), ptr) })
    }

    /// Check if list contains an element using equality function.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.contains` in Lean4.
    pub fn contains<'l, F>(obj: &LeanBound<'l, Self>, elem: &LeanBound<'l, LeanAny>, eq: F) -> bool
    where
        F: Fn(&LeanBound<'l, LeanAny>, &LeanBound<'l, LeanAny>) -> bool,
    {
        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                let head_bound = LeanBound::from_owned_ptr(obj.lean_token(), head);

                if eq(&head_bound, elem) {
                    ffi::lean_dec(current);
                    return true;
                }

                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        false
    }

    /// Check if all elements satisfy a predicate.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.all` in Lean4.
    pub fn all<'l, F>(obj: &LeanBound<'l, Self>, pred: F) -> bool
    where
        F: Fn(&LeanBound<'l, LeanAny>) -> bool,
    {
        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                let head_bound = LeanBound::from_owned_ptr(obj.lean_token(), head);

                if !pred(&head_bound) {
                    ffi::lean_dec(current);
                    return false;
                }

                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        true
    }

    /// Check if any element satisfies a predicate.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.any` in Lean4.
    pub fn any<'l, F>(obj: &LeanBound<'l, Self>, pred: F) -> bool
    where
        F: Fn(&LeanBound<'l, LeanAny>) -> bool,
    {
        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                let head_bound = LeanBound::from_owned_ptr(obj.lean_token(), head);

                if pred(&head_bound) {
                    ffi::lean_dec(current);
                    return true;
                }

                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        false
    }

    /// Find the first element satisfying a predicate.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.find?` in Lean4.
    pub fn find<'l, F>(obj: &LeanBound<'l, Self>, pred: F) -> Option<LeanBound<'l, LeanAny>>
    where
        F: Fn(&LeanBound<'l, LeanAny>) -> bool,
    {
        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                let head_bound = LeanBound::from_owned_ptr(obj.lean_token(), head);

                if pred(&head_bound) {
                    ffi::lean_dec(current);
                    return Some(head_bound);
                }

                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        None
    }

    /// Filter the list with a predicate.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.filter` in Lean4.
    pub fn filter<'l, F>(obj: LeanBound<'l, Self>, pred: F) -> LeanResult<LeanBound<'l, Self>>
    where
        F: Fn(&LeanBound<'l, LeanAny>) -> bool,
    {
        let lean = obj.lean_token();
        let mut elements = Vec::new();

        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                let head_bound: LeanBound<'_, LeanAny> = LeanBound::from_owned_ptr(lean, head);

                if pred(&head_bound) {
                    ffi::lean_inc(head);
                    elements.push(head);
                }

                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        // Build the result list
        let mut result = Self::nil(lean)?;
        for elem_ptr in elements.into_iter().rev() {
            let elem = unsafe { LeanBound::from_owned_ptr(lean, elem_ptr) };
            result = Self::cons(elem, result)?;
        }

        Ok(result)
    }

    /// Map a function over the list.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.map` in Lean4.
    pub fn map<'l, F>(obj: LeanBound<'l, Self>, f: F) -> LeanResult<LeanBound<'l, Self>>
    where
        F: Fn(LeanBound<'l, LeanAny>) -> LeanResult<LeanBound<'l, LeanAny>>,
    {
        let lean = obj.lean_token();
        let mut elements = Vec::new();

        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                let head_bound = LeanBound::from_owned_ptr(lean, head);
                let mapped = f(head_bound)?;
                elements.push(mapped.into_ptr());

                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        // Build the result list
        let mut result = Self::nil(lean)?;
        for elem_ptr in elements.into_iter().rev() {
            let elem = unsafe { LeanBound::from_owned_ptr(lean, elem_ptr) };
            result = Self::cons(elem, result)?;
        }

        Ok(result)
    }

    /// Fold left over the list.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.foldl` in Lean4.
    pub fn foldl<'l, A, F>(obj: &LeanBound<'l, Self>, init: A, f: F) -> A
    where
        F: Fn(A, LeanBound<'l, LeanAny>) -> A,
    {
        let mut acc = init;
        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                let head_bound = LeanBound::from_owned_ptr(obj.lean_token(), head);
                acc = f(acc, head_bound);

                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        acc
    }

    /// Take the first n elements.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.take` in Lean4.
    pub fn take<'l>(obj: LeanBound<'l, Self>, n: usize) -> LeanResult<LeanBound<'l, Self>> {
        let lean = obj.lean_token();
        if n == 0 {
            return Self::nil(lean);
        }

        let mut elements = Vec::new();
        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };
        let mut count = 0;

        unsafe {
            while ffi::lean_obj_tag(current) != 0 && count < n {
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                elements.push(head);
                count += 1;

                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
            }
            ffi::lean_dec(current);
        }

        // Build the result list
        let mut result = Self::nil(lean)?;
        for elem_ptr in elements.into_iter().rev() {
            let elem = unsafe { LeanBound::from_owned_ptr(lean, elem_ptr) };
            result = Self::cons(elem, result)?;
        }

        Ok(result)
    }

    /// Drop the first n elements.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.drop` in Lean4.
    pub fn drop<'l>(obj: LeanBound<'l, Self>, n: usize) -> LeanResult<LeanBound<'l, Self>> {
        let lean = obj.lean_token();
        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };
        let mut count = 0;

        unsafe {
            while ffi::lean_obj_tag(current) != 0 && count < n {
                let next = ffi::lean_ctor_get(current, 1) as *mut ffi::lean_object;
                ffi::lean_inc(next);
                ffi::lean_dec(current);
                current = next;
                count += 1;
            }
        }

        // The remaining list
        Ok(unsafe { LeanBound::from_owned_ptr(lean, current) })
    }

    /// Count elements satisfying a predicate.
    ///
    /// # Lean4 Reference
    /// Corresponds to `List.countP` in Lean4.
    #[allow(non_snake_case)]
    pub fn countP<'l, F>(obj: &LeanBound<'l, Self>, pred: F) -> usize
    where
        F: Fn(&LeanBound<'l, LeanAny>) -> bool,
    {
        let mut count = 0;
        let mut current = unsafe {
            ffi::lean_inc(obj.as_ptr());
            obj.as_ptr()
        };

        unsafe {
            while ffi::lean_obj_tag(current) != 0 {
                let head = ffi::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                ffi::lean_inc(head);
                let head_bound = LeanBound::from_owned_ptr(obj.lean_token(), head);

                if pred(&head_bound) {
                    count += 1;
                }

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
