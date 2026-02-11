//! Lean option type wrapper.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;
use crate::types::LeanList;

/// A Lean option object.
///
/// Options in Lean4 are inductively defined:
/// ```lean
/// inductive Option (α : Type u) where
///   | none : Option α
///   | some (val : α) : Option α
/// ```
///
/// # Lean4 Reference
/// Options can be thought of as:
/// - Nullable types (none = absence, some = presence)
/// - Collections with at most one element
/// - Computations that may fail
pub struct LeanOption {
    _private: (),
}

impl LeanOption {
    /// Create an Option with no value (none).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.none` or `none` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let opt = LeanOption::none(lean)?;
    ///     assert!(LeanOption::isNone(&opt));
    ///     Ok(())
    /// })
    /// ```
    pub fn none<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Option.none is a scalar (lean_box(0)) — NOT a heap-allocated constructor.
            // The C++ runtime checks `is_scalar(raw())` to detect none.
            let ptr = ffi::inline::lean_box(0);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create an Option with a value (some).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.some` or `some` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let value = LeanNat::from_usize(lean, 42)?;
    /// let opt = LeanOption::some(value.unbind())?;
    /// assert!(LeanOption::isSome(&opt));
    /// ```
    pub fn some<'l>(value: LeanBound<'l, LeanAny>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = value.lean_token();
            // Option.some is constructor 1 with 1 field (val)
            let ptr = ffi::lean_alloc_ctor(1, 1, 0);
            ffi::lean_ctor_set(ptr, 0, value.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Check if the option is none.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.isNone` in Lean4.
    #[allow(non_snake_case)]
    pub fn isNone<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe {
            let tag = ffi::lean_obj_tag(obj.as_ptr());
            tag == 0 // none has tag 0
        }
    }

    /// Check if the option is some.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.isSome` in Lean4.
    #[allow(non_snake_case)]
    pub fn isSome<'l>(obj: &LeanBound<'l, Self>) -> bool {
        !Self::isNone(obj)
    }

    /// Get the value from the option if it's some.
    ///
    /// Returns `None` if the option is none.
    ///
    /// # Lean4 Reference
    /// Similar to pattern matching on `some val` in Lean4.
    pub fn get<'l>(obj: &LeanBound<'l, Self>) -> Option<LeanBound<'l, LeanAny>> {
        if Self::isNone(obj) {
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

    /// Convert to Rust Option.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let opt = LeanOption::some(value)?;
    /// if let Some(val) = LeanOption::toRustOption(&opt) {
    ///     // use val
    /// }
    /// ```
    #[allow(non_snake_case)]
    pub fn toRustOption<'l>(obj: &LeanBound<'l, Self>) -> Option<LeanBound<'l, LeanAny>> {
        Self::get(obj)
    }

    /// Get the value with a default if none.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.getD` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let opt = LeanOption::none(lean)?;
    /// let default = LeanNat::from_usize(lean, 0)?;
    /// let val = LeanOption::getD(&opt, default.unbind());
    /// ```
    #[allow(non_snake_case)]
    pub fn getD<'l>(
        obj: &LeanBound<'l, Self>,
        default: LeanBound<'l, LeanAny>,
    ) -> LeanBound<'l, LeanAny> {
        match Self::get(obj) {
            Some(val) => {
                // We got the value, need to decrement default's ref count
                unsafe {
                    ffi::lean_dec(default.into_ptr());
                }
                val
            }
            None => default,
        }
    }

    /// Map a function over the option value.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.map` in Lean4.
    ///
    /// Returns none if the option is none, otherwise applies the function
    /// to the value and wraps the result in some.
    pub fn map<'l, F>(obj: LeanBound<'l, Self>, f: F) -> LeanResult<LeanBound<'l, Self>>
    where
        F: FnOnce(LeanBound<'l, LeanAny>) -> LeanResult<LeanBound<'l, LeanAny>>,
    {
        let lean = obj.lean_token();
        if Self::isNone(&obj) {
            return Self::none(lean);
        }

        match Self::get(&obj) {
            Some(val) => {
                let result = f(val)?;
                Self::some(result)
            }
            None => Self::none(lean),
        }
    }

    /// Bind (flatMap) over the option value.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.bind` in Lean4.
    ///
    /// Returns none if the option is none, otherwise applies the function
    /// to the value and returns the result (which is itself an Option).
    pub fn bind<'l, F>(obj: LeanBound<'l, Self>, f: F) -> LeanResult<LeanBound<'l, Self>>
    where
        F: FnOnce(LeanBound<'l, LeanAny>) -> LeanResult<LeanBound<'l, Self>>,
    {
        let lean = obj.lean_token();
        if Self::isNone(&obj) {
            return Self::none(lean);
        }

        match Self::get(&obj) {
            Some(val) => f(val),
            None => Self::none(lean),
        }
    }

    /// Filter the option based on a predicate.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.filter` in Lean4.
    ///
    /// Returns some(val) if the option is some and the predicate returns true,
    /// otherwise returns none.
    pub fn filter<'l, F>(obj: LeanBound<'l, Self>, pred: F) -> LeanResult<LeanBound<'l, Self>>
    where
        F: FnOnce(&LeanBound<'l, LeanAny>) -> bool,
    {
        let lean = obj.lean_token();
        if Self::isNone(&obj) {
            return Self::none(lean);
        }

        match Self::get(&obj) {
            Some(val) => {
                if pred(&val) {
                    Self::some(val)
                } else {
                    Self::none(lean)
                }
            }
            None => Self::none(lean),
        }
    }

    /// Convert option to a list.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.toList` in Lean4.
    ///
    /// Returns a list with zero or one element.
    #[allow(non_snake_case)]
    pub fn toList<'l>(obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanList>> {
        let lean = obj.lean_token();
        if Self::isNone(&obj) {
            LeanList::nil(lean)
        } else {
            match Self::get(&obj) {
                Some(val) => {
                    let nil = LeanList::nil(lean)?;
                    LeanList::cons(val, nil)
                }
                None => LeanList::nil(lean),
            }
        }
    }

    /// Combine two options using a function.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.merge` in Lean4.
    ///
    /// If both are some, applies the merge function.
    /// If one is none, returns the other.
    /// If both are none, returns none.
    pub fn merge<'l, F>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
        f: F,
    ) -> LeanResult<LeanBound<'l, Self>>
    where
        F: FnOnce(
            LeanBound<'l, LeanAny>,
            LeanBound<'l, LeanAny>,
        ) -> LeanResult<LeanBound<'l, LeanAny>>,
    {
        let lean = a.lean_token();
        let a_is_none = Self::isNone(&a);
        let b_is_none = Self::isNone(&b);

        match (a_is_none, b_is_none) {
            (true, true) => Self::none(lean),
            (true, false) => match Self::get(&b) {
                Some(val) => Self::some(val),
                None => Self::none(lean),
            },
            (false, true) => match Self::get(&a) {
                Some(val) => Self::some(val),
                None => Self::none(lean),
            },
            (false, false) => match (Self::get(&a), Self::get(&b)) {
                (Some(va), Some(vb)) => {
                    let merged = f(va, vb)?;
                    Self::some(merged)
                }
                _ => Self::none(lean),
            },
        }
    }

    /// Or combinator: returns this option if some, otherwise the other.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.or` in Lean4.
    pub fn or<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let lean = a.lean_token();
        if Self::isSome(&a) {
            match Self::get(&a) {
                Some(val) => Self::some(val),
                None => Self::none(lean),
            }
        } else {
            match Self::get(&b) {
                Some(val) => Self::some(val),
                None => Self::none(lean),
            }
        }
    }

    /// Check if the option is some and equals a specific value.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.isEqSome` in Lean4.
    #[allow(non_snake_case)]
    pub fn isEqSome<'l, F>(obj: &LeanBound<'l, Self>, val: &LeanBound<'l, LeanAny>, eq: F) -> bool
    where
        F: FnOnce(&LeanBound<'l, LeanAny>, &LeanBound<'l, LeanAny>) -> bool,
    {
        match Self::get(obj) {
            Some(inner) => eq(&inner, val),
            None => false,
        }
    }

    /// Check if a predicate holds for all elements (true if none).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.all` in Lean4.
    pub fn all<'l, F>(obj: &LeanBound<'l, Self>, pred: F) -> bool
    where
        F: FnOnce(&LeanBound<'l, LeanAny>) -> bool,
    {
        match Self::get(obj) {
            Some(val) => pred(&val),
            None => true,
        }
    }

    /// Check if a predicate holds for any element (false if none).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.any` in Lean4.
    pub fn any<'l, F>(obj: &LeanBound<'l, Self>, pred: F) -> bool
    where
        F: FnOnce(&LeanBound<'l, LeanAny>) -> bool,
    {
        match Self::get(obj) {
            Some(val) => pred(&val),
            None => false,
        }
    }

    /// Flatten a nested option.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Option.join` in Lean4.
    ///
    /// Note: This requires the inner value to be an Option as well.
    pub fn join<'l>(obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let lean = obj.lean_token();
        if Self::isNone(&obj) {
            return Self::none(lean);
        }

        match Self::get(&obj) {
            Some(inner) => {
                // The inner value should be an Option
                // Cast it and return
                unsafe {
                    let ptr = inner.as_ptr();
                    ffi::lean_inc(ptr);
                    Ok(LeanBound::from_owned_ptr(lean, ptr))
                }
            }
            None => Self::none(lean),
        }
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanOption> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if LeanOption::isNone(self) {
            write!(f, "LeanOption::none")
        } else {
            write!(f, "LeanOption::some(...)")
        }
    }
}
