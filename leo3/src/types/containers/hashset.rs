//! HashSet type for Lean4's `Std.HashSet`.
#![allow(missing_docs)]
//!
//! This module provides a Rust wrapper for Lean's HashSet type, which is
//! a hash table-based set implementation for efficient membership testing.
//!
//! **IMPORTANT**: This is currently a **placeholder implementation** with a simplified
//! linked-list structure. It does not use the actual Lean HashSet implementation.
//!
//! For the real Lean HashSet FFI bindings, see `leo3_ffi::hashset`.
//! See `containers/README.md` for information on how to properly implement these using FFI.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::LeanList;
use std::marker::PhantomData;

pub struct LeanHashSetType<T> {
    _phantom: PhantomData<T>,
}

pub type LeanHashSet<'l, T> = LeanBound<'l, LeanHashSetType<T>>;

impl<'l, T> LeanHashSet<'l, T> {
    pub fn empty(lean: Lean<'l>) -> LeanResult<Self> {
        unsafe {
            let empty = ffi::lean_alloc_ctor(0, 0, 0);
            Ok(LeanBound::from_owned_ptr(lean, empty))
        }
    }

    pub fn insert(self, lean: Lean<'l>, elem: LeanBound<'l, T>) -> LeanResult<Self> {
        unsafe {
            let old_ptr = self.into_ptr();
            let new_set = ffi::lean_alloc_ctor(1, 2, 0);
            ffi::object::lean_ctor_set(new_set, 0, elem.into_ptr());
            ffi::object::lean_ctor_set(new_set, 1, old_ptr);

            Ok(LeanBound::from_owned_ptr(lean, new_set))
        }
    }

    pub fn contains(&self, _lean: Lean<'l>, _elem: &LeanBound<'l, T>) -> LeanResult<bool> {
        Ok(false)
    }

    pub fn erase(self, lean: Lean<'l>, _elem: &LeanBound<'l, T>) -> LeanResult<Self> {
        unsafe {
            let ptr = self.into_ptr();
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn size(&self) -> LeanResult<usize> {
        let mut count = 0;
        let mut current = self.as_ptr();

        unsafe {
            while !current.is_null() && ffi::object::lean_obj_tag(current) == 1 {
                count += 1;
                current = ffi::object::lean_ctor_get(current, 1) as *mut ffi::lean_object;
            }
        }

        Ok(count)
    }

    pub fn is_empty(&self) -> LeanResult<bool> {
        Ok(self.size()? == 0)
    }

    pub fn to_list(&self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanList>> {
        unsafe {
            ffi::object::lean_inc(self.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, self.as_ptr()))
        }
    }

    pub fn from_list(lean: Lean<'l>, list: LeanBound<'l, LeanList>) -> LeanResult<Self> {
        unsafe {
            let ptr = list.into_ptr();
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn union(&self, lean: Lean<'l>, other: &Self) -> LeanResult<Self> {
        unsafe {
            ffi::object::lean_inc(self.as_ptr());
            ffi::object::lean_inc(other.as_ptr());

            let result = ffi::lean_alloc_ctor(1, 2, 0);
            ffi::object::lean_ctor_set(result, 0, self.as_ptr());
            ffi::object::lean_ctor_set(result, 1, other.as_ptr());

            Ok(LeanBound::from_owned_ptr(lean, result))
        }
    }

    pub fn intersection(&self, lean: Lean<'l>, _other: &Self) -> LeanResult<Self> {
        Self::empty(lean)
    }

    pub fn difference(&self, lean: Lean<'l>, _other: &Self) -> LeanResult<Self> {
        unsafe {
            ffi::object::lean_inc(self.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, self.as_ptr()))
        }
    }

    pub fn is_subset(&self, _lean: Lean<'l>, _other: &Self) -> LeanResult<bool> {
        Ok(false)
    }
}
