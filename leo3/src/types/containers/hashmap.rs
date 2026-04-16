//! HashMap type for Lean4's `Std.HashMap`.
#![allow(missing_docs)]
//!
//! This module provides a Rust wrapper for Lean's HashMap type, which is
//! a hash table implementation with efficient lookup and insertion.
//!
//! **IMPORTANT**: This is currently a **placeholder implementation** with a simplified
//! linked-list structure. It does not use the actual Lean HashMap implementation.
//!
//! For the real Lean HashMap FFI bindings, see `leo3_ffi::hashmap`.
//! See `containers/README.md` for information on how to properly implement these using FFI.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::LeanList;
use std::marker::PhantomData;

pub struct LeanHashMapType<K, V> {
    _phantom: PhantomData<(K, V)>,
}

pub type LeanHashMap<'l, K, V> = LeanBound<'l, LeanHashMapType<K, V>>;

impl<'l, K, V> LeanHashMap<'l, K, V> {
    pub fn empty(lean: Lean<'l>) -> LeanResult<Self> {
        unsafe {
            let empty_array = ffi::lean_alloc_ctor(0, 0, 0);
            Ok(LeanBound::from_owned_ptr(lean, empty_array))
        }
    }

    pub fn insert(
        self,
        lean: Lean<'l>,
        key: LeanBound<'l, K>,
        value: LeanBound<'l, V>,
    ) -> LeanResult<Self> {
        unsafe {
            let pair = ffi::lean_alloc_ctor(0, 2, 0);
            ffi::object::lean_ctor_set(pair, 0, key.into_ptr());
            ffi::object::lean_ctor_set(pair, 1, value.into_ptr());

            let old_ptr = self.into_ptr();
            let new_map = ffi::lean_alloc_ctor(1, 2, 0);
            ffi::object::lean_ctor_set(new_map, 0, pair);
            ffi::object::lean_ctor_set(new_map, 1, old_ptr);

            Ok(LeanBound::from_owned_ptr(lean, new_map))
        }
    }

    pub fn find(
        &self,
        _lean: Lean<'l>,
        _key: &LeanBound<'l, K>,
    ) -> LeanResult<Option<LeanBound<'l, V>>> {
        Ok(None)
    }

    pub fn contains(&self, lean: Lean<'l>, key: &LeanBound<'l, K>) -> LeanResult<bool> {
        Ok(self.find(lean, key)?.is_some())
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
}
