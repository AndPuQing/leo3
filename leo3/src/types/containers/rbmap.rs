//! Red-Black Map (RBMap) type for Lean4's `Std.RBMap`.
#![allow(missing_docs)]
//!
//! This module provides a Rust wrapper for Lean's RBMap type, which is
//! a balanced binary search tree implementation that maintains sorted order.
//!
//! **IMPORTANT**: This is currently a **placeholder implementation** with a simplified
//! tree structure. It does not use the actual Lean RBMap implementation.
//!
//! For the real Lean RBMap FFI bindings, see `leo3_ffi::rbmap`.
//! See `containers/README.md` for information on how to properly implement these using FFI.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::LeanList;
use std::marker::PhantomData;

pub struct LeanRBMapType<K, V> {
    _phantom: PhantomData<(K, V)>,
}

pub type LeanRBMap<'l, K, V> = LeanBound<'l, LeanRBMapType<K, V>>;

impl<'l, K, V> LeanRBMap<'l, K, V> {
    pub fn empty(lean: Lean<'l>) -> LeanResult<Self> {
        unsafe {
            let empty = ffi::lean_alloc_ctor(0, 0, 0);
            Ok(LeanBound::from_owned_ptr(lean, empty))
        }
    }

    pub fn insert(
        self,
        lean: Lean<'l>,
        key: LeanBound<'l, K>,
        value: LeanBound<'l, V>,
    ) -> LeanResult<Self> {
        unsafe {
            let node = ffi::lean_alloc_ctor(1, 4, 0);
            ffi::object::lean_ctor_set(node, 0, key.into_ptr());
            ffi::object::lean_ctor_set(node, 1, value.into_ptr());
            let empty_left = ffi::lean_alloc_ctor(0, 0, 0);
            let empty_right = ffi::lean_alloc_ctor(0, 0, 0);
            ffi::object::lean_ctor_set(node, 2, empty_left);
            ffi::object::lean_ctor_set(node, 3, empty_right);
            Ok(LeanBound::from_owned_ptr(lean, node))
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

    pub fn is_empty(&self) -> bool {
        unsafe { ffi::object::lean_obj_tag(self.as_ptr()) == 0 }
    }

    pub fn size(&self) -> LeanResult<usize> {
        self.count_nodes(self.as_ptr())
    }

    #[allow(clippy::only_used_in_recursion)]
    fn count_nodes(&self, node: *mut ffi::lean_object) -> LeanResult<usize> {
        unsafe {
            let tag = ffi::object::lean_obj_tag(node);
            if tag == 0 {
                Ok(0)
            } else {
                let left = ffi::object::lean_ctor_get(node, 2) as *mut ffi::lean_object;
                let right = ffi::object::lean_ctor_get(node, 3) as *mut ffi::lean_object;
                Ok(1 + self.count_nodes(left)? + self.count_nodes(right)?)
            }
        }
    }

    pub fn min(&self, lean: Lean<'l>) -> LeanResult<Option<LeanBound<'l, K>>> {
        if self.is_empty() {
            return Ok(None);
        }

        let mut current = self.as_ptr();
        unsafe {
            while ffi::object::lean_obj_tag(current) != 0 {
                let left = ffi::object::lean_ctor_get(current, 2) as *mut ffi::lean_object;
                if ffi::object::lean_obj_tag(left) == 0 {
                    let key_ptr = ffi::object::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                    ffi::object::lean_inc(key_ptr);
                    return Ok(Some(LeanBound::from_owned_ptr(lean, key_ptr)));
                }
                current = left;
            }
        }

        Ok(None)
    }

    pub fn max(&self, lean: Lean<'l>) -> LeanResult<Option<LeanBound<'l, K>>> {
        if self.is_empty() {
            return Ok(None);
        }

        let mut current = self.as_ptr();
        unsafe {
            while ffi::object::lean_obj_tag(current) != 0 {
                let right = ffi::object::lean_ctor_get(current, 3) as *mut ffi::lean_object;
                if ffi::object::lean_obj_tag(right) == 0 {
                    let key_ptr = ffi::object::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                    ffi::object::lean_inc(key_ptr);
                    return Ok(Some(LeanBound::from_owned_ptr(lean, key_ptr)));
                }
                current = right;
            }
        }

        Ok(None)
    }

    pub fn to_list(&self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanList>> {
        unsafe {
            let nil = ffi::lean_alloc_ctor(0, 0, 0);
            Ok(LeanBound::from_owned_ptr(lean, nil))
        }
    }
}
