//! Hash set wrapper for Lean's real `Std.HashSet` runtime representation.
#![allow(missing_docs)]

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::{LeanList, LeanNat, LeanOption};
use std::marker::PhantomData;

pub struct LeanHashSetType<T> {
    _phantom: PhantomData<T>,
}

pub type LeanHashSet<'l, T> = LeanBound<'l, LeanHashSetType<T>>;

pub use super::hashmap::LeanHashKey;

#[inline]
unsafe fn beq_closure<K: LeanHashKey>() -> *mut ffi::lean_object {
    ffi::inline::lean_alloc_closure(K::decidable_eq_boxed(), 2, 0)
}

#[inline]
unsafe fn borrowed_hash<K: LeanHashKey>() -> *mut ffi::lean_object {
    K::hash_closure()
}

#[inline]
unsafe fn owned_view<T>(obj: &LeanBound<'_, T>) -> *mut ffi::lean_object {
    let ptr = obj.as_ptr();
    ffi::lean_inc(ptr);
    ptr
}

impl<'l, T: LeanHashKey> LeanHashSet<'l, T> {
    pub fn empty(lean: Lean<'l>) -> LeanResult<Self> {
        unsafe {
            let ptr = ffi::hashset::lean_hashset_empty(ffi::inline::lean_box(8));
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn insert(self, lean: Lean<'l>, elem: LeanBound<'l, T>) -> LeanResult<Self> {
        unsafe {
            let beq = beq_closure::<T>();
            let ptr = ffi::hashset::l_Std_HashSet_insert___redArg(
                beq,
                borrowed_hash::<T>(),
                self.into_ptr(),
                elem.into_ptr(),
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn contains(&self, _lean: Lean<'l>, elem: &LeanBound<'l, T>) -> LeanResult<bool> {
        let contains = unsafe {
            let beq = beq_closure::<T>();
            ffi::hashset::l_Std_HashSet_contains___redArg(
                beq,
                borrowed_hash::<T>(),
                owned_view(self),
                elem.as_ptr(),
            )
        };
        Ok(contains != 0)
    }

    pub fn get(&self, lean: Lean<'l>, elem: &LeanBound<'l, T>) -> LeanResult<Option<LeanBound<'l, T>>> {
        unsafe {
            let beq = beq_closure::<T>();
            let ptr = ffi::hashset::l_Std_HashSet_get_x3f___redArg(
                beq,
                borrowed_hash::<T>(),
                owned_view(self),
                elem.as_ptr(),
            );
            let opt = LeanBound::<LeanOption>::from_owned_ptr(lean, ptr);
            Ok(LeanOption::get(&opt).map(|value| value.cast()))
        }
    }

    pub fn erase(self, lean: Lean<'l>, elem: &LeanBound<'l, T>) -> LeanResult<Self> {
        unsafe {
            let beq = beq_closure::<T>();
            let ptr = ffi::hashset::l_Std_HashSet_erase___redArg(
                beq,
                borrowed_hash::<T>(),
                self.into_ptr(),
                elem.as_ptr(),
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn size(&self) -> LeanResult<usize> {
        let lean = self.lean_token();
        unsafe {
            let ptr = ffi::hashset::l_Std_HashSet_size___redArg(owned_view(self));
            let size = LeanBound::<LeanNat>::from_owned_ptr(lean, ptr);
            LeanNat::to_usize(&size)
        }
    }

    pub fn is_empty(&self) -> LeanResult<bool> {
        Ok(self.size()? == 0)
    }

    pub fn to_list(&self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanList>> {
        unsafe {
            let ptr = ffi::hashset::l_Std_HashSet_toList___redArg(owned_view(self));
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn from_list(lean: Lean<'l>, list: LeanBound<'l, LeanList>) -> LeanResult<Self> {
        let mut set = Self::empty(lean)?;
        let mut current = list;
        while !crate::types::LeanList::isEmpty(&current) {
            let elem = crate::types::LeanList::head(&current).expect("non-empty list should have head");
            let elem: LeanBound<'l, T> = elem.cast();
            set = set.insert(lean, elem)?;
            current = crate::types::LeanList::tail(&current).expect("non-empty list should have tail");
        }
        Ok(set)
    }
}
