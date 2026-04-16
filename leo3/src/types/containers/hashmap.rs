//! Hash map wrapper for Lean's real `Std.HashMap` runtime representation.
#![allow(missing_docs)]

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::{LeanISize, LeanInt, LeanInt16, LeanInt32, LeanInt64, LeanInt8, LeanList, LeanNat, LeanOption, LeanProd, LeanString};
use std::ffi::c_void;
use std::marker::PhantomData;

pub struct LeanHashMapType<K, V> {
    _phantom: PhantomData<(K, V)>,
}

pub type LeanHashMap<'l, K, V> = LeanBound<'l, LeanHashMapType<K, V>>;

pub trait LeanHashKey {
    #[doc(hidden)]
    unsafe fn decidable_eq_boxed() -> *mut c_void;
    #[doc(hidden)]
    unsafe fn hash_closure() -> *mut ffi::lean_object;
}

unsafe extern "C" {
    static mut l_instHashableNat: *mut ffi::lean_object;
    static mut l_instHashableInt: *mut ffi::lean_object;
    static mut l_instHashableString: *mut ffi::lean_object;
    static mut l_instHashableInt8: *mut ffi::lean_object;
    static mut l_instHashableInt16: *mut ffi::lean_object;
    static mut l_instHashableInt32: *mut ffi::lean_object;
    static mut l_instHashableInt64: *mut ffi::lean_object;
    static mut l_instHashableISize: *mut ffi::lean_object;

    fn l_instDecidableEqNat___boxed(a: *mut ffi::lean_object, b: *mut ffi::lean_object) -> *mut ffi::lean_object;
    fn l_instDecidableEqInt___boxed(a: *mut ffi::lean_object, b: *mut ffi::lean_object) -> *mut ffi::lean_object;
    fn l_instDecidableEqString___boxed(a: *mut ffi::lean_object, b: *mut ffi::lean_object) -> *mut ffi::lean_object;
    fn l_instDecidableEqInt8___boxed(a: *mut ffi::lean_object, b: *mut ffi::lean_object) -> *mut ffi::lean_object;
    fn l_instDecidableEqInt16___boxed(a: *mut ffi::lean_object, b: *mut ffi::lean_object) -> *mut ffi::lean_object;
    fn l_instDecidableEqInt32___boxed(a: *mut ffi::lean_object, b: *mut ffi::lean_object) -> *mut ffi::lean_object;
    fn l_instDecidableEqInt64___boxed(a: *mut ffi::lean_object, b: *mut ffi::lean_object) -> *mut ffi::lean_object;
    fn l_instDecidableEqISize___boxed(a: *mut ffi::lean_object, b: *mut ffi::lean_object) -> *mut ffi::lean_object;
}

impl LeanHashKey for LeanNat {
    unsafe fn decidable_eq_boxed() -> *mut c_void {
        l_instDecidableEqNat___boxed as *mut c_void
    }
    unsafe fn hash_closure() -> *mut ffi::lean_object {
        l_instHashableNat
    }
}

impl LeanHashKey for LeanInt {
    unsafe fn decidable_eq_boxed() -> *mut c_void {
        l_instDecidableEqInt___boxed as *mut c_void
    }
    unsafe fn hash_closure() -> *mut ffi::lean_object {
        l_instHashableInt
    }
}

impl LeanHashKey for LeanString {
    unsafe fn decidable_eq_boxed() -> *mut c_void {
        l_instDecidableEqString___boxed as *mut c_void
    }
    unsafe fn hash_closure() -> *mut ffi::lean_object {
        l_instHashableString
    }
}

impl LeanHashKey for LeanInt8 {
    unsafe fn decidable_eq_boxed() -> *mut c_void {
        l_instDecidableEqInt8___boxed as *mut c_void
    }
    unsafe fn hash_closure() -> *mut ffi::lean_object {
        l_instHashableInt8
    }
}

impl LeanHashKey for LeanInt16 {
    unsafe fn decidable_eq_boxed() -> *mut c_void {
        l_instDecidableEqInt16___boxed as *mut c_void
    }
    unsafe fn hash_closure() -> *mut ffi::lean_object {
        l_instHashableInt16
    }
}

impl LeanHashKey for LeanInt32 {
    unsafe fn decidable_eq_boxed() -> *mut c_void {
        l_instDecidableEqInt32___boxed as *mut c_void
    }
    unsafe fn hash_closure() -> *mut ffi::lean_object {
        l_instHashableInt32
    }
}

impl LeanHashKey for LeanInt64 {
    unsafe fn decidable_eq_boxed() -> *mut c_void {
        l_instDecidableEqInt64___boxed as *mut c_void
    }
    unsafe fn hash_closure() -> *mut ffi::lean_object {
        l_instHashableInt64
    }
}

impl LeanHashKey for LeanISize {
    unsafe fn decidable_eq_boxed() -> *mut c_void {
        l_instDecidableEqISize___boxed as *mut c_void
    }
    unsafe fn hash_closure() -> *mut ffi::lean_object {
        l_instHashableISize
    }
}

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

impl<'l, K: LeanHashKey, V> LeanHashMap<'l, K, V> {
    pub fn empty(lean: Lean<'l>) -> LeanResult<Self> {
        unsafe {
            let ptr = ffi::hashmap::l_Std_HashMap_emptyWithCapacity___redArg(ffi::inline::lean_box(8));
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn insert(
        self,
        lean: Lean<'l>,
        key: LeanBound<'l, K>,
        value: LeanBound<'l, V>,
    ) -> LeanResult<Self> {
        unsafe {
            let beq = beq_closure::<K>();
            let ptr = ffi::hashmap::l_Std_HashMap_insert___redArg(
                beq,
                borrowed_hash::<K>(),
                self.into_ptr(),
                key.into_ptr(),
                value.into_ptr(),
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn find(
        &self,
        lean: Lean<'l>,
        key: &LeanBound<'l, K>,
    ) -> LeanResult<Option<LeanBound<'l, V>>> {
        unsafe {
            let beq = beq_closure::<K>();
            let ptr = ffi::hashmap::l_Std_HashMap_get_x3f___redArg(
                beq,
                borrowed_hash::<K>(),
                owned_view(self),
                key.as_ptr(),
            );
            let opt = LeanBound::<LeanOption>::from_owned_ptr(lean, ptr);
            Ok(LeanOption::get(&opt).map(|value| value.cast()))
        }
    }

    pub fn contains(&self, _lean: Lean<'l>, key: &LeanBound<'l, K>) -> LeanResult<bool> {
        let contains = unsafe {
            let beq = beq_closure::<K>();
            ffi::hashmap::l_Std_HashMap_contains___redArg(
                beq,
                borrowed_hash::<K>(),
                owned_view(self),
                key.as_ptr(),
            )
        };
        Ok(contains != 0)
    }

    pub fn erase(self, lean: Lean<'l>, key: &LeanBound<'l, K>) -> LeanResult<Self> {
        unsafe {
            let beq = beq_closure::<K>();
            let ptr = ffi::hashmap::l_Std_HashMap_erase___redArg(
                beq,
                borrowed_hash::<K>(),
                self.into_ptr(),
                key.as_ptr(),
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn size(&self) -> LeanResult<usize> {
        let lean = self.lean_token();
        unsafe {
            let ptr = ffi::hashmap::l_Std_HashMap_size___redArg(owned_view(self));
            let size = LeanBound::<LeanNat>::from_owned_ptr(lean, ptr);
            LeanNat::to_usize(&size)
        }
    }

    pub fn is_empty(&self) -> LeanResult<bool> {
        Ok(self.size()? == 0)
    }

    pub fn to_list(&self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanList>> {
        unsafe {
            let ptr = ffi::hashmap::l_Std_HashMap_toList___redArg(owned_view(self));
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn from_list(lean: Lean<'l>, list: LeanBound<'l, LeanList>) -> LeanResult<Self> {
        let mut map = Self::empty(lean)?;
        let mut current = list;
        while !crate::types::LeanList::isEmpty(&current) {
            let pair = crate::types::LeanList::head(&current)
                .expect("non-empty list should have head");
            let pair: LeanBound<'l, LeanProd> = pair.cast();
            let key: LeanBound<'l, K> = LeanProd::fst(&pair).cast();
            let value: LeanBound<'l, V> = LeanProd::snd(&pair).cast();
            map = map.insert(lean, key, value)?;
            current = crate::types::LeanList::tail(&current)
                .expect("non-empty list should have tail");
        }
        Ok(map)
    }
}
