//! Semantic constructor helpers for standard Lean types.
//!
//! These replace raw `lean_alloc_ctor` + `lean_ctor_set` sequences with
//! named functions that convey intent and encode the correct tag/arity.
//!
//! lean.h does NOT provide helpers for most of these types (Option, List,
//! Except, Prod, Bool, Sum), so we maintain them here.

use crate::object::{lean_obj_arg, lean_object};

/// Construct a Lean `Bool` value.
///
/// Bool.false = tag 0, Bool.true = tag 1. Both are zero-field constructors
/// and must be represented as **scalars** (`lean_box`), not heap objects.
#[inline]
pub unsafe fn lean_mk_bool(b: bool) -> *mut lean_object {
    crate::inline::lean_box(b as usize)
}

/// Construct Lean `Unit.unit`.
///
/// Unit is a zero-field constructor (tag 0) represented as a scalar.
#[inline]
pub unsafe fn lean_mk_unit() -> *mut lean_object {
    crate::inline::lean_box(0)
}

/// Construct `Option.some a` (tag 1, 1 object field).
#[inline]
pub unsafe fn lean_option_some(a: lean_obj_arg) -> *mut lean_object {
    let obj = super::lean_alloc_ctor(1, 1, 0);
    crate::object::lean_ctor_set(obj, 0, a);
    obj
}

/// Construct `List.cons head tail` (tag 1, 2 object fields).
#[inline]
pub unsafe fn lean_list_cons(head: lean_obj_arg, tail: lean_obj_arg) -> *mut lean_object {
    let obj = super::lean_alloc_ctor(1, 2, 0);
    crate::object::lean_ctor_set(obj, 0, head);
    crate::object::lean_ctor_set(obj, 1, tail);
    obj
}

/// Construct `Except.error e` (tag 0, 1 object field).
#[inline]
pub unsafe fn lean_except_error(e: lean_obj_arg) -> *mut lean_object {
    let obj = super::lean_alloc_ctor(0, 1, 0);
    crate::object::lean_ctor_set(obj, 0, e);
    obj
}

/// Construct `Except.ok a` (tag 1, 1 object field).
#[inline]
pub unsafe fn lean_except_ok(a: lean_obj_arg) -> *mut lean_object {
    let obj = super::lean_alloc_ctor(1, 1, 0);
    crate::object::lean_ctor_set(obj, 0, a);
    obj
}

/// Construct `Prod.mk fst snd` (tag 0, 2 object fields).
///
/// Also used for `Sigma.mk` which has identical runtime representation.
#[inline]
pub unsafe fn lean_prod_mk(fst: lean_obj_arg, snd: lean_obj_arg) -> *mut lean_object {
    let obj = super::lean_alloc_ctor(0, 2, 0);
    crate::object::lean_ctor_set(obj, 0, fst);
    crate::object::lean_ctor_set(obj, 1, snd);
    obj
}

/// Construct `Sum.inl a` (tag 0, 1 object field).
#[inline]
pub unsafe fn lean_sum_inl(a: lean_obj_arg) -> *mut lean_object {
    let obj = super::lean_alloc_ctor(0, 1, 0);
    crate::object::lean_ctor_set(obj, 0, a);
    obj
}

/// Construct `Sum.inr b` (tag 1, 1 object field).
#[inline]
pub unsafe fn lean_sum_inr(b: lean_obj_arg) -> *mut lean_object {
    let obj = super::lean_alloc_ctor(1, 1, 0);
    crate::object::lean_ctor_set(obj, 0, b);
    obj
}

/// Construct a single-field wrapper (tag 0, 1 object field).
///
/// Used for types like `BitVec`, `Fin`, `Subtype` where the runtime
/// representation is a trivial constructor wrapping one value.
#[inline]
pub unsafe fn lean_mk_wrapper(val: lean_obj_arg) -> *mut lean_object {
    let obj = super::lean_alloc_ctor(0, 1, 0);
    crate::object::lean_ctor_set(obj, 0, val);
    obj
}
