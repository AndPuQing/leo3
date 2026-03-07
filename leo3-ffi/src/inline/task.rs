//! Task and thunk inline helpers.

use super::{
    layout::lean_thunk_object,
    object::{
        lean_alloc_small_object, lean_dec, lean_inc, lean_set_st_header, lean_to_thunk, lean_unbox,
    },
};
use crate::object::{b_lean_obj_arg, b_lean_obj_res, lean_obj_arg, lean_obj_res, lean_object};
use libc::c_uint;
use std::sync::atomic::Ordering;

// Task Inline Functions (from lean.h)
// ============================================================================

/// Spawn a task from a closure (inline wrapper around lean_task_spawn_core)
///
/// # Safety
/// - `c` must be a valid closure object (consumed)
/// - `prio` must be a boxed Lean `Task.Priority` scalar (`Nat`)
#[inline(always)]
pub unsafe fn lean_task_spawn(c: lean_obj_arg, prio: lean_obj_arg) -> lean_obj_res {
    crate::closure::lean_task_spawn_core(c, lean_unbox(prio) as c_uint, false)
}

/// Get owned task result (inline from lean.h)
///
/// This is an inline function in Lean headers that wraps lean_task_get.
///
/// # Safety
/// - `t` must be a valid task object (consumed)
#[inline(always)]
pub unsafe fn lean_task_get_own(t: lean_obj_arg) -> lean_obj_res {
    let r = crate::closure::lean_task_get(t) as lean_obj_res;
    lean_inc(r);
    lean_dec(t);
    r
}

/// Map a function over a task (inline wrapper around lean_task_map_core)
///
/// # Safety
/// - `f` must be a valid closure object (consumed)
/// - `t` must be a valid task object (consumed)
/// - `prio` must be a boxed Lean `Task.Priority` scalar (`Nat`)
/// - `sync` indicates if the task should be forced synchronously
#[inline(always)]
pub unsafe fn lean_task_map(
    f: lean_obj_arg,
    t: lean_obj_arg,
    prio: lean_obj_arg,
    sync: bool,
) -> lean_obj_res {
    crate::closure::lean_task_map_core(f, t, lean_unbox(prio) as c_uint, sync, false)
}

/// Bind a function over a task (inline wrapper around lean_task_bind_core)
///
/// # Safety
/// - `x` must be a valid task object (consumed)
/// - `f` must be a valid closure object (consumed)
/// - `prio` must be a boxed Lean `Task.Priority` scalar (`Nat`)
/// - `sync` indicates if the task should be forced synchronously
#[inline(always)]
pub unsafe fn lean_task_bind(
    x: lean_obj_arg,
    f: lean_obj_arg,
    prio: lean_obj_arg,
    sync: bool,
) -> lean_obj_res {
    crate::closure::lean_task_bind_core(x, f, lean_unbox(prio) as c_uint, sync, false)
}

// ============================================================================
// Thunk Inline Functions (from lean.h)
// ============================================================================

extern "C" {
    /// Core thunk evaluation function (exported from libleanshared)
    ///
    /// This is the only thunk function exported from libleanshared.so.
    /// All other thunk functions are static inline in lean.h and must
    /// be reimplemented in Rust.
    pub fn lean_thunk_get_core(t: *mut lean_object) -> *mut lean_object;
}

/// Create a new thunk from a closure (inline from lean.h)
///
/// # Safety
/// - `c` must be a valid closure object (consumed)
#[inline(always)]
pub unsafe fn lean_mk_thunk(c: lean_obj_arg) -> lean_obj_res {
    let o = lean_alloc_small_object(std::mem::size_of::<lean_thunk_object>() as c_uint);
    lean_set_st_header(o, crate::LEAN_THUNK, 0);

    // SAFETY: the object was just allocated with the thunk tag, so the cast to
    // `lean_thunk_object` is valid before initializing its atomic fields.
    let thunk = lean_to_thunk(o);
    // Use atomic stores for consistency with lean_thunk_object definition
    (*thunk)
        .m_value
        .store(std::ptr::null_mut(), Ordering::Relaxed);
    (*thunk).m_closure.store(c, Ordering::Relaxed);

    o
}

/// Create a pure thunk that is already evaluated (inline from lean.h)
///
/// Thunk.pure : A -> Thunk A
///
/// # Safety
/// - `v` must be a valid lean object (consumed)
#[inline(always)]
pub unsafe fn lean_thunk_pure(v: lean_obj_arg) -> lean_obj_res {
    let o = lean_alloc_small_object(std::mem::size_of::<lean_thunk_object>() as c_uint);
    lean_set_st_header(o, crate::LEAN_THUNK, 0);

    // SAFETY: the object was just allocated with the thunk tag, so the cast to
    // `lean_thunk_object` is valid before initializing its atomic fields.
    let thunk = lean_to_thunk(o);
    // Use atomic stores for consistency with lean_thunk_object definition
    (*thunk).m_value.store(v, Ordering::Relaxed);
    (*thunk)
        .m_closure
        .store(std::ptr::null_mut(), Ordering::Relaxed);

    o
}

/// Get the value from a thunk, forcing evaluation if needed (inline from lean.h)
///
/// # Safety
/// - `t` must be a valid thunk object (borrowed)
#[inline(always)]
pub unsafe fn lean_thunk_get(t: b_lean_obj_arg) -> b_lean_obj_res {
    let thunk = lean_to_thunk(t as lean_obj_arg);
    // Use atomic load for consistency
    let r = (*thunk).m_value.load(Ordering::Acquire);
    if !r.is_null() {
        r as b_lean_obj_res
    } else {
        lean_thunk_get_core(t as *mut lean_object) as b_lean_obj_res
    }
}

/// Get owned value from a thunk (inline from lean.h)
///
/// Primitive for implementing Thunk.get : Thunk A -> A
///
/// # Safety
/// - `t` must be a valid thunk object (borrowed)
#[inline(always)]
pub unsafe fn lean_thunk_get_own(t: b_lean_obj_arg) -> lean_obj_res {
    let r = lean_thunk_get(t);
    lean_inc(r as lean_obj_arg);
    r as lean_obj_res
}

// ============================================================================
