//! FFI bindings for Lean4 closure, thunk, and task operations
//!
//! Based on the closure/thunk/task functions from lean.h

use crate::object::{b_lean_obj_arg, b_lean_obj_res, lean_obj_arg, lean_obj_res};
use libc::c_uint;

// ============================================================================
// Closure Functions
// ============================================================================

extern "C" {
    /// Allocate a closure object
    ///
    /// # Safety
    /// - `fun` must be a valid function pointer
    /// - `arity` is the number of arguments the function expects
    /// - `num_fixed` is the number of arguments already applied
    pub fn lean_alloc_closure(
        fun: *mut std::ffi::c_void,
        arity: c_uint,
        num_fixed: c_uint,
    ) -> lean_obj_res;

    /// Apply a closure to an argument
    ///
    /// # Safety
    /// - `c` must be a valid closure object (consumed)
    /// - `a` is the argument to apply (consumed)
    pub fn lean_apply_1(c: lean_obj_arg, a: lean_obj_arg) -> lean_obj_res;

    /// Apply a closure to two arguments
    ///
    /// # Safety
    /// - `c` must be a valid closure object (consumed)
    /// - Both arguments are consumed
    pub fn lean_apply_2(c: lean_obj_arg, a1: lean_obj_arg, a2: lean_obj_arg) -> lean_obj_res;

    /// Apply a closure to three arguments
    pub fn lean_apply_3(
        c: lean_obj_arg,
        a1: lean_obj_arg,
        a2: lean_obj_arg,
        a3: lean_obj_arg,
    ) -> lean_obj_res;

    /// Apply a closure to four arguments
    pub fn lean_apply_4(
        c: lean_obj_arg,
        a1: lean_obj_arg,
        a2: lean_obj_arg,
        a3: lean_obj_arg,
        a4: lean_obj_arg,
    ) -> lean_obj_res;

    /// Apply a closure to multiple arguments
    ///
    /// # Safety
    /// - `c` must be a valid closure object (consumed)
    /// - `args` must be an array of `n` valid lean objects
    pub fn lean_apply_m(c: lean_obj_arg, n: c_uint, args: *mut lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// Thunk Functions
// ============================================================================

extern "C" {
    /// Allocate a thunk (lazy computation)
    ///
    /// # Safety
    /// - `c` must be a valid closure object (consumed)
    pub fn lean_alloc_thunk(c: lean_obj_arg) -> lean_obj_res;

    /// Get the value of a thunk (forcing evaluation if needed)
    ///
    /// # Safety
    /// - `t` must be a valid thunk object
    pub fn lean_thunk_get(t: b_lean_obj_arg) -> b_lean_obj_res;

    /// Get the value of an owned thunk (forcing evaluation if needed)
    ///
    /// # Safety
    /// - `t` must be a valid thunk object (consumed)
    pub fn lean_thunk_get_own(t: lean_obj_arg) -> lean_obj_res;

    /// Check if thunk is pure (no side effects)
    ///
    /// # Safety
    /// - `t` must be a valid thunk object
    pub fn lean_thunk_is_pure(t: b_lean_obj_arg) -> bool;
}

// ============================================================================
// Task Functions (Async/Parallel Computation)
// ============================================================================

extern "C" {
    /// Spawn a new task
    ///
    /// # Safety
    /// - `c` must be a valid closure object (consumed)
    /// - `prio` is the task priority
    pub fn lean_task_spawn(c: lean_obj_arg, prio: c_uint) -> lean_obj_res;

    /// Get task result (blocking if not finished)
    ///
    /// # Safety
    /// - `t` must be a valid task object
    pub fn lean_task_get(t: b_lean_obj_arg) -> b_lean_obj_res;

    /// Get owned task result (blocking if not finished)
    ///
    /// # Safety
    /// - `t` must be a valid task object (consumed)
    pub fn lean_task_get_own(t: lean_obj_arg) -> lean_obj_res;

    /// Map a function over a task
    ///
    /// # Safety
    /// - `f` must be a valid closure object (consumed)
    /// - `t` must be a valid task object (consumed)
    /// - `prio` is the priority for the new task
    pub fn lean_task_map(f: lean_obj_arg, t: lean_obj_arg, prio: c_uint) -> lean_obj_res;

    /// Bind a function over a task (monadic bind)
    ///
    /// # Safety
    /// - `t` must be a valid task object (consumed)
    /// - `f` must be a valid closure object (consumed)
    /// - `sync` indicates if the task should be forced synchronously
    /// - `prio` is the priority for the new task
    pub fn lean_task_bind(t: lean_obj_arg, f: lean_obj_arg, sync: u8, prio: c_uint)
        -> lean_obj_res;

    /// Create a pure task (already completed)
    ///
    /// # Safety
    /// - `v` is the value to wrap (consumed)
    pub fn lean_task_pure(v: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// Promise Functions
// ============================================================================

extern "C" {
    /// Create a new promise
    ///
    /// Returns a promise object that can be resolved later
    pub fn lean_promise_new() -> lean_obj_res;

    /// Resolve a promise with a value
    ///
    /// # Safety
    /// - `p` must be a valid promise object (consumed)
    /// - `v` is the value to set (consumed)
    pub fn lean_promise_resolve(p: lean_obj_arg, v: lean_obj_arg) -> lean_obj_res;

    /// Get the task associated with a promise
    ///
    /// # Safety
    /// - `p` must be a valid promise object
    pub fn lean_promise_get_task(p: b_lean_obj_arg) -> b_lean_obj_res;
}

// ============================================================================
// Reference Objects (Mutable Cells)
// ============================================================================

extern "C" {
    /// Allocate a reference object
    ///
    /// # Safety
    /// - `v` is the initial value (consumed)
    pub fn lean_alloc_ref(v: lean_obj_arg) -> lean_obj_res;

    /// Get the value from a reference
    ///
    /// # Safety
    /// - `r` must be a valid ref object
    pub fn lean_ref_get(r: b_lean_obj_arg) -> b_lean_obj_res;

    /// Set the value of a reference
    ///
    /// # Safety
    /// - `r` must be a valid ref object (consumed)
    /// - `v` is the new value (consumed)
    pub fn lean_ref_set(r: lean_obj_arg, v: lean_obj_arg) -> lean_obj_res;
}
