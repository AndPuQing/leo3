//! Closure inline helpers.

use super::{
    layout::lean_closure_object,
    object::{lean_alloc_small_object, lean_set_st_header, lean_to_closure},
};
use crate::object::{b_lean_obj_arg, b_lean_obj_res, lean_obj_arg, lean_obj_res, lean_object};
use libc::{c_uint, c_void, size_t};

// Closure Inline Functions (from lean.h)
// ============================================================================

/// Get the function pointer from a closure (inline from lean.h)
///
/// # Safety
/// - `o` must be a valid closure object
#[inline(always)]
pub unsafe fn lean_closure_fun(o: *mut lean_object) -> *mut c_void {
    (*lean_to_closure(o)).m_fun
}

/// Get the total arity of a closure (inline from lean.h)
///
/// # Safety
/// - `o` must be a valid closure object
#[inline(always)]
pub unsafe fn lean_closure_arity(o: *mut lean_object) -> c_uint {
    (*lean_to_closure(o)).m_arity as c_uint
}

/// Get the number of fixed (already applied) arguments (inline from lean.h)
///
/// # Safety
/// - `o` must be a valid closure object
#[inline(always)]
pub unsafe fn lean_closure_num_fixed(o: *mut lean_object) -> c_uint {
    (*lean_to_closure(o)).m_num_fixed as c_uint
}

/// Get a pointer to the captured argument array (inline from lean.h)
///
/// # Safety
/// - `o` must be a valid closure object
#[inline(always)]
pub unsafe fn lean_closure_arg_cptr(o: *mut lean_object) -> *mut *mut lean_object {
    (*lean_to_closure(o)).m_objs.as_mut_ptr()
}

/// Allocate a closure object (inline from lean.h)
///
/// Creates a new closure wrapping a function pointer with the given arity.
/// The closure can hold `num_fixed` captured arguments.
///
/// # Safety
/// - `fun` must be a valid function pointer compatible with Lean's calling convention
/// - `arity` must be > 0 (the function must take at least one argument)
/// - `num_fixed` must be < arity (at least one argument slot must remain)
///
/// # Panics
/// Debug builds will panic if arity == 0 or num_fixed >= arity
#[inline(always)]
pub unsafe fn lean_alloc_closure(
    fun: *mut c_void,
    arity: c_uint,
    num_fixed: c_uint,
) -> lean_obj_res {
    debug_assert!(arity > 0, "lean_alloc_closure: arity must be > 0");
    debug_assert!(
        num_fixed < arity,
        "lean_alloc_closure: num_fixed must be < arity"
    );

    let obj_size = std::mem::size_of::<lean_closure_object>()
        + std::mem::size_of::<*mut c_void>() * num_fixed as usize;
    let o = lean_alloc_small_object(obj_size as c_uint);
    lean_set_st_header(o, crate::LEAN_CLOSURE, 0);

    // SAFETY: the allocation was sized for a closure object plus captured
    // arguments, so reinterpreting it as `lean_closure_object` is valid here.
    let closure = o as *mut lean_closure_object;
    (*closure).m_fun = fun;
    (*closure).m_arity = arity as u16;
    (*closure).m_num_fixed = num_fixed as u16;

    o
}

/// Get a captured argument from a closure (inline from lean.h)
///
/// # Safety
/// - `o` must be a valid closure object
/// - `i` must be < num_fixed
#[inline(always)]
pub unsafe fn lean_closure_get(o: b_lean_obj_arg, i: c_uint) -> b_lean_obj_res {
    debug_assert!(
        i < lean_closure_num_fixed(o as lean_obj_arg),
        "lean_closure_get: index out of bounds"
    );
    let cptr = lean_closure_arg_cptr(o as lean_obj_arg);
    *cptr.add(i as usize)
}

/// Set a captured argument in a closure (inline from lean.h)
///
/// This is used during closure construction to store captured values.
///
/// # Safety
/// - `o` must be a valid, uniquely owned closure object
/// - `i` must be < num_fixed
/// - `a` must be a valid lean object (consumed)
#[inline(always)]
pub unsafe fn lean_closure_set(o: lean_obj_arg, i: c_uint, a: lean_obj_arg) {
    debug_assert!(
        i < lean_closure_num_fixed(o),
        "lean_closure_set: index out of bounds"
    );
    let cptr = lean_closure_arg_cptr(o);
    *cptr.add(i as usize) = a;
}

/// Get the byte size of a closure object (inline from lean.h)
///
/// # Safety
/// - `o` must be a valid closure object
#[inline(always)]
pub unsafe fn lean_closure_byte_size(o: *mut lean_object) -> size_t {
    std::mem::size_of::<lean_closure_object>()
        + std::mem::size_of::<*mut c_void>() * lean_closure_num_fixed(o) as usize
}
