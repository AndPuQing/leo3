//! External-object inline helpers.

use super::{
    layout::lean_external_object,
    object::{lean_alloc_small_object, lean_set_st_header, lean_to_external},
};
use crate::object::{b_lean_obj_arg, lean_external_class, lean_obj_arg, lean_obj_res};
use libc::{c_uint, c_void};

// External Object Functions
// ============================================================================

/// Allocate an external object (inline from lean.h)
#[inline(always)]
pub unsafe fn lean_alloc_external(
    cls: *mut lean_external_class,
    data: *mut c_void,
) -> lean_obj_res {
    let o = lean_alloc_small_object(std::mem::size_of::<lean_external_object>() as c_uint);
    lean_set_st_header(o, crate::LEAN_EXTERNAL, 0);

    // SAFETY: the freshly allocated object has just been tagged as external,
    // so viewing it as `lean_external_object` matches the runtime layout.
    let ext = o as *mut lean_external_object;
    (*ext).m_class = cls;
    (*ext).m_data = data;

    o
}

/// Get the external class from an external object (inline from lean.h)
#[inline(always)]
pub unsafe fn lean_get_external_class(o: b_lean_obj_arg) -> *mut lean_external_class {
    let ext = lean_to_external(o as lean_obj_arg);
    (*(ext as *const lean_external_object)).m_class
}

/// Get the data pointer from an external object (inline from lean.h)
#[inline(always)]
pub unsafe fn lean_get_external_data(o: b_lean_obj_arg) -> *mut c_void {
    (*(lean_to_external(o as lean_obj_arg) as *const lean_external_object)).m_data
}
