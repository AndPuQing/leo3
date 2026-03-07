//! Lean runtime layout types used by inline FFI helpers.

use crate::object::{lean_external_class, lean_object};
use libc::{c_void, size_t};
use std::sync::atomic::AtomicPtr;

// Lean object layouts (needed for cast helpers below)
// ========================================================================

#[repr(C)]
pub struct lean_ctor_object {
    pub m_header: lean_object,
    pub m_objs: [*mut lean_object; 0],
}

#[repr(C)]
pub struct lean_array_object {
    pub m_header: lean_object,
    pub m_size: size_t,
    pub m_capacity: size_t,
    pub m_data: [*mut lean_object; 0],
}

#[repr(C)]
pub struct lean_sarray_object {
    pub m_header: lean_object,
    pub m_size: size_t,
    pub m_capacity: size_t,
    pub m_data: [u8; 0],
}

#[repr(C)]
pub struct lean_string_object {
    pub m_header: lean_object,
    pub m_size: size_t,
    pub m_capacity: size_t,
    pub m_length: size_t,
    pub m_data: [u8; 0],
}

#[repr(C)]
pub struct lean_closure_object {
    pub m_header: lean_object,
    pub m_fun: *mut c_void,
    pub m_arity: u16,
    pub m_num_fixed: u16,
    pub m_objs: [*mut lean_object; 0],
}

#[repr(C)]
pub struct lean_ref_object {
    pub m_header: lean_object,
    pub m_value: *mut lean_object,
}

#[repr(C)]
pub struct lean_thunk_object {
    pub m_header: lean_object,
    pub m_value: AtomicPtr<lean_object>,
    pub m_closure: AtomicPtr<lean_object>,
}

#[repr(C)]
pub struct lean_task_imp {
    pub m_closure: *mut lean_object,
    pub m_head_dep: *mut lean_task_object,
    pub m_next_dep: *mut lean_task_object,
    pub m_prio: u32,
    pub m_canceled: u8,
    pub m_keep_alive: u8,
    pub m_deleted: u8,
    pub _padding: u8,
}

#[repr(C)]
pub struct lean_task_object {
    pub m_header: lean_object,
    pub m_value: AtomicPtr<lean_object>,
    pub m_imp: *mut lean_task_imp,
}

#[repr(C)]
pub struct lean_promise_object {
    pub m_header: lean_object,
    pub m_result: *mut lean_task_object,
}

#[repr(C)]
pub struct lean_external_object {
    pub m_header: lean_object,
    pub m_class: *mut lean_external_class,
    pub m_data: *mut c_void,
}
