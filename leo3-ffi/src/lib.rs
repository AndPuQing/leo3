#![allow(non_camel_case_types, non_snake_case, clippy::missing_safety_doc)]
//! Raw FFI declarations for Lean4's C API.
//!
//! This crate provides low-level bindings to the Lean4 runtime and API, based on
//! the actual Lean4 C headers from `/usr/local/include/lean/lean.h`.
//!
//! It is meant for advanced users only - regular Leo3 users shouldn't
//! need to interact with this crate directly.
//!
//! # Safety
//!
//! The functions in this crate are unsafe and require careful handling:
//! - Pointer arguments must point to valid Lean objects of the correct type
//! - Null pointers are sometimes valid input (check function documentation)
//! - Reference counting must be managed carefully (inc_ref/dec_ref)
//! - Most functions require a properly initialized Lean runtime
//!
//! Consult the Lean4 C API documentation for detailed safety requirements.
//!
//! # Module Organization
//!
//! - `object` - Core object manipulation, reference counting, constructors
//! - `string` - String operations
//! - `array` - Array operations
//! - `nat` - Natural number operations
//! - `closure` - Closures, thunks, tasks, and promises

// Re-export libc types used across modules
pub use libc::{c_char, c_int, c_uint, c_void, size_t};

pub mod object;
pub mod string;
pub mod array;
pub mod nat;
pub mod closure;

// Re-export commonly used types from object module
pub use object::{
    lean_object,
    lean_obj_arg,
    b_lean_obj_arg,
    u_lean_obj_arg,
    lean_obj_res,
    // Inline functions
    lean_is_scalar,
    lean_box,
    lean_unbox,
    lean_obj_tag,
};

/// Lean object type tags (from lean.h)
pub const LEAN_MAX_CTOR_TAG: u8 = 243;
pub const LEAN_PROMISE: u8 = 244;
pub const LEAN_CLOSURE: u8 = 245;
pub const LEAN_ARRAY: u8 = 246;
pub const LEAN_STRUCT_ARRAY: u8 = 247;
pub const LEAN_SCALAR_ARRAY: u8 = 248;
pub const LEAN_STRING: u8 = 249;
pub const LEAN_MPZ: u8 = 250;
pub const LEAN_THUNK: u8 = 251;
pub const LEAN_TASK: u8 = 252;
pub const LEAN_REF: u8 = 253;
pub const LEAN_EXTERNAL: u8 = 254;
pub const LEAN_RESERVED: u8 = 255;

// ============================================================================
// Runtime Initialization
// ============================================================================

extern "C" {
    /// Initialize the Lean runtime module
    ///
    /// Must be called once before using any Lean API functions.
    pub fn lean_initialize_runtime_module();

    /// Finalize the Lean runtime module
    ///
    /// Should be called before program exit.
    pub fn lean_finalize_runtime_module();

    /// Initialize thread for Lean
    ///
    /// Must be called for each thread that will use Lean objects.
    pub fn lean_initialize_thread();

    /// Finalize thread for Lean
    ///
    /// Should be called before thread exit.
    pub fn lean_finalize_thread();

    /// Increment heartbeat counter (for interruption)
    ///
    /// Used by the Lean runtime to check for interrupts and resource limits.
    pub fn lean_inc_heartbeat();
}

// ============================================================================
// Object Type Checking Helpers (inline from lean.h)
// ============================================================================

/// Check if object is a constructor
#[inline]
pub unsafe fn lean_is_ctor(o: *const lean_object) -> bool {
    !lean_is_scalar(o) && (*o).m_tag <= LEAN_MAX_CTOR_TAG
}

/// Check if object is a closure
#[inline]
pub unsafe fn lean_is_closure(o: *const lean_object) -> bool {
    !lean_is_scalar(o) && (*o).m_tag == LEAN_CLOSURE
}

/// Check if object is an array
#[inline]
pub unsafe fn lean_is_array(o: *const lean_object) -> bool {
    !lean_is_scalar(o) && (*o).m_tag == LEAN_ARRAY
}

/// Check if object is a scalar array
#[inline]
pub unsafe fn lean_is_sarray(o: *const lean_object) -> bool {
    !lean_is_scalar(o) && (*o).m_tag == LEAN_SCALAR_ARRAY
}

/// Check if object is a string
#[inline]
pub unsafe fn lean_is_string(o: *const lean_object) -> bool {
    !lean_is_scalar(o) && (*o).m_tag == LEAN_STRING
}

/// Check if object is a thunk
#[inline]
pub unsafe fn lean_is_thunk(o: *const lean_object) -> bool {
    !lean_is_scalar(o) && (*o).m_tag == LEAN_THUNK
}

/// Check if object is a task
#[inline]
pub unsafe fn lean_is_task(o: *const lean_object) -> bool {
    !lean_is_scalar(o) && (*o).m_tag == LEAN_TASK
}

/// Check if object is a reference
#[inline]
pub unsafe fn lean_is_ref(o: *const lean_object) -> bool {
    !lean_is_scalar(o) && (*o).m_tag == LEAN_REF
}

/// Check if object is external
#[inline]
pub unsafe fn lean_is_external(o: *const lean_object) -> bool {
    !lean_is_scalar(o) && (*o).m_tag == LEAN_EXTERNAL
}

// ============================================================================
// High-level inc/dec with scalar checking (from lean.h)
// ============================================================================

/// Increment reference count (checks for scalars)
///
/// # Safety
/// - `o` must be a valid lean_object pointer or a boxed scalar
#[inline]
pub unsafe fn lean_inc(o: *mut lean_object) {
    if !lean_is_scalar(o) {
        object::lean_inc_ref(o);
    }
}

/// Increment reference count by n (checks for scalars)
///
/// # Safety
/// - `o` must be a valid lean_object pointer or a boxed scalar
#[inline]
pub unsafe fn lean_inc_n(o: *mut lean_object, n: size_t) {
    if !lean_is_scalar(o) {
        object::lean_inc_ref_n(o, n);
    }
}

/// Decrement reference count (checks for scalars)
///
/// # Safety
/// - `o` must be a valid lean_object pointer or a boxed scalar
/// - Object may be deallocated if refcount reaches zero
#[inline]
pub unsafe fn lean_dec(o: *mut lean_object) {
    if !lean_is_scalar(o) {
        // Fast path: if RC > 1, just decrement
        if (*o).m_rc > 1 {
            (*o).m_rc -= 1;
        } else if (*o).m_rc != 0 {
            object::lean_dec_ref_cold(o);
        }
    }
}

/// Allocate a constructor object (inline from lean.h)
///
/// # Safety
/// - `tag` must be <= LEAN_MAX_CTOR_TAG
/// - `num_objs` must be < LEAN_MAX_CTOR_FIELDS
/// - Must initialize all fields after allocation
#[inline]
pub unsafe fn lean_alloc_ctor(tag: c_uint, num_objs: c_uint, scalar_sz: c_uint) -> *mut lean_object {
    // This is a complex inline function in lean.h
    // For FFI purposes, we'll declare it as extern
    lean_alloc_ctor_impl(tag, num_objs, scalar_sz)
}

extern "C" {
    /// Internal implementation of lean_alloc_ctor
    ///
    /// Note: In lean.h this is actually an inline function, but for FFI
    /// we need to link against the implementation
    #[link_name = "lean_alloc_ctor"]
    fn lean_alloc_ctor_impl(tag: c_uint, num_objs: c_uint, scalar_sz: c_uint) -> *mut lean_object;
}
