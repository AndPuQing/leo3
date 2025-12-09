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
//! - `inline` - Rust re-implementations of Lean4's static inline functions

// Re-export libc types used across modules
pub use libc::{c_char, c_int, c_uint, c_void, size_t};

pub mod array;
pub mod closure;
pub mod float;
pub mod int;
pub mod nat;
pub mod object;
pub mod string;

// Inline function implementations (PyO3-style)
pub mod inline;

// Re-export commonly used types from object module
pub use object::{
    b_lean_obj_arg,
    lean_box,
    // Constructor functions
    lean_ctor_get,
    lean_ctor_get_uint16,
    lean_ctor_get_uint32,
    lean_ctor_get_uint64,
    lean_ctor_get_uint8,
    lean_ctor_set,
    lean_ctor_set_uint16,
    lean_ctor_set_uint32,
    lean_ctor_set_uint64,
    lean_ctor_set_uint8,
    // Inline functions
    lean_is_scalar,
    lean_obj_arg,
    lean_obj_res,
    lean_obj_tag,
    lean_object,
    lean_unbox,
    u_lean_obj_arg,
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

pub use inline::{
    // Float inline functions
    lean_box_float,
    // ByteArray inline functions
    lean_byte_array_uget,
    lean_byte_array_uset,
    lean_is_array,
    lean_is_closure,
    lean_is_ctor,
    lean_is_external,
    lean_is_mpz,
    lean_is_promise,
    lean_is_ref,
    lean_is_sarray,
    lean_is_string,
    lean_is_task,
    lean_is_thunk,
    lean_sarray_cptr,
    lean_sarray_size,
    lean_to_array,
    lean_to_closure,
    lean_to_ctor,
    lean_to_external,
    lean_to_promise,
    lean_to_ref,
    lean_to_sarray,
    lean_to_string,
    lean_to_task,
    lean_to_thunk,
    lean_unbox_float,
};

// ============================================================================
// High-level inc/dec with scalar checking (from lean.h)
// ============================================================================

pub use inline::{lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n};

// ============================================================================
// Array and ByteArray functions
// ============================================================================

pub use array::{lean_byte_array_push, lean_mk_empty_byte_array};

/// Allocate a constructor object (inline from lean.h)
///
/// # Safety
/// - `tag` must be <= LEAN_MAX_CTOR_TAG
/// - `num_objs` must be < LEAN_MAX_CTOR_FIELDS
/// - Must initialize all fields after allocation
#[inline]
pub unsafe fn lean_alloc_ctor(
    tag: c_uint,
    num_objs: c_uint,
    scalar_sz: c_uint,
) -> *mut lean_object {
    // Calculate total size: header + object pointers + scalar bytes
    let sz = std::mem::size_of::<lean_object>()
        + (num_objs as usize) * std::mem::size_of::<*mut lean_object>()
        + (scalar_sz as usize);
    let obj = object::lean_alloc_object(sz);
    // Initialize header (matching lean_set_st_header from lean.h)
    (*obj).m_rc = 1;
    (*obj).m_tag = tag as u8;
    (*obj).m_other = num_objs as u8; // Stores number of object fields
    (*obj).m_cs_sz = 0; // Will be set by allocator or left as 0
    obj
}
