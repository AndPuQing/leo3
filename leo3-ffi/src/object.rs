//! Comprehensive FFI bindings to Lean4 C API (Core Objects)
//!
//! This module provides complete bindings to the Lean4 runtime for core object operations,
//! based on the actual lean.h header file.

use libc::{c_char, c_int, c_uint, c_void, size_t};

/// Opaque struct representing a Lean object
/// Corresponds to the lean_object struct in lean.h
#[repr(C)]
pub struct lean_object {
    pub m_rc: c_int,
    pub m_cs_sz: u16,
    pub m_other: u8,
    pub m_tag: u8,
}

/// Type aliases matching Lean's calling conventions
pub type lean_obj_arg = *mut lean_object; // Standard object argument (consumes RC)
pub type b_lean_obj_arg = *const lean_object; // Borrowed object argument (doesn't consume)
pub type u_lean_obj_arg = *mut lean_object; // Unique (exclusive) object argument
pub type lean_obj_res = *mut lean_object; // Standard object result
pub type b_lean_obj_res = *const lean_object; // Borrowed object result

// ============================================================================
// Reference Counting
// ============================================================================

// Re-export inline implementations from inline module
pub use crate::inline::{
    lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_inc_ref_n, lean_is_exclusive, lean_obj_tag,
};

extern "C" {
    /// Decrement reference count (cold path for RC <= 1)
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    /// - Object may be deallocated if refcount reaches zero
    pub fn lean_dec_ref_cold(o: *mut lean_object);

    /// Check if object is shared (RC > 1)
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    pub fn lean_is_shared(o: *const lean_object) -> bool;

    /// Mark object as multi-threaded
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    pub fn lean_mark_mt(o: *mut lean_object);

    /// Mark object as persistent (RC = 0, never freed)
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    pub fn lean_mark_persistent(o: *mut lean_object);
}

// ============================================================================
// Memory Allocation
// ============================================================================

extern "C" {
    /// Allocate a "big" object (arrays, strings)
    ///
    /// # Safety
    /// - Must initialize the object header after allocation
    pub fn lean_alloc_object(sz: size_t) -> *mut lean_object;

    /// Free an object
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    /// - Object must not be referenced elsewhere
    pub fn lean_free_object(o: *mut lean_object);

    /// Get the byte size of an object
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    pub fn lean_object_byte_size(o: *mut lean_object) -> size_t;

    /// Get the data byte size of an object (excluding padding)
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    pub fn lean_object_data_byte_size(o: *mut lean_object) -> size_t;
}

// ============================================================================
// Constructor Objects
// ============================================================================

// Re-export inline implementations from inline module
pub use crate::inline::{lean_ctor_get, lean_ctor_set};

extern "C" {
    /// Set constructor tag
    ///
    /// # Safety
    /// - `o` must be a valid, exclusive constructor object
    /// - `new_tag` must be <= LEAN_MAX_CTOR_TAG
    pub fn lean_ctor_set_tag(o: lean_obj_arg, new_tag: u8);

    /// Release (dec_ref) a constructor field
    ///
    /// # Safety
    /// - `o` must be a valid constructor object
    /// - `i` must be within bounds
    pub fn lean_ctor_release(o: lean_obj_arg, i: c_uint);

    /// Get usize scalar from constructor
    ///
    /// # Safety
    /// - `o` must be a valid constructor object
    /// - `i` must be in the scalar area (>= num_objs)
    pub fn lean_ctor_get_usize(o: b_lean_obj_arg, i: c_uint) -> size_t;

    /// Set usize scalar in constructor
    ///
    /// # Safety
    /// - `o` must be a valid, exclusive constructor object
    /// - `i` must be in the scalar area
    pub fn lean_ctor_set_usize(o: lean_obj_arg, i: c_uint, v: size_t);

    /// Get float64 scalar
    pub fn lean_ctor_get_float(o: b_lean_obj_arg, offset: c_uint) -> f64;

    /// Set float64 scalar
    pub fn lean_ctor_set_float(o: lean_obj_arg, offset: c_uint, v: f64);

    /// Get float32 scalar
    pub fn lean_ctor_get_float32(o: b_lean_obj_arg, offset: c_uint) -> f32;

    /// Set float32 scalar
    pub fn lean_ctor_set_float32(o: lean_obj_arg, offset: c_uint, v: f32);
}

// Re-export inline implementations of uint accessor functions from inline module
pub use crate::inline::{
    lean_ctor_get_uint16, lean_ctor_get_uint32, lean_ctor_get_uint64, lean_ctor_get_uint8,
    lean_ctor_set_uint16, lean_ctor_set_uint32, lean_ctor_set_uint64, lean_ctor_set_uint8,
};

// ============================================================================
// Boxing/Unboxing (Scalars)
// ============================================================================

// Re-export inline functions from the inline module
pub use crate::inline::{lean_box, lean_is_scalar, lean_unbox};

// ============================================================================
// External Objects
// ============================================================================

/// Finalization callback for external objects
pub type lean_external_finalize_proc = Option<unsafe extern "C" fn(*mut c_void)>;

/// Foreach callback for external objects (for GC marking)
pub type lean_external_foreach_proc = Option<unsafe extern "C" fn(*mut c_void, b_lean_obj_arg)>;

extern "C" {
    /// Register a new external class
    ///
    /// # Safety
    /// - Callbacks must be valid function pointers or null
    pub fn lean_register_external_class(
        finalize: lean_external_finalize_proc,
        foreach: lean_external_foreach_proc,
    ) -> *mut c_void; // Returns lean_external_class*

    /// Allocate an external object
    ///
    /// # Safety
    /// - `class` must be a valid lean_external_class pointer
    /// - `data` will be owned by the object
    pub fn lean_alloc_external(class: *mut c_void, data: *mut c_void) -> lean_obj_res;

    /// Get data from external object
    ///
    /// # Safety
    /// - `o` must be a valid external object
    pub fn lean_get_external_data(o: b_lean_obj_arg) -> *mut c_void;
}

// ============================================================================
// Panic and Error Handling
// ============================================================================

extern "C" {
    /// Set whether to exit on panic
    pub fn lean_set_exit_on_panic(flag: bool);

    /// Enable/disable panic messages
    pub fn lean_set_panic_messages(flag: bool);

    /// Trigger a panic
    ///
    /// # Safety
    /// - May not return
    pub fn lean_panic(msg: *const c_char, force_stderr: bool);

    /// Panic function (returns default value)
    pub fn lean_panic_fn(default_val: lean_obj_arg, msg: lean_obj_arg) -> lean_obj_res;

    /// Internal panic (always terminates)
    ///
    /// # Safety
    /// - Never returns
    pub fn lean_internal_panic(msg: *const c_char) -> !;

    /// Internal panic for out of memory (always terminates)
    ///
    /// # Safety
    /// - Never returns
    pub fn lean_internal_panic_out_of_memory() -> !;

    /// Internal panic for unreachable code (always terminates)
    ///
    /// # Safety
    /// - Never returns
    pub fn lean_internal_panic_unreachable() -> !;

    /// Internal panic for reference count overflow (always terminates)
    ///
    /// # Safety
    /// - Never returns
    pub fn lean_internal_panic_rc_overflow() -> !;
}
