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
pub type lean_obj_arg = *mut lean_object;       // Standard object argument (consumes RC)
pub type b_lean_obj_arg = *const lean_object;   // Borrowed object argument (doesn't consume)
pub type u_lean_obj_arg = *mut lean_object;     // Unique (exclusive) object argument
pub type lean_obj_res = *mut lean_object;       // Standard object result
pub type b_lean_obj_res = *const lean_object;   // Borrowed object result

// ============================================================================
// Reference Counting
// ============================================================================

extern "C" {
    /// Increment reference count of a Lean object
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer or null
    /// - Object must not be a scalar (use lean_inc for mixed types)
    pub fn lean_inc_ref(o: *mut lean_object);

    /// Increment reference count by n
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer or null
    pub fn lean_inc_ref_n(o: *mut lean_object, n: size_t);

    /// Decrement reference count (cold path for RC <= 1)
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    /// - Object may be deallocated if refcount reaches zero
    pub fn lean_dec_ref_cold(o: *mut lean_object);

    /// Check if object is exclusive (RC == 1)
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    pub fn lean_is_exclusive(o: *const lean_object) -> bool;

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

extern "C" {
    /// Get constructor field
    ///
    /// # Safety
    /// - `o` must be a valid constructor object
    /// - `i` must be within bounds (< num_objs)
    pub fn lean_ctor_get(o: b_lean_obj_arg, i: c_uint) -> b_lean_obj_res;

    /// Set constructor field
    ///
    /// # Safety
    /// - `o` must be a valid, exclusive constructor object
    /// - `i` must be within bounds
    /// - Consumes ownership of `v`
    pub fn lean_ctor_set(o: lean_obj_arg, i: c_uint, v: lean_obj_arg);

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

    /// Get uint8 scalar from constructor
    pub fn lean_ctor_get_uint8(o: b_lean_obj_arg, offset: c_uint) -> u8;

    /// Set uint8 scalar in constructor
    pub fn lean_ctor_set_uint8(o: lean_obj_arg, offset: c_uint, v: u8);

    /// Get uint16 scalar
    pub fn lean_ctor_get_uint16(o: b_lean_obj_arg, offset: c_uint) -> u16;

    /// Set uint16 scalar
    pub fn lean_ctor_set_uint16(o: lean_obj_arg, offset: c_uint, v: u16);

    /// Get uint32 scalar
    pub fn lean_ctor_get_uint32(o: b_lean_obj_arg, offset: c_uint) -> u32;

    /// Set uint32 scalar
    pub fn lean_ctor_set_uint32(o: lean_obj_arg, offset: c_uint, v: u32);

    /// Get uint64 scalar
    pub fn lean_ctor_get_uint64(o: b_lean_obj_arg, offset: c_uint) -> u64;

    /// Set uint64 scalar
    pub fn lean_ctor_set_uint64(o: lean_obj_arg, offset: c_uint, v: u64);

    /// Get float64 scalar
    pub fn lean_ctor_get_float(o: b_lean_obj_arg, offset: c_uint) -> f64;

    /// Set float64 scalar
    pub fn lean_ctor_set_float(o: lean_obj_arg, offset: c_uint, v: f64);

    /// Get float32 scalar
    pub fn lean_ctor_get_float32(o: b_lean_obj_arg, offset: c_uint) -> f32;

    /// Set float32 scalar
    pub fn lean_ctor_set_float32(o: lean_obj_arg, offset: c_uint, v: f32);
}

// ============================================================================
// Boxing/Unboxing (Scalars)
// ============================================================================

// These are inline functions in lean.h - we implement them in Rust

/// Check if an object is actually a scalar (not a pointer)
///
/// Scalars have the LSB set: ((size_t)o & 1) == 1
#[inline]
pub unsafe fn lean_is_scalar(o: *const lean_object) -> bool {
    ((o as usize) & 1) == 1
}

/// Box a usize value as a lean_object pointer
///
/// Formula: (n << 1) | 1
#[inline]
pub unsafe fn lean_box(n: size_t) -> *mut lean_object {
    ((n << 1) | 1) as *mut lean_object
}

/// Unbox a lean_object pointer to get the usize value
///
/// Formula: (size_t)o >> 1
#[inline]
pub unsafe fn lean_unbox(o: *const lean_object) -> size_t {
    (o as usize) >> 1
}

// ============================================================================
// Object Type Checking (inline from lean.h)
// ============================================================================

/// Get the tag of an object
///
/// # Safety
/// - `o` must be a valid lean_object pointer or a boxed scalar
#[inline]
pub unsafe fn lean_obj_tag(o: *const lean_object) -> u8 {
    if lean_is_scalar(o) {
        lean_unbox(o) as u8
    } else {
        (*o).m_tag
    }
}

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
}
