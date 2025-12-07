//! Core Lean object FFI bindings
//!
//! This module provides the fundamental types and functions for working with
//! Lean objects at the FFI level.

use libc::{c_char, c_uint, size_t};

/// Opaque struct representing a Lean object
/// The actual definition is in the Lean runtime
#[repr(C)]
pub struct lean_object {
    _private: [u8; 0],
}

// Reference counting functions
extern "C" {
    /// Increment reference count of a Lean object
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer or null
    pub fn lean_inc_ref(o: *mut lean_object);

    /// Decrement reference count of a Lean object
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer or null
    /// - Object may be deallocated if refcount reaches zero
    pub fn lean_dec_ref(o: *mut lean_object);

    /// Increment reference count multiple times
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer or null
    pub fn lean_inc_ref_n(o: *mut lean_object, n: c_uint);

    /// Decrement reference count multiple times
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer or null
    pub fn lean_dec_ref_n(o: *mut lean_object, n: c_uint);
}

// Object inspection functions
extern "C" {
    /// Get the tag of a Lean object
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    pub fn lean_obj_tag(o: *const lean_object) -> u8;

    /// Check if an object is exclusive (refcount == 1)
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    pub fn lean_is_exclusive(o: *const lean_object) -> bool;

    /// Check if an object is shared (refcount > 1)
    ///
    /// # Safety
    /// - `o` must be a valid lean_object pointer
    pub fn lean_is_shared(o: *const lean_object) -> bool;
}

// Constructor objects
extern "C" {
    /// Allocate a constructor object
    ///
    /// # Safety
    /// - Must properly initialize all fields after allocation
    pub fn lean_alloc_ctor(tag: c_uint, num_objs: c_uint, scalar_sz: c_uint) -> *mut lean_object;

    /// Get constructor tag
    ///
    /// # Safety
    /// - `o` must be a valid constructor object
    pub fn lean_ctor_get_tag(o: *const lean_object) -> c_uint;

    /// Get constructor field
    ///
    /// # Safety
    /// - `o` must be a valid constructor object
    /// - `i` must be within bounds
    pub fn lean_ctor_get(o: *const lean_object, i: c_uint) -> *mut lean_object;

    /// Set constructor field
    ///
    /// # Safety
    /// - `o` must be a valid, exclusive constructor object
    /// - `i` must be within bounds
    pub fn lean_ctor_set(o: *mut lean_object, i: c_uint, v: *mut lean_object);
}

// String functions
extern "C" {
    /// Create a new Lean string from C string
    ///
    /// # Safety
    /// - `s` must be a valid null-terminated UTF-8 string
    pub fn lean_mk_string(s: *const c_char) -> *mut lean_object;

    /// Get C string from Lean string
    ///
    /// # Safety
    /// - `o` must be a valid string object
    /// - Returned pointer is valid only while object is alive
    pub fn lean_string_cstr(o: *const lean_object) -> *const c_char;

    /// Get string length in bytes
    ///
    /// # Safety
    /// - `o` must be a valid string object
    pub fn lean_string_len(o: *const lean_object) -> size_t;
}

// Array functions
extern "C" {
    /// Allocate an array with given capacity
    ///
    /// # Safety
    /// - Must properly initialize elements
    pub fn lean_alloc_array(capacity: size_t, elem_size: size_t) -> *mut lean_object;

    /// Get array size
    ///
    /// # Safety
    /// - `o` must be a valid array object
    pub fn lean_array_size(o: *const lean_object) -> size_t;

    /// Get array element
    ///
    /// # Safety
    /// - `o` must be a valid array object
    /// - `i` must be within bounds
    pub fn lean_array_get(o: *const lean_object, i: size_t) -> *mut lean_object;

    /// Set array element
    ///
    /// # Safety
    /// - `o` must be a valid, exclusive array object
    /// - `i` must be within bounds
    pub fn lean_array_set(o: *mut lean_object, i: size_t, v: *mut lean_object);
}

// Natural number functions (stored as usize when small)
extern "C" {
    /// Create a Lean natural number from usize
    pub fn lean_usize_to_nat(n: size_t) -> *mut lean_object;

    /// Convert Lean natural to usize (if it fits)
    ///
    /// # Safety
    /// - `o` must be a valid nat object
    pub fn lean_nat_to_usize(o: *const lean_object) -> size_t;

    /// Check if nat is small (fits in usize)
    ///
    /// # Safety
    /// - `o` must be a valid nat object
    pub fn lean_nat_is_small(o: *const lean_object) -> bool;
}

// Option-like functions
extern "C" {
    /// Box a pointer into a Lean object
    ///
    /// # Safety
    /// - Creates a new Lean object wrapping the pointer
    pub fn lean_box(n: size_t) -> *mut lean_object;

    /// Unbox a Lean object to get size_t value
    ///
    /// # Safety
    /// - `o` must be a valid boxed object
    pub fn lean_unbox(o: *const lean_object) -> size_t;

    /// Check if value is a scalar
    pub fn lean_is_scalar(o: *const lean_object) -> bool;
}
