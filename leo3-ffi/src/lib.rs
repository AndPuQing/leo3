#![allow(non_camel_case_types, non_snake_case, clippy::missing_safety_doc)]
//! Raw FFI declarations for Lean4's C API.
//!
//! This crate provides low-level bindings to the Lean4 runtime and API.
//! It is meant for advanced users only - regular Leo3 users shouldn't
//! need to interact with this crate directly.
//!
//! # Safety
//!
//! The functions in this crate lack individual safety documentation, but
//! generally the following apply:
//! - Pointer arguments must point to valid Lean objects of the correct type
//! - Null pointers are sometimes valid input (check Lean4 documentation)
//! - Reference counting must be managed carefully (inc_ref/dec_ref)
//! - Most functions require a properly initialized Lean runtime
//!
//! Consult the Lean4 C API documentation for detailed safety requirements.
//!
//! # Feature flags
//!
//! Currently no feature flags are defined. Future versions may add:
//! - Version-specific compatibility flags
//! - Optional integrations

// Re-export libc types used by FFI
#[allow(unused_imports)]
use libc::{c_char, c_uint, c_void, size_t};

pub mod object;

// Re-export commonly used types
pub use object::*;

/// Opaque type representing a Lean object pointer
/// This corresponds to lean_object* in the C API
pub type lean_obj_arg = *const lean_object;
pub type lean_obj_res = *mut lean_object;

/// Lean object tag types
/// These correspond to the different kinds of Lean objects
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum LeanObjectTag {
    Ctor = 0,
    Closure = 1,
    Array = 2,
    StructArray = 3,
    ScalarArray = 4,
    String = 5,
    MPZ = 6,
    Thunk = 7,
    Task = 8,
    Ref = 9,
    External = 10,
    Reserved = 11,
}

// Lean runtime initialization and finalization
extern "C" {
    /// Initialize the Lean runtime
    /// Must be called before using any Lean API functions
    pub fn lean_initialize_runtime_module();

    /// Finalize the Lean runtime
    /// Should be called before program exit
    pub fn lean_finalize_runtime_module();

    /// Initialize the Lean thread
    pub fn lean_initialize_thread();

    /// Finalize the Lean thread
    pub fn lean_finalize_thread();
}
