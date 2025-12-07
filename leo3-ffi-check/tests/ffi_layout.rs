//! FFI Layout Validation Tests
//!
//! This test validates that our hand-written FFI bindings in `leo3-ffi`
//! match the actual layout of structures in Lean4's C headers.
//!
//! Inspired by PyO3's pyo3-ffi-check.

#![allow(non_camel_case_types, non_snake_case, dead_code)]

// Include bindgen-generated bindings
mod bindgen {
    #![allow(clippy::all)]
    include!(concat!(env!("OUT_DIR"), "/bindgen.rs"));
}

use leo3_ffi as ffi;
use std::mem::{align_of, size_of};

/// Validates that a struct in our FFI matches bindgen's version
macro_rules! check_struct_layout {
    ($name:ident) => {{
        let our_size = size_of::<ffi::$name>();
        let bindgen_size = size_of::<bindgen::$name>();
        let our_align = align_of::<ffi::$name>();
        let bindgen_align = align_of::<bindgen::$name>();

        println!("Checking struct: {}", stringify!($name));
        println!("  Our size: {}, bindgen size: {}", our_size, bindgen_size);
        println!(
            "  Our align: {}, bindgen align: {}",
            our_align, bindgen_align
        );

        assert_eq!(
            our_size,
            bindgen_size,
            "Size mismatch for {}",
            stringify!($name)
        );
        assert_eq!(
            our_align,
            bindgen_align,
            "Alignment mismatch for {}",
            stringify!($name)
        );
    }};
}

/// Validates that a type alias has the same size
macro_rules! check_type_size {
    ($name:ident) => {{
        let our_size = size_of::<ffi::$name>();
        let bindgen_size = size_of::<bindgen::$name>();

        println!("Checking type: {}", stringify!($name));
        println!("  Our size: {}, bindgen size: {}", our_size, bindgen_size);

        assert_eq!(
            our_size,
            bindgen_size,
            "Size mismatch for {}",
            stringify!($name)
        );
    }};
}

#[test]
fn check_lean_object_layout() {
    check_struct_layout!(lean_object);
}

#[test]
fn check_type_aliases() {
    // These are pointer types, so just check they're pointer-sized
    assert_eq!(size_of::<ffi::lean_obj_arg>(), size_of::<*mut ()>());
    assert_eq!(size_of::<ffi::b_lean_obj_arg>(), size_of::<*const ()>());
    assert_eq!(size_of::<ffi::lean_obj_res>(), size_of::<*mut ()>());
}

#[test]
fn check_constants() {
    // Validate that our constants match Lean's
    println!("Checking constants:");
    println!("  LEAN_MAX_CTOR_TAG: {}", ffi::LEAN_MAX_CTOR_TAG);
    println!("  LEAN_CLOSURE: {}", ffi::LEAN_CLOSURE);
    println!("  LEAN_ARRAY: {}", ffi::LEAN_ARRAY);
    println!("  LEAN_STRING: {}", ffi::LEAN_STRING);

    // These should match the values in lean.h
    // Note: Actual validation would require parsing these from headers
}

// Note: We can't easily check function signatures with bindgen,
// but we can at least ensure the functions exist and are callable
#[test]
fn check_function_existence() {
    // Just check that these symbols would link
    // (They won't actually link without Lean4, but the types should be correct)
    let _: unsafe extern "C" fn() = ffi::lean_initialize_runtime_module;
    let _: unsafe extern "C" fn() = ffi::lean_finalize_runtime_module;
    let _: unsafe extern "C" fn() = ffi::lean_initialize_thread;
    let _: unsafe extern "C" fn() = ffi::lean_finalize_thread;
}
