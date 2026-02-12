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
use std::mem::{align_of, offset_of, size_of};

/// Validates that a struct in our FFI matches bindgen's version (size + alignment)
macro_rules! check_struct_layout {
    ($our_type:ty, $bindgen_type:ty) => {{
        let our_size = size_of::<$our_type>();
        let bindgen_size = size_of::<$bindgen_type>();
        let our_align = align_of::<$our_type>();
        let bindgen_align = align_of::<$bindgen_type>();

        let name = stringify!($our_type);
        println!("Checking struct: {}", name);
        println!("  Our size: {}, bindgen size: {}", our_size, bindgen_size);
        println!(
            "  Our align: {}, bindgen align: {}",
            our_align, bindgen_align
        );

        assert_eq!(our_size, bindgen_size, "Size mismatch for {}", name);
        assert_eq!(our_align, bindgen_align, "Alignment mismatch for {}", name);
    }};
}

/// Validates field offsets between our FFI type and bindgen's type.
/// On mismatch, prints the struct name, field name, and expected vs actual offsets.
macro_rules! check_field_offsets {
    ($our_type:ty, $bindgen_type:ty, $( ($field:ident) ),+ $(,)?) => {{
        let name = stringify!($our_type);
        println!("Checking field offsets for: {}", name);
        $(
            let ours = offset_of!($our_type, $field);
            let theirs = offset_of!($bindgen_type, $field);
            println!("  {}.{}: ours={}, bindgen={}", name, stringify!($field), ours, theirs);
            assert_eq!(
                ours, theirs,
                "Field offset mismatch for {}.{}: ours={}, bindgen={}",
                name, stringify!($field), ours, theirs
            );
        )+
    }};
}

#[test]
fn check_lean_object_layout() {
    check_struct_layout!(ffi::lean_object, bindgen::lean_object);
    // Note: bindgen represents m_cs_sz/m_other/m_tag as a bitfield unit,
    // so we can only check m_rc offset directly.
    check_field_offsets!(ffi::lean_object, bindgen::lean_object, (m_rc));
}

#[test]
fn check_lean_array_object_layout() {
    check_struct_layout!(ffi::inline::lean_array_object, bindgen::lean_array_object);
    check_field_offsets!(
        ffi::inline::lean_array_object,
        bindgen::lean_array_object,
        (m_header),
        (m_size),
        (m_capacity),
        (m_data),
    );
}

#[test]
fn check_lean_string_object_layout() {
    check_struct_layout!(ffi::inline::lean_string_object, bindgen::lean_string_object);
    check_field_offsets!(
        ffi::inline::lean_string_object,
        bindgen::lean_string_object,
        (m_header),
        (m_size),
        (m_capacity),
        (m_length),
        (m_data),
    );
}

#[test]
fn check_lean_closure_object_layout() {
    check_struct_layout!(
        ffi::inline::lean_closure_object,
        bindgen::lean_closure_object
    );
    check_field_offsets!(
        ffi::inline::lean_closure_object,
        bindgen::lean_closure_object,
        (m_header),
        (m_fun),
        (m_arity),
        (m_num_fixed),
        (m_objs),
    );
}

#[test]
fn check_lean_ctor_object_layout() {
    check_struct_layout!(ffi::inline::lean_ctor_object, bindgen::lean_ctor_object);
    check_field_offsets!(
        ffi::inline::lean_ctor_object,
        bindgen::lean_ctor_object,
        (m_header),
        (m_objs),
    );
}

#[test]
fn check_lean_sarray_object_layout() {
    check_struct_layout!(ffi::inline::lean_sarray_object, bindgen::lean_sarray_object);
    check_field_offsets!(
        ffi::inline::lean_sarray_object,
        bindgen::lean_sarray_object,
        (m_header),
        (m_size),
        (m_capacity),
        (m_data),
    );
}

#[test]
fn check_lean_ref_object_layout() {
    check_struct_layout!(ffi::inline::lean_ref_object, bindgen::lean_ref_object);
    check_field_offsets!(
        ffi::inline::lean_ref_object,
        bindgen::lean_ref_object,
        (m_header),
        (m_value),
    );
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
