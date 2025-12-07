//! FFI validation library for leo3-ffi
//!
//! This library provides utilities for validating that our hand-written
//! FFI bindings match the actual Lean4 C API.

/// Macro to generate struct layout checks
#[macro_export]
macro_rules! check_struct_layout {
    ($our_type:ty, $bindgen_type:ty, $name:expr) => {{
        use std::mem::{align_of, size_of};

        let our_size = size_of::<$our_type>();
        let bindgen_size = size_of::<$bindgen_type>();
        let our_align = align_of::<$our_type>();
        let bindgen_align = align_of::<$bindgen_type>();

        println!("Checking struct: {}", $name);
        println!("  Our size: {}, bindgen size: {}", our_size, bindgen_size);
        println!(
            "  Our align: {}, bindgen align: {}",
            our_align, bindgen_align
        );

        assert_eq!(our_size, bindgen_size, "Size mismatch for {}", $name);
        assert_eq!(
            our_align, bindgen_align,
            "Alignment mismatch for {}",
            $name
        );
    }};
}

/// Macro to check pointer type sizes
#[macro_export]
macro_rules! check_pointer_type {
    ($type:ty, $name:expr) => {{
        use std::mem::size_of;

        let type_size = size_of::<$type>();
        let ptr_size = size_of::<*mut ()>();

        println!("Checking pointer type: {}", $name);
        println!("  Size: {}, expected: {}", type_size, ptr_size);

        assert_eq!(
            type_size, ptr_size,
            "Pointer type {} should be pointer-sized",
            $name
        );
    }};
}
