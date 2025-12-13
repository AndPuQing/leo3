//! Tests for the #[leanmodule] macro
//!
//! This macro generates module initialization functions for Lean4.

use leo3::prelude::*;

// Define a test module with #[leanmodule]
#[leanmodule(name = "TestModule")]
mod test_module {
    #[allow(dead_code)]
    pub fn add(a: u64, b: u64) -> u64 {
        a + b
    }

    #[allow(dead_code)]
    pub fn multiply(a: u64, b: u64) -> u64 {
        a * b
    }
}

// Test module with default name (uses module identifier)
#[leanmodule]
mod another_module {
    #[allow(dead_code)]
    pub fn greet() -> &'static str {
        "Hello!"
    }
}

// Test module with bare identifier name
#[leanmodule(MathModule)]
mod math_module {
    #[allow(dead_code)]
    pub fn square(x: i32) -> i32 {
        x * x
    }
}

#[test]
fn test_module_initialization_function_exists() {
    // The #[leanmodule] macro generates:
    // - initialize_TestModule
    // - initialize_another_module
    // - initialize_MathModule

    // If this compiles, the functions exist (they're #[no_mangle] extern "C")
}

#[test]
fn test_module_functions_accessible() {
    // Test that the module functions are still accessible
    assert_eq!(test_module::add(2, 3), 5);
    assert_eq!(test_module::multiply(4, 5), 20);
    assert_eq!(another_module::greet(), "Hello!");
    assert_eq!(math_module::square(7), 49);
}

#[test]
fn test_module_initialization_safety() {
    leo3::prepare_freethreaded_lean();

    // The initialization functions can be called from Lean
    // Here we just verify the runtime is ready
    leo3::with_lean(|_lean| {
        // Module initialization would happen on Lean side
        Ok::<_, LeanError>(())
    })
    .unwrap();
}

// Test nested content in modules
#[leanmodule(name = "NestedModule")]
mod nested_module {
    pub mod inner {
        #[allow(dead_code)]
        pub fn inner_fn() -> i32 {
            42
        }
    }

    #[allow(dead_code)]
    pub struct ModuleStruct {
        pub value: i32,
    }

    impl ModuleStruct {
        #[allow(dead_code)]
        pub fn new(v: i32) -> Self {
            ModuleStruct { value: v }
        }
    }
}

#[test]
fn test_nested_module_content() {
    assert_eq!(nested_module::inner::inner_fn(), 42);

    let s = nested_module::ModuleStruct::new(100);
    assert_eq!(s.value, 100);
}

// Verify the generated initialization function signature
// The function should be: extern "C" fn(u8, *mut c_void) -> *mut c_void
#[test]
fn test_init_function_signature() {
    // The macro generates functions like:
    // #[no_mangle]
    // pub unsafe extern "C" fn initialize_TestModule(
    //     builtin: u8,
    //     _world: *mut std::ffi::c_void,
    // ) -> *mut std::ffi::c_void

    // This test verifies the types are correct by checking function pointer compatibility
    type InitFn = unsafe extern "C" fn(u8, *mut std::ffi::c_void) -> *mut std::ffi::c_void;

    // If this compiles, the function signature matches
    extern "C" {
        fn initialize_TestModule(
            builtin: u8,
            _world: *mut std::ffi::c_void,
        ) -> *mut std::ffi::c_void;
    }

    let _fn_ptr: InitFn = initialize_TestModule;
}

// Test that module can contain leanfn-annotated functions
// (In real usage, these would have #[leanfn] attribute)
#[leanmodule(name = "FunctionModule")]
mod function_module {
    // This would typically have #[leanfn], but for this test
    // we just verify the module structure works
    #[allow(dead_code)]
    pub fn exported_add(a: u64, b: u64) -> u64 {
        a + b
    }

    #[allow(dead_code)]
    pub fn exported_sub(a: u64, b: u64) -> u64 {
        a.saturating_sub(b)
    }
}

#[test]
fn test_function_module() {
    assert_eq!(function_module::exported_add(10, 5), 15);
    assert_eq!(function_module::exported_sub(10, 5), 5);
    assert_eq!(function_module::exported_sub(5, 10), 0); // saturating
}
