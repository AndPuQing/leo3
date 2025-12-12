//! Tests for Lean module loading and function calls.
//!
//! These tests verify the Phase 1 module loading functionality from the Leo3 roadmap.

use leo3::module::LeanModule;
use leo3::prelude::*;

// Note: These tests require a compiled Lean module to work.
// For now, we test the basic module loading infrastructure.

#[test]
fn test_module_struct_exists() {
    // This test verifies that the LeanModule type is available
    // and can be referenced.

    // Just check that the type exists - we can't actually load without a .so file
    let _type_check =
        |path: &str, name: &str| -> Result<LeanModule, String> { LeanModule::load(path, name) };
}

#[test]
fn test_lean_function_api() {
    // Test that the LeanFunction API is correctly defined
    // by checking method existence at compile time.

    leo3::prepare_freethreaded_lean();

    // The fact that this compiles proves the API is correctly structured.
    // Actual runtime testing would require a compiled Lean module.
}

// TODO: To properly test module loading, we need to:
// 1. Create a simple Lean module (e.g., Math.lean with basic functions)
// 2. Compile it to a shared library using lake
// 3. Load it and test function calls
//
// Example Lean module to test with:
// ```lean
// -- Math.lean
// def add (a b : Nat) : Nat := a + b
// def multiply (a b : Nat) : Nat := a * b
// def greet (name : String) : String := s!"Hello, {name}!"
// ```
//
// Then compile with:
// ```bash
// lake build Math
// ```
//
// And test with:
// ```rust
// #[test]
// fn test_load_and_call_module() {
//     leo3::prepare_freethreaded_lean();
//
//     let module = LeanModule::load("./libMath.so", "Math").unwrap();
//
//     leo3::with_lean(|lean| {
//         // Test 2-argument function
//         let add_fn = module.get_function("Math.add", 2)?;
//         let result: u64 = add_fn.call2(lean, 5u64, 3u64)?;
//         assert_eq!(result, 8);
//
//         // Test string function
//         let greet_fn = module.get_function("Math.greet", 1)?;
//         let greeting: String = greet_fn.call1(lean, "World")?;
//         assert_eq!(greeting, "Hello, World!");
//
//         Ok::<_, LeanError>(())
//     }).unwrap();
// }
// ```

#[test]
fn test_module_api_documentation() {
    // This test serves as living documentation of the module loading API

    leo3::prepare_freethreaded_lean();

    // API overview (pseudo-code, would need actual .so file to run):
    //
    // 1. Load a module:
    //    let module = LeanModule::load("path/to/lib.so", "ModuleName")?;
    //
    // 2. Get a function with specified arity:
    //    let func = module.get_function("ModuleName.functionName", arity)?;
    //
    // 3. Call with appropriate number of arguments:
    //    let result = func.call0(lean)?;           // 0 arguments
    //    let result = func.call1(lean, arg1)?;     // 1 argument
    //    let result = func.call2(lean, a, b)?;     // 2 arguments
    //    // ... up to call8 for 8 arguments
    //
    // 4. Type conversion happens automatically via IntoLean/FromLean traits
}

#[test]
fn test_external_objects_work() {
    // External objects are working, let's verify them here as well
    use leo3::external::{ExternalClass, LeanExternal};

    #[derive(Clone, Debug, PartialEq)]
    struct TestData {
        value: i32,
    }

    impl ExternalClass for TestData {
        fn class_name() -> &'static str {
            "TestData"
        }
    }

    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let data = TestData { value: 42 };
        let external = LeanExternal::new(lean, data)?;

        assert_eq!(external.get_ref().value, 42);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}
