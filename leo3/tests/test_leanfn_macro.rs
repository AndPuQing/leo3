//! Integration tests for the `#[leanfn]` macro.

use leo3::prelude::*;

// Test basic u64 function
#[leanfn]
fn double(x: u64) -> u64 {
    x * 2
}

// Test function with custom name
#[leanfn(name = "my_add")]
fn add(a: u64, b: u64) -> u64 {
    a + b
}

// Test function with string parameter
#[leanfn]
fn greet(name: String) -> String {
    format!("Hello, {}!", name)
}

// Test function with bool
#[leanfn]
fn negate(b: bool) -> bool {
    !b
}

// Test function with mixed types
#[leanfn]
fn describe_number(n: u64, positive: bool) -> String {
    if positive {
        format!("positive {}", n)
    } else {
        format!("negative {}", n)
    }
}

// Test function with unit return
#[leanfn]
fn do_nothing(x: u64) {
    let _ = x;
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_double() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        // Create Lean Nat
        let input = LeanNat::from_usize(lean, 21)?;

        // Call via FFI (simulating Lean calling us)
        // Access FFI function via internal name
        unsafe {
            let result_ptr = __leo3_leanfn_double::__ffi_double(input.into_ptr());
            let result = LeanBound::from_owned_ptr(lean, result_ptr);
            assert_eq!(LeanNat::to_usize(&result)?, 42);
        }

        Ok(())
    })
    .unwrap();
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_with_name() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        let a = LeanNat::from_usize(lean, 10)?;
        let b = LeanNat::from_usize(lean, 32)?;

        unsafe {
            // Function is exported as "my_add" (different from rust name "add")
            // So it's available at top level
            let result_ptr = my_add(a.into_ptr(), b.into_ptr());
            let result = LeanBound::from_owned_ptr(lean, result_ptr);
            assert_eq!(LeanNat::to_usize(&result)?, 42);
        }

        Ok(())
    })
    .unwrap();
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_string() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        let name = LeanString::mk(lean, "World")?;

        unsafe {
            let result_ptr = __leo3_leanfn_greet::__ffi_greet(name.into_ptr());
            let result: LeanBound<LeanString> = LeanBound::from_owned_ptr(lean, result_ptr);
            assert_eq!(LeanString::cstr(&result)?, "Hello, World!");
        }

        Ok(())
    })
    .unwrap();
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_bool() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        let input_true = LeanBool::mk(lean, true)?;
        let input_false = LeanBool::mk(lean, false)?;

        unsafe {
            let result_ptr = __leo3_leanfn_negate::__ffi_negate(input_true.into_ptr());
            let result: LeanBound<LeanBool> = LeanBound::from_owned_ptr(lean, result_ptr);
            assert!(!LeanBool::toBool(&result));

            let result_ptr = __leo3_leanfn_negate::__ffi_negate(input_false.into_ptr());
            let result: LeanBound<LeanBool> = LeanBound::from_owned_ptr(lean, result_ptr);
            assert!(LeanBool::toBool(&result));
        }

        Ok(())
    })
    .unwrap();
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_mixed_types() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        let n = LeanNat::from_usize(lean, 42)?;
        let positive = LeanBool::mk(lean, true)?;

        unsafe {
            let result_ptr = __leo3_leanfn_describe_number::__ffi_describe_number(
                n.into_ptr(),
                positive.into_ptr(),
            );
            let result: LeanBound<LeanString> = LeanBound::from_owned_ptr(lean, result_ptr);
            assert_eq!(LeanString::cstr(&result)?, "positive 42");
        }

        Ok(())
    })
    .unwrap();
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_unit_return() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        let input = LeanNat::from_usize(lean, 42)?;

        unsafe {
            let result_ptr = __leo3_leanfn_do_nothing::__ffi_do_nothing(input.into_ptr());
            // Unit return should be a constructor with tag 0 and 0 fields
            // Using LeanNat as a placeholder type since we just check the pointer
            let result: LeanBound<LeanNat> = LeanBound::from_owned_ptr(lean, result_ptr);
            // Just verify it doesn't crash
            assert!(!result.as_ptr().is_null());
        }

        Ok(())
    })
    .unwrap();
}

// Test that we can call the function from Rust-side too
#[test]
fn test_rust_side_call() {
    // The original function should still be callable from Rust
    assert_eq!(double(21), 42);
    assert_eq!(add(10, 32), 42);
    assert_eq!(greet("Rust".to_string()), "Hello, Rust!");
    assert!(!negate(true));
    assert_eq!(describe_number(42, true), "positive 42");
}
