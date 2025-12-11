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

// Test function with Vec<u64> parameter
#[leanfn]
fn sum_vec(numbers: Vec<u64>) -> u64 {
    numbers.iter().sum()
}

// Test function returning Vec<u64>
#[leanfn]
fn range_vec(n: u64) -> Vec<u64> {
    (0..n).collect()
}

// Test function with Vec<String>
#[leanfn]
fn join_strings(strings: Vec<String>) -> String {
    strings.join(", ")
}

// Test function that processes a Vec and returns a Vec
#[leanfn]
fn double_all(numbers: Vec<u64>) -> Vec<u64> {
    numbers.into_iter().map(|n| n * 2).collect()
}

// Test function with large array (for performance testing)
#[leanfn]
fn sum_large_vec(numbers: Vec<u64>) -> u64 {
    numbers.iter().sum()
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_double() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        // Create Lean UInt64
        let input = LeanUInt64::mk(lean, 21)?;

        // Call via FFI (simulating Lean calling us)
        // Access FFI function via internal name
        unsafe {
            let result_ptr = __leo3_leanfn_double::__ffi_double(input.into_ptr());
            let result: LeanBound<LeanUInt64> = LeanBound::from_owned_ptr(lean, result_ptr);
            assert_eq!(LeanUInt64::to_u64(&result), 42);
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
        let a = LeanUInt64::mk(lean, 10)?;
        let b = LeanUInt64::mk(lean, 32)?;

        unsafe {
            // Function is exported as "my_add" (different from rust name "add")
            // So it's available at top level
            let result_ptr = my_add(a.into_ptr(), b.into_ptr());
            let result = LeanBound::from_owned_ptr(lean, result_ptr);
            assert_eq!(LeanUInt64::to_u64(&result), 42);
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
        let n = LeanUInt64::mk(lean, 42)?;
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
        let input = LeanUInt64::mk(lean, 42)?;

        unsafe {
            let result_ptr = __leo3_leanfn_do_nothing::__ffi_do_nothing(input.into_ptr());
            // Unit return should be a constructor with tag 0 and 0 fields
            // Using LeanUInt64 as a placeholder type since we just check the pointer
            let result: LeanBound<LeanUInt64> = LeanBound::from_owned_ptr(lean, result_ptr);
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

    // Test Vec functions
    assert_eq!(sum_vec(vec![1, 2, 3, 4]), 10);
    assert_eq!(range_vec(5), vec![0, 1, 2, 3, 4]);
    assert_eq!(join_strings(vec!["a".to_string(), "b".to_string()]), "a, b");
    assert_eq!(double_all(vec![1, 2, 3]), vec![2, 4, 6]);
    assert_eq!(sum_large_vec((0..1000).collect()), 499500);
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_vec_sum() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        use leo3::types::LeanArray;

        // Create a LeanArray with [10, 20, 30]
        let mut arr = LeanArray::empty(lean)?;
        let n1 = LeanUInt64::mk(lean, 10)?;
        let n2 = LeanUInt64::mk(lean, 20)?;
        let n3 = LeanUInt64::mk(lean, 30)?;

        arr = LeanArray::push(arr, n1.cast())?;
        arr = LeanArray::push(arr, n2.cast())?;
        arr = LeanArray::push(arr, n3.cast())?;

        unsafe {
            let result_ptr = __leo3_leanfn_sum_vec::__ffi_sum_vec(arr.into_ptr());
            let result: LeanBound<LeanUInt64> = LeanBound::from_owned_ptr(lean, result_ptr);
            assert_eq!(LeanUInt64::to_u64(&result), 60);
        }

        Ok(())
    })
    .unwrap();
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_vec_return() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        use leo3::types::LeanArray;

        let n = LeanUInt64::mk(lean, 5)?;

        unsafe {
            let result_ptr = __leo3_leanfn_range_vec::__ffi_range_vec(n.into_ptr());
            let result: LeanBound<LeanArray> = LeanBound::from_owned_ptr(lean, result_ptr);

            // Verify array has 5 elements: [0, 1, 2, 3, 4]
            assert_eq!(LeanArray::size(&result), 5);

            for i in 0..5 {
                let elem = LeanArray::get(&result, i).unwrap();
                let uint: LeanBound<LeanUInt64> = elem.cast();
                assert_eq!(LeanUInt64::to_u64(&uint), i as u64);
            }
        }

        Ok(())
    })
    .unwrap();
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_vec_strings() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        use leo3::types::LeanArray;

        // Create array of strings ["hello", "world"]
        let mut arr = LeanArray::empty(lean)?;
        let s1 = LeanString::mk(lean, "hello")?;
        let s2 = LeanString::mk(lean, "world")?;

        arr = LeanArray::push(arr, s1.cast())?;
        arr = LeanArray::push(arr, s2.cast())?;

        unsafe {
            let result_ptr = __leo3_leanfn_join_strings::__ffi_join_strings(arr.into_ptr());
            let result: LeanBound<LeanString> = LeanBound::from_owned_ptr(lean, result_ptr);
            assert_eq!(LeanString::cstr(&result)?, "hello, world");
        }

        Ok(())
    })
    .unwrap();
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_vec_transform() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        use leo3::types::LeanArray;

        // Create array [1, 2, 3]
        let mut arr = LeanArray::empty(lean)?;
        for i in 1..=3 {
            let n = LeanUInt64::mk(lean, i)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        unsafe {
            let result_ptr = __leo3_leanfn_double_all::__ffi_double_all(arr.into_ptr());
            let result: LeanBound<LeanArray> = LeanBound::from_owned_ptr(lean, result_ptr);

            // Should return [2, 4, 6]
            assert_eq!(LeanArray::size(&result), 3);

            let expected = [2, 4, 6];
            for (i, &expected_val) in expected.iter().enumerate() {
                let elem = LeanArray::get(&result, i).unwrap();
                let uint: LeanBound<LeanUInt64> = elem.cast();
                assert_eq!(LeanUInt64::to_u64(&uint), expected_val);
            }
        }

        Ok(())
    })
    .unwrap();
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_leanfn_large_vec() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> Result<(), Box<dyn std::error::Error>> {
        use leo3::types::LeanArray;

        // Create a large array with 1000 elements
        let size = 1000;
        let mut arr = LeanArray::empty(lean)?;

        for i in 0..size {
            let n = LeanUInt64::mk(lean, i)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        unsafe {
            let result_ptr = __leo3_leanfn_sum_large_vec::__ffi_sum_large_vec(arr.into_ptr());
            let result: LeanBound<LeanUInt64> = LeanBound::from_owned_ptr(lean, result_ptr);

            // Sum of 0..1000 is 999*1000/2 = 499500
            let expected: u64 = (0..size).sum();
            assert_eq!(LeanUInt64::to_u64(&result), expected);
        }

        Ok(())
    })
    .unwrap();
}
