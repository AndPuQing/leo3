//! Conversion tests for Rust ↔ Lean type conversions
//!
//! These tests verify that data can be correctly converted between
//! Rust and Lean types.

use leo3::prelude::*;

// =============================================================================
// Natural Number Conversions
// =============================================================================

#[test]
fn test_nat_from_usize() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Small numbers
        let n = LeanNat::from_usize(lean, 0)?;
        assert_eq!(LeanNat::to_usize(&n)?, 0);

        let n = LeanNat::from_usize(lean, 1)?;
        assert_eq!(LeanNat::to_usize(&n)?, 1);

        let n = LeanNat::from_usize(lean, 42)?;
        assert_eq!(LeanNat::to_usize(&n)?, 42);

        let n = LeanNat::from_usize(lean, 255)?;
        assert_eq!(LeanNat::to_usize(&n)?, 255);

        // Large numbers
        let n = LeanNat::from_usize(lean, 1_000_000)?;
        assert_eq!(LeanNat::to_usize(&n)?, 1_000_000);

        let n = LeanNat::from_usize(lean, usize::MAX / 2)?;
        assert_eq!(LeanNat::to_usize(&n)?, usize::MAX / 2);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_to_usize() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create various nats and convert back
        for value in [0, 1, 10, 100, 1000, 10000, 100000] {
            let n = LeanNat::from_usize(lean, value)?;
            assert_eq!(LeanNat::to_usize(&n)?, value);
        }

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_is_small() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Small numbers should be "small"
        let n = LeanNat::from_usize(lean, 42)?;
        assert!(LeanNat::is_small(&n));

        let n = LeanNat::from_usize(lean, 1000)?;
        assert!(LeanNat::is_small(&n));

        // Note: Whether large numbers are "small" depends on Lean's implementation
        // We just verify the function works
        let n = LeanNat::from_usize(lean, 1_000_000)?;
        let _ = LeanNat::is_small(&n); // Just check it doesn't crash

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// String Conversions
// =============================================================================

#[test]
fn test_string_from_str() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Empty string
        let s = LeanString::new(lean, "")?;
        assert_eq!(LeanString::to_str(&s)?, "");

        // Simple ASCII
        let s = LeanString::new(lean, "Hello")?;
        assert_eq!(LeanString::to_str(&s)?, "Hello");

        // With punctuation
        let s = LeanString::new(lean, "Hello, World!")?;
        assert_eq!(LeanString::to_str(&s)?, "Hello, World!");

        // With newlines
        let s = LeanString::new(lean, "Line 1\nLine 2")?;
        assert_eq!(LeanString::to_str(&s)?, "Line 1\nLine 2");

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_to_str() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let test_strings = [
            "",
            "a",
            "Hello",
            "Hello, World!",
            "1234567890",
            "Special: !@#$%^&*()",
        ];

        for &s in &test_strings {
            let lean_str = LeanString::new(lean, s)?;
            assert_eq!(LeanString::to_str(&lean_str)?, s);
        }

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_unicode() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Various Unicode strings
        let s = LeanString::new(lean, "こんにちは")?; // Japanese
        assert_eq!(LeanString::to_str(&s)?, "こんにちは");

        let s = LeanString::new(lean, "你好")?; // Chinese
        assert_eq!(LeanString::to_str(&s)?, "你好");

        let s = LeanString::new(lean, "Здравствуй")?; // Russian
        assert_eq!(LeanString::to_str(&s)?, "Здравствуй");

        let s = LeanString::new(lean, "🦀🔥")?; // Emoji
        assert_eq!(LeanString::to_str(&s)?, "🦀🔥");

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_lengths() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // ASCII - byte length == char length
        let s = LeanString::new(lean, "Hello")?;
        assert_eq!(LeanString::len(&s), 5);
        assert_eq!(LeanString::byte_size(&s), 5);

        // Empty
        let s = LeanString::new(lean, "")?;
        assert_eq!(LeanString::len(&s), 0);
        assert_eq!(LeanString::byte_size(&s), 0);

        // Note: For multibyte characters, byte_size > len
        // The exact values depend on Lean's UTF-8 handling

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Array Conversions
// =============================================================================

#[test]
fn test_array_empty() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let arr = LeanArray::new(lean)?;

        assert!(LeanArray::is_empty(&arr));
        assert_eq!(LeanArray::size(&arr), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_with_nats() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Add natural numbers
        for i in 0..10 {
            let n = LeanNat::from_usize(lean, i)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        assert_eq!(LeanArray::size(&arr), 10);

        // Get elements back (as LeanAny, can't directly convert to nat without unsafe)
        for i in 0..10 {
            let elem = LeanArray::get(&arr, lean, i);
            assert!(elem.is_some(), "Element {} should exist", i);
        }

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_with_strings() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        let strings = ["first", "second", "third", "fourth", "fifth"];

        for s in &strings {
            let lean_str = LeanString::new(lean, s)?;
            arr = LeanArray::push(arr, lean_str.cast())?;
        }

        assert_eq!(LeanArray::size(&arr), strings.len());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_mixed_types() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Add different types (all cast to LeanAny)
        let n = LeanNat::from_usize(lean, 42)?;
        arr = LeanArray::push(arr, n.cast())?;

        let s = LeanString::new(lean, "Hello")?;
        arr = LeanArray::push(arr, s.cast())?;

        let inner_arr = LeanArray::new(lean)?;
        arr = LeanArray::push(arr, inner_arr.cast())?;

        assert_eq!(LeanArray::size(&arr), 3);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Type Casting Tests
// =============================================================================

#[test]
fn test_cast_nat_to_any() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n: LeanBound<LeanNat> = LeanNat::from_usize(lean, 42)?;
        let any: LeanBound<_> = n.cast();

        // The cast should preserve the object
        // (We can't easily convert back without unsafe, but it shouldn't crash)
        drop(any);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_cast_string_to_any() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s: LeanBound<LeanString> = LeanString::new(lean, "test")?;
        let any: LeanBound<_> = s.cast();

        drop(any);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_cast_array_to_any() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let arr: LeanBound<LeanArray> = LeanArray::new(lean)?;
        let any: LeanBound<_> = arr.cast();

        drop(any);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Unbind/Bind Conversion Tests
// =============================================================================

#[test]
fn test_nat_unbind_bind() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 100)?;
        let n_ref = n.unbind();
        let n2 = n_ref.bind(lean);

        assert_eq!(LeanNat::to_usize(&n2)?, 100);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_unbind_bind() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s = LeanString::new(lean, "Test")?;
        let s_ref = s.unbind();
        let s2 = s_ref.bind(lean);

        assert_eq!(LeanString::to_str(&s2)?, "Test");

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_unbind_bind() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;
        let n = LeanNat::from_usize(lean, 1)?;
        arr = LeanArray::push(arr, n.cast())?;

        let arr_ref = arr.unbind();
        let arr2 = arr_ref.bind(lean);

        assert_eq!(LeanArray::size(&arr2), 1);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Edge Cases and Error Handling
// =============================================================================

#[test]
fn test_string_with_null_byte_fails() {
    leo3::prepare_freethreaded_lean();

    let result = leo3::with_lean(|lean| {
        // Strings with null bytes should fail to create
        let result = LeanString::new(lean, "Hello\0World");
        assert!(result.is_err());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_out_of_bounds_get() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let arr = LeanArray::new(lean)?;

        // Getting from empty array should return None
        assert!(LeanArray::get(&arr, lean, 0).is_none());
        assert!(LeanArray::get(&arr, lean, 100).is_none());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
#[should_panic(expected = "Index out of bounds")]
fn test_array_out_of_bounds_set_panics() {
    leo3::prepare_freethreaded_lean();

    let _ = leo3::with_lean(|lean| {
        let arr = LeanArray::new(lean)?;
        let n = LeanNat::from_usize(lean, 1)?;

        // Setting out of bounds should panic
        let _ = LeanArray::set(arr, 0, n.cast())?;

        Ok::<(), LeanError>(())
    });
}

#[test]
#[should_panic(expected = "Cannot pop from empty array")]
fn test_array_pop_empty_panics() {
    leo3::prepare_freethreaded_lean();

    let _ = leo3::with_lean(|lean| {
        let arr = LeanArray::new(lean)?;

        // Popping from empty array should panic
        let _ = LeanArray::pop(arr)?;

        Ok::<(), LeanError>(())
    });
}
