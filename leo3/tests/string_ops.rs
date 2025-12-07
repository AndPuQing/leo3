//! String operation tests for Leo3
//!
//! These tests demonstrate LeanString functionality including creation,
//! manipulation, and comparison operations.

use leo3::prelude::*;

#[test]
fn test_string_creation_and_conversion() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s = LeanString::new(lean, "Hello, Lean4!")?;

        assert_eq!(LeanString::to_str(&s)?, "Hello, Lean4!");
        assert_eq!(LeanString::len(&s), 13);
        assert!(!LeanString::is_empty(&s));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_empty_string() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s = LeanString::new(lean, "")?;

        assert_eq!(LeanString::to_str(&s)?, "");
        assert_eq!(LeanString::len(&s), 0);
        assert!(LeanString::is_empty(&s));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_push() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s = LeanString::new(lean, "Hello")?;
        let s = LeanString::push(s, '!' as u32)?;

        assert_eq!(LeanString::to_str(&s)?, "Hello!");
        assert_eq!(LeanString::len(&s), 6);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_append() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s1 = LeanString::new(lean, "Hello, ")?;
        let s2 = LeanString::new(lean, "World!")?;
        let result = LeanString::append(s1, &s2)?;

        assert_eq!(LeanString::to_str(&result)?, "Hello, World!");
        assert_eq!(LeanString::len(&result), 13);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_equality() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s1 = LeanString::new(lean, "hello")?;
        let s2 = LeanString::new(lean, "hello")?;
        let s3 = LeanString::new(lean, "world")?;

        assert!(LeanString::eq(&s1, &s2));
        assert!(!LeanString::eq(&s1, &s3));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_comparison() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s1 = LeanString::new(lean, "apple")?;
        let s2 = LeanString::new(lean, "banana")?;

        // "apple" < "banana" lexicographically
        assert!(LeanString::lt(&s1, &s2));
        assert!(!LeanString::lt(&s2, &s1));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_unicode() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test with Unicode characters
        let s = LeanString::new(lean, "Hello, 世界!")?;

        assert_eq!(LeanString::to_str(&s)?, "Hello, 世界!");
        // UTF-8 length: "Hello, " = 7, "世界" = 6 bytes (2 chars), "!" = 1
        // But len() returns character count, not byte count
        assert!(LeanString::len(&s) > 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_substring() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s = LeanString::new(lean, "Hello, World!")?;

        // Extract "Hello" (bytes 0-5)
        let sub = LeanString::substring(lean, &s, 0, 5)?;
        assert_eq!(LeanString::to_str(&sub)?, "Hello");

        // Extract "World" (bytes 7-12)
        let sub = LeanString::substring(lean, &s, 7, 12)?;
        assert_eq!(LeanString::to_str(&sub)?, "World");

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_chaining() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Chain multiple string operations
        let s = LeanString::new(lean, "Hello")?;
        let s = LeanString::push(s, ',' as u32)?;
        let s = LeanString::push(s, ' ' as u32)?;

        let world = LeanString::new(lean, "World")?;
        let s = LeanString::append(s, &world)?;
        let s = LeanString::push(s, '!' as u32)?;

        assert_eq!(LeanString::to_str(&s)?, "Hello, World!");

        Ok(())
    });

    assert!(result.is_ok());
}
