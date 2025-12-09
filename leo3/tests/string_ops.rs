//! String operation tests for Leo3
//!
//! These tests demonstrate LeanString functionality including creation,
//! manipulation, and comparison operations.

use leo3::prelude::*;

#[test]
fn test_string_creation_and_conversion() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s = LeanString::mk(lean, "Hello, Lean4!")?;

        assert_eq!(LeanString::cstr(&s)?, "Hello, Lean4!");
        assert_eq!(LeanString::len(&s), 13);
        assert!(!LeanString::isEmpty(&s));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_empty_string() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s = LeanString::mk(lean, "")?;

        assert_eq!(LeanString::cstr(&s)?, "");
        assert_eq!(LeanString::len(&s), 0);
        assert!(LeanString::isEmpty(&s));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_push() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s = LeanString::mk(lean, "Hello")?;
        let s = LeanString::push(s, '!' as u32)?;

        assert_eq!(LeanString::cstr(&s)?, "Hello!");
        assert_eq!(LeanString::len(&s), 6);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_append() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s1 = LeanString::mk(lean, "Hello, ")?;
        let s2 = LeanString::mk(lean, "World!")?;
        let result = LeanString::append(s1, &s2)?;

        assert_eq!(LeanString::cstr(&result)?, "Hello, World!");
        assert_eq!(LeanString::len(&result), 13);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_equality() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s1 = LeanString::mk(lean, "hello")?;
        let s2 = LeanString::mk(lean, "hello")?;
        let s3 = LeanString::mk(lean, "world")?;

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
        let s1 = LeanString::mk(lean, "apple")?;
        let s2 = LeanString::mk(lean, "banana")?;

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
        let s = LeanString::mk(lean, "Hello, 世界!")?;

        assert_eq!(LeanString::cstr(&s)?, "Hello, 世界!");
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
        let s = LeanString::mk(lean, "Hello, World!")?;

        // Extract "Hello" (bytes 0-5)
        let sub = LeanString::substring(lean, &s, 0, 5)?;
        assert_eq!(LeanString::cstr(&sub)?, "Hello");

        // Extract "World" (bytes 7-12)
        let sub = LeanString::substring(lean, &s, 7, 12)?;
        assert_eq!(LeanString::cstr(&sub)?, "World");

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_chaining() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Chain multiple string operations
        let s = LeanString::mk(lean, "Hello")?;
        let s = LeanString::push(s, ',' as u32)?;
        let s = LeanString::push(s, ' ' as u32)?;

        let world = LeanString::mk(lean, "World")?;
        let s = LeanString::append(s, &world)?;
        let s = LeanString::push(s, '!' as u32)?;

        assert_eq!(LeanString::cstr(&s)?, "Hello, World!");

        Ok(())
    });

    assert!(result.is_ok());
}
