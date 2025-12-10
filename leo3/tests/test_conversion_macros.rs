//! Tests for smart conversion macros (to_lean! and from_lean!)
//!
//! These macros automatically select the most efficient conversion method.

use leo3::prelude::*;

#[test]
fn test_to_lean_vec_u8_optimized() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Should use optimized memcpy version
        let data = vec![1u8, 2, 3, 4, 5];
        let ba = to_lean!(data, lean, Vec<u8>)?;

        // Verify it's a ByteArray
        assert_eq!(LeanByteArray::size(&ba), 5);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_to_lean_slice_u8_optimized() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Should use optimized memcpy version
        let slice = b"Hello, World!";
        let ba = to_lean!(slice, lean, &[u8])?;

        assert_eq!(LeanByteArray::size(&ba), 13);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_to_lean_vec_generic() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Should use generic IntoLean implementation
        let numbers = vec![1u64, 2, 3, 4, 5];
        let arr = to_lean!(numbers, lean)?;

        assert_eq!(LeanArray::size(&arr), 5);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_from_lean_vec_u8_optimized() {
    use leo3::conversion::vec_u8_into_lean;

    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create a ByteArray
        let original = vec![10u8, 20, 30, 40, 50];
        let ba = vec_u8_into_lean(original.clone(), lean)?;

        // Convert back using the macro (should use optimized version)
        let recovered: Vec<u8> = from_lean!(&ba, Vec<u8>)?;

        assert_eq!(recovered, original);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_from_lean_vec_generic() {
    use leo3::conversion::IntoLean;

    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create an array of numbers
        let original = vec![1u64, 2, 3, 4, 5];
        let arr = original.clone().into_lean(lean)?;

        // Convert back using the macro (should use generic FromLean)
        let recovered: Vec<u64> = from_lean!(&arr, Vec<u64>)?;

        assert_eq!(recovered, original);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_roundtrip_vec_u8() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let original: Vec<u8> = (0..=255).cycle().take(1000).collect();

        // Use macros for both conversions
        let ba = to_lean!(original.clone(), lean, Vec<u8>)?;
        let recovered: Vec<u8> = from_lean!(&ba, Vec<u8>)?;

        assert_eq!(recovered, original);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_roundtrip_vec_generic() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let original = vec![10u64, 20, 30, 40, 50];

        // Use macros for both conversions
        let arr = to_lean!(original.clone(), lean)?;
        let recovered: Vec<u64> = from_lean!(&arr, Vec<u64>)?;

        assert_eq!(recovered, original);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_macro_with_empty_vec() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Empty Vec<u8>
        let empty: Vec<u8> = vec![];
        let ba = to_lean!(empty, lean, Vec<u8>)?;
        assert_eq!(LeanByteArray::size(&ba), 0);

        // Empty Vec<u64>
        let empty: Vec<u64> = vec![];
        let arr = to_lean!(empty, lean)?;
        assert_eq!(LeanArray::size(&arr), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_macro_with_large_vec_u8() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Large Vec<u8> to test performance benefit
        let large: Vec<u8> = (0..=255).cycle().take(100_000).collect();
        let ba = to_lean!(large.clone(), lean, Vec<u8>)?;

        assert_eq!(LeanByteArray::size(&ba), 100_000);

        let recovered: Vec<u8> = from_lean!(&ba, Vec<u8>)?;
        assert_eq!(recovered.len(), 100_000);
        assert_eq!(recovered, large);

        Ok(())
    });

    assert!(result.is_ok());
}
