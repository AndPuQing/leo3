//! Basic integration tests for Leo3
//!
//! These tests demonstrate basic runtime initialization and usage patterns.
//!
//! ## Running These Tests
//!
//! Without Lean4 (compile-only):
//! ```bash
//! LEO3_NO_LEAN=1 cargo test
//! ```
//!
//! With Lean4 (full runtime tests):
//! ```bash
//! cargo test --features runtime-tests
//! ```

use leo3::prelude::*;

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_runtime_initialization() {
    // Initialize the Lean runtime
    leo3::prepare_freethreaded_lean();

    // Use with_lean to get a Lean token
    let result: LeanResult<()> = leo3::with_lean(|_lean| {
        // If we get here, initialization succeeded
        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_basic_nat_creation() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create a natural number
        let n = LeanNat::from_usize(lean, 42)?;

        // Convert back to usize
        assert_eq!(LeanNat::to_usize(&n)?, 42);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_basic_string_creation() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create a Lean string
        let s = LeanString::new(lean, "Hello, Lean!")?;

        // Read it back
        assert_eq!(LeanString::to_str(&s)?, "Hello, Lean!");
        assert_eq!(LeanString::len(&s), 12);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_basic_array_creation() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create an empty array
        let arr = LeanArray::new(lean)?;

        // Check it's empty
        assert!(LeanArray::is_empty(&arr));
        assert_eq!(LeanArray::size(&arr), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_leanbound_clone() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n1 = LeanNat::from_usize(lean, 42)?;

        // Clone should increment reference count
        let n2 = n1.clone();

        // Both should have the same value
        assert_eq!(LeanNat::to_usize(&n1)?, 42);
        assert_eq!(LeanNat::to_usize(&n2)?, 42);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_unbind_and_rebind() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create a bound object
        let n = LeanNat::from_usize(lean, 42)?;

        // Unbind it to get a LeanRef
        let n_ref = n.unbind();

        // Later, rebind it
        let n2 = n_ref.bind(lean);

        // Should still have the same value
        assert_eq!(LeanNat::to_usize(&n2)?, 42);

        Ok(())
    });

    assert!(result.is_ok());
}
