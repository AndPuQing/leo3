//! Feature flag testing
//!
//! These tests verify that Leo3 works correctly with different feature combinations.

// Test that core functionality works without any features
#[cfg(not(feature = "macros"))]
#[test]
fn test_no_features() {
    use leo3::prelude::*;

    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Core API should work without macros
        let n = LeanNat::from_usize(lean, 42)?;
        assert_eq!(LeanNat::to_usize(&n)?, 42);

        let s = LeanString::mk(lean, "test")?;
        assert_eq!(LeanString::cstr(&s)?, "test");

        let arr = LeanArray::empty(lean)?;
        assert_eq!(LeanArray::size(&arr), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

// Test that macros feature enables procedural macros
#[cfg(feature = "macros")]
#[test]
fn test_with_macros() {
    // TODO: Once macros are implemented, test them here
    // For now, just check that the feature is enabled
    #[cfg(feature = "macros")]
    {
        // Macros are available
        let _ = ();
    }
}

// Test default features
#[test]
fn test_default_config() {
    use leo3::prelude::*;

    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 100)?;
        assert_eq!(LeanNat::to_usize(&n)?, 100);
        Ok(())
    });

    assert!(result.is_ok());
}
