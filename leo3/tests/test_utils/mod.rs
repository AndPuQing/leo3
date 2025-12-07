//! Test utilities for Leo3 integration tests
//!
//! This module provides helper functions and macros for testing,
//! inspired by PyO3's test infrastructure.

use leo3::prelude::*;

/// Execute Lean code and return result
///
/// This is a helper for tests that need to work with Lean objects.
///
/// # Example
///
/// ```rust,ignore
/// with_lean_test(|lean| {
///     let n = LeanNat::from_usize(lean, 42)?;
///     assert_eq!(LeanNat::to_usize(&n)?, 42);
///     Ok(())
/// });
/// ```
pub fn with_lean_test<F>(f: F)
where
    F: for<'l> FnOnce(Lean<'l>) -> LeanResult<()>,
{
    leo3::prepare_freethreaded_lean();
    let result = leo3::with_lean(f);
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Assert that two Lean natural numbers are equal
#[macro_export]
macro_rules! assert_lean_nat_eq {
    ($a:expr, $b:expr) => {
        assert!(
            LeanNat::eq(&$a, &$b),
            "Lean nat assertion failed: left != right"
        );
    };
}

/// Assert that two Lean strings are equal
#[macro_export]
macro_rules! assert_lean_string_eq {
    ($a:expr, $b:expr) => {
        assert!(
            LeanString::eq(&$a, &$b),
            "Lean string assertion failed: left != right"
        );
    };
}

/// Assert that a Lean nat has the expected usize value
#[macro_export]
macro_rules! assert_lean_nat_value {
    ($nat:expr, $expected:expr) => {
        assert_eq!(
            LeanNat::to_usize(&$nat).expect("Failed to convert to usize"),
            $expected,
            "Lean nat value mismatch"
        );
    };
}

/// Assert that a Lean string has the expected str value
#[macro_export]
macro_rules! assert_lean_string_value {
    ($string:expr, $expected:expr) => {
        assert_eq!(
            LeanString::to_str(&$string).expect("Failed to convert to str"),
            $expected,
            "Lean string value mismatch"
        );
    };
}

/// Assert that a Lean array has the expected size
#[macro_export]
macro_rules! assert_lean_array_size {
    ($array:expr, $expected:expr) => {
        assert_eq!(
            LeanArray::size(&$array),
            $expected,
            "Lean array size mismatch"
        );
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_with_lean_test_helper() {
        with_lean_test(|lean| {
            let n = LeanNat::from_usize(lean, 100)?;
            assert_eq!(LeanNat::to_usize(&n)?, 100);
            Ok(())
        });
    }
}
