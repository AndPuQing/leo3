//! Lean ↔ Rust integration tests
//!
//! These tests call Lean functions from Rust and verify the results.
//!
//! ⚠️  These tests require Lean4 to be installed and the Lean code
//! in ../lean/ to be compiled with Lake.

use leo3::prelude::*;

// FFI declarations for exported Lean functions
extern "C" {
    // Basic arithmetic
    fn lean_test_add(a: usize, b: usize) -> usize;
    fn lean_test_multiply(a: usize, b: usize) -> usize;
    fn lean_test_factorial(n: usize) -> usize;

    // Boolean operations
    fn lean_test_is_even(n: usize) -> bool;
    fn lean_test_is_prime(n: usize) -> bool;
}

// =============================================================================
// Arithmetic Tests
// =============================================================================

#[test]
#[ignore = "Requires Lean4 to be linked"]
fn test_lean_add() {
    leo3::prepare_freethreaded_lean();

    unsafe {
        assert_eq!(lean_test_add(2, 3), 5);
        assert_eq!(lean_test_add(0, 0), 0);
        assert_eq!(lean_test_add(100, 200), 300);
    }
}

#[test]
#[ignore = "Requires Lean4 to be linked"]
fn test_lean_multiply() {
    leo3::prepare_freethreaded_lean();

    unsafe {
        assert_eq!(lean_test_multiply(2, 3), 6);
        assert_eq!(lean_test_multiply(0, 100), 0);
        assert_eq!(lean_test_multiply(7, 8), 56);
    }
}

#[test]
#[ignore = "Requires Lean4 to be linked"]
fn test_lean_factorial() {
    leo3::prepare_freethreaded_lean();

    unsafe {
        assert_eq!(lean_test_factorial(0), 1);
        assert_eq!(lean_test_factorial(1), 1);
        assert_eq!(lean_test_factorial(5), 120);
        assert_eq!(lean_test_factorial(10), 3628800);
    }
}

// =============================================================================
// Boolean Tests
// =============================================================================

#[test]
#[ignore = "Requires Lean4 to be linked"]
fn test_lean_is_even() {
    leo3::prepare_freethreaded_lean();

    unsafe {
        assert!(lean_test_is_even(0));
        assert!(!lean_test_is_even(1));
        assert!(lean_test_is_even(2));
        assert!(!lean_test_is_even(3));
        assert!(lean_test_is_even(100));
        assert!(!lean_test_is_even(101));
    }
}

#[test]
#[ignore = "Requires Lean4 to be linked"]
fn test_lean_is_prime() {
    leo3::prepare_freethreaded_lean();

    unsafe {
        // Not prime
        assert!(!lean_test_is_prime(0));
        assert!(!lean_test_is_prime(1));
        assert!(!lean_test_is_prime(4));
        assert!(!lean_test_is_prime(6));
        assert!(!lean_test_is_prime(8));
        assert!(!lean_test_is_prime(9));

        // Prime
        assert!(lean_test_is_prime(2));
        assert!(lean_test_is_prime(3));
        assert!(lean_test_is_prime(5));
        assert!(lean_test_is_prime(7));
        assert!(lean_test_is_prime(11));
        assert!(lean_test_is_prime(13));
    }
}

// =============================================================================
// Round-Trip Tests (Rust → Lean → Rust)
// =============================================================================

#[test]
#[ignore = "Requires Lean4 to be linked"]
fn test_round_trip_nat() {
    leo3::prepare_freethreaded_lean();

    let result = leo3::with_lean(|lean| {
        // Create Rust nat
        let n = LeanNat::from_usize(lean, 42)?;

        // Convert to usize, pass to Lean, get back
        let value = LeanNat::to_usize(&n)?;
        let lean_result = unsafe { lean_test_add(value, 8) };

        // Create Lean nat from result
        let result_nat = LeanNat::from_usize(lean, lean_result)?;
        assert_eq!(LeanNat::to_usize(&result_nat)?, 50);

        Ok::<(), LeanError>(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Future Tests (requires more complex FFI)
// =============================================================================

#[test]
#[ignore = "Not yet implemented"]
fn test_lean_string_operations() {
    // TODO: Test passing strings to Lean and getting them back
    // This requires proper string marshalling
}

#[test]
#[ignore = "Not yet implemented"]
fn test_lean_array_operations() {
    // TODO: Test passing arrays to Lean and getting them back
    // This requires proper array marshalling
}

#[test]
#[ignore = "Not yet implemented"]
fn test_rust_calling_lean_calling_rust() {
    // TODO: Test Rust → Lean → Rust callback chain
    // This requires callback support
}
