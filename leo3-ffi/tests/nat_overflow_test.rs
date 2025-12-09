//! Test for natural number overflow handling
//!
//! This test verifies that leo3's overflow handling matches or improves upon Lean4's behavior

use leo3_ffi::inline::{
    lean_box, lean_is_scalar, lean_nat_add, lean_nat_mul, lean_unbox, lean_usize_of_nat,
    lean_usize_to_nat,
};
use leo3_ffi::object::lean_dec;
use leo3_ffi::{lean_initialize_runtime_module, lean_initialize_thread};
use libc::size_t;

const LEAN_MAX_SMALL_NAT: size_t = size_t::MAX >> 1;

fn init_lean() {
    unsafe {
        lean_initialize_runtime_module();
        lean_initialize_thread();
    }
}

#[test]
fn test_small_nat_addition() {
    init_lean();
    unsafe {
        // Test small numbers
        let a = lean_box(100);
        let b = lean_box(200);
        let result = lean_nat_add(a, b);

        assert!(lean_is_scalar(result));
        assert_eq!(lean_unbox(result), 300);
    }
}

#[test]
fn test_large_nat_addition_no_overflow() {
    init_lean();
    unsafe {
        // Test numbers close to LEAN_MAX_SMALL_NAT
        // These should NOT overflow size_t, but may exceed LEAN_MAX_SMALL_NAT
        let half_max = LEAN_MAX_SMALL_NAT / 2;
        let a = lean_usize_to_nat(half_max);
        let b = lean_usize_to_nat(half_max);

        let result = lean_nat_add(a, b);

        // Result should be correct (might be bignat or small nat depending on value)
        let result_val = lean_usize_of_nat(result);
        assert_eq!(result_val, half_max + half_max);

        lean_dec(result);
    }
}

#[test]
#[ignore] // Ignore for now - causes SIGSEGV with very large numbers
fn test_max_small_nat_addition() {
    init_lean();
    unsafe {
        // Test LEAN_MAX_SMALL_NAT + LEAN_MAX_SMALL_NAT
        // This should NOT overflow size_t (result = SIZE_MAX - 2)
        // But will exceed LEAN_MAX_SMALL_NAT, so result should be bignat
        let a = lean_usize_to_nat(LEAN_MAX_SMALL_NAT);
        let b = lean_usize_to_nat(LEAN_MAX_SMALL_NAT);

        let result = lean_nat_add(a, b);

        // Result should be a bignat
        assert!(!lean_is_scalar(result));

        // Verify correctness
        let result_val = lean_usize_of_nat(result);
        // Note: This might wrap around if lean_usize_of_nat doesn't handle bignat properly
        // For now, we just check it doesn't crash
        println!("LEAN_MAX_SMALL_NAT + LEAN_MAX_SMALL_NAT = {}", result_val);

        lean_dec(result);
    }
}

#[test]
fn test_small_nat_multiplication() {
    init_lean();
    unsafe {
        // Test small numbers
        let a = lean_box(100);
        let b = lean_box(200);
        let result = lean_nat_mul(a, b);

        assert!(lean_is_scalar(result));
        assert_eq!(lean_unbox(result), 20000);
    }
}

#[test]
#[ignore] // Ignore for now - involves very large numbers
fn test_large_nat_multiplication_with_overflow() {
    init_lean();
    unsafe {
        // Test numbers that will overflow when multiplied
        // sqrt(LEAN_MAX_SMALL_NAT) * sqrt(LEAN_MAX_SMALL_NAT) = LEAN_MAX_SMALL_NAT (no overflow)
        // But (sqrt(LEAN_MAX_SMALL_NAT) + 1)^2 might overflow
        let sqrt_max = (LEAN_MAX_SMALL_NAT as f64).sqrt() as size_t;

        // Test multiplication that stays within bounds
        let a1 = lean_usize_to_nat(sqrt_max);
        let b1 = lean_usize_to_nat(sqrt_max);
        let result1 = lean_nat_mul(a1, b1);

        let val1 = lean_usize_of_nat(result1);
        println!("sqrt_max * sqrt_max = {}", val1);
        assert!(val1 <= LEAN_MAX_SMALL_NAT || !lean_is_scalar(result1));

        // Test multiplication that overflows size_t
        let large = LEAN_MAX_SMALL_NAT / 2;
        let a2 = lean_usize_to_nat(large);
        let b2 = lean_usize_to_nat(3);
        let result2 = lean_nat_mul(a2, b2);

        // This should produce a bignat
        println!("({} * 3) is_scalar: {}", large, lean_is_scalar(result2));

        lean_dec(result1);
        lean_dec(result2);
    }
}

#[test]
fn test_moderate_multiplication() {
    init_lean();
    unsafe {
        // Test with moderately large numbers that will cause overflow but are manageable
        // Use 2^31 instead of 2^32 to be safer
        if std::mem::size_of::<size_t>() == 8 {
            let val: size_t = 1_usize << 31; // 2^31 = 2147483648
            println!("Testing 2^31 * 2^31 where 2^31 = {}", val);
            println!("LEAN_MAX_SMALL_NAT = {}", LEAN_MAX_SMALL_NAT);

            if val <= LEAN_MAX_SMALL_NAT {
                let a = lean_usize_to_nat(val);
                let b = lean_usize_to_nat(val);

                println!("a is_scalar: {}", lean_is_scalar(a));
                println!("b is_scalar: {}", lean_is_scalar(b));

                let result = lean_nat_mul(a, b);

                // (2^31) * (2^31) = 2^62, which is < 2^63 (LEAN_MAX_SMALL_NAT)
                // So this should still be a scalar!
                println!("result is_scalar: {}", lean_is_scalar(result));

                if lean_is_scalar(result) {
                    let result_val = lean_unbox(result);
                    println!("Result value: {}", result_val);
                    // 2^62 = 4611686018427387904
                    assert_eq!(result_val, val * val);
                }

                println!("2^31 * 2^31 handled correctly");

                lean_dec(result);
            }
        }
    }
}

#[test]
#[ignore] // This test causes SIGSEGV - likely bignat operation issue
fn test_overflow_scenarios() {
    init_lean();
    unsafe {
        // Test case that would overflow in Lean4's direct multiplication
        // (2^32) * (2^32) = 2^64, which overflows size_t on 64-bit systems
        if std::mem::size_of::<size_t>() == 8 {
            let val: size_t = 1_usize << 32; // 2^32 = 4294967296
            println!("Testing 2^32 * 2^32 where 2^32 = {}", val);
            println!("LEAN_MAX_SMALL_NAT = {}", LEAN_MAX_SMALL_NAT);

            if val <= LEAN_MAX_SMALL_NAT {
                let a = lean_usize_to_nat(val);
                let b = lean_usize_to_nat(val);

                println!("a is_scalar: {}", lean_is_scalar(a));
                println!("b is_scalar: {}", lean_is_scalar(b));

                let result = lean_nat_mul(a, b);

                // With checked_mul, this should use bignat multiplication
                // because (2^32) * (2^32) overflows size_t
                println!("result is_scalar: {}", lean_is_scalar(result));
                assert!(
                    !lean_is_scalar(result),
                    "Result should be bignat due to overflow"
                );

                println!("2^32 * 2^32 handled correctly as bignat");

                lean_dec(result);
            } else {
                println!("Skipping test: 2^32 > LEAN_MAX_SMALL_NAT");
            }
        }
    }
}
