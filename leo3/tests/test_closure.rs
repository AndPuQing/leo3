//! Tests for LeanClosure<'l>
//!
//! LeanClosure provides safe, ergonomic closure handling with arity checking,
//! creation from Rust functions, and partial application support.

use leo3::closure::{LeanClosure, LeanClosureType, LeanFn1, LeanFn2};
use leo3::instance::LeanAny;
use leo3::prelude::*;
use std::ffi::c_void;

#[test]
fn test_closure_type_size() {
    // LeanClosure should be pointer-sized (same as LeanBound)
    assert_eq!(
        std::mem::size_of::<LeanClosure>(),
        std::mem::size_of::<*mut ()>()
    );
}

#[test]
fn test_closure_is_closure_check() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // A natural number is NOT a closure
        let n = LeanNat::from_usize(lean, 42)?;
        let any: LeanBound<'_, LeanAny> = n.cast();
        assert!(!LeanClosure::is_closure(&any));

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_closure_try_from_any_fails_for_non_closure() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // A string is NOT a closure
        let s = LeanString::mk(lean, "not a closure")?;
        let any: LeanBound<'_, LeanAny> = s.cast();
        assert!(LeanClosure::try_from_any(any).is_none());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_closure_marker_type() {
    // Verify the marker type exists and has the expected properties
    assert_eq!(
        std::mem::size_of::<LeanClosureType>(),
        0,
        "Marker type should be zero-sized"
    );
}

// ============================================================================
// Closure Creation Tests
// ============================================================================

// A simple identity function compatible with Lean's calling convention
unsafe extern "C" fn identity_fn(x: *mut leo3::ffi::lean_object) -> *mut leo3::ffi::lean_object {
    // Identity: just return the argument (ownership is transferred)
    x
}

// An increment function for natural numbers (only works for small values)
unsafe extern "C" fn inc_nat(x: *mut leo3::ffi::lean_object) -> *mut leo3::ffi::lean_object {
    let n = leo3::ffi::inline::lean_unbox(x);
    leo3::ffi::inline::lean_box(n.wrapping_add(1))
}

// A simple add function for natural numbers
unsafe extern "C" fn add_nat(
    a: *mut leo3::ffi::lean_object,
    b: *mut leo3::ffi::lean_object,
) -> *mut leo3::ffi::lean_object {
    let x = leo3::ffi::inline::lean_unbox(a);
    let y = leo3::ffi::inline::lean_unbox(b);
    leo3::ffi::inline::lean_box(x.wrapping_add(y))
}

#[test]
fn test_closure_from_fn1() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create a closure from a 1-arity function
        let closure = LeanClosure::from_fn1(lean, identity_fn)?;

        // Check arity
        assert_eq!(closure.arity(), 1);
        assert_eq!(closure.num_fixed(), 0);
        assert_eq!(closure.remaining_arity(), 1);
        assert!(!closure.is_saturated());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_closure_from_fn2() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create a closure from a 2-arity function
        let closure = LeanClosure::from_fn2(lean, add_nat)?;

        // Check arity
        assert_eq!(closure.arity(), 2);
        assert_eq!(closure.num_fixed(), 0);
        assert_eq!(closure.remaining_arity(), 2);
        assert!(!closure.is_saturated());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_closure_from_raw_fn() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create a closure with custom arity
        let closure = unsafe { LeanClosure::from_raw_fn(lean, identity_fn as *mut c_void, 1, 0)? };

        assert_eq!(closure.arity(), 1);
        assert_eq!(closure.num_fixed(), 0);

        // Function pointer should be preserved
        assert_eq!(closure.function_ptr(), identity_fn as *mut c_void);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_closure_from_raw_fn_validation() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // arity == 0 should fail
        let result = unsafe { LeanClosure::from_raw_fn(lean, identity_fn as *mut c_void, 0, 0) };
        assert!(result.is_err());

        // num_fixed >= arity should fail
        let result = unsafe { LeanClosure::from_raw_fn(lean, add_nat as *mut c_void, 2, 2) };
        assert!(result.is_err());

        let result = unsafe { LeanClosure::from_raw_fn(lean, add_nat as *mut c_void, 2, 3) };
        assert!(result.is_err());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

// ============================================================================
// Closure Application Tests
// ============================================================================

#[test]
fn test_closure_apply_identity() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create identity closure
        let closure = LeanClosure::from_fn1(lean, identity_fn)?;

        // Apply to a value
        let input = LeanNat::from_usize(lean, 42)?;
        let result = closure.apply(input.cast());

        // Check result is a boxed scalar with value 42
        let result_ptr = result.as_ptr() as usize;
        assert_eq!(result_ptr & 1, 1, "Result should be a scalar");
        assert_eq!(result_ptr >> 1, 42);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_closure_apply_inc() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create increment closure
        let closure = LeanClosure::from_fn1(lean, inc_nat)?;

        // Apply to a value
        let input = LeanNat::from_usize(lean, 5)?;
        let result = closure.apply(input.cast());

        // Check result is 6
        let result_ptr = result.as_ptr() as usize;
        assert_eq!(result_ptr & 1, 1, "Result should be a scalar");
        assert_eq!(result_ptr >> 1, 6);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_closure_apply_add() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create add closure
        let closure = LeanClosure::from_fn2(lean, add_nat)?;

        // Create args
        let a = LeanNat::from_usize(lean, 3)?;
        let b = LeanNat::from_usize(lean, 7)?;

        // Apply using apply2 directly
        let result = closure.apply2(a.cast(), b.cast());

        // Check result is 10
        let result_ptr = result.as_ptr() as usize;
        assert_eq!(result_ptr & 1, 1, "Result should be a scalar");
        assert_eq!(result_ptr >> 1, 10);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_closure_with_captured_validation() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let five = LeanNat::from_usize(lean, 5)?;

        // Too many captured arguments should fail
        let result = unsafe {
            LeanClosure::with_captured(
                lean,
                add_nat as *mut c_void,
                2,
                vec![five.clone().cast(), five.clone().cast()],
            )
        };
        assert!(result.is_err());

        // arity 0 should fail
        let result =
            unsafe { LeanClosure::with_captured(lean, identity_fn as *mut c_void, 0, vec![]) };
        assert!(result.is_err());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

// ============================================================================
// Type Checking Tests
// ============================================================================

#[test]
fn test_closure_is_closure_for_real_closure() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let closure = LeanClosure::from_fn1(lean, identity_fn)?;
        let any: LeanBound<'_, LeanAny> = closure.cast();

        assert!(LeanClosure::is_closure(&any));

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_closure_try_from_any_success() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let closure = LeanClosure::from_fn1(lean, identity_fn)?;
        let any: LeanBound<'_, LeanAny> = closure.cast();

        let recovered = LeanClosure::try_from_any(any);
        assert!(recovered.is_some());

        let recovered = recovered.unwrap();
        assert_eq!(recovered.arity(), 1);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[cfg(test)]
mod api_tests {
    use super::*;

    #[test]
    fn test_closure_api_available() {
        // Verify methods are available on the type
        fn _check_api<'l>(closure: &LeanClosure<'l>) {
            let _arity: u16 = closure.arity();
            let _fixed: u16 = closure.num_fixed();
            let _remaining: u16 = closure.remaining_arity();
            let _saturated: bool = closure.is_saturated();
            let _fn_ptr: *mut c_void = closure.function_ptr();
        }
    }

    #[test]
    fn test_apply_api_signature() {
        // Verify apply methods have correct signatures
        fn _check_apply<'l>(
            closure: &LeanClosure<'l>,
            arg: LeanBound<'l, LeanAny>,
        ) -> LeanBound<'l, LeanAny> {
            closure.apply(arg)
        }
    }

    #[test]
    fn test_creation_api_available() {
        // Verify creation methods compile
        fn _check_from_fn1<'l>(
            lean: leo3::marker::Lean<'l>,
            f: LeanFn1,
        ) -> LeanResult<LeanClosure<'l>> {
            LeanClosure::from_fn1(lean, f)
        }

        fn _check_from_fn2<'l>(
            lean: leo3::marker::Lean<'l>,
            f: LeanFn2,
        ) -> LeanResult<LeanClosure<'l>> {
            LeanClosure::from_fn2(lean, f)
        }

        fn _check_with_captured<'l>(
            lean: leo3::marker::Lean<'l>,
            fun: *mut c_void,
            captured: Vec<LeanBound<'l, LeanAny>>,
        ) -> LeanResult<LeanClosure<'l>> {
            // SAFETY: This is just a compile-time signature check
            unsafe { LeanClosure::with_captured(lean, fun, 3, captured) }
        }
    }
}
