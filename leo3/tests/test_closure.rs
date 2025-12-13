//! Tests for LeanClosure<'l>
//!
//! LeanClosure provides safe, ergonomic closure handling with arity checking.

use leo3::closure::{LeanClosure, LeanClosureType};
use leo3::instance::LeanAny;
use leo3::prelude::*;

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

// Note: These tests require actual Lean closures to be created.
// Most closure functionality requires integration with the Lean runtime
// to create closure objects. The following tests verify the API
// compiles and basic type checking works.

#[test]
fn test_closure_marker_type() {
    // Verify the marker type exists and has the expected properties
    assert_eq!(
        std::mem::size_of::<LeanClosureType>(),
        0,
        "Marker type should be zero-sized"
    );
}

#[cfg(test)]
mod api_tests {
    use super::*;

    // These tests verify the API is correct even without runtime closure objects

    #[test]
    fn test_closure_api_available() {
        // Verify methods are available on the type
        fn _check_api<'l>(closure: &LeanClosure<'l>) {
            let _arity: u16 = closure.arity();
            let _fixed: u16 = closure.num_fixed();
            let _remaining: u16 = closure.remaining_arity();
            let _saturated: bool = closure.is_saturated();
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
}
