//! Tests for LeanPromise<'l, T>
//!
//! LeanPromise provides safe wrappers for manually-resolvable async values.

use leo3::instance::LeanAny;
use leo3::prelude::*;
use leo3::promise::{LeanPromise, LeanPromiseType};

#[test]
fn test_promise_type_size() {
    // LeanPromise should be pointer-sized (same as LeanBound)
    assert_eq!(
        std::mem::size_of::<LeanPromise<LeanAny>>(),
        std::mem::size_of::<*mut ()>()
    );
}

#[test]
fn test_promise_marker_type() {
    // Verify the marker type exists and has the expected properties
    assert_eq!(
        std::mem::size_of::<LeanPromiseType<LeanAny>>(),
        0,
        "Marker type should be zero-sized"
    );
}

#[test]
fn test_promise_is_promise_check() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // A natural number is NOT a promise
        let n = LeanNat::from_usize(lean, 42)?;
        let any: LeanBound<'_, LeanAny> = n.cast();
        assert!(!LeanPromise::<LeanAny>::is_promise(&any));

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_promise_try_from_any_fails_for_non_promise() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // A string is NOT a promise
        let s = LeanString::mk(lean, "not a promise")?;
        let any: LeanBound<'_, LeanAny> = s.cast();
        assert!(LeanPromise::<LeanAny>::try_from_any(any).is_none());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

// Note: Runtime tests for promise creation and resolution require
// lean_promise_new, lean_promise_resolve, etc. which may not be
// available in all Lean versions. We test the API signatures instead.

#[cfg(test)]
mod api_tests {
    use super::*;
    use leo3::task::LeanTask;

    // These tests verify the API is correct

    #[test]
    fn test_promise_new_signature() {
        fn _check_new<'l>(lean: leo3::Lean<'l>) -> LeanPromise<'l, LeanAny> {
            LeanPromise::new(lean)
        }
    }

    #[test]
    fn test_promise_resolve_signature() {
        fn _check_resolve<'l>(promise: LeanPromise<'l, LeanAny>, value: LeanBound<'l, LeanAny>) {
            promise.resolve(value);
        }
    }

    #[test]
    fn test_promise_task_signature() {
        fn _check_task<'l>(promise: &LeanPromise<'l, LeanAny>) -> LeanTask<'l, LeanAny> {
            promise.task()
        }
    }
}
