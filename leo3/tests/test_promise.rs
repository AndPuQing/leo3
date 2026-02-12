//! Tests for LeanPromise<'l, T>
//!
//! LeanPromise provides safe wrappers for manually-resolvable async values.

use leo3::instance::LeanAny;
use leo3::prelude::*;
use leo3::promise::{LeanPromise, LeanPromiseType};
use leo3::types::LeanOption;

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
// the Lean task manager to be initialized.

#[cfg(test)]
mod api_tests {
    use super::*;
    use leo3::task::LeanTask;

    // These tests verify the API is correct

    #[test]
    fn test_promise_new_signature() {
        fn _check_new<'l>(lean: leo3::Lean<'l>) -> LeanResult<LeanPromise<'l, LeanAny>> {
            LeanPromise::new(lean)
        }
    }

    #[test]
    fn test_promise_resolve_signature() {
        fn _check_resolve<'l>(
            promise: LeanPromise<'l, LeanAny>,
            value: LeanBound<'l, LeanAny>,
        ) -> LeanResult<()> {
            promise.resolve(value)
        }
    }

    #[test]
    fn test_promise_task_signature() {
        fn _check_task<'l>(promise: &LeanPromise<'l, LeanAny>) -> LeanTask<'l, LeanAny> {
            promise.task()
        }
    }
}

// ============================================================================
// Runtime tests (require Lean runtime)
// ============================================================================

#[test]
fn test_promise_create_and_resolve() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create a promise
        let promise = LeanPromise::<LeanAny>::new(lean)?;

        // Verify it's actually a promise
        assert!(LeanPromise::<LeanAny>::is_promise(&promise.clone().cast()));

        // Get the associated task
        let task = promise.task();

        // Resolve the promise with a Nat value
        let value = LeanNat::from_usize(lean, 42)?;
        promise.resolve(value.cast())?;

        // The task result is Option.some(value) because lean_promise_resolve
        // wraps the value in mk_option_some internally.
        let result = task.get_owned();
        let opt: LeanBound<'_, LeanOption> = result.cast();
        let inner = LeanOption::get(&opt).expect("expected Some");
        let nat: LeanBound<'_, LeanNat> = inner.cast();
        assert_eq!(LeanNat::to_usize(&nat)?, 42);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_promise_task_multiple_refs() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let promise = LeanPromise::<LeanAny>::new(lean)?;

        // Getting the task multiple times should work
        let task1 = promise.task();
        let task2 = promise.task();

        // Resolve
        let value = LeanNat::from_usize(lean, 99)?;
        promise.resolve(value.cast())?;

        // Both tasks should see the same result (wrapped in Option.some)
        let r1: LeanBound<'_, LeanOption> = task1.get_owned().cast();
        let inner1 = LeanOption::get(&r1).expect("expected Some");
        let n1: LeanBound<'_, LeanNat> = inner1.cast();
        assert_eq!(LeanNat::to_usize(&n1)?, 99);

        let r2: LeanBound<'_, LeanOption> = task2.get_owned().cast();
        let inner2 = LeanOption::get(&r2).expect("expected Some");
        let n2: LeanBound<'_, LeanNat> = inner2.cast();
        assert_eq!(LeanNat::to_usize(&n2)?, 99);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}
