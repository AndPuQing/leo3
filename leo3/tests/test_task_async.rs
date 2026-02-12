//! Tests for LeanTask async combinators and Future integration.
//!
//! Runtime tests are gated behind `feature = "runtime-tests"` since they
//! require the Lean4 runtime to be linked.

use leo3::instance::LeanAny;
use leo3::prelude::*;
use leo3::task::LeanTask;
use leo3::task_combinators::{self, Either, TimeoutError};
use std::time::Duration;

// ============================================================================
// Compile-time API signature tests (always run)
// ============================================================================

#[test]
fn test_combinator_types_are_sized() {
    assert_eq!(
        std::mem::size_of::<TimeoutError>(),
        std::mem::size_of::<Duration>(),
    );
    // Either should be an enum
    assert!(std::mem::size_of::<Either<u8, u16>>() > 0);
}

#[test]
fn test_join_signature() {
    fn _check<'l>(
        a: LeanTask<'l, LeanAny>,
        b: LeanTask<'l, LeanAny>,
    ) -> (LeanBound<'l, LeanAny>, LeanBound<'l, LeanAny>) {
        task_combinators::join(a, b)
    }
}

#[test]
fn test_select_signature() {
    fn _check<'l>(
        a: LeanTask<'l, LeanAny>,
        b: LeanTask<'l, LeanAny>,
    ) -> Either<LeanBound<'l, LeanAny>, LeanBound<'l, LeanAny>> {
        task_combinators::select(a, b)
    }
}

#[test]
fn test_race_signature() {
    fn _check<'l>(tasks: Vec<LeanTask<'l, LeanAny>>) -> LeanBound<'l, LeanAny> {
        task_combinators::race(tasks)
    }
}

#[test]
fn test_timeout_signature() {
    fn _check<'l>(task: LeanTask<'l, LeanAny>) -> Result<LeanBound<'l, LeanAny>, TimeoutError> {
        task_combinators::timeout(task, Duration::from_secs(1))
    }
}

#[test]
fn test_timeout_error_display() {
    let err = TimeoutError {
        duration: Duration::from_millis(500),
    };
    let msg = format!("{}", err);
    assert!(msg.contains("500"));
    assert!(msg.contains("timed out"));
}

#[test]
fn test_join_future_signature() {
    fn _check<'l>(
        a: LeanTask<'l, LeanAny>,
        b: LeanTask<'l, LeanAny>,
    ) -> impl std::future::Future<Output = (LeanBound<'l, LeanAny>, LeanBound<'l, LeanAny>)> {
        task_combinators::join_future(a, b)
    }
}

#[test]
fn test_select_future_signature() {
    fn _check<'l>(
        a: LeanTask<'l, LeanAny>,
        b: LeanTask<'l, LeanAny>,
    ) -> impl std::future::Future<Output = Either<LeanBound<'l, LeanAny>, LeanBound<'l, LeanAny>>>
    {
        task_combinators::select_future(a, b)
    }
}

#[test]
fn test_race_future_signature() {
    fn _check<'l>(
        tasks: Vec<LeanTask<'l, LeanAny>>,
    ) -> impl std::future::Future<Output = LeanBound<'l, LeanAny>> {
        task_combinators::race_future(tasks)
    }
}

#[test]
fn test_timeout_future_signature() {
    fn _check<'l>(
        task: LeanTask<'l, LeanAny>,
    ) -> impl std::future::Future<Output = Result<LeanBound<'l, LeanAny>, TimeoutError>> {
        task_combinators::timeout_future(task, Duration::from_secs(1))
    }
}

// ============================================================================
// Runtime tests (require Lean4 linked)
// ============================================================================

/// Helper: create a closure that returns a boxed nat value.
/// The closure takes one argument (the IO world token) and ignores it.
unsafe extern "C" fn slow_nat(_world: *mut leo3::ffi::lean_object) -> *mut leo3::ffi::lean_object {
    std::thread::sleep(Duration::from_millis(200));
    leo3::ffi::inline::lean_box(7)
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_join_with_pure_tasks() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let val_a = LeanNat::from_usize(lean, 10).unwrap();
        let val_b = LeanNat::from_usize(lean, 20).unwrap();

        let task_a = LeanTask::pure(val_a);
        let task_b = LeanTask::pure(val_b);

        let (a, b) = task_combinators::join(task_a, task_b);

        let a_val = LeanNat::to_usize(&a.cast()).unwrap();
        let b_val = LeanNat::to_usize(&b.cast()).unwrap();
        assert_eq!(a_val, 10);
        assert_eq!(b_val, 20);
    });
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_select_returns_first_completed() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Pure task is immediately finished; slow task takes 200ms
        let fast = LeanTask::pure(LeanNat::from_usize(lean, 42).unwrap());
        let slow_closure = leo3::closure::LeanClosure::from_fn1(lean, slow_nat).unwrap();
        let slow: LeanTask<'_, LeanAny> = LeanTask::spawn(slow_closure);

        let result = task_combinators::select(fast, slow);
        match result {
            Either::Left(val) => {
                let n = LeanNat::to_usize(&val.cast()).unwrap();
                assert_eq!(n, 42);
            }
            Either::Right(_) => panic!("Expected Left (fast task) to win"),
        }
    });
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_race_with_multiple_tasks() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // One pure (instant) task among slow ones
        let pure_task: LeanTask<'_, LeanAny> =
            LeanTask::pure(LeanNat::from_usize(lean, 55).unwrap()).cast();

        let slow1: LeanTask<'_, LeanAny> = {
            let c = leo3::closure::LeanClosure::from_fn1(lean, slow_nat).unwrap();
            LeanTask::<LeanAny>::spawn(c)
        };
        let slow2: LeanTask<'_, LeanAny> = {
            let c = leo3::closure::LeanClosure::from_fn1(lean, slow_nat).unwrap();
            LeanTask::<LeanAny>::spawn(c)
        };

        let result = task_combinators::race(vec![slow1, pure_task, slow2]);
        let n = LeanNat::to_usize(&result.cast()).unwrap();
        assert_eq!(n, 55);
    });
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_timeout_succeeds_when_fast() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let task = LeanTask::pure(LeanNat::from_usize(lean, 77).unwrap());
        let result = task_combinators::timeout(task, Duration::from_secs(5));
        assert!(result.is_ok());
        let n = LeanNat::to_usize(&result.unwrap().cast()).unwrap();
        assert_eq!(n, 77);
    });
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_timeout_fails_when_slow() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let c = leo3::closure::LeanClosure::from_fn1(lean, slow_nat).unwrap();
        let task: LeanTask<'_, LeanAny> = LeanTask::spawn(c);
        // 10ms timeout, task takes 200ms
        let result = task_combinators::timeout(task, Duration::from_millis(10));
        assert!(result.is_err());
        match result {
            Err(err) => assert_eq!(err.duration, Duration::from_millis(10)),
            Ok(_) => panic!("Expected timeout error"),
        }
    });
}

// ============================================================================
// Future integration tests (using futures::block_on)
// ============================================================================

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_future_with_block_on() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let task = LeanTask::pure(LeanNat::from_usize(lean, 33).unwrap());
        let future = task.into_future();
        let result = futures::executor::block_on(future);
        let n = LeanNat::to_usize(&result.cast()).unwrap();
        assert_eq!(n, 33);
    });
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_join_future_with_block_on() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let a = LeanTask::pure(LeanNat::from_usize(lean, 11).unwrap());
        let b = LeanTask::pure(LeanNat::from_usize(lean, 22).unwrap());

        let (ra, rb) = futures::executor::block_on(task_combinators::join_future(a, b));
        assert_eq!(LeanNat::to_usize(&ra.cast()).unwrap(), 11);
        assert_eq!(LeanNat::to_usize(&rb.cast()).unwrap(), 22);
    });
}
