//! Demonstrates Lean task/promise async combinators.
//!
//! Shows how to:
//! - Create and resolve promises
//! - Use `TaskHandle` for cross-thread task access
//! - Apply task combinators (`join`, `timeout`, `select`)
//!
//! Requires Lean4 runtime linked (run via `cargo run --example async_task_promise`).

use leo3::closure::LeanClosure;
use leo3::instance::LeanAny;
use leo3::prelude::*;
use leo3::promise::LeanPromise;
use leo3::task::{self, LeanTask, TaskHandle};
use leo3::types::LeanOption;
use std::time::Duration;

/// A slow FFI closure that sleeps then returns a boxed scalar.
unsafe extern "C" fn delayed_value(
    _world: *mut leo3::ffi::lean_object,
) -> *mut leo3::ffi::lean_object {
    std::thread::sleep(Duration::from_millis(100));
    leo3::ffi::inline::lean_box(99)
}

fn main() -> LeanResult<()> {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        task::init_task_manager();

        // ── 1. Promise: create, resolve, read via TaskHandle ────────
        println!("1. Promise create and resolve");

        let promise = LeanPromise::<LeanAny>::new(lean)?;
        let task = promise.task();
        // TaskHandle is Send + Sync — safe for cross-thread result retrieval
        let handle: TaskHandle<LeanAny> = task.into_handle();

        // Resolve the promise with a Nat value
        let value = LeanNat::from_usize(lean, 42)?;
        promise.resolve(value.cast())?;

        // Retrieve the result through the handle
        let bound = handle.bind(lean);
        let opt: LeanBound<'_, LeanOption> = bound.get_owned().cast();
        let inner = LeanOption::get(&opt).expect("expected Some from promise");
        let n: LeanBound<'_, LeanNat> = inner.cast();
        println!("   resolved value: {}", LeanNat::to_usize(&n)?);
        assert_eq!(LeanNat::to_usize(&n)?, 42);

        // ── 2. Join combinator: await two pure tasks ─────────────────
        println!("2. Join two pure tasks");

        let a = LeanTask::pure(LeanNat::from_usize(lean, 10)?);
        let b = LeanTask::pure(LeanNat::from_usize(lean, 20)?);
        let (ra, rb) = join(a, b);

        let va = LeanNat::to_usize(&ra.cast())?;
        let vb = LeanNat::to_usize(&rb.cast())?;
        println!("   join results: ({}, {})", va, vb);
        assert_eq!((va, vb), (10, 20));

        // ── 3. Timeout combinator: fast task succeeds ────────────────
        println!("3. Timeout (task completes in time)");

        let fast = LeanTask::pure(LeanNat::from_usize(lean, 77)?);
        let result = timeout(fast, Duration::from_secs(1));
        assert!(result.is_ok());
        let tv = LeanNat::to_usize(&result.unwrap().cast())?;
        println!("   got {} before deadline", tv);

        // ── 4. Timeout combinator: slow task times out ───────────────
        println!("4. Timeout (task exceeds deadline)");

        let closure = LeanClosure::from_fn1(lean, delayed_value)?;
        let slow: LeanTask<'_, LeanAny> = LeanTask::spawn(closure);
        let result = timeout(slow, Duration::from_millis(10));
        match &result {
            Ok(_) => println!("   unexpectedly completed"),
            Err(e) => println!("   timed out: {}", e),
        }
        assert!(result.is_err());

        // ── 5. Select combinator: first task wins ────────────────────
        println!("5. Select (fast vs slow)");

        let fast = LeanTask::pure(LeanNat::from_usize(lean, 55)?);
        let closure2 = LeanClosure::from_fn1(lean, delayed_value)?;
        let slow2: LeanTask<'_, LeanAny> = LeanTask::spawn(closure2);

        match select(fast.cast(), slow2) {
            Either::Left(v) => {
                let n = LeanNat::to_usize(&v.cast())?;
                println!("   left (fast) won: {}", n);
                assert_eq!(n, 55);
            }
            Either::Right(_) => println!("   right (slow) won unexpectedly"),
        }

        task::finalize_task_manager();
        println!("\nAll demos passed.");
        Ok(())
    })
}
