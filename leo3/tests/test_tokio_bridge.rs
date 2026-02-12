//! Tests for the optional Tokio integration bridge.
//!
//! These tests require both `tokio` and `runtime-tests` features.

#![cfg(all(feature = "tokio", feature = "runtime-tests"))]

use leo3::instance::LeanAny;
use leo3::task::LeanTask;

unsafe extern "C" fn make_nat_10(
    _world: *mut leo3::ffi::lean_object,
) -> *mut leo3::ffi::lean_object {
    leo3::ffi::inline::lean_box(10)
}

unsafe extern "C" fn slow_nat_50(
    _world: *mut leo3::ffi::lean_object,
) -> *mut leo3::ffi::lean_object {
    std::thread::sleep(std::time::Duration::from_millis(50));
    leo3::ffi::inline::lean_box(50)
}

#[tokio::test]
async fn test_spawn_on_tokio() {
    leo3::prepare_freethreaded_lean();

    let result = leo3::with_lean(|lean| {
        let closure = leo3::closure::LeanClosure::from_fn1(lean, make_nat_10).unwrap();
        LeanTask::spawn_on_tokio(closure)
    });

    let unbound = result.await.unwrap();
    let n = unsafe { leo3::ffi::inline::lean_unbox(unbound.as_ptr()) };
    assert_eq!(n, 10);
}

#[tokio::test]
async fn test_task_handle_into_tokio_future() {
    leo3::prepare_freethreaded_lean();

    let handle = leo3::with_lean(|lean| {
        let closure = leo3::closure::LeanClosure::from_fn1(lean, slow_nat_50).unwrap();
        LeanTask::<LeanAny>::spawn(closure).into_handle()
    });

    let unbound = handle.into_tokio_future().await;
    let n = unsafe { leo3::ffi::inline::lean_unbox(unbound.as_ptr()) };
    assert_eq!(n, 50);
}
