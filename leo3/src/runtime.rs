//! Internal Lean runtime initialization and worker-thread coordination.
//!
//! This module is intentionally kept private. Public API exposure is controlled
//! from `lib.rs` via feature-gated modules, while the shared runtime bootstrap
//! remains available to the core crate implementation regardless of feature set.
//!
//! The runtime model has three layers:
//!
//! - a single long-lived worker thread owns one-time Lean runtime/module
//!   initialization and serialized environment/meta operations
//! - Lean's own task manager executes `LeanTask` bodies asynchronously once the
//!   runtime worker has initialized it
//! - caller-created threads may interact with MT-marked Lean objects after
//!   calling `crate::sync::ensure_lean_thread()`
//!
//! Waiting follows the same split: worker calls use blocking rendezvous
//! channels, while task-oriented polling paths share the task backoff helpers
//! in `crate::task`.

use leo3_ffi as ffi;
use std::sync::mpsc;
use std::sync::{Mutex, Once};

static PRELUDE_INIT: Once = Once::new();
static EXPR_INIT: Once = Once::new();
static ENV_INIT: Once = Once::new();

/// Ensure `Init.Prelude` is initialized.
#[inline]
pub(crate) fn ensure_prelude_initialized() {
    PRELUDE_INIT.call_once(|| unsafe {
        ffi::initialize_Init_Prelude(1, std::ptr::null_mut());
    });
}

/// Ensure `Lean.Expr` is initialized.
#[inline]
pub(crate) fn ensure_expr_initialized() {
    ensure_prelude_initialized();

    EXPR_INIT.call_once(|| unsafe {
        ffi::initialize_Lean_Expr(1, std::ptr::null_mut());
    });
}

/// Ensure `Lean.Environment` and its transitive dependencies are initialized.
#[inline]
pub(crate) fn ensure_environment_initialized() {
    ensure_expr_initialized();

    ENV_INIT.call_once(|| unsafe {
        ffi::initialize_Lean_Environment(1, std::ptr::null_mut());
        ffi::initialize_Lean_Meta(1, std::ptr::null_mut());
        ffi::initialize_util_module();
        ffi::initialize_kernel_module();
        ffi::init_default_print_fn();
        ffi::initialize_library_core_module();
        ffi::initialize_library_module();
        ffi::lean_io_mark_end_initialization();
    });
}

/// Ensure `Lean.Meta` is initialized.
#[cfg(feature = "meta")]
#[inline]
pub(crate) fn ensure_meta_initialized() {
    ensure_environment_initialized();
}

/// Wrapper to force `Send` on types that cross the worker-thread channel.
///
/// SAFETY: The calling thread blocks until the worker finishes, so the
/// wrapped value's captures are guaranteed to outlive the worker's use of them.
#[cfg(any(feature = "meta", feature = "task"))]
struct SendBox<T>(T);
#[cfg(any(feature = "meta", feature = "task"))]
unsafe impl<T> Send for SendBox<T> {}

/// Global worker thread state.
#[allow(clippy::type_complexity)]
static WORKER: Mutex<Option<mpsc::SyncSender<Box<dyn FnOnce() + Send>>>> = Mutex::new(None);

/// Ensure the long-lived Lean worker thread is spawned and fully initialized.
///
/// This worker is the canonical serialized path for runtime bootstrap and for
/// operations that must not hop across short-lived threads.
pub(crate) fn ensure_worker_initialized() {
    static WORKER_INIT: Once = Once::new();

    WORKER_INIT.call_once(|| {
        let (tx, rx) = mpsc::sync_channel::<Box<dyn FnOnce() + Send>>(0);
        let (init_tx, init_rx) = mpsc::sync_channel::<()>(0);

        std::thread::Builder::new()
            .name("leo3-runtime-worker".into())
            .spawn(move || {
                unsafe {
                    ffi::lean_initialize_runtime_module();
                    ffi::lean_initialize_thread();
                    ffi::closure::lean_init_task_manager();
                }
                ensure_environment_initialized();

                let _ = init_tx.send(());

                for task in rx {
                    task();
                }

                loop {
                    std::thread::park();
                }
            })
            .expect("failed to spawn leo3-runtime-worker thread");

        init_rx.recv().expect("worker thread initialization failed");

        let mut guard = WORKER.lock().unwrap();
        *guard = Some(tx);
    });
}

/// Dispatch a closure to the long-lived worker thread and block until it completes.
///
/// # Safety
///
/// The closure `f` and its return value cross a thread boundary via channels.
/// Callers must ensure that any captured pointers remain valid and that
/// reference counts are properly managed before and after the call.
#[cfg(any(feature = "meta", feature = "task"))]
pub(crate) fn with_worker<F, R>(f: F) -> R
where
    F: FnOnce() -> R,
{
    ensure_worker_initialized();

    let sender = {
        let guard = WORKER.lock().unwrap();
        guard.as_ref().unwrap().clone()
    };

    let (done_tx, done_rx) = mpsc::sync_channel::<SendBox<R>>(0);
    let task = move || {
        let result = f();
        let _ = done_tx.send(SendBox(result));
    };

    let task: Box<dyn FnOnce() + Send> = unsafe {
        std::mem::transmute::<Box<dyn FnOnce() + '_>, Box<dyn FnOnce() + Send>>(Box::new(task))
    };

    sender.send(task).expect("runtime worker thread died");
    done_rx.recv().expect("runtime worker thread died").0
}
