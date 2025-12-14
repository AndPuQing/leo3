//! Thread safety tests for Leo3
//!
//! These tests verify that the thread safety primitives work correctly:
//! - `LeanUnbound<T>` can be safely shared across threads
//! - `TaskHandle<T>` supports cross-thread task management
//! - `LeanOnceCell<T>` provides thread-safe lazy initialization
//! - `LeanProtected<T>` provides safe concurrent access
//!
//! ## Running These Tests
//!
//! Without Lean4 (compile-only):
//! ```bash
//! LEO3_NO_LEAN=1 cargo test --test test_thread_safety
//! ```
//!
//! With Lean4 (full runtime tests):
//! ```bash
//! cargo test --test test_thread_safety --features runtime-tests
//! ```

use leo3::prelude::*;
use leo3::sync::{ensure_lean_thread, LeanMutexExt, LeanOnceCell, LeanProtected, LeanRwLockExt};
use leo3::unbound::LeanUnbound;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Barrier, Mutex, RwLock};
use std::thread;

// ============================================================================
// LeanUnbound Thread Safety Tests
// ============================================================================

#[test]
fn test_lean_unbound_is_send() {
    // This test verifies at compile-time that LeanUnbound is Send
    fn assert_send<T: Send>() {}
    assert_send::<LeanUnbound<LeanNat>>();
    assert_send::<LeanUnbound<LeanString>>();
    assert_send::<LeanUnbound<LeanArray>>();
}

#[test]
fn test_lean_unbound_is_sync() {
    // This test verifies at compile-time that LeanUnbound is Sync
    fn assert_sync<T: Sync>() {}
    assert_sync::<LeanUnbound<LeanNat>>();
    assert_sync::<LeanUnbound<LeanString>>();
    assert_sync::<LeanUnbound<LeanArray>>();
}

#[test]
fn test_lean_unbound_send_to_thread() {
    leo3::prepare_freethreaded_lean();

    // Create a Lean object and unbind it for MT use
    let unbound = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42).unwrap();
        n.unbind_mt()
    });

    // Send to another thread
    let handle = thread::spawn(move || {
        leo3::prepare_freethreaded_lean();
        leo3::with_lean(|lean| {
            let bound = unbound.bind(lean);
            LeanNat::to_usize(&bound).unwrap()
        })
    });

    let result = handle.join().unwrap();
    assert_eq!(result, 42);
}

#[test]
fn test_lean_unbound_shared_across_threads() {
    leo3::prepare_freethreaded_lean();

    // Create a shared LeanUnbound wrapped in Arc
    let unbound = Arc::new(leo3::with_lean(|lean| {
        let s = LeanString::mk(lean, "shared").unwrap();
        s.unbind_mt()
    }));

    // Spawn multiple threads that all read the same object
    let mut handles = vec![];
    for _ in 0..4 {
        let unbound_clone = Arc::clone(&unbound);
        handles.push(thread::spawn(move || {
            leo3::prepare_freethreaded_lean();
            leo3::with_lean(|lean| {
                let bound = unbound_clone.bind(lean);
                LeanString::cstr(&bound).unwrap().to_string()
            })
        }));
    }

    // All threads should read the same value
    for handle in handles {
        let result = handle.join().unwrap();
        assert_eq!(result, "shared");
    }
}

#[test]
fn test_lean_unbound_clone_ref_across_threads() {
    leo3::prepare_freethreaded_lean();

    let unbound = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 100).unwrap();
        n.unbind_mt()
    });

    // Clone the reference and send to different threads
    let clone1 = unbound.clone_ref();
    let clone2 = unbound.clone_ref();

    let h1 = thread::spawn(move || {
        leo3::prepare_freethreaded_lean();
        leo3::with_lean(|lean| {
            let bound = clone1.bind(lean);
            LeanNat::to_usize(&bound).unwrap()
        })
    });

    let h2 = thread::spawn(move || {
        leo3::prepare_freethreaded_lean();
        leo3::with_lean(|lean| {
            let bound = clone2.bind(lean);
            LeanNat::to_usize(&bound).unwrap()
        })
    });

    // Original also still works
    let original_result = leo3::with_lean(|lean| {
        let bound = unbound.bind(lean);
        LeanNat::to_usize(&bound).unwrap()
    });

    assert_eq!(h1.join().unwrap(), 100);
    assert_eq!(h2.join().unwrap(), 100);
    assert_eq!(original_result, 100);
}

// ============================================================================
// LeanOnceCell Tests
// ============================================================================

#[test]
fn test_lean_once_cell_basic() {
    let cell: LeanOnceCell<i32> = LeanOnceCell::new();

    assert!(cell.get().is_none());

    let value = cell.get_or_init(|| 42);
    assert_eq!(*value, 42);

    // Second call returns the same value
    let value2 = cell.get_or_init(|| 100);
    assert_eq!(*value2, 42);
}

#[test]
fn test_lean_once_cell_concurrent_init() {
    static CELL: LeanOnceCell<u64> = LeanOnceCell::new();
    static INIT_COUNT: AtomicUsize = AtomicUsize::new(0);

    let barrier = Arc::new(Barrier::new(4));
    let mut handles = vec![];

    for _ in 0..4 {
        let barrier = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            // Wait for all threads to be ready
            barrier.wait();

            // All threads try to initialize simultaneously
            let value = CELL.get_or_init(|| {
                INIT_COUNT.fetch_add(1, Ordering::SeqCst);
                42
            });

            *value
        }));
    }

    // All threads should get the same value
    for handle in handles {
        let result = handle.join().unwrap();
        assert_eq!(result, 42);
    }

    // The initializer should have run exactly once
    assert_eq!(INIT_COUNT.load(Ordering::SeqCst), 1);
}

#[test]
fn test_lean_once_cell_with_lean_object() {
    leo3::prepare_freethreaded_lean();

    static CELL: LeanOnceCell<LeanUnbound<LeanNat>> = LeanOnceCell::new();

    let barrier = Arc::new(Barrier::new(4));
    let mut handles = vec![];

    for _ in 0..4 {
        let barrier = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            leo3::prepare_freethreaded_lean();

            barrier.wait();

            let unbound = CELL.get_or_init(|| {
                leo3::with_lean(|lean| LeanNat::from_usize(lean, 999).unwrap().unbind_mt())
            });

            leo3::with_lean(|lean| {
                let bound = unbound.bind(lean);
                LeanNat::to_usize(&bound).unwrap()
            })
        }));
    }

    for handle in handles {
        let result = handle.join().unwrap();
        assert_eq!(result, 999);
    }
}

// ============================================================================
// LeanProtected Tests
// ============================================================================

#[test]
fn test_lean_protected_basic() {
    let protected = LeanProtected::new(42);

    {
        let guard = protected.lock().unwrap();
        assert_eq!(*guard, 42);
    }
}

#[test]
fn test_lean_protected_concurrent_access() {
    leo3::prepare_freethreaded_lean();

    let protected = Arc::new(LeanProtected::new(leo3::with_lean(|lean| {
        LeanNat::from_usize(lean, 0).unwrap().unbind_mt()
    })));

    let mut handles = vec![];

    for i in 0..4 {
        let protected = Arc::clone(&protected);
        handles.push(thread::spawn(move || {
            leo3::prepare_freethreaded_lean();

            for _ in 0..10 {
                let mut guard = protected.lock().unwrap();

                // Read current value
                let current = leo3::with_lean(|lean| {
                    let bound = guard.bind(lean);
                    LeanNat::to_usize(&bound).unwrap()
                });

                // Create new value (increment)
                *guard = leo3::with_lean(|lean| {
                    LeanNat::from_usize(lean, current + 1).unwrap().unbind_mt()
                });
            }
            i
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // Final value should be 40 (4 threads * 10 increments)
    let final_value = {
        let guard = protected.lock().unwrap();
        leo3::with_lean(|lean| {
            let bound = guard.bind(lean);
            LeanNat::to_usize(&bound).unwrap()
        })
    };

    assert_eq!(final_value, 40);
}

// ============================================================================
// Extension Trait Tests
// ============================================================================

#[test]
fn test_mutex_ext_lock_lean() {
    let mutex = Mutex::new(42);

    thread::spawn(move || {
        let guard = mutex.lock_lean().unwrap();
        assert_eq!(*guard, 42);
    })
    .join()
    .unwrap();
}

#[test]
fn test_rwlock_ext_read_write_lean() {
    let rwlock = Arc::new(RwLock::new(42));

    let mut handles = vec![];

    // Multiple readers
    for _ in 0..4 {
        let rwlock = Arc::clone(&rwlock);
        handles.push(thread::spawn(move || {
            let guard = rwlock.read_lean().unwrap();
            assert_eq!(*guard, 42);
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // Single writer
    {
        let mut guard = rwlock.write_lean().unwrap();
        *guard = 100;
    }

    // Read after write
    {
        let guard = rwlock.read_lean().unwrap();
        assert_eq!(*guard, 100);
    }
}

// ============================================================================
// Thread Initialization Tests
// ============================================================================

#[test]
fn test_ensure_lean_thread() {
    // This should not panic even when called multiple times
    ensure_lean_thread();
    ensure_lean_thread();
    ensure_lean_thread();
}

#[test]
fn test_ensure_lean_thread_from_spawned_thread() {
    let handle = thread::spawn(|| {
        ensure_lean_thread();
        // Should be able to use Lean after initialization
        leo3::with_lean(|lean| {
            let n = LeanNat::from_usize(lean, 42).unwrap();
            LeanNat::to_usize(&n).unwrap()
        })
    });

    let result = handle.join().unwrap();
    assert_eq!(result, 42);
}

// ============================================================================
// Stress Tests
// ============================================================================

#[test]
fn test_heavy_concurrent_lean_unbound_usage() {
    leo3::prepare_freethreaded_lean();

    const NUM_THREADS: usize = 8;
    const ITERATIONS: usize = 100;

    let barrier = Arc::new(Barrier::new(NUM_THREADS));
    let mut handles = vec![];

    for thread_id in 0..NUM_THREADS {
        let barrier = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            leo3::prepare_freethreaded_lean();
            barrier.wait();

            for i in 0..ITERATIONS {
                let value = thread_id * ITERATIONS + i;

                // Create, unbind, and rebind
                let unbound =
                    leo3::with_lean(|lean| LeanNat::from_usize(lean, value).unwrap().unbind_mt());

                let result = leo3::with_lean(|lean| {
                    let bound = unbound.bind(lean);
                    LeanNat::to_usize(&bound).unwrap()
                });

                assert_eq!(result, value);
            }

            thread_id
        }));
    }

    // All threads should complete successfully
    for handle in handles {
        handle.join().unwrap();
    }
}

#[test]
fn test_arc_lean_unbound_stress() {
    leo3::prepare_freethreaded_lean();

    const NUM_THREADS: usize = 8;
    const READS_PER_THREAD: usize = 50;

    // Create a bunch of shared objects
    let objects: Vec<Arc<LeanUnbound<LeanNat>>> = (0..10)
        .map(|i| {
            Arc::new(leo3::with_lean(|lean| {
                LeanNat::from_usize(lean, i).unwrap().unbind_mt()
            }))
        })
        .collect();

    let barrier = Arc::new(Barrier::new(NUM_THREADS));
    let objects = Arc::new(objects);
    let mut handles = vec![];

    for _ in 0..NUM_THREADS {
        let barrier = Arc::clone(&barrier);
        let objects = Arc::clone(&objects);

        handles.push(thread::spawn(move || {
            leo3::prepare_freethreaded_lean();
            barrier.wait();

            let mut sum = 0usize;
            for _ in 0..READS_PER_THREAD {
                for (expected, obj) in objects.iter().enumerate() {
                    let value = leo3::with_lean(|lean| {
                        let bound = obj.bind(lean);
                        LeanNat::to_usize(&bound).unwrap()
                    });
                    assert_eq!(value, expected);
                    sum += value;
                }
            }
            sum
        }));
    }

    // Expected sum per thread: (0+1+2+...+9) * READS_PER_THREAD = 45 * 50 = 2250
    let expected_sum_per_thread = 45 * READS_PER_THREAD;

    for handle in handles {
        let sum = handle.join().unwrap();
        assert_eq!(sum, expected_sum_per_thread);
    }
}

// ============================================================================
// LeanUnbound Conversion Tests
// ============================================================================

#[test]
fn test_lean_bound_unbind_mt() {
    leo3::prepare_freethreaded_lean();

    let unbound = leo3::with_lean(|lean| {
        let bound = LeanNat::from_usize(lean, 42).unwrap();
        bound.unbind_mt() // Convert to thread-safe unbound
    });

    // Should be usable from main thread
    let result = leo3::with_lean(|lean| {
        let bound = unbound.bind(lean);
        LeanNat::to_usize(&bound).unwrap()
    });

    assert_eq!(result, 42);
}

#[test]
fn test_lean_ref_into_unbound() {
    leo3::prepare_freethreaded_lean();

    let unbound = leo3::with_lean(|lean| {
        let bound = LeanNat::from_usize(lean, 123).unwrap();
        let lean_ref = bound.unbind();
        lean_ref.into_unbound() // Convert LeanRef to LeanUnbound
    });

    let result = leo3::with_lean(|lean| {
        let bound = unbound.bind(lean);
        LeanNat::to_usize(&bound).unwrap()
    });

    assert_eq!(result, 123);
}

#[test]
fn test_lean_unbound_into_bound_consumes() {
    leo3::prepare_freethreaded_lean();

    let unbound = leo3::with_lean(|lean| LeanNat::from_usize(lean, 456).unwrap().unbind_mt());

    // into_bound consumes the unbound
    let result = leo3::with_lean(|lean| {
        let bound = unbound.into_bound(lean);
        LeanNat::to_usize(&bound).unwrap()
    });

    assert_eq!(result, 456);
    // unbound is now consumed and cannot be used
}

#[test]
fn test_lean_unbound_cast() {
    leo3::prepare_freethreaded_lean();

    let unbound_nat = leo3::with_lean(|lean| LeanNat::from_usize(lean, 789).unwrap().unbind_mt());

    // Cast to LeanAny
    let unbound_any: LeanUnbound<leo3::instance::LeanAny> = unbound_nat.into_any();

    // Still usable (as LeanAny)
    let _ptr = unbound_any.as_ptr();
}

// ============================================================================
// LeanOnceCell Edge Cases
// ============================================================================

#[test]
fn test_lean_once_cell_set() {
    let cell: LeanOnceCell<String> = LeanOnceCell::new();

    assert!(cell.set("hello".to_string()).is_ok());
    assert!(cell.set("world".to_string()).is_err());
    assert_eq!(cell.get().unwrap(), "hello");
}

#[test]
fn test_lean_once_cell_take() {
    let mut cell: LeanOnceCell<i32> = LeanOnceCell::new();
    cell.set(42).unwrap();

    let value = cell.take();
    assert_eq!(value, Some(42));

    // Cell is now empty
    assert!(cell.get().is_none());
}
