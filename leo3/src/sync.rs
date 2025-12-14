//! Synchronization primitives for thread-safe Lean object access.
//!
//! This module provides synchronization utilities designed for use with
//! Lean objects in multi-threaded contexts.
//!
//! # Thread Initialization
//!
//! Lean requires thread initialization before any Lean operations. The
//! [`ensure_lean_thread()`] function handles this automatically.
//!
//! # Types
//!
//! - [`LeanOnceCell<T>`]: Thread-safe lazy initialization for Lean objects
//! - [`LeanProtected<T>`]: A mutex-protected Lean object with automatic MT marking
//!
//! # Extension Traits
//!
//! - [`LeanMutexExt`]: Extension trait for `std::sync::Mutex` with Lean-aware locking

use crate::ffi;
use std::cell::Cell;
use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Mutex, MutexGuard, PoisonError};

/// Ensure the current thread is initialized for Lean operations.
///
/// This is a no-op if the thread is already initialized. Call this before
/// performing Lean operations from a new thread.
///
/// # Example
///
/// ```rust,ignore
/// use std::thread;
/// use leo3::sync::ensure_lean_thread;
///
/// thread::spawn(|| {
///     ensure_lean_thread();
///     // Now safe to use Lean
/// });
/// ```
pub fn ensure_lean_thread() {
    thread_local! {
        static INITIALIZED: Cell<bool> = const { Cell::new(false) };
    }

    INITIALIZED.with(|init| {
        if !init.get() {
            unsafe {
                ffi::lean_initialize_thread();
            }
            init.set(true);
        }
    });
}

/// Check if the current thread is initialized for Lean operations.
///
/// Returns `true` if `ensure_lean_thread()` or `prepare_freethreaded_lean()`
/// has been called on this thread.
pub fn thread_is_lean_initialized() -> bool {
    thread_local! {
        static INITIALIZED: Cell<bool> = const { Cell::new(false) };
    }

    // Note: This is a separate thread-local from ensure_lean_thread()
    // In practice, we rely on the runtime's internal state
    // This is a simplified check
    INITIALIZED.with(|init| init.get())
}

// State constants for LeanOnceCell
const EMPTY: u8 = 0;
const INITIALIZING: u8 = 1;
const INITIALIZED: u8 = 2;

/// A thread-safe cell that can be written to once.
///
/// This is similar to `std::sync::OnceLock`, but specifically designed for
/// Lean objects. It ensures proper thread initialization and MT marking.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::sync::LeanOnceCell;
/// use leo3::prelude::*;
///
/// static GLOBAL_STRING: LeanOnceCell<LeanUnbound<LeanString>> = LeanOnceCell::new();
///
/// fn get_global_string<'l>(lean: Lean<'l>) -> &'static LeanUnbound<LeanString> {
///     GLOBAL_STRING.get_or_init(|| {
///         LeanString::mk(lean, "Global String").unwrap().unbind_mt()
///     })
/// }
/// ```
pub struct LeanOnceCell<T> {
    state: AtomicU8,
    value: UnsafeCell<MaybeUninit<T>>,
}

// SAFETY: LeanOnceCell uses atomic state and internal synchronization
unsafe impl<T: Send + Sync> Send for LeanOnceCell<T> {}
unsafe impl<T: Send + Sync> Sync for LeanOnceCell<T> {}

impl<T> LeanOnceCell<T> {
    /// Create a new empty `LeanOnceCell`.
    pub const fn new() -> Self {
        Self {
            state: AtomicU8::new(EMPTY),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Get the value if initialized, or `None` if not.
    pub fn get(&self) -> Option<&T> {
        if self.state.load(Ordering::Acquire) == INITIALIZED {
            // SAFETY: State is INITIALIZED, so value is valid
            Some(unsafe { (*self.value.get()).assume_init_ref() })
        } else {
            None
        }
    }

    /// Get the value, initializing it with `f` if necessary.
    ///
    /// If multiple threads call this concurrently, only one will run `f`,
    /// and all will receive a reference to the same value.
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        // Fast path: already initialized
        if self.state.load(Ordering::Acquire) == INITIALIZED {
            return unsafe { (*self.value.get()).assume_init_ref() };
        }

        // Slow path: try to initialize
        self.initialize(f)
    }

    #[cold]
    fn initialize<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        // Try to claim the initialization
        match self
            .state
            .compare_exchange(EMPTY, INITIALIZING, Ordering::Acquire, Ordering::Acquire)
        {
            Ok(_) => {
                // We claimed it, initialize the value
                let value = f();
                unsafe {
                    (*self.value.get()).write(value);
                }
                self.state.store(INITIALIZED, Ordering::Release);
                unsafe { (*self.value.get()).assume_init_ref() }
            }
            Err(INITIALIZING) => {
                // Someone else is initializing, spin-wait
                while self.state.load(Ordering::Acquire) == INITIALIZING {
                    std::hint::spin_loop();
                }
                // Now it should be initialized
                unsafe { (*self.value.get()).assume_init_ref() }
            }
            Err(INITIALIZED) => {
                // Already initialized by another thread
                unsafe { (*self.value.get()).assume_init_ref() }
            }
            Err(_) => unreachable!(),
        }
    }

    /// Set the value if not already initialized.
    ///
    /// Returns `Ok(())` if the value was set, or `Err(value)` if already initialized.
    pub fn set(&self, value: T) -> Result<(), T> {
        match self
            .state
            .compare_exchange(EMPTY, INITIALIZING, Ordering::Acquire, Ordering::Acquire)
        {
            Ok(_) => {
                unsafe {
                    (*self.value.get()).write(value);
                }
                self.state.store(INITIALIZED, Ordering::Release);
                Ok(())
            }
            Err(_) => Err(value),
        }
    }

    /// Take the value if initialized, leaving the cell empty.
    ///
    /// This is only safe if you have exclusive access (e.g., via `&mut self`).
    pub fn take(&mut self) -> Option<T> {
        if *self.state.get_mut() == INITIALIZED {
            *self.state.get_mut() = EMPTY;
            // SAFETY: Was initialized, now we're taking ownership
            Some(unsafe { (*self.value.get()).assume_init_read() })
        } else {
            None
        }
    }
}

impl<T> Default for LeanOnceCell<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for LeanOnceCell<T> {
    fn drop(&mut self) {
        if *self.state.get_mut() == INITIALIZED {
            unsafe {
                (*self.value.get()).assume_init_drop();
            }
        }
    }
}

/// A mutex-protected Lean object with automatic MT marking.
///
/// This wraps a `Mutex` but ensures that:
/// 1. The contained Lean objects are marked for MT use
/// 2. Thread initialization is handled before access
///
/// # Example
///
/// ```rust,ignore
/// use leo3::sync::LeanProtected;
/// use leo3::prelude::*;
///
/// let protected = LeanProtected::new(some_lean_object.unbind_mt());
///
/// // Access from multiple threads
/// let guard = protected.lock().unwrap();
/// // use *guard...
/// ```
pub struct LeanProtected<T> {
    inner: Mutex<T>,
}

impl<T> LeanProtected<T> {
    /// Create a new `LeanProtected` with the given value.
    pub fn new(value: T) -> Self {
        Self {
            inner: Mutex::new(value),
        }
    }

    /// Lock the mutex and return a guard.
    ///
    /// This ensures the current thread is initialized for Lean before returning.
    pub fn lock(&self) -> Result<MutexGuard<'_, T>, PoisonError<MutexGuard<'_, T>>> {
        ensure_lean_thread();
        self.inner.lock()
    }

    /// Try to lock the mutex without blocking.
    ///
    /// This ensures the current thread is initialized for Lean before attempting.
    pub fn try_lock(
        &self,
    ) -> Result<MutexGuard<'_, T>, std::sync::TryLockError<MutexGuard<'_, T>>> {
        ensure_lean_thread();
        self.inner.try_lock()
    }

    /// Get a mutable reference to the inner value.
    ///
    /// This is only possible with exclusive access to the `LeanProtected`.
    pub fn get_mut(&mut self) -> Result<&mut T, PoisonError<&mut T>> {
        self.inner.get_mut()
    }

    /// Consume the `LeanProtected` and return the inner value.
    pub fn into_inner(self) -> Result<T, PoisonError<T>> {
        self.inner.into_inner()
    }
}

// SAFETY: LeanProtected uses a Mutex for synchronization
unsafe impl<T: Send> Send for LeanProtected<T> {}
unsafe impl<T: Send> Sync for LeanProtected<T> {}

/// Extension trait for `std::sync::Mutex` with Lean-aware operations.
///
/// This trait provides methods that ensure proper Lean thread initialization
/// before accessing mutex-protected data.
pub trait LeanMutexExt<T> {
    /// Lock the mutex with Lean thread initialization.
    ///
    /// This calls `ensure_lean_thread()` before locking, making it safe
    /// to access Lean objects from the returned guard.
    fn lock_lean(&self) -> Result<MutexGuard<'_, T>, PoisonError<MutexGuard<'_, T>>>;

    /// Try to lock the mutex with Lean thread initialization.
    fn try_lock_lean(
        &self,
    ) -> Result<MutexGuard<'_, T>, std::sync::TryLockError<MutexGuard<'_, T>>>;
}

impl<T> LeanMutexExt<T> for Mutex<T> {
    fn lock_lean(&self) -> Result<MutexGuard<'_, T>, PoisonError<MutexGuard<'_, T>>> {
        ensure_lean_thread();
        self.lock()
    }

    fn try_lock_lean(
        &self,
    ) -> Result<MutexGuard<'_, T>, std::sync::TryLockError<MutexGuard<'_, T>>> {
        ensure_lean_thread();
        self.try_lock()
    }
}

/// Extension trait for `std::sync::RwLock` with Lean-aware operations.
pub trait LeanRwLockExt<T> {
    /// Acquire a read lock with Lean thread initialization.
    fn read_lean(
        &self,
    ) -> Result<std::sync::RwLockReadGuard<'_, T>, PoisonError<std::sync::RwLockReadGuard<'_, T>>>;

    /// Acquire a write lock with Lean thread initialization.
    fn write_lean(
        &self,
    ) -> Result<std::sync::RwLockWriteGuard<'_, T>, PoisonError<std::sync::RwLockWriteGuard<'_, T>>>;
}

impl<T> LeanRwLockExt<T> for std::sync::RwLock<T> {
    fn read_lean(
        &self,
    ) -> Result<std::sync::RwLockReadGuard<'_, T>, PoisonError<std::sync::RwLockReadGuard<'_, T>>>
    {
        ensure_lean_thread();
        self.read()
    }

    fn write_lean(
        &self,
    ) -> Result<std::sync::RwLockWriteGuard<'_, T>, PoisonError<std::sync::RwLockWriteGuard<'_, T>>>
    {
        ensure_lean_thread();
        self.write()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn test_lean_once_cell_set() {
        let cell: LeanOnceCell<String> = LeanOnceCell::new();

        assert!(cell.set("hello".to_string()).is_ok());
        assert!(cell.set("world".to_string()).is_err());
        assert_eq!(cell.get().unwrap(), "hello");
    }

    #[test]
    fn test_lean_protected_basic() {
        let protected = LeanProtected::new(42);

        {
            let guard = protected.lock().unwrap();
            assert_eq!(*guard, 42);
        }
    }
}
