//! # Leo3: Rust bindings for the Lean4 theorem prover
//!
//! Leo3 provides safe, ergonomic Rust bindings to Lean4, similar to how PyO3
//! provides Python bindings for Rust.
//!
//! ## Architecture
//!
//! Leo3 is organized into several layers:
//!
//! - **`leo3-ffi`**: Raw FFI bindings to Lean4's C API
//! - **`leo3-build-config`**: Build-time configuration and Lean4 detection
//! - **`leo3-macros`**: Procedural macros (`#[leanfn]`, etc.)
//! - **`leo3`** (this crate): Safe, high-level abstractions
//!
//! ## Core Concepts
//!
//! ### The `Lean<'l>` Token
//!
//! All interactions with Lean require a `Lean<'l>` token, which proves at
//! compile-time that the Lean runtime is initialized. This prevents accessing
//! Lean objects without proper initialization.
//!
//! ### Smart Pointers
//!
//! Leo3 provides several smart pointer types:
//!
//! - **`LeanBound<'l, T>`**: A Lean object bound to a `Lean<'l>` lifetime
//! - **`LeanRef<T>`**: An owned reference to a Lean object (can cross initialization boundaries)
//! - **`LeanBorrowed<'a, 'l, T>`**: A borrowed reference (zero-cost)
//! - **`LeanUnbound<T>`**: A thread-safe reference with automatic MT marking (`Send + Sync`)
//!
//! ### Reference Counting
//!
//! Lean4 uses reference counting for memory management. Leo3's smart pointers
//! automatically handle reference counting to prevent memory leaks and use-after-free.
//!
//! ### Thread Safety
//!
//! Lean4 uses a dual-mode reference counting system:
//! - **ST (Single-Threaded)**: Non-atomic, faster reference counting
//! - **MT (Multi-Threaded)**: Atomic reference counting for thread safety
//!
//! Use `LeanUnbound<T>` or `unbind_mt()` for objects that need to cross thread boundaries.
//!
//! ## Feature Flags
//!
//! - **`macros`** (default): Enable procedural macros (`#[leanfn]`, etc.)
//!
//! ## Example
//!
//! ```rust,ignore
//! use leo3::prelude::*;
//!
//! #[leanfn]
//! fn add(a: u64, b: u64) -> u64 {
//!     a + b
//! }
//!
//! fn main() -> LeanResult<()> {
//!     leo3::prepare_freethreaded_lean();
//!
//!     leo3::with_lean(|lean| {
//!         // Use Lean objects here
//!         let result = add(2, 3);
//!         println!("Result: {}", result);
//!         Ok(())
//!     })
//! }
//! ```

#![warn(missing_docs)]

pub use leo3_ffi as ffi;

pub mod closure;
pub mod conversion;
pub mod err;
pub mod external;
pub mod instance;
pub mod io;
pub mod marker;
pub mod meta;
pub mod module;
pub mod promise;
pub mod sync;
pub mod task;
pub mod thunk;
pub mod types;
pub mod unbound;

// Re-export key types
pub use err::{LeanError, LeanResult};
pub use instance::{LeanBorrowed, LeanBound, LeanRef};
pub use marker::Lean;
pub use unbound::LeanUnbound;

/// Prelude module for convenient imports
pub mod prelude {
    pub use crate::{Lean, LeanBorrowed, LeanBound, LeanError, LeanRef, LeanResult, LeanUnbound};

    // Re-export conversion traits and macros
    pub use crate::conversion::{FromLean, IntoLean};

    // Re-export smart conversion macros for automatic optimization
    pub use crate::{from_lean, to_lean};

    // Re-export commonly used types
    pub use crate::types::{
        LeanArray, LeanBool, LeanByteArray, LeanChar, LeanFloat, LeanFloat32, LeanHashMap,
        LeanHashSet, LeanISize, LeanInt, LeanInt16, LeanInt32, LeanInt64, LeanInt8, LeanList,
        LeanNat, LeanOption, LeanProd, LeanRBMap, LeanString, LeanUInt16, LeanUInt32, LeanUInt64,
        LeanUInt8, LeanUSize,
    };

    #[cfg(feature = "macros")]
    pub use leo3_macros::{leanclass, leanfn, leanmodule, FromLean, IntoLean};
}

/// Initialize the Lean runtime for standalone use.
///
/// This must be called before any Lean operations. It initializes the
/// Lean runtime and returns a `Lean<'l>` token that proves initialization.
///
/// This function is thread-safe and can be called multiple times - the
/// initialization will only happen once.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
///
/// fn main() -> LeanResult<()> {
///     leo3::prepare_freethreaded_lean();
///
///     leo3::with_lean(|lean| {
///         // Use Lean here
///         Ok(())
///     })
/// }
/// ```
pub fn prepare_freethreaded_lean() {
    // Spawn the long-lived worker thread and wait for it to complete all
    // Lean runtime initialization (lean_initialize_runtime_module,
    // lean_initialize_thread, and all ensure_*_initialized calls).
    //
    // This ensures that:
    // 1. All Lean module initialization happens on the worker thread
    // 2. The Once guards in ensure_*_initialized are triggered on the
    //    worker thread before any short-lived thread can trigger them
    // 3. lean_initialize_thread() is only called on the worker thread,
    //    which never exits, avoiding mimalloc's _mi_thread_done crash
    meta::environment::ensure_worker_initialized();
}

/// Execute a closure with access to the Lean runtime.
///
/// This provides a `Lean<'l>` token to the closure, which can be used to
/// create and manipulate Lean objects.
///
/// # Example
///
/// ```rust,ignore
/// leo3::with_lean(|lean| {
///     let s = LeanString::mk(lean, "Hello, Lean!");
///     println!("{}", s.cstr()?);
///     Ok(())
/// })
/// ```
pub fn with_lean<F, R>(f: F) -> R
where
    F: for<'l> FnOnce(Lean<'l>) -> R,
{
    let lean = unsafe { Lean::assume_initialized() };
    f(lean)
}

/// Execute a test with proper Lean thread lifecycle management.
///
/// This is specifically for testing - it ensures Lean is properly initialized
/// before running the test.
///
/// # Example
///
/// ```rust,ignore
/// #[test]
/// fn my_test() {
///     leo3::test_with_lean(|lean| {
///         let s = LeanString::mk(lean, "Hello!");
///         assert!(!s.cstr().unwrap().is_empty());
///         Ok(())
///     }).unwrap();
/// }
/// ```
pub fn test_with_lean<F, R>(f: F) -> R
where
    F: for<'l> FnOnce(Lean<'l>) -> R,
{
    // Initialize if needed (idempotent per thread)
    prepare_freethreaded_lean();

    // Run the test
    with_lean(f)
}

/// Metadata about a Lean function (used by macros)
#[doc(hidden)]
pub struct LeanFunctionMetadata {
    /// Name of the function in Lean
    pub name: &'static str,
}
