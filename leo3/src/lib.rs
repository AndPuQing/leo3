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
//!
//! ### Reference Counting
//!
//! Lean4 uses reference counting for memory management. Leo3's smart pointers
//! automatically handle reference counting to prevent memory leaks and use-after-free.
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

pub mod marker;
pub mod instance;
pub mod conversion;
pub mod types;
pub mod err;

// Re-export key types
pub use marker::Lean;
pub use instance::{LeanBound, LeanRef};
pub use err::{LeanResult, LeanError};

/// Prelude module for convenient imports
pub mod prelude {
    //! Commonly used items for Leo3 users.
    pub use crate::{
        Lean, LeanBound, LeanRef, LeanResult, LeanError,
    };

    // Re-export commonly used types
    pub use crate::types::{LeanNat, LeanString, LeanArray};

    #[cfg(feature = "macros")]
    pub use leo3_macros::{leanfn, leanclass, leanmodule};
}

/// Initialize the Lean runtime for standalone use.
///
/// This must be called before any Lean operations. It initializes the
/// Lean runtime and returns a `Lean<'l>` token that proves initialization.
///
/// # Safety
///
/// This function is safe, but the Lean runtime must not already be initialized.
/// Only call this once per process.
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
    unsafe {
        ffi::lean_initialize_runtime_module();
        ffi::lean_initialize_thread();
    }
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
///     let s = LeanString::new(lean, "Hello, Lean!");
///     println!("{}", s.to_str()?);
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

/// Metadata about a Lean function (used by macros)
#[doc(hidden)]
pub struct LeanFunctionMetadata {
    /// Name of the function in Lean
    pub name: &'static str,
}
