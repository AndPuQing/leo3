//! Rust re-implementations of Lean4's `static inline` FFI helpers.
//!
//! Lean4's C API defines many helper functions as `static inline` in `lean.h`,
//! so they do not exist as linkable symbols. This module keeps those helpers in
//! smaller domain-oriented submodules and re-exports them at the historical
//! `leo3_ffi::inline::*` paths to preserve public behavior.
//!
//! These implementations are based on Lean4 v4.25.2 headers.

mod array;
mod closure;
mod external;
mod layout;
mod nat;
mod numeric;
mod object;
mod string;
mod task;
mod utils;

pub use array::*;
pub use closure::*;
pub use external::*;
pub use layout::*;
pub use nat::*;
pub use numeric::*;
pub use object::*;
pub use string::*;
pub use task::*;
pub(crate) use utils::likely;
