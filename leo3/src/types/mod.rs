//! Wrappers for Lean built-in types.
//!
//! This module provides safe wrappers around Lean's built-in types like
//! strings, arrays, natural numbers, etc.

pub mod string;
pub mod nat;
pub mod array;

pub use string::LeanString;
pub use nat::LeanNat;
pub use array::LeanArray;
