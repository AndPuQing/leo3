//! Wrappers for Lean built-in types.
//!
//! This module provides safe wrappers around Lean's built-in types like
//! strings, arrays, natural numbers, etc.

pub mod array;
pub mod nat;
pub mod string;

pub use array::LeanArray;
pub use nat::LeanNat;
pub use string::LeanString;
