//! IO error types for Leo3.
//!
//! This module provides error handling for IO operations in Lean4.

use crate::conversion::FromLean;
use crate::err::LeanError;
use crate::ffi;
use crate::instance::LeanBound;
use crate::types::LeanString;
use crate::marker::Lean;
use std::fmt;

/// Result type for IO operations.
pub type IOResult<T> = Result<T, IOError>;

/// Error type for IO operations.
///
/// This corresponds to Lean4's `IO.Error` type.
#[derive(Debug)]
pub enum IOError {
    /// File system error (file not found, permission denied, etc.)
    Filesystem(String),
    /// User-defined error message
    UserError(String),
    /// Interrupted system call
    Interrupted,
    /// Operation not supported
    Unsupported(String),
    /// Other IO errors
    Other(String),
}

impl IOError {
    /// Create a filesystem error.
    pub fn filesystem(msg: impl Into<String>) -> Self {
        IOError::Filesystem(msg.into())
    }

    /// Create a user error.
    pub fn user_error(msg: impl Into<String>) -> Self {
        IOError::UserError(msg.into())
    }

    /// Create an unsupported operation error.
    pub fn unsupported(msg: impl Into<String>) -> Self {
        IOError::Unsupported(msg.into())
    }

    /// Create a generic IO error.
    pub fn other(msg: impl Into<String>) -> Self {
        IOError::Other(msg.into())
    }

    /// Convert Lean IO.Error object to Rust IOError
    ///
    /// # Safety
    ///
    /// - `err_obj` must be a valid Lean IO.Error object
    pub(crate) unsafe fn from_lean_io_error<'l>(
        lean: Lean<'l>,
        err_obj: *mut ffi::lean_object,
    ) -> Self {
        // IO.Error is a constructor with tag and message
        // For now, extract the error message if it's a string
        use crate::instance::LeanAny;
        let bound: LeanBound<LeanAny> = LeanBound::from_owned_ptr(lean, err_obj);

        // Try to extract error message
        // IO.Error structure varies, so we'll attempt to get a string representation
        if let Ok(error_str) = String::from_lean(&bound.cast()) {
            IOError::Other(error_str)
        } else {
            IOError::Other("Unknown IO error".to_string())
        }
    }

    /// Convert this IOError to a Lean IO.Error object
    ///
    /// # Safety
    ///
    /// Creates a new Lean object
    #[allow(dead_code)]
    pub(crate) unsafe fn to_lean_io_error<'l>(&self, lean: Lean<'l>) -> *mut ffi::lean_object {
        let msg = self.to_string();
        let lean_str = LeanString::mk(lean, &msg).expect("Failed to create lean string");
        ffi::lean_mk_io_user_error(lean_str.into_ptr())
    }
}

impl fmt::Display for IOError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IOError::Filesystem(msg) => write!(f, "Filesystem error: {}", msg),
            IOError::UserError(msg) => write!(f, "User error: {}", msg),
            IOError::Interrupted => write!(f, "Operation interrupted"),
            IOError::Unsupported(msg) => write!(f, "Unsupported operation: {}", msg),
            IOError::Other(msg) => write!(f, "IO error: {}", msg),
        }
    }
}

impl std::error::Error for IOError {}

impl From<IOError> for LeanError {
    fn from(err: IOError) -> Self {
        LeanError::runtime(&err.to_string())
    }
}

impl From<LeanError> for IOError {
    fn from(err: LeanError) -> Self {
        IOError::Other(err.to_string())
    }
}
