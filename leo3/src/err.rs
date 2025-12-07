//! Error types for Leo3.

use std::fmt;

/// Result type for Leo3 operations.
pub type LeanResult<T> = Result<T, LeanError>;

/// Error type for Leo3 operations.
#[derive(Debug)]
pub enum LeanError {
    /// Error during type conversion
    Conversion(String),
    /// Error from Lean runtime
    Runtime(String),
    /// Error during FFI call
    Ffi(String),
    /// Other errors
    Other(String),
}

impl LeanError {
    /// Create a conversion error.
    pub fn conversion(msg: &str) -> Self {
        LeanError::Conversion(msg.to_string())
    }

    /// Create a runtime error.
    pub fn runtime(msg: &str) -> Self {
        LeanError::Runtime(msg.to_string())
    }

    /// Create an FFI error.
    pub fn ffi(msg: &str) -> Self {
        LeanError::Ffi(msg.to_string())
    }

    /// Create a generic error.
    pub fn other(msg: &str) -> Self {
        LeanError::Other(msg.to_string())
    }
}

impl fmt::Display for LeanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LeanError::Conversion(msg) => write!(f, "Conversion error: {}", msg),
            LeanError::Runtime(msg) => write!(f, "Lean runtime error: {}", msg),
            LeanError::Ffi(msg) => write!(f, "FFI error: {}", msg),
            LeanError::Other(msg) => write!(f, "Error: {}", msg),
        }
    }
}

impl std::error::Error for LeanError {}
