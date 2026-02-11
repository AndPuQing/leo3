//! Error types for Leo3.

use std::fmt;

/// Result type for Leo3 operations.
pub type LeanResult<T> = Result<T, LeanError>;

/// Error type for Leo3 operations.
#[derive(Debug, PartialEq)]
pub enum LeanError {
    /// Error during type conversion
    Conversion(String),
    /// FFI function returned a null pointer
    NullPointer {
        /// The operation that returned null
        operation: &'static str,
    },
    /// Array/list index out of bounds
    OutOfBounds {
        /// The index that was accessed
        index: usize,
        /// The length of the collection
        len: usize,
    },
    /// Invalid kind tag from FFI (e.g., unknown expression or name kind)
    InvalidKind {
        /// What kind of object had the invalid tag (e.g., "expression", "name")
        kind: &'static str,
        /// The invalid tag value
        tag: u8,
    },
    /// Kernel type-checking exception with a structured code
    KernelException {
        /// The specific kernel exception code
        code: KernelExceptionCode,
        /// Human-readable description
        message: String,
    },
    /// Error from a Lean Exception (MetaM/CoreM failure)
    Exception {
        /// Whether this is an internal exception
        is_internal: bool,
        /// The error message extracted from MessageData (best-effort)
        message: String,
    },
    /// Other errors
    Other(String),
}

/// Kernel exception codes from Lean's `KernelException` type.
///
/// These correspond to the constructor tags of the `KernelException` inductive
/// in the Lean kernel (see `lean4/src/kernel/kernel_exception.h`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KernelExceptionCode {
    /// Referenced an unknown constant
    UnknownConstant = 0,
    /// Constant already declared in the environment
    AlreadyDeclared = 1,
    /// Declaration type doesn't match previous declaration
    DeclTypeMismatch = 2,
    /// Declaration contains metavariables
    DeclHasMVars = 3,
    /// Declaration contains free variables
    DeclHasFVars = 4,
    /// Expected a function type
    FunExpected = 5,
    /// Expected a type (Sort)
    TypeExpected = 6,
    /// Let binding type mismatch
    LetTypeMismatch = 7,
    /// Expression type mismatch
    ExprTypeMismatch = 8,
    /// Application type mismatch
    AppTypeMismatch = 9,
    /// Invalid projection
    InvalidProj = 10,
    /// Theorem type is not Prop (Sort 0)
    ThmTypeNotProp = 11,
    /// Other kernel error
    Other = 12,
    /// Deterministic timeout
    DeterministicTimeout = 13,
    /// Excessive memory usage
    ExcessiveMemory = 14,
    /// Deep recursion limit exceeded
    DeepRecursion = 15,
    /// Computation was interrupted
    Interrupted = 16,
}

impl KernelExceptionCode {
    /// Convert from the FFI tag value.
    pub fn from_tag(tag: usize) -> Self {
        match tag {
            0 => Self::UnknownConstant,
            1 => Self::AlreadyDeclared,
            2 => Self::DeclTypeMismatch,
            3 => Self::DeclHasMVars,
            4 => Self::DeclHasFVars,
            5 => Self::FunExpected,
            6 => Self::TypeExpected,
            7 => Self::LetTypeMismatch,
            8 => Self::ExprTypeMismatch,
            9 => Self::AppTypeMismatch,
            10 => Self::InvalidProj,
            11 => Self::ThmTypeNotProp,
            12 => Self::Other,
            13 => Self::DeterministicTimeout,
            14 => Self::ExcessiveMemory,
            15 => Self::DeepRecursion,
            16 => Self::Interrupted,
            _ => Self::Other,
        }
    }

    /// Human-readable description of this exception code.
    pub fn description(self) -> &'static str {
        match self {
            Self::UnknownConstant => "unknown constant",
            Self::AlreadyDeclared => "already declared",
            Self::DeclTypeMismatch => "declaration type mismatch",
            Self::DeclHasMVars => "declaration has metavariables",
            Self::DeclHasFVars => "declaration has free variables",
            Self::FunExpected => "function expected",
            Self::TypeExpected => "type expected",
            Self::LetTypeMismatch => "let type mismatch",
            Self::ExprTypeMismatch => "expression type mismatch",
            Self::AppTypeMismatch => "application type mismatch",
            Self::InvalidProj => "invalid projection",
            Self::ThmTypeNotProp => "theorem type is not Prop",
            Self::Other => "other kernel error",
            Self::DeterministicTimeout => "deterministic timeout",
            Self::ExcessiveMemory => "excessive memory",
            Self::DeepRecursion => "deep recursion",
            Self::Interrupted => "interrupted",
        }
    }
}

impl fmt::Display for KernelExceptionCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.description())
    }
}

impl LeanError {
    /// Create a conversion error.
    pub fn conversion(msg: &str) -> Self {
        LeanError::Conversion(msg.to_string())
    }

    /// Create a null pointer error.
    pub fn null_pointer(operation: &'static str) -> Self {
        LeanError::NullPointer { operation }
    }

    /// Create an out-of-bounds error.
    pub fn out_of_bounds(index: usize, len: usize) -> Self {
        LeanError::OutOfBounds { index, len }
    }

    /// Create an invalid kind error.
    pub fn invalid_kind(kind: &'static str, tag: u8) -> Self {
        LeanError::InvalidKind { kind, tag }
    }

    /// Create a kernel exception error.
    pub fn kernel_exception(code: KernelExceptionCode) -> Self {
        let message = code.description().to_string();
        LeanError::KernelException { code, message }
    }

    /// Create a runtime error.
    ///
    /// Deprecated: prefer `null_pointer`, `out_of_bounds`, or `invalid_kind`
    /// for specific error conditions.
    pub fn runtime(msg: &str) -> Self {
        LeanError::Other(format!("runtime: {}", msg))
    }

    /// Create an FFI error.
    ///
    /// Deprecated: prefer `kernel_exception` for kernel errors.
    pub fn ffi(msg: &str) -> Self {
        LeanError::Other(format!("FFI: {}", msg))
    }

    /// Create a generic error.
    pub fn other(msg: &str) -> Self {
        LeanError::Other(msg.to_string())
    }

    /// Create an exception error from a Lean Exception.
    pub fn exception(is_internal: bool, message: &str) -> Self {
        LeanError::Exception {
            is_internal,
            message: message.to_string(),
        }
    }
}

impl fmt::Display for LeanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LeanError::Conversion(msg) => write!(f, "conversion error: {}", msg),
            LeanError::NullPointer { operation } => {
                write!(
                    f,
                    "null pointer returned from `{}`; Lean module may not be initialized",
                    operation
                )
            }
            LeanError::OutOfBounds { index, len } => {
                write!(f, "index {} out of bounds for length {}", index, len)
            }
            LeanError::InvalidKind { kind, tag } => {
                write!(f, "invalid {} tag: {}", kind, tag)
            }
            LeanError::KernelException { code, message } => {
                write!(f, "kernel exception: {}", message)?;
                match code {
                    KernelExceptionCode::ThmTypeNotProp => {
                        write!(
                            f,
                            " (hint: use LeanDeclaration::definition for non-Prop types)"
                        )
                    }
                    KernelExceptionCode::AlreadyDeclared => {
                        write!(
                            f,
                            " (hint: a constant with this name already exists in the environment)"
                        )
                    }
                    KernelExceptionCode::DeclHasMVars => {
                        write!(
                            f,
                            " (hint: resolve all metavariables before adding the declaration)"
                        )
                    }
                    KernelExceptionCode::DeclHasFVars => {
                        write!(
                            f,
                            " (hint: abstract all free variables before adding the declaration)"
                        )
                    }
                    _ => Ok(()),
                }
            }
            LeanError::Exception {
                is_internal,
                message,
            } => {
                if *is_internal {
                    write!(f, "Lean internal exception: {}", message)
                } else {
                    write!(f, "Lean exception: {}", message)
                }
            }
            LeanError::Other(msg) => write!(f, "{}", msg),
        }
    }
}

impl std::error::Error for LeanError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

impl From<std::io::Error> for LeanError {
    fn from(err: std::io::Error) -> Self {
        LeanError::Other(format!("runtime: {}", err))
    }
}
