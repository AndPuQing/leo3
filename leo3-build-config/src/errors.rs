//! Custom error types for leo3-build-config.
//!
//! Self-contained module usable from both `lib.rs` (`mod errors;`) and
//! `build.rs` (`#[path = "src/errors.rs"] mod errors;`).
//!
//! Some items (e.g. `ErrorReport`, `with_context`) are public API for
//! downstream users but unused in the build script compilation unit.
#![allow(dead_code)]

use std::fmt;

/// Custom error type for leo3-build-config.
pub struct Error {
    pub value: String,
    source: Option<Box<dyn std::error::Error + Send + Sync>>,
}

impl Error {
    pub fn new(value: impl Into<String>) -> Self {
        Self {
            value: value.into(),
            source: None,
        }
    }

    pub fn with_source(
        value: impl Into<String>,
        source: impl std::error::Error + Send + Sync + 'static,
    ) -> Self {
        Self {
            value: value.into(),
            source: Some(Box::new(source)),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.value)
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Error");
        d.field("value", &self.value);
        if let Some(ref src) = self.source {
            d.field("source", src);
        }
        d.finish()
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source
            .as_ref()
            .map(|e| e.as_ref() as &(dyn std::error::Error + 'static))
    }
}

impl From<String> for Error {
    fn from(s: String) -> Self {
        Self::new(s)
    }
}

impl From<&str> for Error {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

pub type Result<T> = std::result::Result<T, Error>;

// ---------------------------------------------------------------------------
// Macros
// ---------------------------------------------------------------------------

/// Create and return an [`Error`] with format-string support.
///
/// ```ignore
/// bail!("something went wrong: {}", detail);
/// ```
macro_rules! bail {
    ($($tt:tt)*) => {
        return Err($crate::errors::Error::new(format!($($tt)*)))
    };
}
pub(crate) use bail;

/// Like `assert!`, but returns an [`Error`] instead of panicking.
///
/// ```ignore
/// ensure!(x > 0, "x must be positive, got {}", x);
/// ```
macro_rules! ensure {
    ($cond:expr, $($tt:tt)*) => {
        if !$cond {
            bail!($($tt)*);
        }
    };
}
pub(crate) use ensure;

/// Print a `cargo:warning=` prefixed message.
///
/// ```ignore
/// cargo_warn!("something looks off: {}", detail);
/// ```
macro_rules! cargo_warn {
    ($($tt:tt)*) => {
        println!("cargo:warning={}", format!($($tt)*))
    };
}
pub(crate) use cargo_warn;

// ---------------------------------------------------------------------------
// Context trait
// ---------------------------------------------------------------------------

/// Attach contextual messages to `Result` and `Option` values.
pub trait Context<T> {
    fn context(self, msg: impl fmt::Display) -> Result<T>;
    fn with_context(self, f: impl FnOnce() -> String) -> Result<T>;
}

impl<T, E> Context<T> for std::result::Result<T, E>
where
    E: std::error::Error + Send + Sync + 'static,
{
    fn context(self, msg: impl fmt::Display) -> Result<T> {
        self.map_err(|e| Error::with_source(msg.to_string(), e))
    }

    fn with_context(self, f: impl FnOnce() -> String) -> Result<T> {
        self.map_err(|e| Error::with_source(f(), e))
    }
}

impl<T> Context<T> for Option<T> {
    fn context(self, msg: impl fmt::Display) -> Result<T> {
        self.ok_or_else(|| Error::new(msg.to_string()))
    }

    fn with_context(self, f: impl FnOnce() -> String) -> Result<T> {
        self.ok_or_else(|| Error::new(f()))
    }
}

// ---------------------------------------------------------------------------
// ErrorReport
// ---------------------------------------------------------------------------

/// Wraps an [`Error`] and formats the full causal chain on [`fmt::Display`].
pub struct ErrorReport(pub Error);

impl fmt::Display for ErrorReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}", self.0)?;
        let mut cur: Option<&dyn std::error::Error> = self
            .0
            .source
            .as_deref()
            .map(|e| e as &dyn std::error::Error);
        while let Some(src) = cur {
            write!(f, "\n  caused by: {}", src)?;
            cur = src.source();
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_from_string() {
        let e = Error::from("boom".to_string());
        assert_eq!(e.to_string(), "boom");
        assert!(e.source.is_none());
    }

    #[test]
    fn error_from_str() {
        let e = Error::from("oops");
        assert_eq!(e.to_string(), "oops");
    }

    #[test]
    fn error_with_source() {
        let io_err = std::io::Error::new(std::io::ErrorKind::NotFound, "file missing");
        let e = Error::with_source("could not read config", io_err);
        assert_eq!(e.to_string(), "could not read config");
        assert!(std::error::Error::source(&e).is_some());
    }

    #[test]
    fn context_on_result() {
        let res: std::result::Result<(), std::io::Error> = Err(std::io::Error::other("disk full"));
        let mapped = res.context("writing output");
        let e = mapped.unwrap_err();
        assert_eq!(e.to_string(), "writing output");
        assert!(std::error::Error::source(&e).is_some());
    }

    #[test]
    fn with_context_on_result() {
        let res: std::result::Result<(), std::io::Error> = Err(std::io::Error::other("nope"));
        let mapped = res.with_context(|| "lazy msg".to_string());
        let e = mapped.unwrap_err();
        assert_eq!(e.to_string(), "lazy msg");
    }

    #[test]
    fn context_on_option() {
        let val: Option<i32> = None;
        let e = val.context("missing value").unwrap_err();
        assert_eq!(e.to_string(), "missing value");
        assert!(e.source.is_none());
    }

    #[test]
    fn with_context_on_option() {
        let val: Option<i32> = None;
        let e = val.with_context(|| "computed msg".to_string()).unwrap_err();
        assert_eq!(e.to_string(), "computed msg");
    }

    fn bail_helper(fail: bool) -> Result<()> {
        if fail {
            bail!("went wrong: {}", 42);
        }
        Ok(())
    }

    #[test]
    fn bail_macro() {
        let e = bail_helper(true).unwrap_err();
        assert_eq!(e.to_string(), "went wrong: 42");
        assert!(bail_helper(false).is_ok());
    }

    fn ensure_helper(x: i32) -> Result<()> {
        ensure!(x > 0, "x must be positive, got {}", x);
        Ok(())
    }

    #[test]
    fn ensure_macro() {
        assert!(ensure_helper(1).is_ok());
        let e = ensure_helper(-1).unwrap_err();
        assert_eq!(e.to_string(), "x must be positive, got -1");
    }

    #[test]
    fn error_report_no_source() {
        let e = Error::new("top-level");
        let report = ErrorReport(e).to_string();
        assert_eq!(report, "error: top-level");
    }

    #[test]
    fn error_report_with_chain() {
        let inner = std::io::Error::new(std::io::ErrorKind::NotFound, "not found");
        let outer = Error::with_source("open failed", inner);
        let report = ErrorReport(outer).to_string();
        assert!(report.starts_with("error: open failed"));
        assert!(report.contains("caused by: not found"));
    }
}
