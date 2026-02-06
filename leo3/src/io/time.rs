//! Time operations for Lean4.
//!
//! This module provides safe wrappers around Lean4's time primitives,
//! including monotonic time and Unix timestamps.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{ LeanBound};
use crate::marker::Lean;
use crate::io::LeanIO;

/// Get monotonic time in nanoseconds.
///
/// This corresponds to Lean's `IO.monoNanosNow` function.
/// Returns a monotonically increasing timestamp suitable for measuring durations.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::time;
///
/// leo3::with_lean(|lean| {
///     let io = time::mono_nanos(lean)?;
///     let nanos = io.run()?;
///     println!("Monotonic time: {} ns", nanos);
///     Ok(())
/// })
/// ```
pub fn mono_nanos<'l>(lean: Lean<'l>) -> LeanResult<LeanIO<'l, u64>> {
    unsafe {
        let closure = ffi::inline::lean_alloc_closure(
            ffi::io::lean_io_prim_mono_nanos as *mut std::ffi::c_void,
            0,
            0,
        );

        Ok(LeanIO::from_raw(LeanBound::from_owned_ptr(lean, closure)))
    }
}

/// Get Unix time in milliseconds since epoch.
///
/// This corresponds to Lean's `IO.currentTimeMillis` function.
/// Returns the current wall-clock time as milliseconds since Unix epoch (1970-01-01).
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::time;
///
/// leo3::with_lean(|lean| {
///     let io = time::unix_time_millis(lean)?;
///     let millis = io.run()?;
///     println!("Unix time: {} ms", millis);
///     Ok(())
/// })
/// ```
pub fn unix_time_millis<'l>(lean: Lean<'l>) -> LeanResult<LeanIO<'l, u64>> {
    unsafe {
        let closure = ffi::inline::lean_alloc_closure(
            ffi::io::lean_io_prim_get_unix_time_millis as *mut std::ffi::c_void,
            0,
            0,
        );

        Ok(LeanIO::from_raw(LeanBound::from_owned_ptr(lean, closure)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_time_io_types() {
        assert_eq!(
            std::mem::size_of::<LeanIO<u64>>(),
            std::mem::size_of::<*mut ()>()
        );
    }
}
