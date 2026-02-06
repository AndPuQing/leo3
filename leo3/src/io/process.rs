//! Process control operations for Lean4.
//!
//! This module provides safe wrappers around Lean4's process control primitives,
//! including exit codes and process termination.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{ LeanBound};
use crate::marker::Lean;
use crate::io::LeanIO;

/// Get the current process exit code.
///
/// This corresponds to Lean's `IO.getExitCode` function.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::process;
///
/// leo3::with_lean(|lean| {
///     let io = process::get_exit_code(lean)?;
///     let code = io.run()?;
///     println!("Exit code: {}", code);
///     Ok(())
/// })
/// ```
pub fn get_exit_code<'l>(lean: Lean<'l>) -> LeanResult<LeanIO<'l, u32>> {
    unsafe {
        let closure = ffi::inline::lean_alloc_closure(
            ffi::io::lean_io_prim_get_exit_code as *mut std::ffi::c_void,
            0,
            0,
        );

        Ok(LeanIO::from_raw(LeanBound::from_owned_ptr(lean, closure)))
    }
}

/// Set the process exit code.
///
/// This corresponds to Lean's `IO.setExitCode` function.
/// The exit code will be used when the process terminates.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::process;
///
/// leo3::with_lean(|lean| {
///     let io = process::set_exit_code(lean, 1)?;
///     io.run()?;
///     Ok(())
/// })
/// ```
pub fn set_exit_code<'l>(lean: Lean<'l>, code: u32) -> LeanResult<LeanIO<'l, ()>> {
    unsafe {
        let closure = ffi::inline::lean_alloc_closure(
            ffi::io::lean_io_prim_set_exit_code as *mut std::ffi::c_void,
            1,
            1,
        );
        ffi::inline::lean_closure_set(closure, 0, ffi::lean_box(code as usize));

        Ok(LeanIO::from_raw(LeanBound::from_owned_ptr(lean, closure)))
    }
}

/// Exit the process immediately with the given exit code.
///
/// This corresponds to Lean's `IO.Process.exit` function.
/// This function does not return.
///
/// # Safety
///
/// This function terminates the process immediately without running destructors
/// or cleanup code. Use with caution.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::process;
///
/// leo3::with_lean(|lean| {
///     // This will terminate the process
///     process::exit(1);
/// })
/// ```
pub fn exit(code: u32) -> ! {
    unsafe {
        ffi::io::lean_io_prim_exit(code)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_process_io_types() {
        assert_eq!(
            std::mem::size_of::<LeanIO<u32>>(),
            std::mem::size_of::<*mut ()>()
        );
        assert_eq!(
            std::mem::size_of::<LeanIO<()>>(),
            std::mem::size_of::<*mut ()>()
        );
    }
}
