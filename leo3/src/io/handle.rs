//! File handle operations for Lean4.
//!
//! This module provides safe wrappers around Lean4's file handle primitives,
//! including opening, reading, writing, and closing files.

use crate::conversion::{FromLean, IntoLean};
use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::io::LeanIO;
use crate::marker::Lean;

/// A Lean file handle.
///
/// This corresponds to Lean's `IO.FS.Handle` type.
/// Handles must be closed when done to avoid resource leaks.
#[repr(transparent)]
pub struct LeanHandle<'l> {
    inner: LeanBound<'l, LeanHandleAny>,
}

/// Marker type for file handles.
pub struct LeanHandleAny {
    _private: (),
}

/// File open mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileMode {
    /// Open for reading
    Read,
    /// Open for writing (truncate if exists)
    Write,
    /// Open for reading and writing
    ReadWrite,
    /// Open for appending
    Append,
}

impl FileMode {
    /// Convert to Lean's mode representation.
    ///
    /// Lean uses constructor tags:
    /// - 0: read
    /// - 1: write
    /// - 2: readWrite
    /// - 3: append
    fn to_lean_tag(self) -> u8 {
        match self {
            FileMode::Read => 0,
            FileMode::Write => 1,
            FileMode::ReadWrite => 2,
            FileMode::Append => 3,
        }
    }
}

impl<'l> LeanHandle<'l> {
    /// Create a handle from a raw Lean object.
    ///
    /// # Safety
    ///
    /// - `obj` must be a valid Lean handle object
    #[inline]
    pub unsafe fn from_raw(obj: LeanBound<'l, LeanHandleAny>) -> Self {
        LeanHandle { inner: obj }
    }

    /// Get the underlying Lean object.
    #[inline]
    pub fn as_inner(&self) -> &LeanBound<'l, LeanHandleAny> {
        &self.inner
    }

    /// Get the underlying Lean object pointer.
    #[inline]
    pub fn as_ptr(&self) -> *mut ffi::lean_object {
        self.inner.as_ptr()
    }
}

impl<'l> FromLean<'l> for LeanHandle<'l> {
    type Source = LeanHandleAny;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(unsafe { LeanHandle::from_raw(obj.clone()) })
    }
}

/// Open a file with the specified mode.
///
/// # Arguments
///
/// * `path` - Path to the file
/// * `mode` - File open mode
/// * `binary` - Whether to open in binary mode (true) or text mode (false)
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::handle::{open, FileMode};
///
/// leo3::with_lean(|lean| {
///     let io = open(lean, "test.txt", FileMode::Read, false)?;
///     let handle = io.run()?;
///     // Use handle...
///     Ok(())
/// })
/// ```
pub fn open<'l>(
    lean: Lean<'l>,
    path: &str,
    mode: FileMode,
    binary: bool,
) -> LeanResult<LeanIO<'l, LeanHandle<'l>>> {
    unsafe {
        // Convert path to Lean string
        let lean_path = path.into_lean(lean)?;

        // Create mode constructor
        let mode_tag = mode.to_lean_tag();
        let lean_mode = ffi::lean_alloc_ctor(mode_tag as u32, 0, 0);

        // Create IO computation
        let closure = ffi::inline::lean_alloc_closure(
            ffi::io::lean_io_prim_handle_mk as *mut std::ffi::c_void,
            3,
            3,
        );
        ffi::inline::lean_closure_set(closure, 0, lean_path.into_ptr());
        ffi::inline::lean_closure_set(closure, 1, lean_mode);
        ffi::inline::lean_closure_set(closure, 2, ffi::lean_box(binary as usize));

        Ok(LeanIO::from_raw(LeanBound::from_owned_ptr(lean, closure)))
    }
}

/// Close a file handle.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::handle::{open, close, FileMode};
///
/// leo3::with_lean(|lean| {
///     let handle = open(lean, "test.txt", FileMode::Read, false)?.run()?;
///     close(lean, handle)?.run()?;
///     Ok(())
/// })
/// ```
pub fn close<'l>(lean: Lean<'l>, handle: LeanHandle<'l>) -> LeanResult<LeanIO<'l, ()>> {
    unsafe {
        let closure = ffi::inline::lean_alloc_closure(
            ffi::io::lean_io_prim_handle_close as *mut std::ffi::c_void,
            1,
            1,
        );
        ffi::inline::lean_closure_set(closure, 0, handle.inner.into_ptr());

        Ok(LeanIO::from_raw(LeanBound::from_owned_ptr(lean, closure)))
    }
}

/// Read bytes from a file handle.
///
/// # Arguments
///
/// * `handle` - The file handle to read from
/// * `size` - Number of bytes to read
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::handle::{open, read, FileMode};
///
/// leo3::with_lean(|lean| {
///     let handle = open(lean, "test.txt", FileMode::Read, true)?.run()?;
///     let io = read(lean, &handle, 1024)?;
///     let bytes = io.run()?;
///     Ok(())
/// })
/// ```
pub fn read<'l>(
    lean: Lean<'l>,
    handle: &LeanHandle<'l>,
    size: usize,
) -> LeanResult<LeanIO<'l, Vec<u8>>> {
    unsafe {
        let closure = ffi::inline::lean_alloc_closure(
            ffi::io::lean_io_prim_handle_read as *mut std::ffi::c_void,
            2,
            2,
        );
        ffi::inline::lean_closure_set(closure, 0, handle.as_ptr());
        ffi::inline::lean_closure_set(closure, 1, ffi::lean_box(size));

        Ok(LeanIO::from_raw(LeanBound::from_owned_ptr(lean, closure)))
    }
}

/// Read a line from a file handle.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::handle::{open, get_line, FileMode};
///
/// leo3::with_lean(|lean| {
///     let handle = open(lean, "test.txt", FileMode::Read, false)?.run()?;
///     let io = get_line(lean, &handle)?;
///     let line = io.run()?;
///     Ok(())
/// })
/// ```
pub fn get_line<'l>(lean: Lean<'l>, handle: &LeanHandle<'l>) -> LeanResult<LeanIO<'l, String>> {
    unsafe {
        let closure = ffi::inline::lean_alloc_closure(
            ffi::io::lean_io_prim_handle_get_line as *mut std::ffi::c_void,
            1,
            1,
        );
        ffi::inline::lean_closure_set(closure, 0, handle.as_ptr());

        Ok(LeanIO::from_raw(LeanBound::from_owned_ptr(lean, closure)))
    }
}

/// Write a string to a file handle.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::handle::{open, write, FileMode};
///
/// leo3::with_lean(|lean| {
///     let handle = open(lean, "test.txt", FileMode::Write, false)?.run()?;
///     write(lean, &handle, "Hello, World!")?.run()?;
///     Ok(())
/// })
/// ```
pub fn write<'l>(
    lean: Lean<'l>,
    handle: &LeanHandle<'l>,
    content: &str,
) -> LeanResult<LeanIO<'l, ()>> {
    unsafe {
        let lean_str = content.into_lean(lean)?;

        let closure = ffi::inline::lean_alloc_closure(
            ffi::io::lean_io_prim_handle_write as *mut std::ffi::c_void,
            2,
            2,
        );
        ffi::inline::lean_closure_set(closure, 0, handle.as_ptr());
        ffi::inline::lean_closure_set(closure, 1, lean_str.into_ptr());

        Ok(LeanIO::from_raw(LeanBound::from_owned_ptr(lean, closure)))
    }
}

/// Flush a file handle's buffers.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::handle::{open, write, flush, FileMode};
///
/// leo3::with_lean(|lean| {
///     let handle = open(lean, "test.txt", FileMode::Write, false)?.run()?;
///     write(lean, &handle, "Hello")?.run()?;
///     flush(lean, &handle)?.run()?;
///     Ok(())
/// })
/// ```
pub fn flush<'l>(lean: Lean<'l>, handle: &LeanHandle<'l>) -> LeanResult<LeanIO<'l, ()>> {
    unsafe {
        let closure = ffi::inline::lean_alloc_closure(
            ffi::io::lean_io_prim_handle_flush as *mut std::ffi::c_void,
            1,
            1,
        );
        ffi::inline::lean_closure_set(closure, 0, handle.as_ptr());

        Ok(LeanIO::from_raw(LeanBound::from_owned_ptr(lean, closure)))
    }
}

/// Check if a file handle is at end-of-file.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::handle::{open, is_eof, FileMode};
///
/// leo3::with_lean(|lean| {
///     let handle = open(lean, "test.txt", FileMode::Read, false)?.run()?;
///     let io = is_eof(lean, &handle)?;
///     let at_eof = io.run()?;
///     Ok(())
/// })
/// ```
pub fn is_eof<'l>(lean: Lean<'l>, handle: &LeanHandle<'l>) -> LeanResult<LeanIO<'l, bool>> {
    unsafe {
        let closure = ffi::inline::lean_alloc_closure(
            ffi::io::lean_io_prim_handle_is_eof as *mut std::ffi::c_void,
            1,
            1,
        );
        ffi::inline::lean_closure_set(closure, 0, handle.as_ptr());

        Ok(LeanIO::from_raw(LeanBound::from_owned_ptr(lean, closure)))
    }
}

/// Get the stdin handle.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::handle::{stdin, get_line};
///
/// leo3::with_lean(|lean| {
///     let handle = stdin(lean);
///     let io = get_line(lean, &handle)?;
///     let line = io.run()?;
///     Ok(())
/// })
/// ```
pub fn stdin<'l>(lean: Lean<'l>) -> LeanHandle<'l> {
    unsafe {
        let handle_ptr = ffi::io::lean_io_prim_handle_get_stdin();
        LeanHandle::from_raw(LeanBound::from_borrowed_ptr(lean, handle_ptr))
    }
}

/// Get the stdout handle.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::handle::{stdout, write};
///
/// leo3::with_lean(|lean| {
///     let handle = stdout(lean);
///     write(lean, &handle, "Hello, World!")?.run()?;
///     Ok(())
/// })
/// ```
pub fn stdout<'l>(lean: Lean<'l>) -> LeanHandle<'l> {
    unsafe {
        let handle_ptr = ffi::io::lean_io_prim_handle_get_stdout();
        LeanHandle::from_raw(LeanBound::from_borrowed_ptr(lean, handle_ptr))
    }
}

/// Get the stderr handle.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::handle::{stderr, write};
///
/// leo3::with_lean(|lean| {
///     let handle = stderr(lean);
///     write(lean, &handle, "Error occurred!")?.run()?;
///     Ok(())
/// })
/// ```
pub fn stderr<'l>(lean: Lean<'l>) -> LeanHandle<'l> {
    unsafe {
        let handle_ptr = ffi::io::lean_io_prim_handle_get_stderr();
        LeanHandle::from_raw(LeanBound::from_borrowed_ptr(lean, handle_ptr))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_handle_size() {
        assert_eq!(
            std::mem::size_of::<LeanHandle>(),
            std::mem::size_of::<*mut ()>()
        );
    }

    #[test]
    fn test_file_mode() {
        assert_eq!(FileMode::Read.to_lean_tag(), 0);
        assert_eq!(FileMode::Write.to_lean_tag(), 1);
        assert_eq!(FileMode::ReadWrite.to_lean_tag(), 2);
        assert_eq!(FileMode::Append.to_lean_tag(), 3);
    }
}
