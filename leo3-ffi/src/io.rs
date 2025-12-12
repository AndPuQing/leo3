//! FFI bindings for Lean4 IO operations
//!
//! This module provides low-level bindings to Lean4's IO primitives,
//! including file operations, handles, and environment variables.
//!
//! Based on the Lean4 C API for IO operations.

use crate::object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res};

// ============================================================================
// IO Result Type Checking
// ============================================================================

extern "C" {
    /// Check if an IO result represents an error
    ///
    /// # Safety
    /// - `r` must be a valid IO result object
    ///
    /// Returns true if the result is an error (Except.error), false if ok (Except.ok)
    pub fn lean_io_result_is_error(r: b_lean_obj_arg) -> bool;

    /// Check if an IO result represents success
    ///
    /// # Safety
    /// - `r` must be a valid IO result object
    pub fn lean_io_result_is_ok(r: b_lean_obj_arg) -> bool;

    /// Get the value from a successful IO result
    ///
    /// # Safety
    /// - `r` must be a valid IO result object with Except.ok
    /// - Calling this on an error result is undefined behavior
    pub fn lean_io_result_get_value(r: lean_obj_arg) -> lean_obj_res;

    /// Get the error from a failed IO result
    ///
    /// # Safety
    /// - `r` must be a valid IO result object with Except.error
    /// - Calling this on an ok result is undefined behavior
    pub fn lean_io_result_get_error(r: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// File System Operations
// ============================================================================

extern "C" {
    /// Read entire file contents as a string
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error String)
    pub fn lean_io_prim_fs_read_file(path: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Write string to file (overwrites if exists)
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - `content` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_fs_write_file(
        path: lean_obj_arg,
        content: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Read file contents as byte array
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error ByteArray)
    pub fn lean_io_prim_fs_read_bin_file(path: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Write byte array to file
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - `content` must be a valid Lean ByteArray object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_fs_write_bin_file(
        path: lean_obj_arg,
        content: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Check if file exists
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Bool)
    pub fn lean_io_prim_fs_file_exists(path: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Check if directory exists
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Bool)
    pub fn lean_io_prim_fs_dir_exists(path: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Remove file
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_fs_remove_file(path: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Remove directory
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_fs_remove_dir(path: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Create directory
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_fs_create_dir(path: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Rename/move file or directory
    ///
    /// # Safety
    /// - `old_path` must be a valid Lean string object (consumed)
    /// - `new_path` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_fs_rename(
        old_path: lean_obj_arg,
        new_path: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;
}

// ============================================================================
// File Metadata Operations
// ============================================================================

extern "C" {
    /// Get file size in bytes
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error USize)
    pub fn lean_io_prim_fs_file_size(path: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Get current working directory
    ///
    /// # Safety
    /// - Returns IO (Except IO.Error String)
    pub fn lean_io_prim_fs_get_cwd(world: lean_obj_arg) -> lean_obj_res;

    /// Set current working directory
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_fs_set_cwd(path: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// File Handle Operations
// ============================================================================

extern "C" {
    /// Open file for reading
    ///
    /// # Safety
    /// - `path` must be a valid Lean string object (consumed)
    /// - `binary` indicates binary mode (true) vs text mode (false)
    /// - Returns IO (Except IO.Error FS.Handle)
    pub fn lean_io_prim_handle_mk(
        path: lean_obj_arg,
        mode: lean_obj_arg,
        binary: u8,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Close file handle
    ///
    /// # Safety
    /// - `handle` must be a valid file handle object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_handle_close(handle: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Read from file handle
    ///
    /// # Safety
    /// - `handle` must be a valid file handle object (borrowed)
    /// - `size` is the number of bytes to read
    /// - Returns IO (Except IO.Error ByteArray)
    pub fn lean_io_prim_handle_read(
        handle: b_lean_obj_arg,
        size: usize,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Read line from file handle
    ///
    /// # Safety
    /// - `handle` must be a valid file handle object (borrowed)
    /// - Returns IO (Except IO.Error String)
    pub fn lean_io_prim_handle_get_line(
        handle: b_lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Write to file handle
    ///
    /// # Safety
    /// - `handle` must be a valid file handle object (borrowed)
    /// - `content` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_handle_write(
        handle: b_lean_obj_arg,
        content: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Flush file handle buffers
    ///
    /// # Safety
    /// - `handle` must be a valid file handle object (borrowed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_handle_flush(handle: b_lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Check if at end of file
    ///
    /// # Safety
    /// - `handle` must be a valid file handle object (borrowed)
    /// - Returns IO (Except IO.Error Bool)
    pub fn lean_io_prim_handle_is_eof(handle: b_lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// Standard Streams
// ============================================================================

extern "C" {
    /// Get stdin handle
    ///
    /// # Safety
    /// - Returns a borrowed handle to stdin
    pub fn lean_io_prim_handle_get_stdin() -> lean_obj_res;

    /// Get stdout handle
    ///
    /// # Safety
    /// - Returns a borrowed handle to stdout
    pub fn lean_io_prim_handle_get_stdout() -> lean_obj_res;

    /// Get stderr handle
    ///
    /// # Safety
    /// - Returns a borrowed handle to stderr
    pub fn lean_io_prim_handle_get_stderr() -> lean_obj_res;
}

// ============================================================================
// Environment Variables
// ============================================================================

extern "C" {
    /// Get environment variable value
    ///
    /// # Safety
    /// - `name` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error (Option String))
    pub fn lean_io_prim_get_env(name: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Set environment variable
    ///
    /// # Safety
    /// - `name` must be a valid Lean string object (consumed)
    /// - `value` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_set_env(
        name: lean_obj_arg,
        value: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Unset environment variable
    ///
    /// # Safety
    /// - `name` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_unset_env(name: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// Process Operations
// ============================================================================

extern "C" {
    /// Get process exit code
    ///
    /// # Safety
    /// - Returns IO (Except IO.Error UInt32)
    pub fn lean_io_prim_get_exit_code(world: lean_obj_arg) -> lean_obj_res;

    /// Set process exit code
    ///
    /// # Safety
    /// - `code` is the exit code to set
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_set_exit_code(code: u32, world: lean_obj_arg) -> lean_obj_res;

    /// Exit process immediately
    ///
    /// # Safety
    /// - This function does not return
    /// - `code` is the exit code
    pub fn lean_io_prim_exit(code: u32) -> !;
}

// ============================================================================
// Console I/O
// ============================================================================

extern "C" {
    /// Print string to stdout
    ///
    /// # Safety
    /// - `s` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_put_str(s: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Print string to stdout with newline
    ///
    /// # Safety
    /// - `s` must be a valid Lean string object (consumed)
    /// - Returns IO (Except IO.Error Unit)
    pub fn lean_io_prim_put_str_ln(s: lean_obj_arg, world: lean_obj_arg) -> lean_obj_res;

    /// Read line from stdin
    ///
    /// # Safety
    /// - Returns IO (Except IO.Error String)
    pub fn lean_io_prim_get_line(world: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// Time Operations
// ============================================================================

extern "C" {
    /// Get current time in nanoseconds since epoch
    ///
    /// # Safety
    /// - Returns IO (Except IO.Error UInt64)
    pub fn lean_io_prim_mono_nanos(world: lean_obj_arg) -> lean_obj_res;

    /// Get current real time in milliseconds since epoch
    ///
    /// # Safety
    /// - Returns IO (Except IO.Error UInt64)
    pub fn lean_io_prim_get_unix_time_millis(world: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// RealWorld Token
// ============================================================================

/// Create a RealWorld token
///
/// In Lean4, IO operations take a RealWorld token to enforce ordering.
/// This function creates the initial RealWorld token.
///
/// # Safety
/// - Should only be called once per IO computation chain
#[inline]
pub unsafe fn lean_io_mk_world() -> lean_obj_res {
    // RealWorld is represented as a boxed 0
    crate::lean_box(0)
}
