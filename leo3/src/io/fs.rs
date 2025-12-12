//! File system operations.
//!
//! This module provides high-level wrappers for file system operations.
//!
//! Lean4's older C file system primitives are no longer exported in recent
//! Lean toolchains. These APIs therefore delegate to Rust's standard library.

use crate::err::LeanResult;
use crate::marker::Lean;
use std::env as std_env;
use std::fs as std_fs;
use std::path::Path;

// ============================================================================
// File Reading and Writing
// ============================================================================

/// Read entire file contents as a string.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     let content = fs::read_file(lean, "config.txt")?;
///     println!("Content: {}", content);
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the file doesn't exist or cannot be read.
pub fn read_file<'l>(lean: Lean<'l>, path: &str) -> LeanResult<String> {
    let _ = lean;
    Ok(std_fs::read_to_string(path)?)
}

/// Write string to file (overwrites if exists).
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     fs::write_file(lean, "output.txt", "Hello, Lean!")?;
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the file cannot be written (e.g., permission denied).
pub fn write_file<'l>(lean: Lean<'l>, path: &str, content: &str) -> LeanResult<()> {
    let _ = lean;
    std_fs::write(path, content)?;
    Ok(())
}

/// Read file contents as byte array.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     let bytes = fs::read_bytes(lean, "image.png")?;
///     println!("Read {} bytes", bytes.len());
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the file doesn't exist or cannot be read.
pub fn read_bytes<'l>(lean: Lean<'l>, path: &str) -> LeanResult<Vec<u8>> {
    let _ = lean;
    Ok(std_fs::read(path)?)
}

/// Write byte array to file.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     let data = vec![0u8, 1, 2, 3, 4];
///     fs::write_bytes(lean, "data.bin", &data)?;
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the file cannot be written.
pub fn write_bytes<'l>(lean: Lean<'l>, path: &str, content: &[u8]) -> LeanResult<()> {
    let _ = lean;
    std_fs::write(path, content)?;
    Ok(())
}

// ============================================================================
// File System Queries
// ============================================================================

/// Check if file exists.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     if fs::file_exists(lean, "config.txt")? {
///         println!("Config file found!");
///     }
///     Ok(())
/// })
/// ```
pub fn file_exists<'l>(lean: Lean<'l>, path: &str) -> LeanResult<bool> {
    let _ = lean;
    Ok(Path::new(path).is_file())
}

/// Check if directory exists.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     if fs::dir_exists(lean, "/tmp")? {
///         println!("/tmp exists!");
///     }
///     Ok(())
/// })
/// ```
pub fn dir_exists<'l>(lean: Lean<'l>, path: &str) -> LeanResult<bool> {
    let _ = lean;
    Ok(Path::new(path).is_dir())
}

/// Get file size in bytes.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     let size = fs::file_size(lean, "large_file.dat")?;
///     println!("File size: {} bytes", size);
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the file doesn't exist.
pub fn file_size<'l>(lean: Lean<'l>, path: &str) -> LeanResult<usize> {
    let _ = lean;
    let metadata = std_fs::metadata(path)?;
    Ok(metadata.len() as usize)
}

// ============================================================================
// File System Modifications
// ============================================================================

/// Remove a file.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     fs::remove_file(lean, "temp.txt")?;
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the file doesn't exist or cannot be deleted.
pub fn remove_file<'l>(lean: Lean<'l>, path: &str) -> LeanResult<()> {
    let _ = lean;
    std_fs::remove_file(path)?;
    Ok(())
}

/// Remove a directory.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     fs::remove_dir(lean, "temp_dir")?;
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the directory doesn't exist, is not empty, or cannot be deleted.
pub fn remove_dir<'l>(lean: Lean<'l>, path: &str) -> LeanResult<()> {
    let _ = lean;
    std_fs::remove_dir(path)?;
    Ok(())
}

/// Create a directory.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     fs::create_dir(lean, "new_folder")?;
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the directory already exists or cannot be created.
pub fn create_dir<'l>(lean: Lean<'l>, path: &str) -> LeanResult<()> {
    let _ = lean;
    std_fs::create_dir(path)?;
    Ok(())
}

/// Rename or move a file or directory.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     fs::rename(lean, "old_name.txt", "new_name.txt")?;
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the source doesn't exist or the operation fails.
pub fn rename<'l>(lean: Lean<'l>, old_path: &str, new_path: &str) -> LeanResult<()> {
    let _ = lean;
    std_fs::rename(old_path, new_path)?;
    Ok(())
}

// ============================================================================
// Working Directory
// ============================================================================

/// Get current working directory.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     let cwd = fs::get_cwd(lean)?;
///     println!("Current directory: {}", cwd);
///     Ok(())
/// })
/// ```
pub fn get_cwd<'l>(lean: Lean<'l>) -> LeanResult<String> {
    let _ = lean;
    Ok(std_env::current_dir()?.to_string_lossy().into_owned())
}

/// Set current working directory.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::fs;
///
/// leo3::with_lean(|lean| {
///     fs::set_cwd(lean, "/tmp")?;
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the directory doesn't exist or permission is denied.
pub fn set_cwd<'l>(lean: Lean<'l>, path: &str) -> LeanResult<()> {
    let _ = lean;
    std_env::set_current_dir(path)?;
    Ok(())
}
