//! Tests for IO operations (file system and environment variables).
//!
//! These tests verify the Phase 1 IO functionality from the Leo3 roadmap.

use leo3::io::{env, fs};
use leo3::prelude::*;
use std::fs as std_fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

static GLOBAL_LOCK: Mutex<()> = Mutex::new(());
static DIR_COUNTER: AtomicUsize = AtomicUsize::new(0);

struct TestDir {
    path: PathBuf,
}

impl TestDir {
    fn new(test_name: &str) -> Self {
        let unique = DIR_COUNTER.fetch_add(1, Ordering::Relaxed);
        let mut path = std::env::temp_dir();
        path.push(format!(
            "leo3_io_tests_{}_{}_{}",
            std::process::id(),
            test_name,
            unique
        ));
        std_fs::create_dir_all(&path).unwrap();
        Self { path }
    }

    fn file(&self, name: &str) -> String {
        self.path.join(name).to_string_lossy().into_owned()
    }

    fn dir(&self, name: &str) -> String {
        self.path.join(name).to_string_lossy().into_owned()
    }
}

impl Drop for TestDir {
    fn drop(&mut self) {
        let _ = std_fs::remove_dir_all(&self.path);
    }
}

// ============================================================================
// File Reading and Writing Tests
// ============================================================================

#[test]
fn test_write_and_read_file() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();
    let test_dir = TestDir::new("write_and_read_file");

    leo3::with_lean(|lean| {
        let test_path = test_dir.file("test_file.txt");
        let content = "Hello, Lean4 from Rust!";

        // Write file
        fs::write_file(lean, &test_path, content)?;

        // Read file back
        let read_content = fs::read_file(lean, &test_path)?;

        assert_eq!(read_content, content);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_read_nonexistent_file() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let nonexistent = std::env::temp_dir()
            .join("nonexistent_file_12345.txt")
            .to_string_lossy()
            .into_owned();
        let result = fs::read_file(lean, &nonexistent);

        // Should return an error
        assert!(result.is_err(), "Reading nonexistent file should fail");

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_write_and_read_bytes() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();
    let test_dir = TestDir::new("write_and_read_bytes");

    leo3::with_lean(|lean| {
        let test_path = test_dir.file("test_bytes.bin");
        let bytes: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 255, 128];

        // Write bytes
        fs::write_bytes(lean, &test_path, &bytes)?;

        // Read bytes back
        let read_bytes = fs::read_bytes(lean, &test_path)?;

        assert_eq!(read_bytes, bytes);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_file_overwrite() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();
    let test_dir = TestDir::new("file_overwrite");

    leo3::with_lean(|lean| {
        let test_path = test_dir.file("overwrite.txt");

        // Write initial content
        fs::write_file(lean, &test_path, "First version")?;

        // Overwrite with new content
        fs::write_file(lean, &test_path, "Second version")?;

        // Read and verify
        let content = fs::read_file(lean, &test_path)?;
        assert_eq!(content, "Second version");

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

// ============================================================================
// File System Query Tests
// ============================================================================

#[test]
fn test_file_exists() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();
    let test_dir = TestDir::new("file_exists");

    leo3::with_lean(|lean| {
        let test_path = test_dir.file("exists_test.txt");

        // File should not exist initially
        assert!(!fs::file_exists(lean, &test_path)?);

        // Create the file
        fs::write_file(lean, &test_path, "test")?;

        // File should now exist
        assert!(fs::file_exists(lean, &test_path)?);

        // Cleanup
        fs::remove_file(lean, &test_path)?;

        // File should not exist after removal
        assert!(!fs::file_exists(lean, &test_path)?);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_dir_exists() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();
    let test_dir = TestDir::new("dir_exists");

    leo3::with_lean(|lean| {
        let test_subdir = test_dir.dir("test_subdir");

        // Directory should not exist initially
        assert!(!fs::dir_exists(lean, &test_subdir)?);

        // Create the directory
        fs::create_dir(lean, &test_subdir)?;

        // Directory should now exist
        assert!(fs::dir_exists(lean, &test_subdir)?);

        // Cleanup
        fs::remove_dir(lean, &test_subdir)?;

        // Directory should not exist after removal
        assert!(!fs::dir_exists(lean, &test_subdir)?);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_file_size() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();
    let test_dir = TestDir::new("file_size");

    leo3::with_lean(|lean| {
        let test_path = test_dir.file("size_test.txt");
        let content = "Hello, World!"; // 13 bytes

        // Write file
        fs::write_file(lean, &test_path, content)?;

        // Check size
        let size = fs::file_size(lean, &test_path)?;
        assert_eq!(size, content.len());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

// ============================================================================
// Directory Operations Tests
// ============================================================================

#[test]
fn test_create_and_remove_dir() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();
    let test_dir = TestDir::new("create_and_remove_dir");

    leo3::with_lean(|lean| {
        let new_dir = test_dir.dir("new_directory");

        // Create directory
        fs::create_dir(lean, &new_dir)?;

        // Verify it exists
        assert!(fs::dir_exists(lean, &new_dir)?);

        // Remove directory
        fs::remove_dir(lean, &new_dir)?;

        // Verify it's gone
        assert!(!fs::dir_exists(lean, &new_dir)?);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_rename_file() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();
    let test_dir = TestDir::new("rename_file");

    leo3::with_lean(|lean| {
        let old_path = test_dir.file("old_name.txt");
        let new_path = test_dir.file("new_name.txt");

        // Create file
        fs::write_file(lean, &old_path, "content")?;

        // Rename
        fs::rename(lean, &old_path, &new_path)?;

        // Old path should not exist
        assert!(!fs::file_exists(lean, &old_path)?);

        // New path should exist
        assert!(fs::file_exists(lean, &new_path)?);

        // Content should be preserved
        let content = fs::read_file(lean, &new_path)?;
        assert_eq!(content, "content");

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

// ============================================================================
// Working Directory Tests
// ============================================================================

#[test]
fn test_get_cwd() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let cwd = fs::get_cwd(lean)?;

        // Should return a non-empty string
        assert!(!cwd.is_empty());

        // Should be a valid path
        assert!(Path::new(&cwd).exists());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_set_cwd() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Get original cwd
        let original_cwd = fs::get_cwd(lean)?;

        // Use temp directory that exists on all platforms
        let temp_dir = if cfg!(windows) {
            std::env::var("TEMP").unwrap_or_else(|_| "C:\\Windows\\Temp".to_string())
        } else {
            "/tmp".to_string()
        };

        // Change to temp directory
        fs::set_cwd(lean, &temp_dir)?;

        // Verify the change
        let new_cwd = fs::get_cwd(lean)?;
        assert!(
            new_cwd.contains("tmp") || new_cwd.contains("Temp"),
            "Expected temp directory, got: {}",
            new_cwd
        );

        // Restore original cwd
        fs::set_cwd(lean, &original_cwd)?;

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

// ============================================================================
// Environment Variable Tests
// ============================================================================

#[test]
fn test_get_env_existing() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // PATH should exist on all systems
        let path = env::get_env(lean, "PATH")?;
        assert!(path.is_some(), "PATH should exist");
        assert!(!path.unwrap().is_empty(), "PATH should not be empty");

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_get_env_nonexistent() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let result = env::get_env(lean, "LEO3_NONEXISTENT_VAR_XYZ")?;
        assert!(result.is_none(), "Nonexistent var should return None");

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_set_and_get_env() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let var_name = "LEO3_TEST_VAR";
        let var_value = "test_value_123";

        // Set variable
        env::set_env(lean, var_name, var_value)?;

        // Get it back
        let result = env::get_env(lean, var_name)?;
        assert_eq!(result, Some(var_value.to_string()));

        // Cleanup
        env::unset_env(lean, var_name)?;

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_unset_env() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let var_name = "LEO3_TEST_VAR_UNSET";

        // Set variable
        env::set_env(lean, var_name, "value")?;
        assert!(env::get_env(lean, var_name)?.is_some());

        // Unset it
        env::unset_env(lean, var_name)?;

        // Should be gone
        assert!(env::get_env(lean, var_name)?.is_none());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_env_overwrite() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let var_name = "LEO3_TEST_VAR_OVERWRITE";

        // Set initial value
        env::set_env(lean, var_name, "first")?;
        assert_eq!(env::get_env(lean, var_name)?, Some("first".to_string()));

        // Overwrite with new value
        env::set_env(lean, var_name, "second")?;
        assert_eq!(env::get_env(lean, var_name)?, Some("second".to_string()));

        // Cleanup
        env::unset_env(lean, var_name)?;

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

// ============================================================================
// Integration Tests
// ============================================================================

#[test]
fn test_io_operations_integration() {
    let _lock = GLOBAL_LOCK.lock().unwrap();
    leo3::prepare_freethreaded_lean();
    let test_dir = TestDir::new("io_integration");

    leo3::with_lean(|lean| {
        // Create a directory
        let dir = test_dir.dir("integration_test");
        fs::create_dir(lean, &dir)?;
        assert!(fs::dir_exists(lean, &dir)?);

        // Create files in the directory
        let file1 = format!("{}/file1.txt", dir);
        let file2 = format!("{}/file2.txt", dir);

        fs::write_file(lean, &file1, "File 1 content")?;
        fs::write_file(lean, &file2, "File 2 content")?;

        // Verify files exist
        assert!(fs::file_exists(lean, &file1)?);
        assert!(fs::file_exists(lean, &file2)?);

        // Read and verify
        assert_eq!(fs::read_file(lean, &file1)?, "File 1 content");
        assert_eq!(fs::read_file(lean, &file2)?, "File 2 content");

        // Set environment variable with path
        let var_name = format!("LEO3_TEST_DIR_{}", std::process::id());
        env::set_env(lean, &var_name, &dir)?;
        assert_eq!(env::get_env(lean, &var_name)?, Some(dir.clone()));

        // Cleanup files
        fs::remove_file(lean, &file1)?;
        fs::remove_file(lean, &file2)?;

        // Cleanup directory
        fs::remove_dir(lean, &dir)?;
        assert!(!fs::dir_exists(lean, &dir)?);

        // Cleanup env var
        env::unset_env(lean, &var_name)?;

        Ok::<_, LeanError>(())
    })
    .unwrap();
}
