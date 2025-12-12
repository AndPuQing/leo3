//! Environment variable operations.
//!
//! Lean4 no longer exports the environment variable primitives that older
//! versions exposed to C. For portability across Lean versions, these wrappers
//! delegate to Rust's standard library.

use crate::err::LeanResult;
use crate::marker::Lean;
use std::env as std_env;

// ============================================================================
// Environment Variable Operations
// ============================================================================

/// Get the value of an environment variable.
///
/// Returns `Some(value)` if the variable is set, or `None` if it doesn't exist.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::env;
///
/// leo3::with_lean(|lean| {
///     match env::get_env(lean, "HOME")? {
///         Some(home) => println!("HOME: {}", home),
///         None => println!("HOME not set"),
///     }
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the IO operation fails (rare for environment variables).
pub fn get_env<'l>(lean: Lean<'l>, name: &str) -> LeanResult<Option<String>> {
    let _ = lean;
    Ok(std_env::var(name).ok())
}

/// Set an environment variable.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::env;
///
/// leo3::with_lean(|lean| {
///     env::set_env(lean, "MY_VAR", "my_value")?;
///     println!("Variable set!");
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the IO operation fails.
pub fn set_env<'l>(lean: Lean<'l>, name: &str, value: &str) -> LeanResult<()> {
    let _ = lean;
    std_env::set_var(name, value);
    Ok(())
}

/// Unset (remove) an environment variable.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::env;
///
/// leo3::with_lean(|lean| {
///     env::unset_env(lean, "MY_VAR")?;
///     println!("Variable removed!");
///     Ok(())
/// })
/// ```
///
/// # Errors
///
/// Returns an error if the IO operation fails.
pub fn unset_env<'l>(lean: Lean<'l>, name: &str) -> LeanResult<()> {
    let _ = lean;
    std_env::remove_var(name);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_env() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            // PATH should exist on all systems
            let path = get_env(lean, "PATH")?;
            assert!(path.is_some(), "PATH environment variable should exist");

            // A non-existent variable
            let nonexistent = get_env(lean, "LEO3_NONEXISTENT_VAR_12345")?;
            assert!(
                nonexistent.is_none(),
                "Non-existent variable should return None"
            );

            Ok::<_, crate::LeanError>(())
        })
        .unwrap();
    }

    #[test]
    fn test_set_and_get_env() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let var_name = "LEO3_TEST_VAR";
            let var_value = "test_value_12345";

            // Set the variable
            set_env(lean, var_name, var_value)?;

            // Get it back
            let result = get_env(lean, var_name)?;
            assert_eq!(result, Some(var_value.to_string()));

            // Clean up
            unset_env(lean, var_name)?;

            // Verify it's gone
            let result = get_env(lean, var_name)?;
            assert_eq!(result, None);

            Ok::<_, crate::LeanError>(())
        })
        .unwrap();
    }

    #[test]
    fn test_unset_env() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let var_name = "LEO3_TEST_VAR_TO_UNSET";

            // Set a variable
            set_env(lean, var_name, "some_value")?;
            assert!(get_env(lean, var_name)?.is_some());

            // Unset it
            unset_env(lean, var_name)?;

            // Verify it's gone
            assert!(get_env(lean, var_name)?.is_none());

            Ok::<_, crate::LeanError>(())
        })
        .unwrap();
    }
}
