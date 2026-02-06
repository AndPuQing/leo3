//! Console I/O operations for Lean4.
//!
//! This module provides safe wrappers for console I/O,
//! implemented using file handle operations on stdout/stdin.

use crate::err::LeanResult;
use crate::io::{handle, LeanIO};
use crate::marker::Lean;

/// Print a string to stdout without a newline.
///
/// This corresponds to Lean's `IO.print` function.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::console;
///
/// leo3::with_lean(|lean| {
///     let io = console::put_str(lean, "Hello, ")?;
///     io.run()?;
///     Ok(())
/// })
/// ```
pub fn put_str<'l>(lean: Lean<'l>, s: &str) -> LeanResult<LeanIO<'l, ()>> {
    let stdout = handle::stdout(lean);
    handle::write(lean, &stdout, s)
}

/// Print a string to stdout with a newline.
///
/// This corresponds to Lean's `IO.println` function.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::console;
///
/// leo3::with_lean(|lean| {
///     let io = console::put_str_ln(lean, "Hello, World!")?;
///     io.run()?;
///     Ok(())
/// })
/// ```
pub fn put_str_ln<'l>(lean: Lean<'l>, s: &str) -> LeanResult<LeanIO<'l, ()>> {
    let stdout = handle::stdout(lean);
    let s_with_newline = format!("{}\n", s);
    handle::write(lean, &stdout, &s_with_newline)
}

/// Read a line from stdin.
///
/// This corresponds to Lean's `IO.getLine` function.
/// The returned string includes the trailing newline character.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::console;
///
/// leo3::with_lean(|lean| {
///     let io = console::get_line(lean)?;
///     let line = io.run()?;
///     println!("You entered: {}", line);
///     Ok(())
/// })
/// ```
pub fn get_line<'l>(lean: Lean<'l>) -> LeanResult<LeanIO<'l, String>> {
    let stdin = handle::stdin(lean);
    handle::get_line(lean, &stdin)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_console_io_types() {
        // Ensure types are correctly sized
        assert_eq!(
            std::mem::size_of::<LeanIO<()>>(),
            std::mem::size_of::<*mut ()>()
        );
        assert_eq!(
            std::mem::size_of::<LeanIO<String>>(),
            std::mem::size_of::<*mut ()>()
        );
    }
}
