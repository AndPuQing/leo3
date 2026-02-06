//! Example demonstrating IO monad support in leo3.
//!
//! This example shows how to use Lean4's IO primitives from Rust,
//! including console I/O, file handle operations, and IO sequencing.

use leo3::prelude::*;
use leo3::io::{console, handle};
use leo3::io::handle::FileMode;

fn main() -> LeanResult<()> {
    // Initialize Lean runtime
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        println!("=== IO Monad Example ===\n");

        // 1. Console I/O
        println!("1. Console I/O:");
        let io = console::put_str_ln(lean, "Hello from Lean IO!")?;
        io.run()?;

        // 2. Pure values in IO monad
        println!("\n2. Pure values:");
        let pure_io = leo3::io::LeanIO::pure(lean, 42)?;
        let value = pure_io.run()?;
        println!("Pure value: {}", value);

        // 3. Sequencing IO operations
        println!("\n3. Sequencing IO operations:");
        let io1 = console::put_str(lean, "First... ")?;
        let io2 = console::put_str_ln(lean, "Second!")?;
        let sequenced = io1.then(io2);
        sequenced.run()?;

        // 4. File handle operations
        println!("\n4. File handle operations:");

        // Write to a file using handles
        let write_handle_io = handle::open(lean, "/tmp/leo3_test.txt", FileMode::Write, false)?;
        let write_handle = write_handle_io.run()?;

        handle::write(lean, &write_handle, "Hello from leo3!\n")?.run()?;
        handle::write(lean, &write_handle, "This is line 2.\n")?.run()?;
        handle::flush(lean, &write_handle)?.run()?;
        handle::close(lean, write_handle)?.run()?;

        println!("Wrote to /tmp/leo3_test.txt");

        // Read from the file using handles
        let read_handle_io = handle::open(lean, "/tmp/leo3_test.txt", FileMode::Read, false)?;
        let read_handle = read_handle_io.run()?;

        let line1_io = handle::get_line(lean, &read_handle)?;
        let line1 = line1_io.run()?;
        println!("Read line 1: {}", line1.trim());

        let line2_io = handle::get_line(lean, &read_handle)?;
        let line2 = line2_io.run()?;
        println!("Read line 2: {}", line2.trim());

        let eof_io = handle::is_eof(lean, &read_handle)?;
        let at_eof = eof_io.run()?;
        println!("At EOF: {}", at_eof);

        handle::close(lean, read_handle)?.run()?;

        // 5. Standard streams
        println!("\n5. Standard streams:");
        let stdout = handle::stdout(lean);
        handle::write(lean, &stdout, "Writing to stdout via handle\n")?.run()?;
        handle::flush(lean, &stdout)?.run()?;

        let stderr = handle::stderr(lean);
        handle::write(lean, &stderr, "Writing to stderr via handle\n")?.run()?;
        handle::flush(lean, &stderr)?.run()?;

        println!("\n=== All IO operations completed successfully! ===");

        Ok(())
    })
}
