use leo3::prelude::*;

fn main() -> LeanResult<()> {
    println!("Leo3 Basic Example");
    println!("==================\n");

    // Note: This example demonstrates the API structure.
    // It won't actually run without Lean4 installed and linked.

    println!("Initializing Lean runtime...");
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|_lean| {
        println!("Lean runtime initialized!");
        println!("Lean token obtained successfully!");

        // Example usage (will work once FFI is properly linked):
        // let s = LeanString::new(lean, "Hello from Rust!")?;
        // println!("Created string: {}", LeanString::to_str(&s)?);

        // let n = LeanNat::from_usize(lean, 42)?;
        // println!("Created nat: {}", LeanNat::to_usize(&n)?);

        println!("\nStructure is set up correctly!");
        Ok(())
    })
}
