//! Test that Lean objects cannot outlive the Lean<'l> token

use leo3::prelude::*;

fn main() {
    leo3::prepare_freethreaded_lean();

    // Try to create a Lean object outside of with_lean
    let n = {
        let result = leo3::with_lean(|lean| {
            LeanNat::from_usize(lean, 42)
        });
        result.unwrap()
    }; // Error: n cannot outlive the with_lean scope

    println!("{:?}", n);
}
