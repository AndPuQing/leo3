//! Test that creating Lean objects without a token fails

use leo3::prelude::*;

fn main() {
    leo3::prepare_freethreaded_lean();

    // Try to create without Lean token
    // This should fail because LeanNat::from_usize requires a Lean<'l> token
    let n = LeanNat::from_usize(42);

    println!("{:?}", n);
}
