//! Test that type mismatches are caught

use leo3::prelude::*;

fn main() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42).unwrap();

        // Try to use a Nat where a String is expected
        let _ = LeanString::cstr(&n);

        Ok::<(), LeanError>(())
    });
}
