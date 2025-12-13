//! Minimal reproduction test
use leo3::meta::*;
use leo3::prelude::*;

#[test]
fn test_hash_minimal() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        eprintln!("Created bvar0");

        // First, verify the expression is valid
        assert!(LeanExpr::is_bvar(&bvar0));
        eprintln!("is_bvar check passed");

        // Manually increment before hash to test if it's a refcount issue
        unsafe {
            leo3::ffi::lean_inc(bvar0.as_ptr());
        }
        eprintln!("Incremented ref count");

        // Now try hash
        eprintln!("About to call hash...");
        let hash = LeanExpr::hash(&bvar0);
        eprintln!("Hash: {}", hash);

        eprintln!("Test body done, about to clean up");
        Ok(())
    });

    eprintln!("After test_with_lean");
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}
