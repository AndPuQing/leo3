//! Test to verify MetaM FFI symbols are available at link time

use leo3_ffi::meta::*;

#[test]
fn test_meta_symbols_exist() {
    // This test verifies that the MetaM FFI symbols are available at link time.
    // We don't actually call the functions (which would require a full Lean runtime),
    // but the test will fail to link if the symbols don't exist.

    // Get function pointers to verify symbols exist
    let _run_ptr = l_Lean_Meta_MetaM_run_x27___rarg as *const ();
    let _infer_type_ptr = l_Lean_Meta_inferType___boxed as *const ();
    let _check_ptr = l_Lean_Meta_check as *const ();

    // If we got here, all symbols are available
    assert!(!_run_ptr.is_null());
    assert!(!_infer_type_ptr.is_null());
    assert!(!_check_ptr.is_null());
}
