//! Test to verify MetaM FFI symbols are available at link time

use leo3_ffi::meta::*;

#[test]
fn test_meta_symbols_exist() {
    // This test verifies that the MetaM FFI symbols are available at link time.
    // We don't actually call the functions (which would require a full Lean runtime),
    // but the test will fail to link if the symbols don't exist.

    // Get function pointers to verify symbols exist
    // The MetaM.run' symbol name changed in Lean 4.22 (_rarg → _redArg),
    // so we use the version-agnostic wrapper.
    let _run_ptr = lean_meta_metam_run as *const ();
    let _infer_type_ptr = l_Lean_Meta_inferType___boxed as *const ();
    let _check_ptr = l_Lean_Meta_check as *const ();

    // If we got here, all symbols are available
    assert!(!_run_ptr.is_null());
    assert!(!_infer_type_ptr.is_null());
    assert!(!_check_ptr.is_null());
}
