//! FFI layout and signature validation tests.
//!
//! These tests validate that our hand-written FFI bindings in `leo3-ffi`
//! still match Lean4's C headers as seen by bindgen.

#![allow(non_camel_case_types, non_snake_case, dead_code)]

mod bindgen {
    #![allow(clippy::all)]
    include!(concat!(env!("OUT_DIR"), "/bindgen.rs"));
}

use leo3_ffi as ffi;
use leo3_ffi_check::{
    check_field_offset, check_function_signature, check_pointer_type, check_struct_full,
    check_struct_layout,
};

#[test]
fn check_lean_object_layout() {
    check_struct_layout!(ffi::lean_object, bindgen::lean_object, "lean_object");
    // bindgen packs the remaining header fields into a bitfield helper, so only
    // the `m_rc` offset can be compared directly.
    check_field_offset!(ffi::lean_object, bindgen::lean_object, "lean_object", (m_rc, m_rc));
}

#[test]
fn check_inline_layouts() {
    check_struct_full!(
        ffi::inline::lean_array_object,
        bindgen::lean_array_object,
        "lean_array_object",
        (m_header, m_header),
        (m_size, m_size),
        (m_capacity, m_capacity),
        (m_data, m_data)
    );
    check_struct_full!(
        ffi::inline::lean_string_object,
        bindgen::lean_string_object,
        "lean_string_object",
        (m_header, m_header),
        (m_size, m_size),
        (m_capacity, m_capacity),
        (m_length, m_length),
        (m_data, m_data)
    );
    check_struct_full!(
        ffi::inline::lean_closure_object,
        bindgen::lean_closure_object,
        "lean_closure_object",
        (m_header, m_header),
        (m_fun, m_fun),
        (m_arity, m_arity),
        (m_num_fixed, m_num_fixed),
        (m_objs, m_objs)
    );
    check_struct_full!(
        ffi::inline::lean_ctor_object,
        bindgen::lean_ctor_object,
        "lean_ctor_object",
        (m_header, m_header),
        (m_objs, m_objs)
    );
    check_struct_full!(
        ffi::inline::lean_sarray_object,
        bindgen::lean_sarray_object,
        "lean_sarray_object",
        (m_header, m_header),
        (m_size, m_size),
        (m_capacity, m_capacity),
        (m_data, m_data)
    );
    check_struct_full!(
        ffi::inline::lean_ref_object,
        bindgen::lean_ref_object,
        "lean_ref_object",
        (m_header, m_header),
        (m_value, m_value)
    );
    check_struct_full!(
        ffi::inline::lean_thunk_object,
        bindgen::lean_thunk_object,
        "lean_thunk_object",
        (m_header, m_header),
        (m_value, m_value),
        (m_closure, m_closure)
    );
    check_struct_full!(
        ffi::inline::lean_task_imp,
        bindgen::lean_task_imp,
        "lean_task_imp",
        (m_closure, m_closure),
        (m_head_dep, m_head_dep),
        (m_next_dep, m_next_dep),
        (m_prio, m_prio),
        (m_canceled, m_canceled),
        (m_keep_alive, m_keep_alive),
        (m_deleted, m_deleted)
    );
    check_struct_full!(
        ffi::inline::lean_task_object,
        bindgen::lean_task_object,
        "lean_task_object",
        (m_header, m_header),
        (m_value, m_value),
        (m_imp, m_imp)
    );
    check_struct_full!(
        ffi::inline::lean_promise_object,
        bindgen::lean_promise_object,
        "lean_promise_object",
        (m_header, m_header),
        (m_result, m_result)
    );
    check_struct_full!(
        ffi::inline::lean_external_object,
        bindgen::lean_external_object,
        "lean_external_object",
        (m_header, m_header),
        (m_class, m_class),
        (m_data, m_data)
    );
}

#[test]
fn check_type_aliases() {
    check_pointer_type!(ffi::lean_obj_arg, "lean_obj_arg");
    check_pointer_type!(ffi::b_lean_obj_arg, "b_lean_obj_arg");
    check_pointer_type!(ffi::lean_obj_res, "lean_obj_res");
    check_pointer_type!(ffi::object::b_lean_obj_res, "b_lean_obj_res");
}

#[test]
fn check_constants() {
    assert_eq!(ffi::LEAN_MAX_CTOR_TAG, 243);
    assert_eq!(ffi::LEAN_CLOSURE, 245);
    assert_eq!(ffi::LEAN_ARRAY, 246);
    assert_eq!(ffi::LEAN_STRING, 249);
    assert_eq!(ffi::LEAN_TASK, 252);
    assert_eq!(ffi::LEAN_EXTERNAL, 254);
}

#[test]
fn check_bindgen_visible_function_signatures() {
    type HeartbeatFn = unsafe extern "C" fn();
    type AllocObjectFn = unsafe extern "C" fn(ffi::size_t) -> *mut ffi::lean_object;
    type FreeObjectFn = unsafe extern "C" fn(*mut ffi::lean_object);
    type AllocSmallFn = unsafe extern "C" fn(ffi::size_t, ffi::c_uint) -> *mut ffi::c_void;
    type FreeSmallFn = unsafe extern "C" fn(*mut ffi::c_void);
    type RegisterExternalClassFn = unsafe extern "C" fn(
        ffi::object::lean_external_finalize_proc,
        ffi::object::lean_external_foreach_proc,
    ) -> *mut ffi::c_void;

    check_function_signature!(
        ffi::lean_inc_heartbeat,
        bindgen::lean_inc_heartbeat,
        HeartbeatFn,
        "lean_inc_heartbeat"
    );
    check_function_signature!(
        ffi::object::lean_alloc_object,
        bindgen::lean_alloc_object,
        AllocObjectFn,
        "lean_alloc_object"
    );
    check_function_signature!(
        ffi::object::lean_free_object,
        bindgen::lean_free_object,
        FreeObjectFn,
        "lean_free_object"
    );
    check_function_signature!(
        ffi::object::lean_alloc_small,
        bindgen::lean_alloc_small,
        AllocSmallFn,
        "lean_alloc_small"
    );
    check_function_signature!(
        ffi::object::lean_free_small,
        bindgen::lean_free_small,
        FreeSmallFn,
        "lean_free_small"
    );
    check_function_signature!(
        ffi::lean_register_external_class,
        bindgen::lean_register_external_class,
        RegisterExternalClassFn,
        "lean_register_external_class"
    );
}

#[test]
fn check_runtime_and_module_init_signatures() {
    // These initialization exports are part of Leo3's supported Lean ABI surface,
    // but they are not declared in the installed `lean.h`, so bindgen cannot
    // provide a second declaration to compare against.
    type InitFn = unsafe extern "C" fn();
    type ModuleInitFn = unsafe extern "C" fn(u8, *mut std::ffi::c_void) -> *mut std::ffi::c_void;

    check_function_signature!(
        ffi::lean_initialize_runtime_module,
        InitFn,
        "lean_initialize_runtime_module"
    );
    check_function_signature!(
        ffi::lean_finalize_runtime_module,
        InitFn,
        "lean_finalize_runtime_module"
    );
    check_function_signature!(
        ffi::lean_initialize_thread,
        InitFn,
        "lean_initialize_thread"
    );
    check_function_signature!(
        ffi::lean_finalize_thread,
        InitFn,
        "lean_finalize_thread"
    );
    check_function_signature!(
        ffi::initialize_Lean_Expr,
        ModuleInitFn,
        "initialize_Lean_Expr"
    );
    check_function_signature!(
        ffi::initialize_Init_Prelude,
        ModuleInitFn,
        "initialize_Init_Prelude"
    );
    check_function_signature!(
        ffi::initialize_Lean_Environment,
        ModuleInitFn,
        "initialize_Lean_Environment"
    );
    check_function_signature!(
        ffi::initialize_Lean_Meta,
        ModuleInitFn,
        "initialize_Lean_Meta"
    );
}
