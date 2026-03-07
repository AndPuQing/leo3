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

#[repr(C)]
struct FakeCtorWithU32 {
    inner: ffi::inline::lean_ctor_object,
    obj0: *mut ffi::lean_object,
    scalar: u32,
}

#[repr(C)]
struct FakeCtorWithF64 {
    inner: ffi::inline::lean_ctor_object,
    obj0: *mut ffi::lean_object,
    scalar: f64,
}

#[repr(C)]
struct FakeCtorWithF32 {
    inner: ffi::inline::lean_ctor_object,
    obj0: *mut ffi::lean_object,
    scalar: f32,
}

#[repr(C)]
struct FakeString<const N: usize> {
    inner: ffi::inline::lean_string_object,
    data: [u8; N],
}

fn lean_header(tag: u8, other: u8) -> ffi::lean_object {
    ffi::lean_object {
        m_rc: 1,
        m_cs_sz: 0,
        m_other: other,
        m_tag: tag,
    }
}

fn fake_ascii_string<const N: usize>(data: [u8; N], len: usize) -> FakeString<N> {
    FakeString {
        inner: ffi::inline::lean_string_object {
            m_header: lean_header(ffi::LEAN_STRING, 0),
            m_size: N,
            m_capacity: N,
            m_length: len,
            m_data: [],
        },
        data,
    }
}

#[test]
fn check_lean_object_layout() {
    check_struct_layout!(ffi::lean_object, bindgen::lean_object, "lean_object");
    // bindgen packs the remaining header fields into a bitfield helper, so only
    // the `m_rc` offset can be compared directly.
    check_field_offset!(
        ffi::lean_object,
        bindgen::lean_object,
        "lean_object",
        (m_rc, m_rc)
    );
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
    type AllocObjectFn = unsafe extern "C" fn(usize) -> *mut ffi::lean_object;
    type BindgenAllocObjectFn = unsafe extern "C" fn(usize) -> *mut bindgen::lean_object;
    type FreeObjectFn = unsafe extern "C" fn(*mut ffi::lean_object);
    type BindgenFreeObjectFn = unsafe extern "C" fn(*mut bindgen::lean_object);
    type AllocSmallFn = unsafe extern "C" fn(u32, u32) -> *mut std::ffi::c_void;
    type BindgenAllocSmallFn = unsafe extern "C" fn(u32, u32) -> *mut std::ffi::c_void;
    type FreeSmallFn = unsafe extern "C" fn(*mut std::ffi::c_void);
    type BindgenFreeSmallFn = unsafe extern "C" fn(*mut std::ffi::c_void);
    type RegisterExternalClassFn = unsafe extern "C" fn(
        ffi::object::lean_external_finalize_proc,
        ffi::object::lean_external_foreach_proc,
    )
        -> *mut ffi::object::lean_external_class;
    type BindgenRegisterExternalClassFn = unsafe extern "C" fn(
        bindgen::lean_external_finalize_proc,
        bindgen::lean_external_foreach_proc,
    )
        -> *mut bindgen::lean_external_class;

    check_function_signature!(
        ffi::lean_inc_heartbeat,
        bindgen::lean_inc_heartbeat,
        HeartbeatFn,
        "lean_inc_heartbeat"
    );
    check_function_signature!(
        ffi::object::lean_alloc_object,
        AllocObjectFn,
        "lean_alloc_object"
    );
    check_function_signature!(
        bindgen::lean_alloc_object,
        BindgenAllocObjectFn,
        "bindgen::lean_alloc_object"
    );
    check_function_signature!(
        ffi::object::lean_free_object,
        FreeObjectFn,
        "lean_free_object"
    );
    check_function_signature!(
        bindgen::lean_free_object,
        BindgenFreeObjectFn,
        "bindgen::lean_free_object"
    );
    check_function_signature!(
        ffi::lean_register_external_class,
        RegisterExternalClassFn,
        "lean_register_external_class"
    );
    check_function_signature!(
        bindgen::lean_register_external_class,
        BindgenRegisterExternalClassFn,
        "bindgen::lean_register_external_class"
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
        ffi::lean_initialize_thread,
        InitFn,
        "lean_initialize_thread"
    );
    check_function_signature!(ffi::lean_finalize_thread, InitFn, "lean_finalize_thread");
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

#[test]
fn check_inline_only_function_signatures() {
    type BoxFloatFn = unsafe fn(f64) -> ffi::lean_obj_res;
    type UnboxFloatFn = unsafe fn(ffi::b_lean_obj_arg) -> f64;
    type BoxFloat32Fn = unsafe fn(f32) -> ffi::lean_obj_res;
    type UnboxFloat32Fn = unsafe fn(ffi::b_lean_obj_arg) -> f32;
    type CtorGetFloatFn = unsafe fn(ffi::b_lean_obj_arg, ffi::c_uint) -> f64;
    type CtorSetFloatFn = unsafe fn(ffi::lean_obj_arg, ffi::c_uint, f64);
    type CtorGetFloat32Fn = unsafe fn(ffi::b_lean_obj_arg, ffi::c_uint) -> f32;
    type CtorSetFloat32Fn = unsafe fn(ffi::lean_obj_arg, ffi::c_uint, f32);
    type StringGetFastFn = unsafe fn(ffi::b_lean_obj_arg, ffi::b_lean_obj_arg) -> u32;
    type StringNextFastFn =
        unsafe fn(ffi::b_lean_obj_arg, ffi::b_lean_obj_arg) -> ffi::lean_obj_res;
    type StringByteFastFn = unsafe fn(ffi::b_lean_obj_arg, ffi::b_lean_obj_arg) -> u8;
    type StringAtEndFn = unsafe fn(ffi::b_lean_obj_arg, ffi::b_lean_obj_arg) -> u8;
    type StringDecEqFn = unsafe fn(ffi::b_lean_obj_arg, ffi::b_lean_obj_arg) -> u8;
    type StringDecLtFn = unsafe fn(ffi::b_lean_obj_arg, ffi::b_lean_obj_arg) -> u8;
    type AllocExternalFn =
        unsafe fn(*mut ffi::object::lean_external_class, *mut ffi::c_void) -> ffi::lean_obj_res;
    type GetExternalClassFn =
        unsafe fn(ffi::b_lean_obj_arg) -> *mut ffi::object::lean_external_class;
    type GetExternalDataFn = unsafe fn(ffi::b_lean_obj_arg) -> *mut ffi::c_void;

    check_function_signature!(ffi::inline::lean_box_float, BoxFloatFn, "lean_box_float");
    check_function_signature!(
        ffi::inline::lean_unbox_float,
        UnboxFloatFn,
        "lean_unbox_float"
    );
    check_function_signature!(
        ffi::inline::lean_box_float32,
        BoxFloat32Fn,
        "lean_box_float32"
    );
    check_function_signature!(
        ffi::inline::lean_unbox_float32,
        UnboxFloat32Fn,
        "lean_unbox_float32"
    );
    check_function_signature!(
        ffi::object::lean_ctor_get_float,
        CtorGetFloatFn,
        "lean_ctor_get_float"
    );
    check_function_signature!(
        ffi::object::lean_ctor_set_float,
        CtorSetFloatFn,
        "lean_ctor_set_float"
    );
    check_function_signature!(
        ffi::object::lean_ctor_get_float32,
        CtorGetFloat32Fn,
        "lean_ctor_get_float32"
    );
    check_function_signature!(
        ffi::object::lean_ctor_set_float32,
        CtorSetFloat32Fn,
        "lean_ctor_set_float32"
    );
    check_function_signature!(
        ffi::string::lean_string_utf8_get_fast,
        StringGetFastFn,
        "lean_string_utf8_get_fast"
    );
    check_function_signature!(
        ffi::string::lean_string_utf8_next_fast,
        StringNextFastFn,
        "lean_string_utf8_next_fast"
    );
    check_function_signature!(
        ffi::string::lean_string_get_byte_fast,
        StringByteFastFn,
        "lean_string_get_byte_fast"
    );
    check_function_signature!(
        ffi::string::lean_string_utf8_at_end,
        StringAtEndFn,
        "lean_string_utf8_at_end"
    );
    check_function_signature!(
        ffi::string::lean_string_dec_eq,
        StringDecEqFn,
        "lean_string_dec_eq"
    );
    check_function_signature!(
        ffi::string::lean_string_dec_lt,
        StringDecLtFn,
        "lean_string_dec_lt"
    );
    check_function_signature!(
        ffi::object::lean_alloc_external,
        AllocExternalFn,
        "lean_alloc_external"
    );
    check_function_signature!(
        ffi::object::lean_get_external_class,
        GetExternalClassFn,
        "lean_get_external_class"
    );
    check_function_signature!(
        ffi::object::lean_get_external_data,
        GetExternalDataFn,
        "lean_get_external_data"
    );
}

#[test]
fn check_ctor_scalar_helpers_use_header_offsets() {
    #[repr(C)]
    struct FakeZeroObjCtorWithF64 {
        inner: ffi::inline::lean_ctor_object,
        scalar: f64,
    }

    #[repr(C)]
    struct FakeZeroObjCtorWithF32 {
        inner: ffi::inline::lean_ctor_object,
        scalar: f32,
    }

    let offset = std::mem::size_of::<*mut ffi::lean_object>() as ffi::c_uint;

    let mut u32_ctor = FakeCtorWithU32 {
        inner: ffi::inline::lean_ctor_object {
            m_header: lean_header(0, 1),
            m_objs: [],
        },
        obj0: std::ptr::null_mut(),
        scalar: 0,
    };
    let mut f64_ctor = FakeCtorWithF64 {
        inner: ffi::inline::lean_ctor_object {
            m_header: lean_header(0, 1),
            m_objs: [],
        },
        obj0: std::ptr::null_mut(),
        scalar: 0.0,
    };
    let mut f32_ctor = FakeCtorWithF32 {
        inner: ffi::inline::lean_ctor_object {
            m_header: lean_header(0, 1),
            m_objs: [],
        },
        obj0: std::ptr::null_mut(),
        scalar: 0.0,
    };
    let zero_obj_f64 = FakeZeroObjCtorWithF64 {
        inner: ffi::inline::lean_ctor_object {
            m_header: lean_header(0, 0),
            m_objs: [],
        },
        scalar: 6.25,
    };
    let zero_obj_f32 = FakeZeroObjCtorWithF32 {
        inner: ffi::inline::lean_ctor_object {
            m_header: lean_header(0, 0),
            m_objs: [],
        },
        scalar: 3.5,
    };

    unsafe {
        ffi::inline::lean_ctor_set_uint32(&mut u32_ctor.inner.m_header, offset, 0xDEADBEEF);
        assert_eq!(u32_ctor.scalar, 0xDEADBEEF);
        assert_eq!(
            ffi::inline::lean_ctor_get_uint32(&u32_ctor.inner.m_header, offset),
            0xDEADBEEF
        );

        ffi::inline::lean_ctor_set_float(&mut f64_ctor.inner.m_header, offset, 6.25);
        assert_eq!(f64_ctor.scalar.to_bits(), 6.25f64.to_bits());
        assert_eq!(
            ffi::inline::lean_ctor_get_float(&f64_ctor.inner.m_header, offset).to_bits(),
            6.25f64.to_bits()
        );

        ffi::inline::lean_ctor_set_float32(&mut f32_ctor.inner.m_header, offset, 3.5);
        assert_eq!(f32_ctor.scalar.to_bits(), 3.5f32.to_bits());
        assert_eq!(
            ffi::inline::lean_ctor_get_float32(&f32_ctor.inner.m_header, offset).to_bits(),
            3.5f32.to_bits()
        );
        assert_eq!(
            ffi::inline::lean_unbox_float(&zero_obj_f64.inner.m_header).to_bits(),
            6.25f64.to_bits()
        );
        assert_eq!(
            ffi::inline::lean_unbox_float32(&zero_obj_f32.inner.m_header).to_bits(),
            3.5f32.to_bits()
        );
    }
}

#[test]
fn check_string_fast_path_edge_cases() {
    let ascii = fake_ascii_string(*b"abc\0", 3);
    let s = &ascii.inner.m_header as *const ffi::lean_object;

    unsafe {
        let zero = ffi::lean_box(0) as ffi::b_lean_obj_arg;
        let one = ffi::lean_box(1) as ffi::b_lean_obj_arg;
        let end = ffi::lean_box(3) as ffi::b_lean_obj_arg;

        assert_eq!(ffi::string::lean_string_utf8_get_fast(s, zero), b'a' as u32);
        assert_eq!(ffi::string::lean_string_get_byte_fast(s, one), b'b');
        assert_eq!(
            ffi::lean_unbox(ffi::string::lean_string_utf8_next_fast(s, one)),
            2
        );
        assert!(ffi::string::lean_string_eq(s, s));
        assert_eq!(ffi::string::lean_string_dec_eq(s, s), 1);
        assert_eq!(ffi::string::lean_string_dec_lt(s, s), 0);
        assert_eq!(ffi::string::lean_string_utf8_at_end(s, one), 0);
        assert_eq!(ffi::string::lean_string_utf8_at_end(s, end), 1);
        assert_eq!(ffi::string::lean_string_utf8_at_end(s, s), 1);
    }
}

#[test]
fn check_external_inline_getters_follow_layout() {
    let class = 0x1234usize as *mut ffi::object::lean_external_class;
    let data = 0x5678usize as *mut ffi::c_void;
    let external = ffi::inline::lean_external_object {
        m_header: lean_header(ffi::LEAN_EXTERNAL, 0),
        m_class: class,
        m_data: data,
    };
    let o = &external.m_header as *const ffi::lean_object;

    unsafe {
        assert_eq!(ffi::inline::lean_get_external_class(o), class);
        assert_eq!(ffi::inline::lean_get_external_data(o), data);
        assert_eq!(ffi::object::lean_get_external_class(o), class);
        assert_eq!(ffi::object::lean_get_external_data(o), data);
    }
}
