//! FFI bindings for Lean4 array operations
//!
//! Based on the array functions from lean.h

use crate::{
    inline::{lean_has_rc, lean_to_array},
    object::{
        b_lean_obj_arg, b_lean_obj_res, lean_is_exclusive, lean_obj_arg, lean_obj_res, lean_object,
        u_lean_obj_arg,
    },
};
use libc::size_t;

extern "C" {
    /// Create an array from a list
    ///
    /// # Safety
    /// - `l` must be a valid list object (consumed)
    pub fn lean_array_mk(l: lean_obj_arg) -> lean_obj_res;

    /// Copy an array, optionally expanding capacity
    ///
    /// # Safety
    /// - `a` must be a valid array object (consumed)
    /// - When `expand` is true, capacity is grown to at least (capacity + 1) * 2
    pub fn lean_copy_expand_array(a: lean_obj_arg, expand: bool) -> lean_obj_res;

    /// Convert array to list
    ///
    /// # Safety
    /// - `a` must be a valid array object (consumed)
    pub fn lean_array_to_list(a: lean_obj_arg) -> lean_obj_res;

    /// Push an element to the end of an array
    ///
    /// # Safety
    /// - `a` must be a valid array object (consumed)
    /// - `v` must be a valid object (consumed)
    pub fn lean_array_push(a: lean_obj_arg, v: lean_obj_arg) -> lean_obj_res;

    /// Create an array with n elements, all initialized to v
    ///
    /// # Safety
    /// - `n` must be a boxed usize (or scalar nat)
    /// - `v` must be a valid object
    /// - All elements will share the same reference to `v` (reference count is incremented)
    pub fn lean_mk_array(n: lean_obj_arg, v: lean_obj_arg) -> lean_obj_res;

    /// Get array element with panic on out of bounds
    ///
    /// # Safety
    /// - Creates a panic thunk for out of bounds access
    pub fn lean_array_get_panic(def_val: lean_obj_arg) -> lean_obj_res;

    /// Set array element with panic on out of bounds
    ///
    /// # Safety
    /// - Creates a panic thunk for out of bounds access
    pub fn lean_array_set_panic(a: lean_obj_arg, v: lean_obj_arg) -> lean_obj_res;
}

// Inline functions from lean.h

/// Get array size
///
/// # Safety
/// - `o` must be a valid array object
#[inline]
pub unsafe fn lean_array_size(o: b_lean_obj_arg) -> size_t {
    (*lean_to_array(o as *mut lean_object)).m_size
}

/// Get array capacity
///
/// # Safety
/// - `o` must be a valid array object
#[inline]
pub unsafe fn lean_array_capacity(o: b_lean_obj_arg) -> size_t {
    (*lean_to_array(o as *mut lean_object)).m_capacity
}

/// Get pointer to array data
///
/// # Safety
/// - `o` must be a valid array object
#[inline]
pub unsafe fn lean_array_cptr(o: *mut lean_object) -> *mut *mut lean_object {
    (*lean_to_array(o)).m_data.as_ptr() as *mut *mut lean_object
}

/// Get array element (unchecked)
///
/// # Safety
/// - `o` must be a valid array object
/// - `i` must be < array size
#[inline]
pub unsafe fn lean_array_get_core(o: b_lean_obj_arg, i: size_t) -> b_lean_obj_res {
    assert!(i < lean_array_size(o));
    *lean_array_cptr(o as *mut lean_object).add(i)
}

/// Set array element
///
/// # Safety
/// - `o` must be a valid, exclusive array object
/// - `i` must be < array size
/// - Consumes `v`
#[inline]
pub unsafe fn lean_array_set_core(o: u_lean_obj_arg, i: size_t, v: lean_obj_arg) {
    assert!(!lean_has_rc(o) || lean_is_exclusive(o));
    assert!(i < lean_array_size(o));
    *lean_array_cptr(o).add(i) = v;
}

/// Set array size
///
/// # Safety
/// - `o` must be a valid, exclusive array object
/// - `sz` must be <= capacity
#[inline]
pub unsafe fn lean_array_set_size(o: u_lean_obj_arg, sz: size_t) {
    (*lean_to_array(o)).m_size = sz;
}

/// Get array size as boxed object
///
/// # Safety
/// - `a` must be a valid array object
#[inline]
pub unsafe fn lean_array_get_size(a: b_lean_obj_arg) -> lean_obj_res {
    crate::object::lean_box(lean_array_size(a))
}

/// Get array element at unboxed index
///
/// # Safety
/// - `a` must be a valid array object
/// - `i` must be < array size
/// - Increments reference count of result
#[inline]
pub unsafe fn lean_array_uget(a: b_lean_obj_arg, i: size_t) -> lean_obj_res {
    let elem = lean_array_get_core(a, i);
    crate::object::lean_inc(elem as *mut lean_object);
    elem as *mut lean_object
}

/// Get array element at boxed index
///
/// # Safety
/// - `a` must be a valid array object
/// - `i` must be a boxed usize < array size
/// - Increments reference count of result
#[inline]
pub unsafe fn lean_array_fget(a: b_lean_obj_arg, i: b_lean_obj_arg) -> lean_obj_res {
    lean_array_uget(a, crate::object::lean_unbox(i))
}

/// Get array element at boxed index (borrowed)
///
/// # Safety
/// - `a` must be a valid array object
/// - `i` must be a boxed usize < array size
/// - Does NOT increment reference count
#[inline]
pub unsafe fn lean_array_fget_borrowed(a: b_lean_obj_arg, i: b_lean_obj_arg) -> b_lean_obj_arg {
    lean_array_get_core(a, crate::object::lean_unbox(i))
}

/// Copy an array without expanding capacity.
///
/// # Safety
/// - `a` must be a valid array object (consumed)
#[inline]
pub unsafe fn lean_copy_array(a: lean_obj_arg) -> lean_obj_res {
    lean_copy_expand_array(a, false)
}

/// Ensure an array is exclusively owned, copying when necessary.
///
/// # Safety
/// - `a` must be a valid array object (consumed)
#[inline]
pub unsafe fn lean_ensure_exclusive_array(a: lean_obj_arg) -> lean_obj_res {
    if crate::object::lean_is_exclusive(a) {
        a
    } else {
        lean_copy_array(a)
    }
}

/// Set array element at unboxed index
///
/// # Safety
/// - `a` must be a valid array object (consumed)
/// - `i` must be < array size
/// - `v` is consumed
#[inline]
pub unsafe fn lean_array_uset(a: lean_obj_arg, i: size_t, v: lean_obj_arg) -> lean_obj_res {
    let r = lean_ensure_exclusive_array(a);
    let slot = lean_array_cptr(r).add(i);
    crate::object::lean_dec(*slot);
    *slot = v;
    r
}

/// Set array element at boxed index
///
/// # Safety
/// - `a` must be a valid array object (consumed)
/// - `i` must be a boxed usize < array size
/// - `v` is consumed
#[inline]
pub unsafe fn lean_array_fset(a: lean_obj_arg, i: b_lean_obj_arg, v: lean_obj_arg) -> lean_obj_res {
    lean_array_uset(a, crate::object::lean_unbox(i), v)
}

/// Pop last element from array
///
/// # Safety
/// - `a` must be a valid, non-empty array object (consumed)
#[inline]
pub unsafe fn lean_array_pop(a: lean_obj_arg) -> lean_obj_res {
    let r = lean_ensure_exclusive_array(a);
    let sz = lean_array_size(r);
    if sz == 0 {
        return r;
    }
    let last = lean_array_cptr(r).add(sz - 1);
    crate::object::lean_dec(*last);
    lean_array_set_size(r, sz - 1);
    r
}

/// Swap two array elements (unboxed indices)
///
/// # Safety
/// - `a` must be a valid array object (consumed)
/// - `i` and `j` must be < array size
#[inline]
pub unsafe fn lean_array_uswap(a: lean_obj_arg, i: size_t, j: size_t) -> lean_obj_res {
    if i == j {
        return a;
    }

    let r = lean_ensure_exclusive_array(a);
    let ptr = lean_array_cptr(r);
    let v1 = *ptr.add(i);
    lean_array_set_core(r, i, *ptr.add(j));
    lean_array_set_core(r, j, v1);
    r
}

/// Swap two array elements (boxed indices)
///
/// # Safety
/// - `a` must be a valid array object (consumed)
/// - `i` and `j` must be boxed usize < array size
#[inline]
pub unsafe fn lean_array_fswap(
    a: lean_obj_arg,
    i: b_lean_obj_arg,
    j: b_lean_obj_arg,
) -> lean_obj_res {
    lean_array_uswap(
        a,
        crate::object::lean_unbox(i),
        crate::object::lean_unbox(j),
    )
}

/// Allocate an array with given size and capacity (low-level)
///
/// # Safety
/// - This is a low-level function that allocates memory
/// - The caller must initialize all elements up to `size`
/// - `capacity` must be >= `size`
#[inline]
pub unsafe fn lean_alloc_array(size: size_t, capacity: size_t) -> lean_obj_res {
    use crate::inline::{lean_array_object, lean_set_st_header};
    use crate::LEAN_ARRAY;

    let data_size = std::mem::size_of::<*mut lean_object>() * capacity;
    let total_size = std::mem::size_of::<lean_array_object>() + data_size;

    let ptr = crate::object::lean_alloc_object(total_size) as *mut lean_array_object;

    lean_set_st_header(&mut (*ptr).m_header as *mut lean_object, LEAN_ARRAY, 0);

    (*ptr).m_size = size;
    (*ptr).m_capacity = capacity;

    ptr as *mut lean_object
}

/// Create an empty array with no capacity
///
/// # Safety
/// - Returns a new empty array
#[inline]
pub unsafe fn lean_mk_empty_array() -> lean_obj_res {
    lean_alloc_array(0, 0)
}

/// Create an empty array with pre-allocated capacity
///
/// # Safety
/// - `capacity` must be a boxed usize (scalar value)
#[inline]
pub unsafe fn lean_mk_empty_array_with_capacity(capacity: b_lean_obj_arg) -> lean_obj_res {
    use crate::object::{lean_is_scalar, lean_unbox};

    // Declare extern panic function
    extern "C" {
        fn lean_internal_panic_out_of_memory() -> !;
    }

    if !lean_is_scalar(capacity) {
        lean_internal_panic_out_of_memory()
    }
    lean_alloc_array(0, lean_unbox(capacity))
}

// Re-export inline implementation from inline module
pub use crate::inline::lean_mk_empty_byte_array;

extern "C" {
    /// Push a byte to byte array
    pub fn lean_byte_array_push(a: lean_obj_arg, b: u8) -> lean_obj_res;
}
