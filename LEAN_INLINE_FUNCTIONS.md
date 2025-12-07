# Handling Lean4's Static Inline Functions

## The Challenge

Lean4's C API (`lean/lean.h`) defines many functions as `static inline`, which means:
- They don't exist as linkable symbols in `libleanshared.so`
- They can only be called from C code that `#include`s the header
- Rust FFI cannot directly call them

Examples of static inline functions:
- `lean_usize_to_nat`, `lean_usize_of_nat`
- `lean_nat_add`, `lean_nat_sub`, `lean_nat_mul`, `lean_nat_div`, `lean_nat_mod`
- `lean_nat_dec_eq`, `lean_nat_dec_lt`, `lean_nat_dec_le`
- `lean_string_cstr`, `lean_string_len`
- `lean_array_size`, `lean_array_get_core`
- `lean_is_scalar`, `lean_is_exclusive`
- `lean_inc_ref`, `lean_dec_ref`, `lean_inc`, `lean_dec`
- `lean_alloc_ctor`
- `lean_box`, `lean_unbox`
- And many more...

## Current Approach: Rust Inline

### How PyO3 Does It

PyO3 **manually re-implements** Python's C API inline functions directly in Rust:

```rust
#[inline]
pub unsafe fn PyList_GET_ITEM(op: *mut PyObject, i: Py_ssize_t) -> *mut PyObject {
    *(*(op as *mut PyListObject)).ob_item.offset(i)
}

#[inline(always)]
pub unsafe fn Py_INCREF(op: *mut PyObject) {
    #[cfg(not(any(Py_LIMITED_API, Py_GIL_DISABLED)))]
    {
        (*op).ob_refcnt += 1;
    }
    #[cfg(any(Py_LIMITED_API, Py_GIL_DISABLED))]
    {
        Py_IncRef(op);  // Calls exported function
    }
}
```

### Benefits

1. **No C compilation needed**: Pure Rust
2. **Better performance**: Direct inlining, no C call overhead
3. **Type safety**: Rust's type system catches errors
4. **Conditional compilation**: Easy to handle different Lean versions
5. **Full control**: Can add safety checks, better error handling

## Implementation Example

```rust
// In leo3-ffi/src/nat.rs
#[inline]
pub unsafe fn lean_usize_to_nat(n: size_t) -> lean_obj_res {
    if n < LEAN_MAX_SMALL_NAT {
        lean_box(n)
    } else {
        lean_alloc_big_nat(n)
    }
}

// Helper functions
#[inline(always)]
pub unsafe fn lean_box(n: size_t) -> lean_obj_res {
    (n << 1) as lean_obj_res
}
```

## Using Bindgen for Verification

Like PyO3's `pyo3-ffi-check`, we should use bindgen to:
1. Generate bindings from `lean/lean.h` for struct layouts
2. Verify our manual implementations match
3. NOT use bindgen for production code generation

This is what `leo3-ffi-check` is for!

## Action Items

1. **Short term**: Complete C wrappers for all currently needed functions
2. **Medium term**: Create Rust inline implementations for common functions
3. **Long term**: Full migration to PyO3-style pure Rust approach
4. **Always**: Use `leo3-ffi-check` with bindgen to verify correctness

## References

- PyO3 source: `/home/happy/work/pyo3/pyo3-ffi/`
  - See `src/refcount.rs`, `src/object.rs`, `src/cpython/listobject.rs`
- PyO3 FFI check: `/home/happy/work/pyo3/pyo3-ffi-check/`
- Lean4 headers: `~/.elan/toolchains/.../include/lean/lean.h`

## Conclusion

The C wrapper approach is a valid stepping stone, but PyO3 demonstrates that mature Rust FFI bindings use direct Rust inline implementations. We should plan to migrate Leo3 to this approach for long-term maintainability and performance.
