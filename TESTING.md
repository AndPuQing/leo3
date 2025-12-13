# Leo3 Testing Guide

Quick reference for testing Leo3, inspired by PyO3's testing infrastructure.

## Running Tests

### Quick Commands

```bash
# Run all tests (requires Lean4 runtime linked)
export LD_LIBRARY_PATH=~/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean:$LD_LIBRARY_PATH
cargo test

# Run only library tests (compile-time checks, no runtime needed)
LEO3_NO_LEAN=1 cargo test --lib

# Run specific test suite
cargo test --test nat_ops
cargo test --test string_ops
```

### Testing Without Lean4

Set `LEO3_NO_LEAN=1` to skip Lean4 detection and linking. This allows:
- ✅ Compilation checks
- ✅ Library unit tests (types, markers, etc.)
- ❌ Integration tests (require actual Lean4 runtime)

```bash
LEO3_NO_LEAN=1 cargo test --lib
LEO3_NO_LEAN=1 cargo check
```

## Test Organization

### Integration Tests (`leo3/tests/`)
- `basic.rs` - Runtime initialization and basic operations
- `string_ops.rs` - String operations
- `nat_ops.rs` - Natural number arithmetic
- `array_ops.rs` - Array operations
- `test_conversion.rs` - Type conversions
- `test_gc.rs` - Reference counting and memory management

### FFI Validation (`leo3-ffi-check/`)
- Verifies struct layouts match Lean4 headers using bindgen
- Runs automatically with `cargo test`

## Test Utilities

**Available macros:**
- `assert_lean_nat_eq!(a, b)` - Assert Lean nats are equal
- `assert_lean_string_eq!(a, b)` - Assert Lean strings are equal
- `assert_lean_nat_value!(nat, expected)` - Assert nat value
- `assert_lean_string_value!(str, expected)` - Assert string value
- `assert_lean_array_size!(arr, size)` - Assert array size

**Helper functions:**
- `with_lean_test(f)` - Run test with Lean runtime initialized

## Adding Tests

When adding new functionality:
1. Add unit tests in the implementation module
2. Add integration tests in `leo3/tests/`
3. Update FFI checks in `leo3-ffi-check/` if needed
4. Add examples demonstrating usage

## Architecture Notes

- **Inline Functions**: Leo3 follows PyO3's pattern of re-implementing static inline C functions in Rust (see `LEAN_INLINE_FUNCTIONS.md`)
- **FFI Validation**: Uses bindgen to verify struct layouts match Lean4 headers
- **Reference Counting**: Lean4 uses single-threaded RC by default; tests verify proper inc/dec behavior

## Troubleshooting

**"cannot open shared object file: libleanshared.so"**
```bash
export LD_LIBRARY_PATH=~/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean:$LD_LIBRARY_PATH
```

**"undefined symbol: lean_*"**
- Check if the function is a static inline (needs Rust implementation in `inline.rs`)
- Verify Lean4 is properly linked

**Windows: `link.exe` LNK2019/LNK1120 for `lean_mk_*` / `lean_constant_info_*`**
- Ensure the Lean toolchain’s `lib/lean` directory is on the linker search path (handled by `leo3-build-config`)
- Ensure Lean core libraries (e.g. `libLean.a` / `Lean.lib`) are present in the Lean installation and are being linked

**Compilation errors but Lean4 is installed**
- Use `LEO3_NO_LEAN=1` to isolate the issue
- Check `leo3-build-config` output for detection errors
