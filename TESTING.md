# Leo3 Testing Guide

Quick reference for testing Leo3, inspired by PyO3's testing infrastructure.

## Running Tests

### Quick Commands

```bash
# Run all tests (requires Lean4 runtime linked)
export LD_LIBRARY_PATH=~/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean:$LD_LIBRARY_PATH
cargo test --all-features

# Run only library checks without Lean4
LEO3_NO_LEAN=1 cargo test --lib

# Run specific feature-scoped suites
cargo test --no-default-features --test test_features
cargo test --no-default-features --features meta --test meta_basic
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

## Lean Discovery Order

Build scripts share the same strict precedence rules:

1. `LEO3_NO_LEAN=1` short-circuits detection and linking.
2. If present, `DEP_LEAN4_LEO3_CONFIG` wins.
3. Otherwise `LEO3_CONFIG_FILE` provides an explicit config file.
4. Otherwise host discovery tries `LEO3_CROSS_LIB_DIR` + `LEO3_CROSS_LEAN_VERSION`, then `LEAN_HOME`, then `lake`, then `elan`, then `PATH`.

Explicit higher-priority inputs are authoritative: if `DEP_LEAN4_LEO3_CONFIG`, `LEO3_CONFIG_FILE`, `LEO3_CROSS_*`, `LEAN_HOME`, `LEAN_LIB_DIR`, or `LEAN_INCLUDE_DIR` is set but invalid, Leo3 reports that error instead of silently falling back.

`leo3-ffi` resolves the config first and re-exports it as `DEP_LEAN4_LEO3_CONFIG`; `leo3` intentionally consumes that propagated value so both crates use identical cfg flags.

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
- Check the `cargo:warning=` lines from `leo3-build-config`; they now list each attempted source in order
- If you want to bypass host discovery, set `LEO3_CONFIG_FILE=/path/to/leo3-build-config.txt`
- Use `LEO3_NO_LEAN=1` to isolate the issue
- Check `leo3-build-config` output for detection errors
