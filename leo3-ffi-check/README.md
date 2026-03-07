# leo3-ffi-check

FFI validation tool for Leo3, ensuring our hand-written FFI bindings match Lean4's actual C API.

## Purpose

This crate is inspired by PyO3's `pyo3-ffi-check` and serves to:

1. **Validate struct layouts**: Ensures our `lean_object` and related runtime structs match the actual sizes and alignments in Lean4's headers.
2. **Check type aliases**: Verifies pointer-like FFI aliases still have the expected ABI shape.
3. **Check critical function signatures**: Verifies runtime/thread initialization and selected module initializer signatures against bindgen output.
4. **Prevent ABI breakage**: Catches mismatches that could cause crashes or undefined behavior.
5. **Support multiple Lean versions**: Can validate against different Lean4 versions.

## How It Works

1. **Build script**: Uses `bindgen` to generate Rust bindings directly from `lean/lean.h`.
2. **Layout tests**: Compares sizes, alignments, and field offsets between our hand-written FFI and bindgen's output.
3. **Signature tests**: Coerces our declarations and bindgen declarations to the same function-pointer types.
4. **Validation**: Fails the test run with a non-zero exit code if any mismatch is detected.

## Running

```bash
# Run FFI validation checks from the workspace root
cargo test --manifest-path leo3-ffi-check/Cargo.toml

# With specific Lean4 headers
LEAN_INCLUDE_DIR=/path/to/lean/include cargo test --manifest-path leo3-ffi-check/Cargo.toml
```

If Lean is installed through `elan`, you may also need Lean's shared library directory on the runtime loader path when executing the tests:

```bash
LEAN_PREFIX="$("$HOME"/.elan/bin/lean --print-prefix)"
LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean" cargo test --manifest-path leo3-ffi-check/Cargo.toml
```

The CI workflow uses the same pattern so mismatches fail the job.

## Requirements

- **bindgen**: For generating bindings from C headers.
- **Lean4 headers**: Must have `lean/lean.h` accessible.
- **Lean4 shared libraries**: Needed when executing the generated test binaries.
- **libclang**: Required by bindgen for parsing C headers.

## Environment Variables

- `LEAN_INCLUDE_DIR`: Path to directory containing `lean/lean.h`.
- If not set, checks common locations:
  - `/usr/local/include`
  - `/usr/include`
  - `/opt/homebrew/include`
  - Lean paths discovered by `leo3-build-config`

## What Gets Checked

### Structures
- [x] `lean_object` - Core Lean object struct (size, alignment, `m_rc` offset)
- [x] `lean_array_object`
- [x] `lean_string_object`
- [x] `lean_closure_object`
- [x] `lean_ctor_object`
- [x] `lean_sarray_object`
- [x] `lean_ref_object`
- [x] `lean_thunk_object`
- [x] `lean_task_imp`
- [x] `lean_task_object`
- [x] `lean_promise_object`
- [x] `lean_external_object`

### Type Aliases
- [x] `lean_obj_arg`
- [x] `b_lean_obj_arg`
- [x] `lean_obj_res`
- [x] `b_lean_obj_res`

### Constants
- [x] `LEAN_MAX_CTOR_TAG`
- [x] `LEAN_CLOSURE`
- [x] `LEAN_ARRAY`
- [x] `LEAN_STRING`
- [x] `LEAN_TASK`
- [x] `LEAN_EXTERNAL`

### Functions
- [x] `lean_initialize_runtime_module`
- [x] `lean_finalize_runtime_module`
- [x] `lean_initialize_thread`
- [x] `lean_finalize_thread`
- [x] `initialize_Lean_Expr`
- [x] `initialize_Init_Prelude`
- [x] `initialize_Lean_Environment`
- [x] `initialize_Lean_Meta`

## Why This Matters

FFI bugs are hard to debug and can cause:

- **Segmentation faults** from incorrect struct layouts.
- **Memory corruption** from wrong field offsets.
- **Undefined behavior** from ABI mismatches.
- **Version drift** that only appears after upgrading Lean.

By validating against the actual headers, we catch these issues at compile/test time instead of runtime in Leo3 itself.

## Limitations

- **Function coverage is intentionally selective**: We currently focus on the most drift-prone initialization signatures rather than every exported symbol.
- **Preprocessor macros**: Some Lean macros may not be captured by bindgen.
- **Inline functions**: Header-only inline functions still require manual Rust implementations and separate behavioral review.

## Future Improvements

- [ ] Validate more structs from `lean.h`.
- [x] Check field offsets in addition to sizes.
- [x] Validate critical function signatures.
- [ ] Validate more function pointer types.
- [ ] Support multiple Lean4 versions in a dedicated matrix.
- [x] Run automatically in GitHub Actions via the `ffi-check` job.

## Related

- **leo3-ffi**: The actual FFI bindings this validates.
- **leo3-build-config**: Detects Lean4 installation.
- **PyO3's pyo3-ffi-check**: Inspiration for this approach.
