# Phase 6/7 Boundary Contract

## Status

The `conversion` and `#[leanclass]` support surface is now treated as a
documented contract instead of an inferred property of the current code.

## Conversion Matrix

Leo3's built-in conversion rules are:

| Rust shape | Lean shape | `IntoLean` | `FromLean` | Cost / ownership |
| --- | --- | --- | --- | --- |
| scalar primitives plus `()` | scalar wrappers / `Unit` | yes | yes | value conversion; Rust -> Lean allocates a Lean object |
| `String` | `String` | yes | yes | allocative copy |
| `&str` | `String` | yes | no | allocative copy into Lean only |
| `Vec<T>` | `Array` | yes | yes | allocates the container and converts elements recursively |
| `Option<T>` | `Option` | yes | yes | recursive container conversion |
| `Result<T, E>` | `Except E T` | yes | yes | recursive container conversion |
| `(A, B)` | `Prod A B` | yes | yes | recursive pair conversion |
| `Vec<u8>` / `&[u8]` helper path | `ByteArray` | helper only | helper only | bulk memcpy path, exposed through helper fns and conversion macros |
| `T: ExternalClass` | Lean external object | yes | yes, if `T: Clone` | stores owned Rust value in Lean; extraction clones the Rust value |

Formal rules:

- `FromLean` for external objects is intentionally clone-based. Borrow-based
  access is a separate API surface: `LeanExternal<T>::get_ref()`,
  `LeanExternal<T>::get_mut()`, and `take_inner()`.
- `Vec<u8>` uses helper functions instead of trait specialization on stable
  Rust. The optimized path is `vec_u8_into_lean`, `slice_u8_into_lean`,
  `vec_u8_from_lean`, `to_lean!(..., Vec<u8>)`, `to_lean!(..., &[u8])`, and
  `from_lean!(..., Vec<u8>)`.
- Proc-macro generated wrappers inherit this contract: parameter types must
  implement `FromLean`, and return types must implement `IntoLean`.
- `#[derive(IntoLean, FromLean)]` or manual impls can extend the Rust-side
  conversion set, but they do not automatically widen the `#[leanclass]`
  declaration grammar.

## `#[leanclass]` Receiver Matrix

`#[leanclass]` method receivers map to Lean-visible behavior as follows:

| Rust receiver | Lean-visible type rule | Runtime behavior |
| --- | --- | --- |
| no receiver | `A -> ... -> R` | static call, no external object parameter |
| `&self` | `Self -> A -> ... -> R` | shared borrow of the wrapped Rust value |
| `&mut self`, `-> ()` | `Self -> A -> ... -> Self` | copy-on-write mutation; updated object is returned |
| `&mut self`, `-> R` | `Self -> A -> ... -> Prod Self R` | copy-on-write mutation; updated object and return value are both preserved |
| `self` | `Self -> A -> ... -> R` | exclusive receiver moves out; shared receiver clones first |

Formal rules:

- Any class exposing `&mut self` or `self` methods must implement `Clone`,
  because shared-receiver fallbacks clone the Rust value.
- Methods returning `Self` are supported through the normal `IntoLean`
  conversion path for external objects.
- Generated Lean declaration strings describe runtime behavior literally; the
  mutation-preserving `Prod Self R` form is part of the contract.

## `#[leanclass]` Declaration Grammar

Generated Lean declarations support these Rust type shapes:

- scalar primitives, `bool`, `char`, `String`, and `()`
- `Self`, the current struct name, and other plain non-generic path types
- `Vec<T>`, `Option<T>`, and `Result<T, E>`
- pairs `(A, B)`

Generated Lean declarations intentionally reject these Rust type shapes:

- references such as `&str` or `&T`
- tuples with arity other than `0` or `2`
- generic path types other than `Vec<T>`, `Option<T>`, and `Result<T, E>`
- generic `#[leanclass]` structs
- generic `#[leanclass]` impl blocks
- generic methods inside `#[leanclass]` impls
- non-identifier parameter patterns

Plain non-generic path types are emitted verbatim into the Lean declaration
string. That is a declaration-format rule, not a promise that Leo3 defines or
initializes the corresponding Lean type automatically.

## Compile-Fail Matrix

These unsupported shapes are guarded by `trybuild` UI tests:

| Rule | UI test |
| --- | --- |
| generic `#[leanclass]` struct is rejected | `leo3/tests/ui/leanclass_generic_struct.rs` |
| generic `#[leanclass]` impl is rejected | `leo3/tests/ui/leanclass_generic_impl.rs` |
| generic `#[leanclass]` method is rejected | `leo3/tests/ui/leanclass_generic_method.rs` |
| non-identifier parameter pattern is rejected | `leo3/tests/ui/leanclass_unsupported_pattern.rs` |
| reference type in generated declaration is rejected | `leo3/tests/ui/leanclass_unsupported_ref.rs` |
| tuple arity other than pair is rejected | `leo3/tests/ui/leanclass_unsupported_tuple_arity.rs` |
| unsupported generic path type is rejected | `leo3/tests/ui/leanclass_unsupported_generic_type.rs` |

That matrix is the Phase 7 lock on the Phase 6 surface: if Leo3 widens or
narrows the boundary, the README, this document, and the UI suite must move
together.
