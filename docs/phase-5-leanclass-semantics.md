# Phase 5: Leanclass Semantics

## Status

First implementation pass completed.

## What Changed

### `&mut self -> ()`

This still returns the modified object on the Lean side.

### `&mut self -> T`

This no longer discards mutation state.

Generated wrappers now return:

- `Prod Self T`

That means Lean-visible semantics preserve both:

- the updated object
- the method's ordinary return value

## Why

The previous behavior returned only `T` and silently lost the updated external
object. That was a semantic bug in the binding layer.

## Validation

- runtime integration test verifies the returned `Prod` contains both the
  updated object and the returned value
- codegen tests verify the generated Lean declaration now uses
  `Prod Struct Return`
- macro pipeline example demonstrates the new shape

## Follow-Up

Possible next improvements:

- decide whether future Lean declaration generation should prefer a prettier
  notation like `Struct × Return` instead of `Prod Struct Return`
- expand tests for more complex return types and nested mutation flows
