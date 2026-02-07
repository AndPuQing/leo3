//! Core.Context construction for MetaM integration
//!
//! This module provides helper functions to construct Lean's Core.Context
//! with default values, which is required for running MetaM computations.
//!
//! Based on:
//! - `/lean4/src/Lean/CoreM.lean`
//! - Issue #26 - MetaM Integration Phase 1.2

use crate::err::LeanResult;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::meta::{LeanExpr, LeanName};
use crate::types::{LeanList, LeanOption, LeanString};
use leo3_ffi as ffi;

/// Core.Context - context for CoreM monad
///
/// This structure has 15 fields (constructor tag 0):
/// 0. `fileName: String` - use `"<rust>"`
/// 1. `fileMap: FileMap` - create empty
/// 2. `options: Options` - use empty
/// 3. `currRecDepth: Nat` - use 0
/// 4. `maxRecDepth: Nat` - use 1000
/// 5. `ref: Syntax` - use `Syntax.missing`
/// 6. `currNamespace: Name` - use anonymous
/// 7. `openDecls: List OpenDecl` - use empty list
/// 8. `initHeartbeats: Nat` - use 0
/// 9. `maxHeartbeats: Nat` - use 200000000
/// 10. `currMacroScope: MacroScope` - use default
/// 11. `diag: Bool` - use false
/// 12. `cancelTk?: Option IO.CancelToken` - use none
/// 13. `suppressElabErrors: Bool` - use false
/// 14. `inheritedTraceOptions: Std.HashSet Name` - use empty
#[repr(transparent)]
pub struct CoreContext {
    _private: (),
}

impl CoreContext {
    /// Create a Core.Context with default values
    ///
    /// This creates a minimal Core.Context suitable for running MetaM computations.
    /// All fields are set to sensible defaults:
    /// - fileName: "<rust>"
    /// - maxRecDepth: 1000
    /// - maxHeartbeats: 200000000
    /// - All other fields: empty/zero/false
    ///
    /// # Example
    ///
    /// ```ignore
    /// use leo3::prelude::*;
    /// use leo3::meta::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let ctx = CoreContext::mk_default(lean)?;
    ///     Ok(())
    /// })
    /// ```
    pub fn mk_default<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Core.Context has 15 fields (constructor tag 0)
            let ctx = ffi::lean_alloc_ctor(0, 15, 0);

            // Field 0: fileName (String) - use "<rust>"
            let filename = LeanString::mk(lean, "<rust>")?;
            ffi::lean_ctor_set(ctx, 0, filename.into_ptr());

            // Field 1: fileMap (FileMap) - create empty
            let filemap = Self::mk_empty_filemap(lean)?;
            ffi::lean_ctor_set(ctx, 1, filemap.into_ptr());

            // Field 2: options (Options) - use empty
            let options = Self::mk_empty_options(lean)?;
            ffi::lean_ctor_set(ctx, 2, options.into_ptr());

            // Field 3: currRecDepth (Nat) - use 0
            let curr_rec_depth = ffi::lean_box(0);
            ffi::lean_ctor_set(ctx, 3, curr_rec_depth);

            // Field 4: maxRecDepth (Nat) - use 1000
            let max_rec_depth = ffi::lean_box(1000);
            ffi::lean_ctor_set(ctx, 4, max_rec_depth);

            // Field 5: ref (Syntax) - use Syntax.missing
            let syntax_missing = Self::mk_syntax_missing(lean)?;
            ffi::lean_ctor_set(ctx, 5, syntax_missing.into_ptr());

            // Field 6: currNamespace (Name) - use anonymous
            let anon_name = LeanName::anonymous(lean)?;
            ffi::lean_ctor_set(ctx, 6, anon_name.into_ptr());

            // Field 7: openDecls (List OpenDecl) - use empty list
            let empty_list = LeanList::nil(lean)?;
            ffi::lean_ctor_set(ctx, 7, empty_list.into_ptr());

            // Field 8: initHeartbeats (Nat) - use 0
            let init_heartbeats = ffi::lean_box(0);
            ffi::lean_ctor_set(ctx, 8, init_heartbeats);

            // Field 9: maxHeartbeats (Nat) - use 200000000
            let max_heartbeats = ffi::lean_box(200000000);
            ffi::lean_ctor_set(ctx, 9, max_heartbeats);

            // Field 10: currMacroScope (MacroScope) - use default (0)
            let macro_scope = ffi::lean_box(0);
            ffi::lean_ctor_set(ctx, 10, macro_scope);

            // Field 11: diag (Bool) - use false
            let diag = ffi::lean_box(0); // false
            ffi::lean_ctor_set(ctx, 11, diag);

            // Field 12: cancelTk? (Option IO.CancelToken) - use none
            let cancel_token = LeanOption::none(lean)?;
            ffi::lean_ctor_set(ctx, 12, cancel_token.into_ptr());

            // Field 13: suppressElabErrors (Bool) - use false
            let suppress_elab = ffi::lean_box(0); // false
            ffi::lean_ctor_set(ctx, 13, suppress_elab);

            // Field 14: inheritedTraceOptions (Std.HashSet Name) - use empty
            let empty_hashset = Self::mk_empty_hashset(lean)?;
            ffi::lean_ctor_set(ctx, 14, empty_hashset.into_ptr());

            Ok(LeanBound::from_owned_ptr(lean, ctx))
        }
    }

    /// Create an empty FileMap
    ///
    /// FileMap is a structure that maps positions in a file to line/column information.
    /// For now, we create a minimal empty FileMap.
    ///
    /// Based on Lean.Data.Position.FileMap structure:
    /// - source: String (empty)
    /// - positions: Array Nat (empty array)
    fn mk_empty_filemap<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        unsafe {
            // FileMap is a structure with 2 fields (constructor tag 0)
            let filemap = ffi::lean_alloc_ctor(0, 2, 0);

            // Field 0: source (String) - empty string
            let empty_source = LeanString::mk(lean, "")?;
            ffi::lean_ctor_set(filemap, 0, empty_source.into_ptr());

            // Field 1: positions (Array Nat) - empty array
            // Create empty array
            let empty_array = ffi::array::lean_mk_empty_array();
            ffi::lean_ctor_set(filemap, 1, empty_array);

            Ok(LeanBound::from_owned_ptr(lean, filemap))
        }
    }

    /// Create empty Options
    ///
    /// Options is Lean's key-value store for configuration.
    /// For now, we use lean_box(0) which represents an empty options object.
    fn mk_empty_options<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        unsafe {
            // Empty options is represented as lean_box(0)
            let options = ffi::lean_box(0);
            Ok(LeanBound::from_owned_ptr(lean, options))
        }
    }

    /// Create Syntax.missing
    ///
    /// Syntax.missing is a placeholder syntax node used when no specific
    /// syntax reference is available.
    ///
    /// Based on Lean.Syntax structure, Syntax.missing is typically
    /// represented as a specific constructor.
    fn mk_syntax_missing<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        unsafe {
            // Syntax.missing is constructor 0 with no fields
            // This is a simplified representation - the actual Lean implementation
            // may be more complex, but this should work for basic MetaM operations
            let syntax = ffi::lean_alloc_ctor(0, 0, 0);
            Ok(LeanBound::from_owned_ptr(lean, syntax))
        }
    }

    /// Create an empty HashSet
    ///
    /// Creates an empty Std.HashSet for the inheritedTraceOptions field.
    fn mk_empty_hashset<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        unsafe {
            // Empty HashSet is typically represented as a constructor with empty buckets
            // For simplicity, we use lean_box(0) which should work for an empty set
            let hashset = ffi::lean_box(0);
            Ok(LeanBound::from_owned_ptr(lean, hashset))
        }
    }
}
