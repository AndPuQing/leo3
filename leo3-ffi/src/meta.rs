//! FFI bindings for Lean's MetaM monad
//!
//! This module provides raw C FFI bindings for working with Lean's MetaM monad,
//! which is used for meta-level operations like type inference and type checking.
//!
//! Based on:
//! - `/lean4/src/Lean/Meta/Basic.lean`
//! - `/lean4/src/Lean/Meta/InferType.lean`
//! - `/lean4/src/Lean/Meta/Check.lean`

use super::*;

// ============================================================================
// MetaM Monad Functions
// ============================================================================

// In Lean < 4.22, the reduced-arity suffix is `_rarg`.
// In Lean >= 4.22, it was renamed to `_redArg`.
#[cfg(not(lean_4_22))]
extern "C" {
    /// Run a MetaM computation (Lean < 4.22)
    ///
    /// `Lean.Meta.MetaM.run' : MetaM α → Meta.Context → Meta.State → CoreM α`
    ///
    /// The compiled `_rarg` version takes 6 arguments:
    /// 1. `x`: MetaM computation (closure)
    /// 2. `ctx`: Meta.Context
    /// 3. `state`: Meta.State (raw — wrapped in ST.Ref internally)
    /// 4. `core_ctx`: Core.Context
    /// 5. `core_state_ref`: ST.Ref Core.State (must be created via `lean_st_mk_ref`)
    /// 6. `world`: IO world token (`lean_box(0)`)
    pub fn l_Lean_Meta_MetaM_run_x27___rarg(
        x: lean_obj_arg,
        ctx: lean_obj_arg,
        state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state_ref: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;
}

#[cfg(all(lean_4_22, not(lean_4_26)))]
extern "C" {
    /// Run a MetaM computation (Lean 4.22..4.25)
    ///
    /// Same as `l_Lean_Meta_MetaM_run_x27___rarg` but for Lean >= 4.22.
    pub fn l_Lean_Meta_MetaM_run_x27___redArg(
        x: lean_obj_arg,
        ctx: lean_obj_arg,
        state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state_ref: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;
}

#[cfg(lean_4_26)]
extern "C" {
    /// Run a MetaM computation (Lean >= 4.26)
    ///
    /// In Lean 4.26+, the IO world token was removed from the calling convention.
    /// The function internally creates the Meta.State ST.Ref and uses `lean_box(0)`
    /// as the world token.
    pub fn l_Lean_Meta_MetaM_run_x27___redArg(
        x: lean_obj_arg,
        ctx: lean_obj_arg,
        state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state_ref: lean_obj_arg,
    ) -> lean_obj_res;
}

/// Run a MetaM computation, dispatching to the correct symbol for the Lean version.
///
/// In Lean < 4.26, the caller must provide an IO world token and an ST.Ref for Core.State.
/// In Lean >= 4.26, the world token was removed from the calling convention.
///
/// # Safety
/// - `x` must be a valid MetaM computation (consumed)
/// - `ctx` must be a valid Meta.Context object (consumed)
/// - `state` must be a valid Meta.State object (raw, consumed)
/// - `core_ctx` must be a valid Core.Context object (consumed)
/// - `core_state_ref` must be an ST.Ref wrapping Core.State (created via `lean_st_mk_ref`)
/// - `world` must be an IO world token (typically `lean_box(0)`) — ignored in Lean >= 4.26
#[inline]
pub unsafe fn lean_meta_metam_run(
    x: lean_obj_arg,
    ctx: lean_obj_arg,
    state: lean_obj_arg,
    core_ctx: lean_obj_arg,
    core_state_ref: lean_obj_arg,
    world: lean_obj_arg,
) -> lean_obj_res {
    #[cfg(not(lean_4_22))]
    {
        l_Lean_Meta_MetaM_run_x27___rarg(x, ctx, state, core_ctx, core_state_ref, world)
    }
    #[cfg(all(lean_4_22, not(lean_4_26)))]
    {
        l_Lean_Meta_MetaM_run_x27___redArg(x, ctx, state, core_ctx, core_state_ref, world)
    }
    #[cfg(lean_4_26)]
    {
        // In Lean 4.26+, the world token is no longer passed as an argument.
        // The function handles it internally.
        let _ = world;
        l_Lean_Meta_MetaM_run_x27___redArg(x, ctx, state, core_ctx, core_state_ref)
    }
}

extern "C" {
    /// Infer the type of an expression
    ///
    /// `@[extern 6 "lean_infer_type"] opaque inferType : Expr → MetaM Expr`
    ///
    /// Takes 6 arguments: expr, meta_ctx, meta_state_ref, core_ctx, core_state_ref, world
    /// Returns an EIO result (Except Exception Expr) packed with the IO world.
    ///
    /// # Safety
    /// - All arguments must be valid Lean objects (consumed)
    pub fn lean_infer_type(
        expr: lean_obj_arg,
        meta_ctx: lean_obj_arg,
        meta_state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Type check an expression
    ///
    /// `def check (e : Expr) : MetaM Unit`
    ///
    /// Compiled by Lean's compiler. Takes 6 arguments like other MetaM functions:
    /// expr, meta_ctx, meta_state_ref, core_ctx, core_state_ref, world
    ///
    /// # Safety
    /// - All arguments must be valid Lean objects (consumed)
    pub fn l_Lean_Meta_check(
        expr: lean_obj_arg,
        meta_ctx: lean_obj_arg,
        meta_state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Reduce an expression to weak head normal form
    ///
    /// `@[export lean_whnf] partial def whnfImp (e : Expr) : MetaM Expr`
    ///
    /// Takes 6 arguments: expr, meta_ctx, meta_state_ref, core_ctx, core_state_ref, world
    ///
    /// # Safety
    /// - All arguments must be valid Lean objects (consumed)
    pub fn lean_whnf(
        expr: lean_obj_arg,
        meta_ctx: lean_obj_arg,
        meta_state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Check if two expressions are definitionally equal
    ///
    /// `@[extern 7 "lean_is_expr_def_eq"] opaque isExprDefEqAux : Expr → Expr → MetaM Bool`
    ///
    /// Takes 7 arguments: expr_a, expr_b, meta_ctx, meta_state_ref, core_ctx, core_state_ref, world
    /// Returns MetaM Bool — the Bool is a Lean Bool (lean_box(0) = false, lean_box(1) = true)
    ///
    /// # Safety
    /// - All arguments must be valid Lean objects (consumed)
    pub fn lean_is_expr_def_eq(
        a: lean_obj_arg,
        b: lean_obj_arg,
        meta_ctx: lean_obj_arg,
        meta_state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;
}

// ============================================================================
// Inhabited Instances (default values for Meta types)
// ============================================================================
//
// These are global variables set during `initialize_Lean_Meta`. They hold
// properly constructed default values for various Meta types. Reading them
// avoids the need to manually construct complex structures from Rust.
//
// On Linux/macOS, shared libraries export all symbols by default, so we use
// `extern static` declarations (zero overhead).
//
// On Windows, BSS globals are NOT exported from DLLs. All accessor functions
// return null, and callers (in context.rs) fall back to manual construction.

#[cfg(not(target_os = "windows"))]
extern "C" {
    pub static l_Lean_Meta_instInhabitedConfig: *mut lean_object;
    #[cfg(lean_4_25)]
    pub static l_Lean_Meta_instInhabitedContext: *mut lean_object;
    pub static l_Lean_Meta_instInhabitedState: *mut lean_object;
    pub static l_Lean_Meta_instInhabitedCache: *mut lean_object;
    pub static l_Lean_Meta_instInhabitedDiagnostics: *mut lean_object;
    pub static l_Lean_instInhabitedMetavarContext: *mut lean_object;
    pub static l_Lean_instInhabitedLocalContext: *mut lean_object;
    pub static l_Lean_instInhabitedTraceState: *mut lean_object;
    pub static l_Lean_Core_instInhabitedCache: *mut lean_object;
    pub static l_Lean_Elab_instInhabitedInfoState: *mut lean_object;
    #[cfg(not(lean_4_28))]
    pub static l_Lean_instInhabitedOptions: *mut lean_object;
    #[cfg(lean_4_28)]
    pub static l_Lean_Options_instInhabited: *mut lean_object;
    pub static l_Lean_instInhabitedMessageLog: *mut lean_object;
    pub static l_Lean_instInhabitedNameGenerator: *mut lean_object;
    #[cfg(lean_4_25)]
    pub static l_Lean_instInhabitedDeclNameGenerator: *mut lean_object;
    pub static l_Lean_instInhabitedSyntax: *mut lean_object;
    pub static l_Lean_instInhabitedFileMap: *mut lean_object;
    // Building-block symbols for PersistentHashMap/PersistentArray/KVMap
    pub static l_Lean_PersistentHashMap_empty: *mut lean_object;
    pub static l_Lean_PersistentArray_empty: *mut lean_object;
    pub static l_Lean_KVMap_empty: *mut lean_object;
}

// ============================================================================
// Cross-platform accessor functions
// ============================================================================
//
// On non-Windows these read the extern statics directly (zero cost).
// On Windows they return null — callers must handle this with manual fallbacks.

// Helper macro: on non-Windows read the extern static, on Windows return null.
macro_rules! bss_accessor {
    ($(#[$meta:meta])* $vis:vis fn $name:ident() -> $sym:ident) => {
        $(#[$meta])*
        #[inline]
        $vis unsafe fn $name() -> *mut lean_object {
            #[cfg(not(target_os = "windows"))]
            { $sym }
            #[cfg(target_os = "windows")]
            { std::ptr::null_mut() }
        }
    };
}

bss_accessor!(/// Get the default `Meta.Config`.
    pub fn get_instInhabitedConfig() -> l_Lean_Meta_instInhabitedConfig);

#[cfg(lean_4_25)]
bss_accessor!(/// Get the default `Meta.Context` (Lean >= 4.25).
    pub fn get_instInhabitedContext() -> l_Lean_Meta_instInhabitedContext);

bss_accessor!(/// Get the default `Meta.State`.
    pub fn get_instInhabitedState() -> l_Lean_Meta_instInhabitedState);

bss_accessor!(/// Get the default `Meta.Cache`.
    pub fn get_instInhabitedCache() -> l_Lean_Meta_instInhabitedCache);

bss_accessor!(/// Get the default `Meta.Diagnostics`.
    pub fn get_instInhabitedDiagnostics() -> l_Lean_Meta_instInhabitedDiagnostics);

bss_accessor!(/// Get the default `MetavarContext`.
    pub fn get_instInhabitedMetavarContext() -> l_Lean_instInhabitedMetavarContext);

bss_accessor!(/// Get the default `LocalContext`.
    pub fn get_instInhabitedLocalContext() -> l_Lean_instInhabitedLocalContext);

bss_accessor!(/// Get the default `TraceState`.
    pub fn get_instInhabitedTraceState() -> l_Lean_instInhabitedTraceState);

bss_accessor!(/// Get the default `Core.Cache`.
    pub fn get_CoreInstInhabitedCache() -> l_Lean_Core_instInhabitedCache);

bss_accessor!(/// Get the default `Elab.InfoState`.
    pub fn get_ElabInstInhabitedInfoState() -> l_Lean_Elab_instInhabitedInfoState);

bss_accessor!(/// Get the default `MessageLog`.
    pub fn get_instInhabitedMessageLog() -> l_Lean_instInhabitedMessageLog);

bss_accessor!(/// Get the default `NameGenerator`.
    pub fn get_instInhabitedNameGenerator() -> l_Lean_instInhabitedNameGenerator);

#[cfg(lean_4_25)]
bss_accessor!(/// Get the default `DeclNameGenerator` (Lean >= 4.25).
    pub fn get_instInhabitedDeclNameGenerator() -> l_Lean_instInhabitedDeclNameGenerator);

bss_accessor!(/// Get the default `Syntax` (`Syntax.missing`).
    pub fn get_instInhabitedSyntax() -> l_Lean_instInhabitedSyntax);

bss_accessor!(/// Get the default `FileMap`.
    pub fn get_instInhabitedFileMap() -> l_Lean_instInhabitedFileMap);

/// Get the default `Options` / `KVMap` (empty), dispatching to the correct
/// symbol for the Lean version.
///
/// In Lean < 4.28 the symbol is `l_Lean_instInhabitedOptions`.
/// In Lean >= 4.28 it was renamed to `l_Lean_Options_instInhabited`.
#[inline]
pub unsafe fn lean_inhabited_options() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        #[cfg(not(lean_4_28))]
        {
            l_Lean_instInhabitedOptions
        }
        #[cfg(lean_4_28)]
        {
            l_Lean_Options_instInhabited
        }
    }
    #[cfg(target_os = "windows")]
    {
        std::ptr::null_mut()
    }
}

/// Get the empty `PersistentHashMap` singleton.
///
/// On non-Windows, reads the BSS global directly.
/// On Windows, manually constructs the value (cached via `OnceLock`).
///
/// Layout: `PersistentHashMap.mk (Node.entries (mkArray 32 Entry.null)) 0`
pub unsafe fn get_PersistentHashMapEmpty() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_PersistentHashMap_empty
    }
    #[cfg(target_os = "windows")]
    {
        use std::sync::OnceLock;
        static CACHED: OnceLock<usize> = OnceLock::new();
        let ptr = *CACHED.get_or_init(|| {
            // Entry.null = lean_box(2) (tag 2, 0 fields → scalar)
            let entries = crate::array::lean_mk_array(lean_box(32), lean_box(2));
            // Node.entries: ctor tag 0, 1 obj field
            let node = crate::lean_alloc_ctor(0, 1, 0);
            lean_ctor_set(node, 0, entries);
            // PersistentHashMap.mk: ctor tag 0, 2 obj fields
            let phm = crate::lean_alloc_ctor(0, 2, 0);
            lean_ctor_set(phm, 0, node);
            lean_ctor_set(phm, 1, lean_box(0)); // size = 0
            phm as usize
        });
        ptr as *mut lean_object
    }
}

/// Get the empty `PersistentArray` singleton.
///
/// On non-Windows, reads the BSS global directly.
/// On Windows, manually constructs the value (cached via `OnceLock`).
///
/// Layout: `PersistentArray.mk (Node.node #[]) #[] 0 initShift 0`
pub unsafe fn get_PersistentArrayEmpty() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_PersistentArray_empty
    }
    #[cfg(target_os = "windows")]
    {
        use std::sync::OnceLock;
        static CACHED: OnceLock<usize> = OnceLock::new();
        let ptr = *CACHED.get_or_init(|| {
            // PersistentArrayNode.node: ctor tag 0, 1 obj field (children: Array)
            let root_node = crate::lean_alloc_ctor(0, 1, 0);
            lean_ctor_set(root_node, 0, crate::array::lean_mk_empty_array());
            // PersistentArray: ctor tag 0, 4 obj fields, 4 scalar bytes (shift: UInt32)
            let pa = crate::lean_alloc_ctor(0, 4, 4);
            lean_ctor_set(pa, 0, root_node); // root
            lean_ctor_set(pa, 1, crate::array::lean_mk_empty_array()); // tail
            lean_ctor_set(pa, 2, lean_box(0)); // size = 0
            lean_ctor_set(pa, 3, lean_box(0)); // tailOff = 0
            lean_ctor_set_uint32(pa, 0, 5); // shift = initShift = 5
            pa as usize
        });
        ptr as *mut lean_object
    }
}

/// Get the empty `KVMap` (Options) singleton.
///
/// On non-Windows, reads the BSS global directly.
/// On Windows, returns `lean_box(0)` — KVMap.empty is a zero-field enum (tag 0).
#[inline]
pub unsafe fn get_KVMapEmpty() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_KVMap_empty
    }
    #[cfg(target_os = "windows")]
    {
        lean_box(0)
    }
}

// ============================================================================
// MetaM Tactic-Supporting Operations
// ============================================================================

extern "C" {
    /// Check if two levels are definitionally equal
    ///
    /// `@[extern "lean_is_level_def_eq"] opaque isLevelDefEqAux : Level → Level → MetaM Bool`
    ///
    /// Takes 7 arguments: level_a, level_b, meta_ctx, meta_state, core_ctx, core_state, world
    /// Returns MetaM Bool — the Bool is a Lean Bool (lean_box(0) = false, lean_box(1) = true)
    ///
    /// # Safety
    /// - All arguments must be valid Lean objects (consumed)
    pub fn lean_is_level_def_eq(
        a: lean_obj_arg,
        b: lean_obj_arg,
        meta_ctx: lean_obj_arg,
        meta_state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Synthesize a pending metavariable (e.g., typeclass instance)
    ///
    /// `@[extern "lean_synth_pending"] protected opaque synthPending : MVarId → MetaM Bool`
    ///
    /// Takes 6 arguments: mvarId, meta_ctx, meta_state, core_ctx, core_state, world
    ///
    /// # Safety
    /// - All arguments must be valid Lean objects (consumed)
    pub fn lean_synth_pending(
        mvar_id: lean_obj_arg,
        meta_ctx: lean_obj_arg,
        meta_state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;

    /// Assign a metavariable with type-checking validation
    ///
    /// `@[extern "lean_checked_assign"] opaque Lean.MVarId.checkedAssign (mvarId : MVarId) (val : Expr) : MetaM Bool`
    ///
    /// Takes 7 arguments: mvarId, val, meta_ctx, meta_state, core_ctx, core_state, world
    /// Returns MetaM Bool — true if assignment succeeded
    ///
    /// # Safety
    /// - All arguments must be valid Lean objects (consumed)
    pub fn lean_checked_assign(
        mvar_id: lean_obj_arg,
        val: lean_obj_arg,
        meta_ctx: lean_obj_arg,
        meta_state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state: lean_obj_arg,
        world: lean_obj_arg,
    ) -> lean_obj_res;
}

// ============================================================================
// MetavarContext Operations (pure, non-monadic)
// ============================================================================

extern "C" {
    /// Create an empty MetavarContext
    ///
    /// `@[export lean_mk_metavar_ctx] def mkMetavarContext : Unit → MetavarContext`
    ///
    /// # Safety
    /// - `unit` must be `lean_box(0)`
    pub fn lean_mk_metavar_ctx(unit: lean_obj_arg) -> lean_obj_res;

    /// Get the assignment for an expression metavariable
    ///
    /// `@[export lean_get_mvar_assignment] def MetavarContext.getExprAssignmentExp (m : MetavarContext) (mvarId : MVarId) : Option Expr`
    ///
    /// Returns `Option Expr` — `none` (lean_box(0)) or `some expr` (ctor tag 1, field 0 = expr)
    ///
    /// # Safety
    /// - `mctx` must be a valid MetavarContext (borrowed)
    /// - `mvar_id` must be a valid MVarId (borrowed)
    pub fn lean_get_mvar_assignment(mctx: b_lean_obj_arg, mvar_id: b_lean_obj_arg) -> lean_obj_res;

    /// Get the assignment for a level metavariable
    ///
    /// `@[export lean_get_lmvar_assignment] def getLevelMVarAssignmentExp (m : MetavarContext) (mvarId : LMVarId) : Option Level`
    ///
    /// # Safety
    /// - `mctx` must be a valid MetavarContext (borrowed)
    /// - `mvar_id` must be a valid LMVarId (borrowed)
    pub fn lean_get_lmvar_assignment(mctx: b_lean_obj_arg, mvar_id: b_lean_obj_arg)
        -> lean_obj_res;

    /// Get the delayed assignment for a metavariable
    ///
    /// `@[export lean_get_delayed_mvar_assignment] def MetavarContext.getDelayedMVarAssignmentExp (mctx : MetavarContext) (mvarId : MVarId) : Option DelayedMetavarAssignment`
    ///
    /// # Safety
    /// - `mctx` must be a valid MetavarContext (borrowed)
    /// - `mvar_id` must be a valid MVarId (borrowed)
    pub fn lean_get_delayed_mvar_assignment(
        mctx: b_lean_obj_arg,
        mvar_id: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// Assign an expression metavariable (low-level, no checking)
    ///
    /// `@[export lean_assign_mvar] def assignExp (m : MetavarContext) (mvarId : MVarId) (val : Expr) : MetavarContext`
    ///
    /// # Safety
    /// - `mctx` must be a valid MetavarContext (consumed)
    /// - `mvar_id` must be a valid MVarId (consumed)
    /// - `val` must be a valid Expr (consumed)
    pub fn lean_assign_mvar(
        mctx: lean_obj_arg,
        mvar_id: lean_obj_arg,
        val: lean_obj_arg,
    ) -> lean_obj_res;

    /// Assign a level metavariable (low-level, no checking)
    ///
    /// `@[export lean_assign_lmvar] def assignLevelMVarExp (m : MetavarContext) (mvarId : LMVarId) (val : Level) : MetavarContext`
    ///
    /// # Safety
    /// - `mctx` must be a valid MetavarContext (consumed)
    /// - `mvar_id` must be a valid LMVarId (consumed)
    /// - `val` must be a valid Level (consumed)
    pub fn lean_assign_lmvar(
        mctx: lean_obj_arg,
        mvar_id: lean_obj_arg,
        val: lean_obj_arg,
    ) -> lean_obj_res;

    /// Instantiate expression metavariables in an expression
    ///
    /// `@[extern "lean_instantiate_expr_mvars"] opaque instantiateExprMVarsImp (mctx : MetavarContext) (e : Expr) : MetavarContext × Expr`
    ///
    /// Returns a pair (MetavarContext, Expr) — the updated mctx and the instantiated expression.
    ///
    /// # Safety
    /// - `mctx` must be a valid MetavarContext (consumed)
    /// - `expr` must be a valid Expr (consumed)
    pub fn lean_instantiate_expr_mvars(mctx: lean_obj_arg, expr: lean_obj_arg) -> lean_obj_res;

    /// Instantiate level metavariables in a level
    ///
    /// `@[extern "lean_instantiate_level_mvars"] opaque instantiateLevelMVarsImp (mctx : MetavarContext) (l : Level) : MetavarContext × Level`
    ///
    /// Returns a pair (MetavarContext, Level) — the updated mctx and the instantiated level.
    ///
    /// # Safety
    /// - `mctx` must be a valid MetavarContext (consumed)
    /// - `level` must be a valid Level (consumed)
    pub fn lean_instantiate_level_mvars(mctx: lean_obj_arg, level: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// LocalContext Operations (pure, non-monadic)
// ============================================================================

extern "C" {
    /// Create an empty LocalContext
    ///
    /// `@[export lean_mk_empty_local_ctx] def mkEmpty : Unit → LocalContext`
    ///
    /// # Safety
    /// - `unit` must be `lean_box(0)`
    pub fn lean_mk_empty_local_ctx(unit: lean_obj_arg) -> lean_obj_res;

    /// Check if a LocalContext is empty
    ///
    /// `@[export lean_local_ctx_is_empty] def isEmpty (lctx : LocalContext) : Bool`
    ///
    /// # Safety
    /// - `lctx` must be a valid LocalContext (borrowed)
    pub fn lean_local_ctx_is_empty(lctx: b_lean_obj_arg) -> u8;

    /// Add a local declaration to a LocalContext
    ///
    /// `@[export lean_local_ctx_mk_local_decl] private def mkLocalDeclExported (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo) : LocalContext`
    ///
    /// # Safety
    /// - `lctx` must be a valid LocalContext (consumed)
    /// - `fvar_id` must be a valid FVarId/Name (consumed)
    /// - `user_name` must be a valid Name (consumed)
    /// - `type` must be a valid Expr (consumed)
    /// - `bi` must be a valid BinderInfo (consumed, scalar)
    pub fn lean_local_ctx_mk_local_decl(
        lctx: lean_obj_arg,
        fvar_id: lean_obj_arg,
        user_name: lean_obj_arg,
        r#type: lean_obj_arg,
        bi: u8,
    ) -> lean_obj_res;

    /// Add a let declaration to a LocalContext
    ///
    /// `@[export lean_local_ctx_mk_let_decl] private def mkLetDeclExported (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr) (value : Expr) (nondep : Bool) : LocalContext`
    ///
    /// # Safety
    /// - `lctx` must be a valid LocalContext (consumed)
    /// - `fvar_id` must be a valid FVarId/Name (consumed)
    /// - `user_name` must be a valid Name (consumed)
    /// - `type` must be a valid Expr (consumed)
    /// - `value` must be a valid Expr (consumed)
    /// - `nondep` must be a Lean Bool (lean_box(0) = false, lean_box(1) = true)
    pub fn lean_local_ctx_mk_let_decl(
        lctx: lean_obj_arg,
        fvar_id: lean_obj_arg,
        user_name: lean_obj_arg,
        r#type: lean_obj_arg,
        value: lean_obj_arg,
        nondep: u8,
    ) -> lean_obj_res;

    /// Find a local declaration by FVarId
    ///
    /// `@[export lean_local_ctx_find] def find? (lctx : LocalContext) (fvarId : FVarId) : Option LocalDecl`
    ///
    /// Returns `Option LocalDecl` — `none` (lean_box(0)) or `some decl`
    ///
    /// # Safety
    /// - `lctx` must be a valid LocalContext (borrowed)
    /// - `fvar_id` must be a valid FVarId/Name (borrowed)
    pub fn lean_local_ctx_find(lctx: b_lean_obj_arg, fvar_id: b_lean_obj_arg) -> lean_obj_res;

    /// Erase a local declaration from a LocalContext
    ///
    /// `@[export lean_local_ctx_erase] def erase (lctx : LocalContext) (fvarId : FVarId) : LocalContext`
    ///
    /// # Safety
    /// - `lctx` must be a valid LocalContext (consumed)
    /// - `fvar_id` must be a valid FVarId/Name (consumed)
    pub fn lean_local_ctx_erase(lctx: lean_obj_arg, fvar_id: lean_obj_arg) -> lean_obj_res;

    /// Get the number of indices in a LocalContext
    ///
    /// `@[export lean_local_ctx_num_indices] def numIndices (lctx : LocalContext) : Nat`
    ///
    /// # Safety
    /// - `lctx` must be a valid LocalContext (borrowed)
    pub fn lean_local_ctx_num_indices(lctx: b_lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// LocalDecl Operations
// ============================================================================

extern "C" {
    /// Create a local (non-let) declaration
    ///
    /// `@[export lean_mk_local_decl] def mkLocalDeclEx (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo) : LocalDecl`
    ///
    /// # Safety
    /// - `index` must be a valid Nat (consumed)
    /// - `fvar_id` must be a valid FVarId/Name (consumed)
    /// - `user_name` must be a valid Name (consumed)
    /// - `type` must be a valid Expr (consumed)
    /// - `bi` must be a valid BinderInfo (scalar)
    pub fn lean_mk_local_decl(
        index: lean_obj_arg,
        fvar_id: lean_obj_arg,
        user_name: lean_obj_arg,
        r#type: lean_obj_arg,
        bi: u8,
    ) -> lean_obj_res;

    /// Create a let declaration
    ///
    /// `@[export lean_mk_let_decl] def mkLetDeclEx (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (val : Expr) : LocalDecl`
    ///
    /// # Safety
    /// - `index` must be a valid Nat (consumed)
    /// - `fvar_id` must be a valid FVarId/Name (consumed)
    /// - `user_name` must be a valid Name (consumed)
    /// - `type` must be a valid Expr (consumed)
    /// - `val` must be a valid Expr (consumed)
    pub fn lean_mk_let_decl(
        index: lean_obj_arg,
        fvar_id: lean_obj_arg,
        user_name: lean_obj_arg,
        r#type: lean_obj_arg,
        val: lean_obj_arg,
    ) -> lean_obj_res;

    /// Get the BinderInfo of a LocalDecl
    ///
    /// `@[export lean_local_decl_binder_info] def LocalDecl.binderInfoEx : LocalDecl → BinderInfo`
    ///
    /// Returns a BinderInfo enum value as a scalar.
    ///
    /// # Safety
    /// - `decl` must be a valid LocalDecl (borrowed)
    pub fn lean_local_decl_binder_info(decl: b_lean_obj_arg) -> u8;
}

// ============================================================================
// Environment Query Helpers (pure, non-monadic)
// ============================================================================

extern "C" {
    /// Check if a declaration is a global typeclass instance
    ///
    /// `@[export lean_is_instance] def isGlobalInstance (env : Environment) (declName : Name) : Bool`
    ///
    /// # Safety
    /// - `env` must be a valid Environment (borrowed)
    /// - `decl_name` must be a valid Name (borrowed)
    pub fn lean_is_instance(env: b_lean_obj_arg, decl_name: b_lean_obj_arg) -> u8;

    /// Check if a declaration is a match expression
    ///
    /// `@[export lean_is_matcher] def isMatcherCore (env : Environment) (declName : Name) : Bool`
    ///
    /// # Safety
    /// - `env` must be a valid Environment (borrowed)
    /// - `decl_name` must be a valid Name (borrowed)
    pub fn lean_is_matcher(env: b_lean_obj_arg, decl_name: b_lean_obj_arg) -> u8;
}
