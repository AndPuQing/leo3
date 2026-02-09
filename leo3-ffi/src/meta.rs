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

#[cfg(lean_4_22)]
extern "C" {
    /// Run a MetaM computation (Lean >= 4.22)
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

/// Run a MetaM computation, dispatching to the correct symbol for the Lean version.
///
/// # Safety
/// - `x` must be a valid MetaM computation (consumed)
/// - `ctx` must be a valid Meta.Context object (consumed)
/// - `state` must be a valid Meta.State object (raw, consumed)
/// - `core_ctx` must be a valid Core.Context object (consumed)
/// - `core_state_ref` must be an ST.Ref wrapping Core.State (created via `lean_st_mk_ref`)
/// - `world` must be an IO world token (typically `lean_box(0)`)
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
    #[cfg(lean_4_22)]
    {
        l_Lean_Meta_MetaM_run_x27___redArg(x, ctx, state, core_ctx, core_state_ref, world)
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

#[cfg_attr(target_os = "windows", link(name = "leanshared", kind = "raw-dylib"))]
extern "C" {
    /// Default `Meta.Config` (all boolean flags at their default values)
    pub static l_Lean_Meta_instInhabitedConfig: *mut lean_object;

    /// Default `Meta.Context` (Lean >= 4.25)
    ///
    /// This symbol was introduced when `Meta.Context` was restructured to use
    /// `ConfigWithKey` as a wrapper field. Using this runtime instance avoids
    /// hardcoding the struct layout.
    #[cfg(lean_4_25)]
    pub static l_Lean_Meta_instInhabitedContext: *mut lean_object;

    /// Default `Meta.State` (empty metavar context, empty caches)
    pub static l_Lean_Meta_instInhabitedState: *mut lean_object;

    /// Default `Meta.Cache` (empty inference/whnf/synth caches)
    pub static l_Lean_Meta_instInhabitedCache: *mut lean_object;

    /// Default `Meta.Diagnostics` (empty counters)
    pub static l_Lean_Meta_instInhabitedDiagnostics: *mut lean_object;

    /// Default `MetavarContext` (empty)
    pub static l_Lean_instInhabitedMetavarContext: *mut lean_object;

    /// Default `LocalContext` (empty)
    pub static l_Lean_instInhabitedLocalContext: *mut lean_object;

    /// Default `TraceState` (empty)
    pub static l_Lean_instInhabitedTraceState: *mut lean_object;

    /// Default `Core.Cache` (empty)
    pub static l_Lean_Core_instInhabitedCache: *mut lean_object;

    /// Default `Elab.InfoState` (empty)
    pub static l_Lean_Elab_instInhabitedInfoState: *mut lean_object;

    /// Default `Options` / `KVMap` (empty, Lean < 4.28)
    #[cfg(not(lean_4_28))]
    pub static l_Lean_instInhabitedOptions: *mut lean_object;

    /// Default `Options` / `KVMap` (empty, Lean >= 4.28 — renamed)
    #[cfg(lean_4_28)]
    pub static l_Lean_Options_instInhabited: *mut lean_object;

    /// Default `MessageLog` (empty)
    pub static l_Lean_instInhabitedMessageLog: *mut lean_object;

    /// Default `NameGenerator` (`_uniq`, idx=1)
    pub static l_Lean_instInhabitedNameGenerator: *mut lean_object;

    /// Default `DeclNameGenerator` (Lean >= 4.25)
    ///
    /// This symbol was introduced when Core.State added the `auxDeclNGen` field.
    #[cfg(lean_4_25)]
    pub static l_Lean_instInhabitedDeclNameGenerator: *mut lean_object;

    /// Default `Syntax` (`Syntax.missing`)
    pub static l_Lean_instInhabitedSyntax: *mut lean_object;

    /// Default `FileMap` (empty source, empty positions)
    pub static l_Lean_instInhabitedFileMap: *mut lean_object;
}

/// Get the default `Options` / `KVMap` (empty), dispatching to the correct
/// symbol for the Lean version.
///
/// In Lean < 4.28 the symbol is `l_Lean_instInhabitedOptions`.
/// In Lean >= 4.28 it was renamed to `l_Lean_Options_instInhabited`.
#[inline]
pub unsafe fn lean_inhabited_options() -> *mut lean_object {
    #[cfg(not(lean_4_28))]
    {
        l_Lean_instInhabitedOptions
    }
    #[cfg(lean_4_28)]
    {
        l_Lean_Options_instInhabited
    }
}
