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
    /// Lean.Meta.MetaM.run' : MetaM α → Context → State → CoreM α
    pub fn l_Lean_Meta_MetaM_run_x27___rarg(
        x: lean_obj_arg,
        ctx: lean_obj_arg,
        state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state: lean_obj_arg,
    ) -> lean_obj_res;
}

#[cfg(lean_4_22)]
extern "C" {
    /// Run a MetaM computation (Lean >= 4.22)
    ///
    /// Lean.Meta.MetaM.run' : MetaM α → Context → State → CoreM α
    pub fn l_Lean_Meta_MetaM_run_x27___redArg(
        x: lean_obj_arg,
        ctx: lean_obj_arg,
        state: lean_obj_arg,
        core_ctx: lean_obj_arg,
        core_state: lean_obj_arg,
    ) -> lean_obj_res;
}

/// Run a MetaM computation, dispatching to the correct symbol for the Lean version.
///
/// # Safety
/// - `x` must be a valid MetaM computation (consumed)
/// - `ctx` must be a valid Meta.Context object (consumed)
/// - `state` must be a valid Meta.State object (consumed)
/// - `core_ctx` must be a valid Core.Context object (consumed)
/// - `core_state` must be a valid Core.State object (consumed)
#[inline]
pub unsafe fn lean_meta_metam_run(
    x: lean_obj_arg,
    ctx: lean_obj_arg,
    state: lean_obj_arg,
    core_ctx: lean_obj_arg,
    core_state: lean_obj_arg,
) -> lean_obj_res {
    #[cfg(not(lean_4_22))]
    {
        l_Lean_Meta_MetaM_run_x27___rarg(x, ctx, state, core_ctx, core_state)
    }
    #[cfg(lean_4_22)]
    {
        l_Lean_Meta_MetaM_run_x27___redArg(x, ctx, state, core_ctx, core_state)
    }
}

extern "C" {
    /// Infer the type of an expression
    ///
    /// Lean.Meta.inferType : Expr → MetaM Expr
    ///
    /// # Safety
    /// - `expr` must be a valid Expr object (consumed)
    pub fn l_Lean_Meta_inferType___boxed(expr: lean_obj_arg) -> lean_obj_res;

    /// Type check an expression
    ///
    /// Lean.Meta.check : Expr → MetaM Unit
    ///
    /// # Safety
    /// - `expr` must be a valid Expr object (consumed)
    pub fn l_Lean_Meta_check(expr: lean_obj_arg) -> lean_obj_res;
}
