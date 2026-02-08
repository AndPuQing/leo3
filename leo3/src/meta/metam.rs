//! MetaMContext - high-level wrapper for running MetaM computations
//!
//! This module provides `MetaMContext`, which bundles all the context and state
//! objects needed to run Lean's MetaM monad computations from Rust.
//!
//! Based on:
//! - `/lean4/src/Lean/Meta/Basic.lean`
//! - Issue #30 - MetaM Integration Phase 1.6

use crate::err::{LeanError, LeanResult};
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;
use crate::meta::context::{CoreContext, CoreState, MetaContext, MetaState};
use crate::meta::LeanEnvironment;
use leo3_ffi as ffi;

/// Context for running MetaM computations.
///
/// `MetaMContext` bundles together all the context and state objects required
/// by Lean's MetaM monad: `Core.Context`, `Core.State`, `Meta.Context`, and
/// `Meta.State`. It provides a `run()` method to execute MetaM computations.
///
/// # Example
///
/// ```ignore
/// use leo3::prelude::*;
/// use leo3::meta::*;
///
/// leo3::with_lean(|lean| {
///     let env = LeanEnvironment::empty(lean, 0)?;
///     let mut ctx = MetaMContext::new(lean, env)?;
///     // ctx.run(some_metam_computation)?;
///     Ok(())
/// })?;
/// ```
pub struct MetaMContext<'l> {
    lean: Lean<'l>,
    env: LeanBound<'l, LeanEnvironment>,
    core_ctx: LeanBound<'l, CoreContext>,
    core_state: LeanBound<'l, CoreState>,
    meta_ctx: LeanBound<'l, MetaContext>,
    meta_state: LeanBound<'l, MetaState>,
}

impl<'l> MetaMContext<'l> {
    /// Create a new MetaMContext from an environment.
    ///
    /// This constructs all required context and state objects with default values:
    /// - `Core.Context`: default settings (maxRecDepth=1000, maxHeartbeats=200M)
    /// - `Core.State`: initialized with the given environment
    /// - `Meta.Context`: default Meta configuration
    /// - `Meta.State`: empty metavariable context and caches
    ///
    /// # Arguments
    ///
    /// * `lean` - Lean runtime token
    /// * `env` - Environment to use for computations
    ///
    /// # Example
    ///
    /// ```ignore
    /// let env = LeanEnvironment::empty(lean, 0)?;
    /// let ctx = MetaMContext::new(lean, env)?;
    /// ```
    pub fn new(lean: Lean<'l>, env: LeanBound<'l, LeanEnvironment>) -> LeanResult<Self> {
        let core_ctx = CoreContext::mk_default(lean)?;
        let core_state = CoreState::mk_core_state(lean, &env)?;
        let meta_ctx = MetaContext::mk_default(lean)?;
        let meta_state = MetaState::mk_meta_state(lean)?;

        Ok(Self {
            lean,
            env,
            core_ctx,
            core_state,
            meta_ctx,
            meta_state,
        })
    }

    /// Run a MetaM computation.
    ///
    /// Executes the given MetaM computation using the stored context and state.
    /// The computation is consumed by this call. Context and state objects are
    /// cloned before being passed to the FFI, so the `MetaMContext` can be
    /// reused for multiple `run()` calls.
    ///
    /// # Arguments
    ///
    /// * `computation` - A MetaM computation object (consumed)
    ///
    /// # Returns
    ///
    /// The result of the computation, or an error if the computation failed.
    ///
    /// # EIO Result Handling
    ///
    /// `MetaM.run'` returns `EIO Exception T`:
    /// - Tag 0 (`Except.ok`) → field 0 contains the result value
    /// - Tag 1 (`Except.error`) → field 0 contains the error
    pub fn run(
        &mut self,
        computation: LeanBound<'l, LeanAny>,
    ) -> LeanResult<LeanBound<'l, LeanAny>> {
        unsafe {
            // Clone all context/state objects since FFI consumes them
            let meta_ctx = self.meta_ctx.clone();
            let meta_state = self.meta_state.clone();
            let core_ctx = self.core_ctx.clone();
            let core_state = self.core_state.clone();

            let result = ffi::meta::lean_meta_metam_run(
                computation.into_ptr(),
                meta_ctx.into_ptr(),
                meta_state.into_ptr(),
                core_ctx.into_ptr(),
                core_state.into_ptr(),
            );

            // Handle EIO result: tag 0 = ok, tag 1 = error
            let tag = ffi::lean_obj_tag(result);
            if tag == 1 {
                let err_ptr = ffi::lean_ctor_get(result, 0) as *mut ffi::lean_object;
                ffi::lean_inc(err_ptr);
                ffi::lean_dec(result);
                ffi::lean_dec(err_ptr);
                return Err(LeanError::runtime("MetaM computation failed"));
            }

            // Extract value from Except.ok (field 0)
            let value_ptr = ffi::lean_ctor_get(result, 0) as *mut ffi::lean_object;
            ffi::lean_inc(value_ptr);
            ffi::lean_dec(result);

            Ok(LeanBound::from_owned_ptr(self.lean, value_ptr))
        }
    }

    /// Get a reference to the environment.
    pub fn env(&self) -> &LeanBound<'l, LeanEnvironment> {
        &self.env
    }

    /// Get the Lean runtime token.
    pub fn lean(&self) -> Lean<'l> {
        self.lean
    }
}
