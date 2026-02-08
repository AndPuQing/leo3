//! Context and state types for Lean's CoreM / MetaM monad stack.
//!
//! Lean's metaprogramming monads are layered as `MetaM = ReaderT Meta.Context
//! (StateRefT Meta.State CoreM)`, where `CoreM = ReaderT Core.Context
//! (StateRefT Core.State ...)`. Running a MetaM computation therefore requires
//! four objects:
//!
//! | Type | Kind | Purpose |
//! |------|------|---------|
//! | [`CoreContext`] | Read-only | Core settings: file name, recursion depth, heartbeats, namespace |
//! | [`CoreState`] | Mutable | Core state: environment, name generator, messages, trace |
//! | [`MetaContext`] | Read-only | Meta settings: local context, config, local instances |
//! | [`MetaState`] | Mutable | Meta state: metavariable context, caches, diagnostics |
//!
//! Each type provides an `mk_default` / `mk_*` constructor that fills in
//! sensible defaults so callers can get started without manually constructing
//! every field. These are used internally by [`MetaMContext::new()`].
//!
//! Based on:
//! - `/lean4/src/Lean/CoreM.lean`
//! - `/lean4/src/Lean/Meta/Basic.lean`
//! - Issue #26 - MetaM Integration Phase 1.2
//!
//! [`MetaMContext::new()`]: super::metam::MetaMContext::new

use crate::err::LeanResult;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::meta::{LeanEnvironment, LeanExpr, LeanName};
use crate::types::{LeanList, LeanOption, LeanString};
use leo3_ffi as ffi;

/// Core.Context - context for CoreM monad
///
/// Lean structure with 13 object fields + 2 scalar bytes (constructor tag 0).
///
/// Object fields (Bool fields are stored as scalars, not objects):
/// 0. `fileName: String`
/// 1. `fileMap: FileMap`
/// 2. `options: Options`
/// 3. `currRecDepth: Nat`
/// 4. `maxRecDepth: Nat`
/// 5. `ref: Syntax`
/// 6. `currNamespace: Name`
/// 7. `openDecls: List OpenDecl`
/// 8. `initHeartbeats: Nat`
/// 9. `maxHeartbeats: Nat`
/// 10. `currMacroScope: MacroScope`
/// 11. `cancelTk?: Option IO.CancelToken`
/// 12. `inheritedTraceOptions: Std.HashSet Name`
///
/// Scalar fields:
/// offset 0: `diag: Bool` (1 byte)
/// offset 1: `suppressElabErrors: Bool` (1 byte)
#[repr(transparent)]
pub struct CoreContext {
    _private: (),
}

impl CoreContext {
    /// Create a Core.Context with default values
    ///
    /// This creates a minimal Core.Context suitable for running MetaM computations.
    /// All fields are set to sensible defaults:
    /// - fileName: `"<rust>"`
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
            // Core.Context: 13 object fields + 2 scalar bytes (constructor tag 0)
            // Bool fields (diag, suppressElabErrors) are stored as scalars.
            let ctx = ffi::lean_alloc_ctor(0, 13, 2);

            // Object field 0: fileName (String) - use "<rust>"
            let filename = LeanString::mk(lean, "<rust>")?;
            ffi::lean_ctor_set(ctx, 0, filename.into_ptr());

            // Object field 1: fileMap (FileMap) - use Inhabited instance
            let filemap = Self::mk_empty_filemap(lean)?;
            ffi::lean_ctor_set(ctx, 1, filemap.into_ptr());

            // Object field 2: options (Options) - use empty
            let options = Self::mk_empty_options(lean)?;
            ffi::lean_ctor_set(ctx, 2, options.into_ptr());

            // Object field 3: currRecDepth (Nat) - use 0
            ffi::lean_ctor_set(ctx, 3, ffi::lean_box(0));

            // Object field 4: maxRecDepth (Nat) - use 1000
            ffi::lean_ctor_set(ctx, 4, ffi::lean_box(1000));

            // Object field 5: ref (Syntax) - use Syntax.missing
            let syntax_missing = Self::mk_syntax_missing(lean)?;
            ffi::lean_ctor_set(ctx, 5, syntax_missing.into_ptr());

            // Object field 6: currNamespace (Name) - use anonymous
            let anon_name = LeanName::anonymous(lean)?;
            ffi::lean_ctor_set(ctx, 6, anon_name.into_ptr());

            // Object field 7: openDecls (List OpenDecl) - use empty list
            let empty_list = LeanList::nil(lean)?;
            ffi::lean_ctor_set(ctx, 7, empty_list.into_ptr());

            // Object field 8: initHeartbeats (Nat) - use 0
            ffi::lean_ctor_set(ctx, 8, ffi::lean_box(0));

            // Object field 9: maxHeartbeats (Nat) - use 200000000
            ffi::lean_ctor_set(ctx, 9, ffi::lean_box(200000000));

            // Object field 10: currMacroScope (MacroScope = Nat) - use 0
            ffi::lean_ctor_set(ctx, 10, ffi::lean_box(0));

            // Object field 11: cancelTk? (Option IO.CancelToken) - use none
            let cancel_token = LeanOption::none(lean)?;
            ffi::lean_ctor_set(ctx, 11, cancel_token.into_ptr());

            // Object field 12: inheritedTraceOptions (Std.HashSet Name) - use empty
            let empty_hashset = Self::mk_empty_hashset(lean)?;
            ffi::lean_ctor_set(ctx, 12, empty_hashset.into_ptr());

            // Scalar offset 0: diag (Bool) - use false (0)
            ffi::inline::lean_ctor_set_uint8(ctx, 0, 0);

            // Scalar offset 1: suppressElabErrors (Bool) - use false (0)
            ffi::inline::lean_ctor_set_uint8(ctx, 1, 0);

            Ok(LeanBound::from_owned_ptr(lean, ctx))
        }
    }

    /// Get an empty `FileMap` from the Lean runtime's `Inhabited FileMap` instance.
    ///
    /// Uses the `l_Lean_instInhabitedFileMap` BSS global which is initialized
    /// during `initialize_Lean_Meta`.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_empty_filemap<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let filemap = ffi::meta::l_Lean_instInhabitedFileMap;
            if filemap.is_null() {
                return Err(crate::LeanError::runtime(
                    "FileMap Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(filemap);
            Ok(LeanBound::from_owned_ptr(lean, filemap))
        }
    }

    /// Create empty Options
    ///
    /// Uses the `Inhabited Options` instance from the Lean runtime.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_empty_options<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let options = ffi::meta::l_Lean_instInhabitedOptions;
            if options.is_null() {
                return Err(crate::LeanError::runtime(
                    "Options Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(options);
            Ok(LeanBound::from_owned_ptr(lean, options))
        }
    }

    /// Get `Syntax.missing` from the Lean runtime's `Inhabited Syntax` instance.
    ///
    /// Uses the `l_Lean_instInhabitedSyntax` BSS global which is initialized
    /// during `initialize_Lean_Meta`.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_syntax_missing<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let syntax = ffi::meta::l_Lean_instInhabitedSyntax;
            if syntax.is_null() {
                return Err(crate::LeanError::runtime(
                    "Syntax Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(syntax);
            Ok(LeanBound::from_owned_ptr(lean, syntax))
        }
    }

    /// Create an empty `Std.HashSet Name` for `inheritedTraceOptions`.
    ///
    /// Calls `l_Std_HashSet_empty___rarg` with the default capacity (8),
    /// which is the reduced-arity specialization with BEq/Hashable instances
    /// already resolved by the Lean compiler.
    fn mk_empty_hashset<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        unsafe {
            let hashset = ffi::hashset::l_Std_HashSet_empty___rarg(ffi::lean_box(8));
            Ok(LeanBound::from_owned_ptr(lean, hashset))
        }
    }
}

/// Core.State - state for CoreM monad
///
/// This structure has 8 fields (constructor tag 0):
/// 0. `env: Environment` - from parameter
/// 1. `nextMacroScope: MacroScope` - use default (firstFrontendMacroScope + 1)
/// 2. `ngen: NameGenerator` - create new
/// 3. `traceState: TraceState` - use empty
/// 4. `cache: Cache` - use empty
/// 5. `messages: MessageLog` - use empty
/// 6. `infoState: Elab.InfoState` - use empty
/// 7. `snapshotTasks: Array SnapshotTask` - use empty array
#[repr(transparent)]
pub struct CoreState {
    _private: (),
}

impl CoreState {
    /// Create a Core.State with an Environment
    ///
    /// This creates a minimal Core.State suitable for running MetaM computations.
    /// All fields except the environment are set to sensible defaults:
    /// - env: from parameter
    /// - nextMacroScope: firstFrontendMacroScope + 1 (= 1)
    /// - ngen: new NameGenerator
    /// - All other fields: empty
    ///
    /// # Example
    ///
    /// ```ignore
    /// use leo3::prelude::*;
    /// use leo3::meta::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let env = LeanEnvironment::empty(lean, 0)?;
    ///     let state = CoreState::mk_core_state(lean, &env)?;
    ///     Ok(())
    /// })
    /// ```
    pub fn mk_core_state<'l>(
        lean: Lean<'l>,
        env: &LeanBound<'l, LeanEnvironment>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Core.State has 8 fields (constructor tag 0)
            let state = ffi::lean_alloc_ctor(0, 8, 0);

            // Field 0: env (Environment) - from parameter
            let env_ptr = env.as_ptr();
            ffi::lean_inc(env_ptr);
            ffi::lean_ctor_set(state, 0, env_ptr);

            // Field 1: nextMacroScope (MacroScope) - use firstFrontendMacroScope + 1
            // firstFrontendMacroScope is 0, so we use 1
            let next_macro_scope = ffi::lean_box(1);
            ffi::lean_ctor_set(state, 1, next_macro_scope);

            // Field 2: ngen (NameGenerator) - create new
            let ngen = Self::mk_name_generator(lean)?;
            ffi::lean_ctor_set(state, 2, ngen.into_ptr());

            // Field 3: traceState (TraceState) - use empty
            let trace_state = Self::mk_empty_trace_state(lean)?;
            ffi::lean_ctor_set(state, 3, trace_state.into_ptr());

            // Field 4: cache (Cache) - use empty
            let cache = Self::mk_empty_cache(lean)?;
            ffi::lean_ctor_set(state, 4, cache.into_ptr());

            // Field 5: messages (MessageLog) - use empty
            let messages = Self::mk_empty_message_log(lean)?;
            ffi::lean_ctor_set(state, 5, messages.into_ptr());

            // Field 6: infoState (Elab.InfoState) - use empty
            let info_state = Self::mk_empty_info_state(lean)?;
            ffi::lean_ctor_set(state, 6, info_state.into_ptr());

            // Field 7: snapshotTasks (Array SnapshotTask) - use empty array
            let empty_array = ffi::array::lean_mk_empty_array();
            ffi::lean_ctor_set(state, 7, empty_array);

            Ok(LeanBound::from_owned_ptr(lean, state))
        }
    }

    /// Create a new NameGenerator
    ///
    /// Uses the `Inhabited NameGenerator` instance from the Lean runtime,
    /// which provides `{ namePrefix := `_uniq, idx := 1 }`.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_name_generator<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let ngen = ffi::meta::l_Lean_instInhabitedNameGenerator;
            if ngen.is_null() {
                return Err(crate::LeanError::runtime(
                    "NameGenerator Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(ngen);
            Ok(LeanBound::from_owned_ptr(lean, ngen))
        }
    }

    /// Create an empty TraceState
    ///
    /// Uses the `Inhabited TraceState` instance from the Lean runtime.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_empty_trace_state<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let trace_state = ffi::meta::l_Lean_instInhabitedTraceState;
            if trace_state.is_null() {
                return Err(crate::LeanError::runtime(
                    "TraceState Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(trace_state);
            Ok(LeanBound::from_owned_ptr(lean, trace_state))
        }
    }

    /// Create an empty Cache
    ///
    /// Uses the `Inhabited Core.Cache` instance from the Lean runtime.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_empty_cache<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let cache = ffi::meta::l_Lean_Core_instInhabitedCache;
            if cache.is_null() {
                return Err(crate::LeanError::runtime(
                    "Core.Cache Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(cache);
            Ok(LeanBound::from_owned_ptr(lean, cache))
        }
    }

    /// Create an empty MessageLog
    ///
    /// Uses the `Inhabited MessageLog` instance from the Lean runtime.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_empty_message_log<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let msg_log = ffi::meta::l_Lean_instInhabitedMessageLog;
            if msg_log.is_null() {
                return Err(crate::LeanError::runtime(
                    "MessageLog Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(msg_log);
            Ok(LeanBound::from_owned_ptr(lean, msg_log))
        }
    }

    /// Create an empty Elab.InfoState
    ///
    /// Uses the `Inhabited Elab.InfoState` instance from the Lean runtime.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_empty_info_state<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let info_state = ffi::meta::l_Lean_Elab_instInhabitedInfoState;
            if info_state.is_null() {
                return Err(crate::LeanError::runtime(
                    "Elab.InfoState Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(info_state);
            Ok(LeanBound::from_owned_ptr(lean, info_state))
        }
    }
}

/// Meta.Context - context for MetaM monad
///
/// Lean structure with 7 object fields + 11 scalar bytes (constructor tag 0).
///
/// Object fields (Bool fields are stored as scalars, not objects):
/// 0. `config: Config`
/// 1. `zetaDeltaSet: FVarIdSet`
/// 2. `lctx: LocalContext`
/// 3. `localInstances: LocalInstances`
/// 4. `defEqCtx?: Option DefEqContext`
/// 5. `synthPendingDepth: Nat`
/// 6. `canUnfold?: Option (Config → ConstantInfo → CoreM Bool)`
///
/// Scalar fields:
/// offset 0: `configKey: UInt64` (8 bytes)
/// offset 8: `trackZetaDelta: Bool` (1 byte)
/// offset 9: `univApprox: Bool` (1 byte)
/// offset 10: `inTypeClassResolution: Bool` (1 byte)
#[repr(transparent)]
pub struct MetaContext {
    _private: (),
}

impl MetaContext {
    /// Create a Meta.Context with default values
    ///
    /// This creates a minimal Meta.Context suitable for running MetaM computations.
    /// All fields are set to sensible defaults:
    /// - config: default Meta.Config (all false/zero)
    /// - configKey: 0 (computed from config hash)
    /// - trackZetaDelta: false
    /// - zetaDeltaSet: empty FVarIdSet
    /// - lctx: empty LocalContext
    /// - localInstances: empty array
    ///
    /// # Example
    ///
    /// ```ignore
    /// use leo3::prelude::*;
    /// use leo3::meta::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let ctx = MetaContext::mk_default(lean)?;
    ///     Ok(())
    /// })
    /// ```
    pub fn mk_default<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Meta.Context: 7 object fields + 11 scalar bytes (constructor tag 0)
            // Bool fields (trackZetaDelta, univApprox, inTypeClassResolution) are scalars.
            let ctx = ffi::lean_alloc_ctor(0, 7, 11);

            // Object field 0: config (Meta.Config) - use default config
            let config = Self::mk_default_config(lean)?;
            ffi::lean_ctor_set(ctx, 0, config.into_ptr());

            // Object field 1: zetaDeltaSet (FVarIdSet) - use empty
            let empty_fvar_set = Self::mk_empty_fvar_id_set(lean)?;
            ffi::lean_ctor_set(ctx, 1, empty_fvar_set.into_ptr());

            // Object field 2: lctx (LocalContext) - use empty
            let empty_lctx = Self::mk_empty_local_context(lean)?;
            ffi::lean_ctor_set(ctx, 2, empty_lctx.into_ptr());

            // Object field 3: localInstances (LocalInstances) - use empty array
            let empty_array = ffi::array::lean_mk_empty_array();
            ffi::lean_ctor_set(ctx, 3, empty_array);

            // Object field 4: defEqCtx? (Option DefEqContext) - use none
            let none = LeanOption::none(lean)?;
            ffi::lean_ctor_set(ctx, 4, none.into_ptr());

            // Object field 5: synthPendingDepth (Nat) - use 0
            ffi::lean_ctor_set(ctx, 5, ffi::lean_box(0));

            // Object field 6: canUnfold? (Option ...) - use none
            let none2 = LeanOption::none(lean)?;
            ffi::lean_ctor_set(ctx, 6, none2.into_ptr());

            // Scalar offset 0-7: configKey (UInt64) - use 0
            ffi::lean_ctor_set_uint64(ctx, 0, 0);

            // Scalar offset 8: trackZetaDelta (Bool) - use false (0)
            ffi::inline::lean_ctor_set_uint8(ctx, 8, 0);

            // Scalar offset 9: univApprox (Bool) - use false (0)
            ffi::inline::lean_ctor_set_uint8(ctx, 9, 0);

            // Scalar offset 10: inTypeClassResolution (Bool) - use false (0)
            ffi::inline::lean_ctor_set_uint8(ctx, 10, 0);

            Ok(LeanBound::from_owned_ptr(lean, ctx))
        }
    }

    /// Create a default Meta.Config
    ///
    /// Uses the `Inhabited Meta.Config` instance from the Lean runtime, which
    /// provides a properly constructed default configuration with all boolean
    /// flags at their documented default values.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_default_config<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let config = ffi::meta::l_Lean_Meta_instInhabitedConfig;
            if config.is_null() {
                return Err(crate::LeanError::runtime(
                    "Meta.Config Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(config);
            Ok(LeanBound::from_owned_ptr(lean, config))
        }
    }

    /// Create an empty FVarIdSet
    ///
    /// FVarIdSet is a hash set of free variable IDs.
    /// For now, we use lean_box(0) which represents an empty set.
    fn mk_empty_fvar_id_set<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        unsafe {
            // Empty FVarIdSet is represented as lean_box(0)
            let fvar_set = ffi::lean_box(0);
            Ok(LeanBound::from_owned_ptr(lean, fvar_set))
        }
    }

    /// Create an empty LocalContext
    ///
    /// Uses the `Inhabited LocalContext` instance from the Lean runtime.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_empty_local_context<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let lctx = ffi::meta::l_Lean_instInhabitedLocalContext;
            if lctx.is_null() {
                return Err(crate::LeanError::runtime(
                    "LocalContext Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(lctx);
            Ok(LeanBound::from_owned_ptr(lean, lctx))
        }
    }
}

/// Meta.State - state for MetaM monad
///
/// This structure has 5 fields (constructor tag 0):
/// 0. `mctx: MetavarContext` - use empty
/// 1. `cache: Cache` - use empty
/// 2. `zetaDeltaFVarIds: FVarIdSet` - use empty
/// 3. `postponed: PersistentArray PostponedEntry` - use empty
/// 4. `diag: Diagnostics` - use empty
#[repr(transparent)]
pub struct MetaState {
    _private: (),
}

impl MetaState {
    /// Create a Meta.State with empty state
    ///
    /// This creates a minimal Meta.State suitable for running MetaM computations.
    /// All fields are set to empty/default values:
    /// - mctx: empty MetavarContext
    /// - cache: empty Cache
    /// - zetaDeltaFVarIds: empty FVarIdSet
    /// - postponed: empty PersistentArray
    /// - diag: empty Diagnostics
    ///
    /// # Example
    ///
    /// ```ignore
    /// use leo3::prelude::*;
    /// use leo3::meta::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let meta_state = MetaState::mk_meta_state(lean)?;
    ///     Ok(())
    /// })
    /// ```
    pub fn mk_meta_state<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Allocate Meta.State constructor (tag 0, 5 fields, 0 scalars)
            let state = ffi::lean_alloc_ctor(0, 5, 0);

            // Field 0: mctx (MetavarContext) - use empty
            let empty_mctx = Self::mk_empty_metavar_context(lean)?;
            ffi::lean_ctor_set(state, 0, empty_mctx.into_ptr());

            // Field 1: cache (Cache) - use empty
            let empty_cache = Self::mk_empty_cache(lean)?;
            ffi::lean_ctor_set(state, 1, empty_cache.into_ptr());

            // Field 2: zetaDeltaFVarIds (FVarIdSet) - use empty
            let empty_fvar_set = Self::mk_empty_fvar_id_set(lean)?;
            ffi::lean_ctor_set(state, 2, empty_fvar_set.into_ptr());

            // Field 3: postponed (PersistentArray PostponedEntry) - use empty array
            let empty_array = ffi::array::lean_mk_empty_array();
            ffi::lean_ctor_set(state, 3, empty_array);

            // Field 4: diag (Diagnostics) - use empty
            let empty_diag = Self::mk_empty_diagnostics(lean)?;
            ffi::lean_ctor_set(state, 4, empty_diag.into_ptr());

            Ok(LeanBound::from_owned_ptr(lean, state))
        }
    }

    /// Create an empty MetavarContext
    ///
    /// Uses the `Inhabited MetavarContext` instance from the Lean runtime.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_empty_metavar_context<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let mctx = ffi::meta::l_Lean_instInhabitedMetavarContext;
            if mctx.is_null() {
                return Err(crate::LeanError::runtime(
                    "MetavarContext Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(mctx);
            Ok(LeanBound::from_owned_ptr(lean, mctx))
        }
    }

    /// Create an empty Cache
    ///
    /// Uses the `Inhabited Meta.Cache` instance from the Lean runtime.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_empty_cache<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let cache = ffi::meta::l_Lean_Meta_instInhabitedCache;
            if cache.is_null() {
                return Err(crate::LeanError::runtime(
                    "Meta.Cache Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(cache);
            Ok(LeanBound::from_owned_ptr(lean, cache))
        }
    }

    /// Create an empty FVarIdSet
    ///
    /// FVarIdSet is a hash set of free variable IDs.
    /// For now, we use lean_box(0) which represents an empty set.
    fn mk_empty_fvar_id_set<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        unsafe {
            // Empty FVarIdSet is represented as lean_box(0)
            let fvar_set = ffi::lean_box(0);
            Ok(LeanBound::from_owned_ptr(lean, fvar_set))
        }
    }

    /// Create an empty Diagnostics
    ///
    /// Uses the `Inhabited Meta.Diagnostics` instance from the Lean runtime.
    ///
    /// Requires: `ensure_meta_initialized()` must have been called.
    fn mk_empty_diagnostics<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
        crate::meta::ensure_meta_initialized();
        unsafe {
            let diag = ffi::meta::l_Lean_Meta_instInhabitedDiagnostics;
            if diag.is_null() {
                return Err(crate::LeanError::runtime(
                    "Meta.Diagnostics Inhabited instance is null - Lean.Meta may not be initialized",
                ));
            }
            ffi::lean_inc(diag);
            Ok(LeanBound::from_owned_ptr(lean, diag))
        }
    }
}
