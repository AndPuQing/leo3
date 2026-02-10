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
// On Windows, BSS globals are NOT exported from DLLs by default. We load
// them at runtime via `libloading::Library::get()` (GetProcAddress).

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
    // Building-block symbols for manual construction fallbacks
    pub static l_Lean_PersistentHashMap_empty: *mut lean_object;
    pub static l_Lean_PersistentArray_empty: *mut lean_object;
    pub static l_Lean_KVMap_empty: *mut lean_object;
}

// ---------------------------------------------------------------------------
// Windows: runtime symbol loading via libloading
// ---------------------------------------------------------------------------

#[cfg(target_os = "windows")]
mod win_bss {
    use super::lean_object;
    use std::sync::OnceLock;

    /// Pointers to BSS globals loaded from libleanshared.dll at runtime.
    struct BssSymbols {
        inst_inhabited_config: *mut lean_object,
        #[cfg(lean_4_25)]
        inst_inhabited_context: *mut lean_object,
        inst_inhabited_state: *mut lean_object,
        inst_inhabited_cache: *mut lean_object,
        inst_inhabited_diagnostics: *mut lean_object,
        inst_inhabited_metavar_context: *mut lean_object,
        inst_inhabited_local_context: *mut lean_object,
        inst_inhabited_trace_state: *mut lean_object,
        core_inst_inhabited_cache: *mut lean_object,
        elab_inst_inhabited_info_state: *mut lean_object,
        #[cfg(not(lean_4_28))]
        inst_inhabited_options: *mut lean_object,
        #[cfg(lean_4_28)]
        options_inst_inhabited: *mut lean_object,
        inst_inhabited_message_log: *mut lean_object,
        inst_inhabited_name_generator: *mut lean_object,
        #[cfg(lean_4_25)]
        inst_inhabited_decl_name_generator: *mut lean_object,
        inst_inhabited_syntax: *mut lean_object,
        inst_inhabited_file_map: *mut lean_object,
        // Building-block symbols (exported on Windows)
        persistent_hashmap_empty: *mut lean_object,
        persistent_array_empty: *mut lean_object,
        kvmap_empty: *mut lean_object,
    }

    // SAFETY: The pointers are to Lean globals that are initialized once during
    // `initialize_Lean_Meta` and never moved. Access is read-only after init.
    unsafe impl Send for BssSymbols {}
    unsafe impl Sync for BssSymbols {}

    static SYMBOLS: OnceLock<BssSymbols> = OnceLock::new();

    /// Load a single BSS global pointer from the library.
    ///
    /// Returns the *value* stored at the global (i.e. dereferences the symbol
    /// pointer once), which is the `*mut lean_object` that callers expect.
    ///
    /// Returns `null` if the symbol is not exported from the DLL (common on
    /// Windows where most BSS globals are not exported).
    unsafe fn load_ptr(lib: &libloading::Library, name: &[u8]) -> *mut lean_object {
        match lib.get::<*mut *mut lean_object>(name) {
            Ok(sym) => {
                // Dereference: the symbol is a `*mut lean_object` in the DLL's BSS;
                // `lib.get` gives us a pointer *to* that global, so we read through it.
                **sym
            }
            Err(_) => std::ptr::null_mut(),
        }
    }

    fn load_symbols() -> BssSymbols {
        // SAFETY: libleanshared.dll is already loaded by the linker (it is a
        // link-time dependency). We just need a handle to look up symbols.
        let lib = unsafe {
            libloading::Library::new("libleanshared.dll")
                .expect("failed to open libleanshared.dll for BSS symbol loading")
        };

        unsafe {
            BssSymbols {
                inst_inhabited_config: load_ptr(&lib, b"l_Lean_Meta_instInhabitedConfig\0"),
                #[cfg(lean_4_25)]
                inst_inhabited_context: load_ptr(&lib, b"l_Lean_Meta_instInhabitedContext\0"),
                inst_inhabited_state: load_ptr(&lib, b"l_Lean_Meta_instInhabitedState\0"),
                inst_inhabited_cache: load_ptr(&lib, b"l_Lean_Meta_instInhabitedCache\0"),
                inst_inhabited_diagnostics: load_ptr(
                    &lib,
                    b"l_Lean_Meta_instInhabitedDiagnostics\0",
                ),
                inst_inhabited_metavar_context: load_ptr(
                    &lib,
                    b"l_Lean_instInhabitedMetavarContext\0",
                ),
                inst_inhabited_local_context: load_ptr(&lib, b"l_Lean_instInhabitedLocalContext\0"),
                inst_inhabited_trace_state: load_ptr(&lib, b"l_Lean_instInhabitedTraceState\0"),
                core_inst_inhabited_cache: load_ptr(&lib, b"l_Lean_Core_instInhabitedCache\0"),
                elab_inst_inhabited_info_state: load_ptr(
                    &lib,
                    b"l_Lean_Elab_instInhabitedInfoState\0",
                ),
                #[cfg(not(lean_4_28))]
                inst_inhabited_options: load_ptr(&lib, b"l_Lean_instInhabitedOptions\0"),
                #[cfg(lean_4_28)]
                options_inst_inhabited: load_ptr(&lib, b"l_Lean_Options_instInhabited\0"),
                inst_inhabited_message_log: load_ptr(&lib, b"l_Lean_instInhabitedMessageLog\0"),
                inst_inhabited_name_generator: load_ptr(
                    &lib,
                    b"l_Lean_instInhabitedNameGenerator\0",
                ),
                #[cfg(lean_4_25)]
                inst_inhabited_decl_name_generator: load_ptr(
                    &lib,
                    b"l_Lean_instInhabitedDeclNameGenerator\0",
                ),
                inst_inhabited_syntax: load_ptr(&lib, b"l_Lean_instInhabitedSyntax\0"),
                inst_inhabited_file_map: load_ptr(&lib, b"l_Lean_instInhabitedFileMap\0"),
                persistent_hashmap_empty: load_ptr(&lib, b"l_Lean_PersistentHashMap_empty\0"),
                persistent_array_empty: load_ptr(&lib, b"l_Lean_PersistentArray_empty\0"),
                kvmap_empty: load_ptr(&lib, b"l_Lean_KVMap_empty\0"),
            }
        }
    }

    fn symbols() -> &'static BssSymbols {
        SYMBOLS.get_or_init(load_symbols)
    }

    // --- public accessors (one per symbol) ---

    pub unsafe fn get_instInhabitedConfig() -> *mut lean_object {
        symbols().inst_inhabited_config
    }
    #[cfg(lean_4_25)]
    pub unsafe fn get_instInhabitedContext() -> *mut lean_object {
        symbols().inst_inhabited_context
    }
    pub unsafe fn get_instInhabitedState() -> *mut lean_object {
        symbols().inst_inhabited_state
    }
    pub unsafe fn get_instInhabitedCache() -> *mut lean_object {
        symbols().inst_inhabited_cache
    }
    pub unsafe fn get_instInhabitedDiagnostics() -> *mut lean_object {
        symbols().inst_inhabited_diagnostics
    }
    pub unsafe fn get_instInhabitedMetavarContext() -> *mut lean_object {
        symbols().inst_inhabited_metavar_context
    }
    pub unsafe fn get_instInhabitedLocalContext() -> *mut lean_object {
        symbols().inst_inhabited_local_context
    }
    pub unsafe fn get_instInhabitedTraceState() -> *mut lean_object {
        symbols().inst_inhabited_trace_state
    }
    pub unsafe fn get_CoreInstInhabitedCache() -> *mut lean_object {
        symbols().core_inst_inhabited_cache
    }
    pub unsafe fn get_ElabInstInhabitedInfoState() -> *mut lean_object {
        symbols().elab_inst_inhabited_info_state
    }
    pub unsafe fn get_instInhabitedOptions() -> *mut lean_object {
        #[cfg(not(lean_4_28))]
        {
            symbols().inst_inhabited_options
        }
        #[cfg(lean_4_28)]
        {
            symbols().options_inst_inhabited
        }
    }
    pub unsafe fn get_instInhabitedMessageLog() -> *mut lean_object {
        symbols().inst_inhabited_message_log
    }
    pub unsafe fn get_instInhabitedNameGenerator() -> *mut lean_object {
        symbols().inst_inhabited_name_generator
    }
    #[cfg(lean_4_25)]
    pub unsafe fn get_instInhabitedDeclNameGenerator() -> *mut lean_object {
        symbols().inst_inhabited_decl_name_generator
    }
    pub unsafe fn get_instInhabitedSyntax() -> *mut lean_object {
        symbols().inst_inhabited_syntax
    }
    pub unsafe fn get_instInhabitedFileMap() -> *mut lean_object {
        symbols().inst_inhabited_file_map
    }
    pub unsafe fn get_PersistentHashMapEmpty() -> *mut lean_object {
        symbols().persistent_hashmap_empty
    }
    pub unsafe fn get_PersistentArrayEmpty() -> *mut lean_object {
        symbols().persistent_array_empty
    }
    pub unsafe fn get_KVMapEmpty() -> *mut lean_object {
        symbols().kvmap_empty
    }
}

// ============================================================================
// Cross-platform accessor functions
// ============================================================================
//
// On non-Windows these read the extern statics directly (zero cost).
// On Windows they delegate to the runtime-loaded pointers above.

/// Get the default `Meta.Config`.
#[inline]
pub unsafe fn get_instInhabitedConfig() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_Meta_instInhabitedConfig
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedConfig()
    }
}

/// Get the default `Meta.Context` (Lean >= 4.25).
#[cfg(lean_4_25)]
#[inline]
pub unsafe fn get_instInhabitedContext() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_Meta_instInhabitedContext
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedContext()
    }
}

/// Get the default `Meta.State`.
#[inline]
pub unsafe fn get_instInhabitedState() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_Meta_instInhabitedState
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedState()
    }
}

/// Get the default `Meta.Cache`.
#[inline]
pub unsafe fn get_instInhabitedCache() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_Meta_instInhabitedCache
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedCache()
    }
}

/// Get the default `Meta.Diagnostics`.
#[inline]
pub unsafe fn get_instInhabitedDiagnostics() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_Meta_instInhabitedDiagnostics
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedDiagnostics()
    }
}

/// Get the default `MetavarContext`.
#[inline]
pub unsafe fn get_instInhabitedMetavarContext() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_instInhabitedMetavarContext
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedMetavarContext()
    }
}

/// Get the default `LocalContext`.
#[inline]
pub unsafe fn get_instInhabitedLocalContext() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_instInhabitedLocalContext
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedLocalContext()
    }
}

/// Get the default `TraceState`.
#[inline]
pub unsafe fn get_instInhabitedTraceState() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_instInhabitedTraceState
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedTraceState()
    }
}

/// Get the default `Core.Cache`.
#[inline]
pub unsafe fn get_CoreInstInhabitedCache() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_Core_instInhabitedCache
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_CoreInstInhabitedCache()
    }
}

/// Get the default `Elab.InfoState`.
#[inline]
pub unsafe fn get_ElabInstInhabitedInfoState() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_Elab_instInhabitedInfoState
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_ElabInstInhabitedInfoState()
    }
}

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
        win_bss::get_instInhabitedOptions()
    }
}

/// Get the default `MessageLog`.
#[inline]
pub unsafe fn get_instInhabitedMessageLog() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_instInhabitedMessageLog
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedMessageLog()
    }
}

/// Get the default `NameGenerator`.
#[inline]
pub unsafe fn get_instInhabitedNameGenerator() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_instInhabitedNameGenerator
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedNameGenerator()
    }
}

/// Get the default `DeclNameGenerator` (Lean >= 4.25).
#[cfg(lean_4_25)]
#[inline]
pub unsafe fn get_instInhabitedDeclNameGenerator() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_instInhabitedDeclNameGenerator
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedDeclNameGenerator()
    }
}

/// Get the default `Syntax` (`Syntax.missing`).
#[inline]
pub unsafe fn get_instInhabitedSyntax() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_instInhabitedSyntax
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedSyntax()
    }
}

/// Get the default `FileMap`.
#[inline]
pub unsafe fn get_instInhabitedFileMap() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_instInhabitedFileMap
    }
    #[cfg(target_os = "windows")]
    {
        win_bss::get_instInhabitedFileMap()
    }
}

/// Get the empty `PersistentHashMap` singleton.
///
/// On non-Windows, reads the BSS global directly. On Windows, tries the BSS
/// global first, then falls back to manual construction (cached via `OnceLock`).
///
/// Layout: `PersistentHashMap.mk (Node.entries (mkArray 32 Entry.null)) 0`
/// - ctor tag 0, 2 obj fields, 0 scalar bytes
/// - field 0: `Node.entries` (ctor 0, 1 obj field = Array of 32 `Entry.null`)
/// - field 1: size = 0
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
            let bss = win_bss::get_PersistentHashMapEmpty();
            if !bss.is_null() {
                return bss as usize;
            }
            // Manual construction: PersistentHashMap.empty
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
/// On non-Windows, reads the BSS global directly. On Windows, tries the BSS
/// global first, then falls back to manual construction (cached via `OnceLock`).
///
/// Layout: `PersistentArray.mk (Node.node #[]) #[] 0 initShift 0`
/// - ctor tag 0, 4 obj fields (root, tail, size, tailOff), 4 scalar bytes (shift: UInt32)
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
            let bss = win_bss::get_PersistentArrayEmpty();
            if !bss.is_null() {
                return bss as usize;
            }
            // Manual construction: PersistentArray.empty
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
/// On non-Windows, reads the BSS global directly. On Windows, tries the BSS
/// global first, then falls back to `lean_box(0)` (KVMap is an inductive where
/// the empty constructor has tag 0 and 0 fields, so it's a scalar).
pub unsafe fn get_KVMapEmpty() -> *mut lean_object {
    #[cfg(not(target_os = "windows"))]
    {
        l_Lean_KVMap_empty
    }
    #[cfg(target_os = "windows")]
    {
        let bss = win_bss::get_KVMapEmpty();
        if !bss.is_null() {
            return bss;
        }
        // KVMap.empty = lean_box(0) — zero-field enum constructor (tag 0)
        lean_box(0)
    }
}
