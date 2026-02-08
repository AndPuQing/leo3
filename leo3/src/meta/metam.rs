//! High-level wrapper for running Lean's MetaM monad computations from Rust.
//!
//! Lean's `MetaM` monad is the primary interface for type-checking, unification,
//! and metavariable management in Lean 4. It sits atop the `CoreM` monad and
//! adds a local context, metavariable context, and type-inference caches.
//!
//! This module provides [`MetaMContext`], which bundles all four context/state
//! objects required by the MetaM monad stack:
//!
//! | Lean type | Rust wrapper | Role |
//! |-----------|-------------|------|
//! | `Core.Context` | [`CoreContext`] | Read-only core settings (recursion depth, heartbeats, etc.) |
//! | `Core.State` | [`CoreState`] | Mutable core state (environment, name generator, messages) |
//! | `Meta.Context` | [`MetaContext`] | Read-only meta settings (local context, config) |
//! | `Meta.State` | [`MetaState`] | Mutable meta state (metavariable context, caches) |
//!
//! # Usage
//!
//! ```ignore
//! use leo3::prelude::*;
//! use leo3::meta::*;
//!
//! leo3::with_lean(|lean| {
//!     let env = LeanEnvironment::empty(lean, 0)?;
//!     let mut ctx = MetaMContext::new(lean, env)?;
//!
//!     // Once Phase 2 FFI bindings are available:
//!     // let result = ctx.run(some_metam_computation)?;
//!     Ok(())
//! })?;
//! ```
//!
//! # Architecture
//!
//! `MetaMContext::run()` calls the Lean FFI function `lean_meta_metam_run`,
//! which executes a `MetaM α` computation and returns `EIO Exception α`
//! (i.e., `Except Exception α` in the IO monad). The result is decoded
//! internally, extracting the success value or converting the `Exception`
//! into a [`LeanError::Exception`].
//!
//! Based on `/lean4/src/Lean/Meta/Basic.lean` (Issue #30).

use crate::err::{LeanError, LeanResult};
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;
use crate::meta::context::{CoreContext, CoreState, MetaContext, MetaState};
use crate::meta::LeanEnvironment;
use leo3_ffi as ffi;
use std::ffi::CStr;

/// Context for running MetaM computations.
///
/// `MetaMContext` bundles together all the context and state objects required
/// by Lean's MetaM monad: [`CoreContext`], [`CoreState`], [`MetaContext`], and
/// [`MetaState`]. It provides a [`run()`](Self::run) method to execute MetaM
/// computations and can be reused across multiple calls (context/state objects
/// are cloned before each FFI invocation).
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
///
///     // Access the environment
///     assert!(!ctx.env().as_ptr().is_null());
///
///     // The Lean runtime token is also available
///     let _lean = ctx.lean();
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
    /// Create a new `MetaMContext` from an environment.
    ///
    /// Constructs all required context and state objects with default values:
    /// - `Core.Context`: default settings (`maxRecDepth=1000`, `maxHeartbeats=200_000_000`)
    /// - `Core.State`: initialized with the given environment
    /// - `Meta.Context`: default Meta configuration (empty local context)
    /// - `Meta.State`: empty metavariable context and caches
    ///
    /// # Errors
    ///
    /// Returns [`LeanError`] if any of the underlying context/state constructors
    /// fail (e.g., due to allocation failure).
    ///
    /// # Example
    ///
    /// ```ignore
    /// use leo3::prelude::*;
    /// use leo3::meta::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let env = LeanEnvironment::empty(lean, 0)?;
    ///     let ctx = MetaMContext::new(lean, env)?;
    ///     assert!(!ctx.env().as_ptr().is_null());
    ///     Ok(())
    /// })?;
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
    /// # Errors
    ///
    /// Returns [`LeanError::Exception`] if the MetaM computation raises a
    /// Lean exception. The error includes:
    /// - `is_internal`: whether the exception is an internal error
    /// - `message`: best-effort extraction of the human-readable message
    ///
    /// # EIO Result Handling
    ///
    /// `MetaM.run'` returns `EIO Exception T`:
    /// - Tag 0 (`Except.ok`) -- field 0 contains the result value
    /// - Tag 1 (`Except.error`) -- field 0 contains the `Exception`
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

            let value_ptr = handle_eio_result(result)?;
            Ok(LeanBound::from_owned_ptr(self.lean, value_ptr))
        }
    }

    /// Get a reference to the [`LeanEnvironment`] used by this context.
    pub fn env(&self) -> &LeanBound<'l, LeanEnvironment> {
        &self.env
    }

    /// Get the [`Lean`] runtime token associated with this context.
    pub fn lean(&self) -> Lean<'l> {
        self.lean
    }
}

/// Handle an EIO result from a MetaM computation.
///
/// The EIO result is `Except Exception T`:
/// - Tag 0 = `Except.ok` → field 0 is the success value
/// - Tag 1 = `Except.error` → field 0 is the `Exception` object
///
/// On success, returns the owned value pointer. On error, extracts the
/// `Exception` and returns a `LeanError::Exception`.
///
/// # Safety
///
/// - `result` must be a valid Lean `Except Exception T` object (consumed)
unsafe fn handle_eio_result(result: *mut ffi::lean_object) -> LeanResult<*mut ffi::lean_object> {
    let tag = ffi::lean_obj_tag(result);
    if tag == 0 {
        // Except.ok - extract value
        let value_ptr = ffi::lean_ctor_get(result, 0) as *mut ffi::lean_object;
        ffi::lean_inc(value_ptr);
        ffi::lean_dec(result);
        return Ok(value_ptr);
    }

    // Except.error - extract Exception
    let exception_ptr = ffi::lean_ctor_get(result, 0) as *mut ffi::lean_object;
    ffi::lean_inc(exception_ptr);
    ffi::lean_dec(result);

    let exc_tag = ffi::lean_obj_tag(exception_ptr);
    let is_internal = exc_tag == 1;

    // Field 1 of both Exception constructors is MessageData
    let msg_data = ffi::lean_ctor_get(exception_ptr, 1) as *mut ffi::lean_object;
    let message = extract_message_data(msg_data);

    ffi::lean_dec(exception_ptr);

    Err(LeanError::exception(is_internal, &message))
}

/// Best-effort extraction of a human-readable string from Lean's `MessageData`.
///
/// `MessageData` is a complex inductive type. This function handles the most
/// common cases:
/// - `ofFormat` (tag 0): checks for `Format.text` (tag 0) containing a string
/// - `compose` (tag 10): recursively extracts from both children and concatenates
///
/// For other constructors, returns a descriptive fallback like `"<MessageData:expr>"`.
///
/// # Safety
///
/// - `msg_data` must be a valid Lean `MessageData` object (borrowed, not consumed)
unsafe fn extract_message_data(msg_data: *mut ffi::lean_object) -> String {
    if ffi::inline::lean_is_scalar(msg_data) {
        return "<MessageData:scalar>".to_string();
    }

    let tag = ffi::lean_obj_tag(msg_data);
    match tag {
        // MessageData.ofFormat (tag 0): field 0 is a Format
        0 => {
            let format = ffi::lean_ctor_get(msg_data, 0) as *mut ffi::lean_object;
            extract_format(format)
        }
        // MessageData.compose (tag 10): field 0 and field 1 are MessageData
        10 => {
            let left = ffi::lean_ctor_get(msg_data, 0) as *mut ffi::lean_object;
            let right = ffi::lean_ctor_get(msg_data, 1) as *mut ffi::lean_object;
            let left_str = extract_message_data(left);
            let right_str = extract_message_data(right);
            format!("{}{}", left_str, right_str)
        }
        1 => "<MessageData:level>".to_string(),
        2 => "<MessageData:name>".to_string(),
        3 => "<MessageData:syntax>".to_string(),
        4 => "<MessageData:expr>".to_string(),
        5 => "<MessageData:goal>".to_string(),
        6 => "<MessageData:withContext>".to_string(),
        7 => "<MessageData:withNamingContext>".to_string(),
        8 => "<MessageData:tagged>".to_string(),
        9 => "<MessageData:nest>".to_string(),
        11 => "<MessageData:group>".to_string(),
        12 => "<MessageData:node>".to_string(),
        13 => "<MessageData:trace>".to_string(),
        14 => "<MessageData:lazy>".to_string(),
        _ => format!("<MessageData:unknown(tag={})>", tag),
    }
}

/// Best-effort extraction of a string from Lean's `Format` type.
///
/// ```lean
/// inductive Format where
///   | text : String → Format       -- tag 0
///   | append : Format → Format → Format  -- tag 1
///   | ...
/// ```
///
/// # Safety
///
/// - `format` must be a valid Lean `Format` object (borrowed, not consumed)
unsafe fn extract_format(format: *mut ffi::lean_object) -> String {
    if ffi::inline::lean_is_scalar(format) {
        return "<Format:scalar>".to_string();
    }

    let tag = ffi::lean_obj_tag(format);
    match tag {
        // Format.text (tag 0): field 0 is a String
        0 => {
            let str_obj = ffi::lean_ctor_get(format, 0) as *mut ffi::lean_object;
            if str_obj.is_null() || ffi::inline::lean_is_scalar(str_obj) {
                return "<Format:invalid-string>".to_string();
            }
            let c_str = ffi::inline::lean_string_cstr(str_obj);
            match CStr::from_ptr(c_str).to_str() {
                Ok(s) => s.to_string(),
                Err(_) => "<Format:non-utf8>".to_string(),
            }
        }
        // Format.append (tag 1): field 0 and field 1 are Format
        1 => {
            let left = ffi::lean_ctor_get(format, 0) as *mut ffi::lean_object;
            let right = ffi::lean_ctor_get(format, 1) as *mut ffi::lean_object;
            let left_str = extract_format(left);
            let right_str = extract_format(right);
            format!("{}{}", left_str, right_str)
        }
        _ => format!("<Format:tag={}>", tag),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a synthetic `Except.ok value` object (tag 0, 1 field).
    unsafe fn mk_except_ok(value: *mut ffi::lean_object) -> *mut ffi::lean_object {
        let obj = ffi::lean_alloc_ctor(0, 1, 0);
        ffi::lean_ctor_set(obj, 0, value);
        obj
    }

    /// Build a synthetic `Except.error exception` object (tag 1, 1 field).
    unsafe fn mk_except_error(exception: *mut ffi::lean_object) -> *mut ffi::lean_object {
        let obj = ffi::lean_alloc_ctor(1, 1, 0);
        ffi::lean_ctor_set(obj, 0, exception);
        obj
    }

    /// Build a synthetic `Exception.error ref msg_data` (tag 0, 2 fields).
    unsafe fn mk_exception_error(
        ref_obj: *mut ffi::lean_object,
        msg_data: *mut ffi::lean_object,
    ) -> *mut ffi::lean_object {
        let obj = ffi::lean_alloc_ctor(0, 2, 0);
        ffi::lean_ctor_set(obj, 0, ref_obj);
        ffi::lean_ctor_set(obj, 1, msg_data);
        obj
    }

    /// Build a synthetic `Exception.internal id msg_data` (tag 1, 2 fields).
    unsafe fn mk_exception_internal(
        id: *mut ffi::lean_object,
        msg_data: *mut ffi::lean_object,
    ) -> *mut ffi::lean_object {
        let obj = ffi::lean_alloc_ctor(1, 2, 0);
        ffi::lean_ctor_set(obj, 0, id);
        ffi::lean_ctor_set(obj, 1, msg_data);
        obj
    }

    /// Build `MessageData.ofFormat fmt` (tag 0, 1 field).
    unsafe fn mk_msg_data_of_format(fmt: *mut ffi::lean_object) -> *mut ffi::lean_object {
        let obj = ffi::lean_alloc_ctor(0, 1, 0);
        ffi::lean_ctor_set(obj, 0, fmt);
        obj
    }

    /// Build `Format.text str` (tag 0, 1 field).
    unsafe fn mk_format_text(s: &str) -> *mut ffi::lean_object {
        let lean_str = ffi::string::lean_mk_string_from_bytes(s.as_ptr() as *const _, s.len());
        let obj = ffi::lean_alloc_ctor(0, 1, 0);
        ffi::lean_ctor_set(obj, 0, lean_str);
        obj
    }

    #[test]
    fn test_handle_eio_result_ok() {
        let result: LeanResult<()> = crate::test_with_lean(|_lean| {
            unsafe {
                // Create a dummy value (boxed 42)
                let value = ffi::lean_box(42);
                let except_ok = mk_except_ok(value);

                let result = handle_eio_result(except_ok);
                assert!(result.is_ok());

                let ptr = result.unwrap();
                // The value should be the boxed 42
                let unboxed = ffi::lean_unbox(ptr);
                assert_eq!(unboxed, 42);
                // ptr is a scalar (boxed), no need to dec
            }
            Ok(())
        });
        assert!(result.is_ok(), "test failed: {:?}", result.err());
    }

    #[test]
    fn test_handle_eio_result_error_with_text_message() {
        let result: LeanResult<()> = crate::test_with_lean(|_lean| {
            unsafe {
                // Build: Except.error (Exception.error ref (MessageData.ofFormat (Format.text "test error")))
                let format_text = mk_format_text("test error");
                let msg_data = mk_msg_data_of_format(format_text);
                let ref_obj = ffi::lean_box(0); // dummy Ref (scalar)
                let exception = mk_exception_error(ref_obj, msg_data);
                let except_err = mk_except_error(exception);

                let result = handle_eio_result(except_err);
                assert!(result.is_err());

                let err = result.unwrap_err();
                match &err {
                    LeanError::Exception {
                        is_internal,
                        message,
                    } => {
                        assert!(!is_internal);
                        assert_eq!(message, "test error");
                    }
                    other => panic!("Expected Exception, got: {:?}", other),
                }
            }
            Ok(())
        });
        assert!(result.is_ok(), "test failed: {:?}", result.err());
    }

    #[test]
    fn test_handle_eio_result_internal_exception() {
        let result: LeanResult<()> = crate::test_with_lean(|_lean| {
            unsafe {
                // Build: Except.error (Exception.internal id (MessageData.ofFormat (Format.text "internal fail")))
                let format_text = mk_format_text("internal fail");
                let msg_data = mk_msg_data_of_format(format_text);
                let id_obj = ffi::lean_box(0); // dummy InternalExceptionId (scalar)
                let exception = mk_exception_internal(id_obj, msg_data);
                let except_err = mk_except_error(exception);

                let result = handle_eio_result(except_err);
                assert!(result.is_err());

                let err = result.unwrap_err();
                match &err {
                    LeanError::Exception {
                        is_internal,
                        message,
                    } => {
                        assert!(is_internal);
                        assert_eq!(message, "internal fail");
                    }
                    other => panic!("Expected Exception, got: {:?}", other),
                }
            }
            Ok(())
        });
        assert!(result.is_ok(), "test failed: {:?}", result.err());
    }

    #[test]
    fn test_extract_message_data_scalar() {
        let result: LeanResult<()> = crate::test_with_lean(|_lean| {
            unsafe {
                // A scalar (tagged pointer) should return the fallback
                let scalar = ffi::lean_box(0);
                let msg = extract_message_data(scalar);
                assert_eq!(msg, "<MessageData:scalar>");
            }
            Ok(())
        });
        assert!(result.is_ok(), "test failed: {:?}", result.err());
    }

    #[test]
    fn test_extract_format_text() {
        let result: LeanResult<()> = crate::test_with_lean(|_lean| {
            unsafe {
                let format_text = mk_format_text("hello world");
                let msg = extract_format(format_text);
                assert_eq!(msg, "hello world");
                ffi::lean_dec(format_text);
            }
            Ok(())
        });
        assert!(result.is_ok(), "test failed: {:?}", result.err());
    }
}
