//! Dynamic loading and calling of Lean4 compiled functions
//!
//! This module provides infrastructure for loading Lean4 compiled shared libraries
//! and calling exported functions from Rust.

use crate::ffi::{
    inline::lean_usize_of_nat, lean_initialize_runtime_module, lean_initialize_thread,
};
use crate::marker::Lean;
use crate::types::{LeanNat, LeanString};
use crate::{LeanBound, LeanResult};
use libloading::{Library, Symbol};
use std::path::Path;

/// A loaded Lean module with its exported functions
pub struct LeanModule {
    _library: Library,
    module_name: String,
}

impl LeanModule {
    /// Load a Lean module from a shared library file
    ///
    /// # Safety
    /// - The library must be a valid Lean4 compiled shared library
    /// - The library must export an `initialize_<ModuleName>` function
    ///
    /// # Example
    /// ```no_run
    /// use leo3::module::LeanModule;
    ///
    /// leo3::prepare_freethreaded_lean();
    ///
    /// let module = LeanModule::load("./libMyModule.so", "MyModule").unwrap();
    /// ```
    pub fn load<P: AsRef<Path>>(path: P, module_name: &str) -> Result<Self, String> {
        unsafe {
            // Ensure Lean runtime is initialized
            lean_initialize_runtime_module();
            lean_initialize_thread();

            // Load the library
            let library = Library::new(path.as_ref())
                .map_err(|e| format!("Failed to load library: {}", e))?;

            // Call the module's initialize function
            let init_fn_name = format!("initialize_{}", module_name);
            let init_fn: Symbol<
                unsafe extern "C" fn(u8, *mut std::ffi::c_void) -> *mut std::ffi::c_void,
            > = library.get(init_fn_name.as_bytes()).map_err(|e| {
                format!(
                    "Failed to find initialization function {}: {}",
                    init_fn_name, e
                )
            })?;

            // Call initialize function (builtin=0, world=null)
            let result = init_fn(0, std::ptr::null_mut());

            // Check if initialization was successful
            // TODO: Properly check lean_io_result_is_error
            if result.is_null() {
                return Err(format!("Module {} initialization failed", module_name));
            }

            Ok(Self {
                _library: library,
                module_name: module_name.to_string(),
            })
        }
    }

    /// Get the module name
    pub fn name(&self) -> &str {
        &self.module_name
    }
}

/// A handle to a Lean exported function
pub struct LeanFunction<'lib> {
    #[allow(dead_code)] // TODO: Implement call() method using this symbol
    symbol: Symbol<'lib, unsafe extern "C" fn() -> *mut std::ffi::c_void>,
    name: String,
}

impl<'lib> LeanFunction<'lib> {
    /// Look up an exported function by name
    ///
    /// # Safety
    /// - The function must exist and have the correct signature
    pub unsafe fn lookup(library: &'lib Library, name: &str) -> Result<Self, String> {
        let symbol: Symbol<unsafe extern "C" fn() -> *mut std::ffi::c_void> = library
            .get(name.as_bytes())
            .map_err(|e| format!("Failed to find function {}: {}", name, e))?;

        Ok(Self {
            symbol,
            name: name.to_string(),
        })
    }

    /// Get the function name
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// Trait for converting Rust types to Lean objects
///
/// Implement this trait for types that can be passed as arguments to Lean functions.
pub trait ToLean<'l> {
    /// The Lean type this converts to
    type Output;

    /// Convert this Rust value to a Lean object
    fn to_lean(self, lean: Lean<'l>) -> LeanResult<Self::Output>;
}

/// Trait for converting Lean objects to Rust types
///
/// Implement this trait for types that can be returned from Lean functions.
pub trait FromLean<'l>: Sized {
    /// Convert a Lean object to a Rust value
    fn from_lean(lean: Lean<'l>, obj: *mut std::ffi::c_void) -> LeanResult<Self>;
}

// Implementations for common types
impl<'l> ToLean<'l> for usize {
    type Output = LeanBound<'l, LeanNat>;

    fn to_lean(self, lean: Lean<'l>) -> LeanResult<Self::Output> {
        LeanNat::from_usize(lean, self)
    }
}

impl<'l> FromLean<'l> for usize {
    fn from_lean(_lean: Lean<'l>, obj: *mut std::ffi::c_void) -> LeanResult<Self> {
        unsafe {
            let nat_obj = obj as *mut crate::ffi::object::lean_object;
            Ok(lean_usize_of_nat(nat_obj))
        }
    }
}

impl<'l> ToLean<'l> for &str {
    type Output = LeanBound<'l, LeanString>;

    fn to_lean(self, lean: Lean<'l>) -> LeanResult<Self::Output> {
        LeanString::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for String {
    fn from_lean(lean: Lean<'l>, obj: *mut std::ffi::c_void) -> LeanResult<Self> {
        unsafe {
            let str_obj =
                LeanBound::from_owned_ptr(lean, obj as *mut crate::ffi::object::lean_object);
            let s = LeanString::cstr(&str_obj)?;
            Ok(s.to_string())
        }
    }
}
