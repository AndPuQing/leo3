//! Dynamic loading and calling of Lean4 compiled functions
//!
//! This module provides infrastructure for loading Lean4 compiled shared libraries
//! and calling exported functions from Rust.

use crate::conversion::{FromLean, IntoLean};
use crate::err::LeanResult;
use crate::ffi;
use crate::marker::Lean;
use crate::{LeanBound, LeanError};
use libloading::{Library, Symbol};
use std::path::Path;

/// A loaded Lean module with its exported functions
pub struct LeanModule {
    library: Library,
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
            ffi::lean_initialize_runtime_module();
            ffi::lean_initialize_thread();

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
                library,
                module_name: module_name.to_string(),
            })
        }
    }

    /// Get a function from the module by name
    ///
    /// The arity parameter specifies the number of arguments the function takes.
    /// This is used for runtime validation and proper calling convention.
    ///
    /// # Example
    /// ```no_run
    /// # use leo3::module::LeanModule;
    /// # leo3::prepare_freethreaded_lean();
    /// # let module = LeanModule::load("./libMyModule.so", "MyModule").unwrap();
    /// // Get a function that takes 2 arguments
    /// let add_fn = module.get_function("add", 2).unwrap();
    /// ```
    pub fn get_function<'lib>(
        &'lib self,
        name: &str,
        arity: usize,
    ) -> Result<LeanFunction<'lib>, String> {
        unsafe { LeanFunction::lookup(&self.library, name, arity) }
    }

    /// Get the module name
    pub fn name(&self) -> &str {
        &self.module_name
    }
}

/// A handle to a Lean exported function
///
/// Provides type-safe methods for calling Lean functions with different arities.
pub struct LeanFunction<'lib> {
    symbol: Symbol<'lib, unsafe extern "C" fn() -> *mut ffi::lean_object>,
    name: String,
    arity: usize,
}

impl<'lib> LeanFunction<'lib> {
    /// Look up an exported function by name
    ///
    /// # Safety
    /// - The function must exist and have the correct signature
    /// - The arity must match the actual function signature
    unsafe fn lookup(library: &'lib Library, name: &str, arity: usize) -> Result<Self, String> {
        let symbol: Symbol<unsafe extern "C" fn() -> *mut ffi::lean_object> = library
            .get(name.as_bytes())
            .map_err(|e| format!("Failed to find function {}: {}", name, e))?;

        Ok(Self {
            symbol,
            name: name.to_string(),
            arity,
        })
    }

    /// Get the function name
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the function arity (number of parameters)
    pub fn arity(&self) -> usize {
        self.arity
    }

    /// Check if the provided arity matches the function's arity
    fn check_arity(&self, provided: usize) -> LeanResult<()> {
        if self.arity != provided {
            Err(LeanError::other(&format!(
                "Function '{}' expects {} argument(s), but {} provided",
                self.name, self.arity, provided
            )))
        } else {
            Ok(())
        }
    }

    /// Call a 0-argument Lean function
    pub fn call0<'l, R>(&self, lean: Lean<'l>) -> LeanResult<R>
    where
        R: FromLean<'l> + 'l,
    {
        self.check_arity(0)?;

        unsafe {
            let func: unsafe extern "C" fn() -> *mut ffi::lean_object = *self.symbol;
            let result_ptr = func();
            let result_bound: LeanBound<R::Source> = LeanBound::from_owned_ptr(lean, result_ptr);
            R::from_lean(&result_bound)
        }
    }

    /// Call a 1-argument Lean function
    pub fn call1<'l, A, R>(&self, lean: Lean<'l>, arg: A) -> LeanResult<R>
    where
        A: IntoLean<'l> + 'l,
        R: FromLean<'l> + 'l,
    {
        self.check_arity(1)?;

        unsafe {
            let arg_obj = arg.into_lean(lean)?;
            let func: unsafe extern "C" fn() -> *mut ffi::lean_object = *self.symbol;
            let func_ptr = func();
            let result_ptr = ffi::closure::lean_apply_1(func_ptr, arg_obj.into_ptr());
            let result_bound: LeanBound<R::Source> = LeanBound::from_owned_ptr(lean, result_ptr);
            R::from_lean(&result_bound)
        }
    }

    /// Call a 2-argument Lean function
    pub fn call2<'l, A, B, R>(&self, lean: Lean<'l>, a: A, b: B) -> LeanResult<R>
    where
        A: IntoLean<'l> + 'l,
        B: IntoLean<'l> + 'l,
        R: FromLean<'l> + 'l,
    {
        self.check_arity(2)?;

        unsafe {
            let a_obj = a.into_lean(lean)?;
            let b_obj = b.into_lean(lean)?;
            let func: unsafe extern "C" fn() -> *mut ffi::lean_object = *self.symbol;
            let func_ptr = func();
            let result_ptr =
                ffi::closure::lean_apply_2(func_ptr, a_obj.into_ptr(), b_obj.into_ptr());
            let result_bound: LeanBound<R::Source> = LeanBound::from_owned_ptr(lean, result_ptr);
            R::from_lean(&result_bound)
        }
    }
}

// Macro to generate call3..call8 methods
macro_rules! impl_call_n {
    (
        $method_name:ident,
        $arity:literal,
        $apply_fn:ident,
        [$($ty:ident),+],
        [$($arg:ident),+]
    ) => {
        #[doc = concat!("Call a ", stringify!($arity), "-argument Lean function")]
        #[allow(clippy::too_many_arguments)]
        pub fn $method_name<'l, $($ty,)+ R>(
            &self,
            lean: Lean<'l>,
            $($arg: $ty,)+
        ) -> LeanResult<R>
        where
            $($ty: IntoLean<'l> + 'l,)+
            R: FromLean<'l> + 'l,
        {
            self.check_arity($arity)?;

            unsafe {
                // Convert arguments
                $(let $arg = $arg.into_lean(lean)?;)+

                // Get function pointer
                let func: unsafe extern "C" fn() -> *mut ffi::lean_object = *self.symbol;
                let func_ptr = func();

                // Call with lean_apply_N
                let result_ptr = ffi::closure::$apply_fn(
                    func_ptr,
                    $($arg.into_ptr(),)+
                );

                // Convert result
                let result_bound: LeanBound<R::Source> =
                    LeanBound::from_owned_ptr(lean, result_ptr);
                R::from_lean(&result_bound)
            }
        }
    };
}

// Implement call3..call8 using the macro
impl<'lib> LeanFunction<'lib> {
    impl_call_n!(call3, 3, lean_apply_3, [A, B, C], [a, b, c]);
    impl_call_n!(call4, 4, lean_apply_4, [A, B, C, D], [a, b, c, d]);
    impl_call_n!(call5, 5, lean_apply_5, [A, B, C, D, E], [a, b, c, d, e]);
    impl_call_n!(
        call6,
        6,
        lean_apply_6,
        [A, B, C, D, E, F],
        [a, b, c, d, e, f]
    );
    impl_call_n!(
        call7,
        7,
        lean_apply_7,
        [A, B, C, D, E, F, G],
        [a, b, c, d, e, f, g]
    );
    impl_call_n!(
        call8,
        8,
        lean_apply_8,
        [A, B, C, D, E, F, G, H],
        [a, b, c, d, e, f, g, h]
    );
}
