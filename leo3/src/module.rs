//! Dynamic loading and calling of Lean4 compiled functions
//!
//! This module provides infrastructure for loading Lean4 compiled shared libraries
//! and calling exported functions from Rust.

use crate::conversion::{FromLean, IntoLean};
use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanAny;
use crate::marker::Lean;
use crate::{LeanBound, LeanError};
use libloading::{Library, Symbol};
use std::path::Path;

unsafe fn set_importing_flag(importing: bool) {
    let value = ffi::inline::lean_box(importing as usize);
    let world = ffi::io::lean_io_mk_world();
    let result = ffi::lean_st_ref_set(ffi::lean_importing_ref, value, world);
    ffi::lean_dec(result);
}

unsafe fn try_decode_error_string<'l>(
    lean: Lean<'l>,
    ptr: *mut ffi::lean_object,
) -> Option<String> {
    ffi::lean_inc(ptr);
    let bound: LeanBound<'l, LeanAny> = LeanBound::from_owned_ptr(lean, ptr);
    String::from_lean(&bound.cast()).ok()
}

unsafe fn decode_io_error_message<'l>(lean: Lean<'l>, result: *mut ffi::lean_object) -> String {
    let err_ptr = ffi::io::lean_io_result_get_error(result) as *mut ffi::lean_object;

    if let Some(message) = try_decode_error_string(lean, err_ptr) {
        return message;
    }

    if !ffi::inline::lean_is_scalar(err_ptr) && ffi::inline::lean_ctor_num_objs(err_ptr) > 0 {
        let payload_ptr = ffi::lean_ctor_get(err_ptr, 0) as *mut ffi::lean_object;
        if let Some(message) = try_decode_error_string(lean, payload_ptr) {
            return message;
        }
    }

    "Lean IO.Error".to_string()
}

/// A loaded Lean module with its exported functions
pub struct LeanModule {
    library: Library,
    module_name: String,
}

impl LeanModule {
    /// Load a Lean module from a shared library file
    ///
    /// This method aligns module loading with Leo3's safe caller-thread entry
    /// path and temporarily enables Lean's importing mode while the shared
    /// library is loaded. Lean plugin/static initializers may register options
    /// after `IO.initializing` has ended, and Lean's own plugin loader permits
    /// that work through the same importing flag.
    ///
    /// # Safety
    /// - The library must be a valid Lean4 compiled shared library
    /// - The library must export an `initialize_<ModuleName>` function
    ///
    /// # Example
    /// ```no_run
    /// use leo3::module::LeanModule;
    ///
    /// let module = LeanModule::load("./libMyModule.so", "MyModule").unwrap();
    /// ```
    pub fn load<P: AsRef<Path>>(path: P, module_name: &str) -> LeanResult<Self> {
        unsafe {
            let path = path.as_ref();

            // Align module initialization with the same safe caller-thread
            // entry path used by `with_lean()`: make sure the runtime worker
            // exists and the current thread is attached before constructing
            // worlds or invoking module initialization code.
            crate::sync::ensure_lean_thread();

            // Match Lean's `withImporting` behavior around plugin loading so
            // load-time initializers can register options and environment
            // extensions even though Leo3's core runtime has completed
            // `IO.initializing`.
            set_importing_flag(true);
            let library = match Library::new(path) {
                Ok(library) => {
                    set_importing_flag(false);
                    library
                }
                Err(error) => {
                    set_importing_flag(false);
                    return Err(LeanError::module_load(path, error.to_string()));
                }
            };

            // Call the module's initialize function
            let init_fn_name = format!("initialize_{}", module_name);
            let init_fn: Symbol<
                unsafe extern "C" fn(u8, *mut std::ffi::c_void) -> *mut std::ffi::c_void,
            > = library
                .get(init_fn_name.as_bytes())
                .map_err(|e| LeanError::symbol_lookup(&init_fn_name, e.to_string()))?;

            // Call initialize function (builtin=0, world token). Keep the same
            // importing window open for module initializers declared with
            // Lean's `initialize` command.
            let world = ffi::io::lean_io_mk_world();
            set_importing_flag(true);
            let result = init_fn(0, world as *mut std::ffi::c_void);
            set_importing_flag(false);

            // Check if initialization was successful
            let result_ptr = result as *mut ffi::lean_object;
            if ffi::io::lean_io_result_is_error(result_ptr) {
                let lean = Lean::assume_initialized();
                let message = decode_io_error_message(lean, result_ptr);
                ffi::lean_dec(result_ptr);
                return Err(LeanError::module_initialization(module_name, message));
            }
            ffi::lean_dec(result_ptr);

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
    ) -> LeanResult<LeanFunction<'lib>> {
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
    unsafe fn lookup(library: &'lib Library, name: &str, arity: usize) -> LeanResult<Self> {
        let symbol: Symbol<unsafe extern "C" fn() -> *mut ffi::lean_object> = library
            .get(name.as_bytes())
            .map_err(|e| LeanError::symbol_lookup(name, e.to_string()))?;

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
            Err(LeanError::arity_mismatch(&self.name, self.arity, provided))
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
            let func: unsafe extern "C" fn(*mut ffi::lean_object) -> *mut ffi::lean_object =
                std::mem::transmute(*self.symbol);
            let result_ptr = func(arg_obj.into_ptr());
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
            let func: unsafe extern "C" fn(
                *mut ffi::lean_object,
                *mut ffi::lean_object,
            ) -> *mut ffi::lean_object = std::mem::transmute(*self.symbol);
            let result_ptr = func(a_obj.into_ptr(), b_obj.into_ptr());
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
        [$($ty:ident),+],
        [$($arg:ident),+],
        $fn_ty:ty
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

                let func: $fn_ty = std::mem::transmute(*self.symbol);
                let result_ptr = func(
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
    impl_call_n!(
        call3,
        3,
        [A, B, C],
        [a, b, c],
        unsafe extern "C" fn(
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
        ) -> *mut ffi::lean_object
    );
    impl_call_n!(
        call4,
        4,
        [A, B, C, D],
        [a, b, c, d],
        unsafe extern "C" fn(
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
        ) -> *mut ffi::lean_object
    );
    impl_call_n!(
        call5,
        5,
        [A, B, C, D, E],
        [a, b, c, d, e],
        unsafe extern "C" fn(
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
        ) -> *mut ffi::lean_object
    );
    impl_call_n!(
        call6,
        6,
        [A, B, C, D, E, F],
        [a, b, c, d, e, f],
        unsafe extern "C" fn(
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
        ) -> *mut ffi::lean_object
    );
    impl_call_n!(
        call7,
        7,
        [A, B, C, D, E, F, G],
        [a, b, c, d, e, f, g],
        unsafe extern "C" fn(
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
        ) -> *mut ffi::lean_object
    );
    impl_call_n!(
        call8,
        8,
        [A, B, C, D, E, F, G, H],
        [a, b, c, d, e, f, g, h],
        unsafe extern "C" fn(
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
            *mut ffi::lean_object,
        ) -> *mut ffi::lean_object
    );
}
