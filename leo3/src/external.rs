//! External objects for wrapping Rust types in Lean4.
//!
//! This module provides infrastructure for creating Lean external objects
//! that wrap Rust types, allowing them to be passed between Rust and Lean.
//!
//! # Example
//!
//! ```rust,ignore
//! use leo3::prelude::*;
//! use leo3::external::{ExternalClass, LeanExternal};
//!
//! // Define a Rust type
//! struct Counter {
//!     value: i32,
//! }
//!
//! // Implement ExternalClass
//! impl ExternalClass for Counter {
//!     fn class_name() -> &'static str {
//!         "Counter"
//!     }
//! }
//!
//! // Use it in Lean
//! leo3::with_lean(|lean| {
//!     let counter = Counter { value: 42 };
//!     let external = LeanExternal::new(lean, counter)?;
//!
//!     // Pass to Lean functions
//!     let result = some_lean_fn.call1(lean, external)?;
//!     Ok(())
//! })
//! ```

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;
use std::any::TypeId;
use std::collections::HashMap;
use std::sync::Mutex;

/// Trait for Rust types that can be wrapped as Lean external objects.
///
/// Types implementing this trait can be passed to Lean as opaque external objects.
pub trait ExternalClass: Sized + 'static {
    /// The name of this external class.
    ///
    /// This should be unique across your application.
    fn class_name() -> &'static str;

    /// Optional finalizer called when the Lean object is garbage collected.
    ///
    /// Default implementation does nothing. Override if you need cleanup logic.
    fn finalize(&mut self) {}
}

/// A Lean external object wrapping a Rust value.
///
/// This type represents a Lean external object that contains a Rust value of type `T`.
pub struct LeanExternalType<T: ExternalClass> {
    _phantom: std::marker::PhantomData<T>,
}

/// A bound Lean external object containing a Rust value.
pub type LeanExternal<'l, T> = LeanBound<'l, LeanExternalType<T>>;

// Global registry for external class information
static EXTERNAL_REGISTRY: Mutex<Option<ExternalRegistry>> = Mutex::new(None);

struct ExternalRegistry {
    classes: HashMap<TypeId, ExternalClassInfo>,
}

struct ExternalClassInfo {
    #[allow(dead_code)]
    name: &'static str,
    external_class: *mut std::ffi::c_void,
}

unsafe impl Send for ExternalClassInfo {}
unsafe impl Sync for ExternalClassInfo {}

impl ExternalRegistry {
    fn new() -> Self {
        Self {
            classes: HashMap::new(),
        }
    }

    fn get_or_register<T: ExternalClass>(&mut self) -> *mut std::ffi::c_void {
        let type_id = TypeId::of::<T>();

        if let Some(info) = self.classes.get(&type_id) {
            return info.external_class;
        }

        // Create new external class
        unsafe {
            let external_class = create_external_class::<T>();
            let info = ExternalClassInfo {
                name: T::class_name(),
                external_class,
            };
            self.classes.insert(type_id, info);
            external_class
        }
    }
}

/// Get or create the global external registry
fn get_registry() -> std::sync::MutexGuard<'static, Option<ExternalRegistry>> {
    let mut guard = EXTERNAL_REGISTRY.lock().unwrap();
    if guard.is_none() {
        *guard = Some(ExternalRegistry::new());
    }
    guard
}

/// Get the external class for a Rust type
fn get_external_class<T: ExternalClass>() -> *mut std::ffi::c_void {
    let mut registry = get_registry();
    registry.as_mut().unwrap().get_or_register::<T>()
}

// FFI callback for finalization
unsafe extern "C" fn finalize_external<T: ExternalClass>(data: *mut std::ffi::c_void) {
    if !data.is_null() {
        let value = Box::from_raw(data as *mut T);
        let mut value = *value;
        value.finalize();
    }
}

// FFI callback for foreach (mark phase of GC)
unsafe extern "C" fn foreach_external<T: ExternalClass>(
    _data: *mut std::ffi::c_void,
    _fn: ffi::object::b_lean_obj_arg,
) {
    // Default implementation: no nested Lean objects to mark
}

/// Create a new external class descriptor for type T
unsafe fn create_external_class<T: ExternalClass>() -> *mut std::ffi::c_void {
    ffi::object::lean_register_external_class(
        Some(finalize_external::<T>),
        Some(foreach_external::<T>),
    )
}

impl<'l, T: ExternalClass> LeanExternal<'l, T> {
    /// Create a new Lean external object wrapping a Rust value.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let counter = Counter { value: 42 };
    /// let external = LeanExternal::new(lean, counter)?;
    /// ```
    pub fn new(lean: Lean<'l>, value: T) -> LeanResult<Self> {
        unsafe {
            // Get or register the external class
            let external_class = get_external_class::<T>();

            // Box the value and convert to raw pointer
            let boxed = Box::new(value);
            let data_ptr = Box::into_raw(boxed) as *mut std::ffi::c_void;

            // Create the Lean external object
            let obj_ptr = ffi::lean_alloc_external(external_class, data_ptr);

            Ok(LeanBound::from_owned_ptr(lean, obj_ptr))
        }
    }

    /// Get a reference to the wrapped Rust value.
    ///
    /// # Safety
    ///
    /// This assumes the external object was created with the correct type `T`.
    /// Using the wrong type will result in undefined behavior.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let value: &Counter = external.get_ref();
    /// println!("Counter value: {}", value.value);
    /// ```
    pub fn get_ref(&self) -> &T {
        unsafe {
            let data_ptr = ffi::lean_get_external_data(self.as_ptr());
            &*(data_ptr as *const T)
        }
    }

    /// Get a mutable reference to the wrapped Rust value.
    ///
    /// # Safety
    ///
    /// This assumes:
    /// - The external object was created with the correct type `T`
    /// - The object is not shared (reference count is 1)
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let value: &mut Counter = unsafe { external.get_mut() };
    /// value.value += 1;
    /// ```
    pub unsafe fn get_mut(&mut self) -> &mut T {
        let data_ptr = ffi::lean_get_external_data(self.as_ptr());
        &mut *(data_ptr as *mut T)
    }

    /// Take the inner value out of an exclusively-owned external object.
    ///
    /// This moves the Rust value out without cloning. The external object's
    /// data pointer is set to null so the finalizer will not double-free.
    ///
    /// # Safety
    ///
    /// - The object must be exclusively owned (reference count == 1).
    /// - After calling this, the `LeanBound` wrapper should still be dropped
    ///   normally (it will dec-ref the Lean object, whose finalizer will see
    ///   null data and skip the Rust destructor).
    pub unsafe fn take_inner(&mut self) -> T {
        let data_ptr = ffi::lean_get_external_data(self.as_ptr());
        debug_assert!(
            !data_ptr.is_null(),
            "take_inner called on already-taken external object"
        );
        // Read the value out of the Box allocation.
        let value = std::ptr::read(data_ptr as *const T);
        // Null out m_data so the finalizer skips the Rust destructor.
        let ext = ffi::lean_to_external(self.as_ptr());
        (*ext).m_data = std::ptr::null_mut();
        // Free the Box allocation (without running T's destructor).
        std::alloc::dealloc(data_ptr as *mut u8, std::alloc::Layout::new::<T>());
        value
    }

    /// Check if this external object is of the correct type.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// if external.is_type::<Counter>() {
    ///     let counter = external.get_ref();
    ///     // ...
    /// }
    /// ```
    pub fn is_type<U: ExternalClass>(&self) -> bool {
        unsafe {
            let obj_class = ffi::lean_get_external_class(self.as_ptr());
            let expected_class = get_external_class::<U>();
            obj_class == expected_class
        }
    }

    /// Try to downcast to a different external type.
    ///
    /// Returns `None` if the types don't match.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// if let Some(counter) = any_external.try_cast::<Counter>() {
    ///     println!("It's a counter: {}", counter.get_ref().value);
    /// }
    /// ```
    pub fn try_cast<U: ExternalClass>(self) -> Option<LeanExternal<'l, U>> {
        if self.is_type::<U>() {
            Some(self.cast())
        } else {
            None
        }
    }
}

// Implement conversion traits
use crate::conversion::{FromLean, IntoLean};

impl<'l, T: ExternalClass> IntoLean<'l> for T {
    type Target = LeanExternalType<T>;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanExternal::new(lean, self)
    }
}

impl<'l, T: ExternalClass + Clone> FromLean<'l> for T {
    type Source = LeanExternalType<T>;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        let external: &LeanExternal<T> = unsafe { std::mem::transmute(obj) };
        Ok(external.get_ref().clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::LeanError;

    #[derive(Clone, Debug, PartialEq)]
    struct TestCounter {
        value: i32,
    }

    impl ExternalClass for TestCounter {
        fn class_name() -> &'static str {
            "TestCounter"
        }
    }

    #[derive(Clone, Debug, PartialEq)]
    struct TestData {
        name: String,
        count: usize,
    }

    impl ExternalClass for TestData {
        fn class_name() -> &'static str {
            "TestData"
        }
    }

    #[test]
    fn test_external_object_size() {
        // LeanExternal should be pointer-sized
        assert_eq!(
            std::mem::size_of::<LeanExternal<TestCounter>>(),
            std::mem::size_of::<*mut ()>()
        );
    }

    #[test]
    fn test_create_and_access_external() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let counter = TestCounter { value: 42 };
            let external = LeanExternal::new(lean, counter).unwrap();

            // Get reference to wrapped value
            let value_ref = external.get_ref();
            assert_eq!(value_ref.value, 42);

            Ok::<_, LeanError>(())
        })
        .unwrap();
    }

    #[test]
    fn test_external_type_checking() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let counter = TestCounter { value: 100 };
            let external = LeanExternal::new(lean, counter).unwrap();

            // Check correct type
            assert!(external.is_type::<TestCounter>());

            // Check incorrect type
            assert!(!external.is_type::<TestData>());

            Ok::<_, LeanError>(())
        })
        .unwrap();
    }

    #[test]
    fn test_external_try_cast() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let counter = TestCounter { value: 99 };
            let external = LeanExternal::new(lean, counter).unwrap();

            // Cast to correct type should succeed
            let external_any: LeanBound<LeanExternalType<TestCounter>> = external.clone();
            let casted = external_any.try_cast::<TestCounter>();
            assert!(casted.is_some());
            assert_eq!(casted.unwrap().get_ref().value, 99);

            // Cast to incorrect type should fail
            let external2 = LeanExternal::new(lean, TestCounter { value: 50 }).unwrap();
            let casted_wrong = external2.try_cast::<TestData>();
            assert!(casted_wrong.is_none());

            Ok::<_, LeanError>(())
        })
        .unwrap();
    }

    #[test]
    fn test_external_into_from_lean() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let original = TestCounter { value: 77 };

            // Test IntoLean
            let external: LeanBound<LeanExternalType<TestCounter>> =
                original.clone().into_lean(lean).unwrap();

            // Test FromLean
            let recovered: TestCounter = TestCounter::from_lean(&external).unwrap();

            assert_eq!(original, recovered);

            Ok::<_, LeanError>(())
        })
        .unwrap();
    }

    #[test]
    fn test_external_with_complex_type() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let data = TestData {
                name: "Test".to_string(),
                count: 123,
            };

            let external = LeanExternal::new(lean, data.clone()).unwrap();
            let retrieved = external.get_ref();

            assert_eq!(retrieved.name, "Test");
            assert_eq!(retrieved.count, 123);

            Ok::<_, LeanError>(())
        })
        .unwrap();
    }

    // Test with finalization callback
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    struct TestWithFinalizer {
        finalized: Arc<AtomicBool>,
    }

    impl ExternalClass for TestWithFinalizer {
        fn class_name() -> &'static str {
            "TestWithFinalizer"
        }

        fn finalize(&mut self) {
            self.finalized.store(true, Ordering::SeqCst);
        }
    }

    #[test]
    fn test_external_finalization() {
        crate::prepare_freethreaded_lean();

        let finalized = Arc::new(AtomicBool::new(false));
        let finalized_clone = finalized.clone();

        crate::with_lean(|lean| {
            let obj = TestWithFinalizer {
                finalized: finalized_clone,
            };

            let external = LeanExternal::new(lean, obj).unwrap();

            // Drop the external object
            drop(external);

            // Force garbage collection by creating many objects
            // Note: This is implementation-dependent and may not always trigger GC
            for _ in 0..1000 {
                let _ = LeanExternal::new(lean, TestCounter { value: 1 }).unwrap();
            }

            Ok::<_, LeanError>(())
        })
        .unwrap();

        // The finalization may or may not have been called yet
        // We just verify the test doesn't crash
    }
}
