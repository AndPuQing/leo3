//! Tests for the #[leanclass] macro

use leo3::external::LeanExternal;
use leo3::prelude::*;

#[derive(Clone, Debug, PartialEq)]
#[leanclass]
struct Counter {
    value: i32,
}

#[leanclass]
impl Counter {
    fn new() -> Self {
        Counter { value: 0 }
    }

    fn new_with_value(initial: i32) -> Self {
        Counter { value: initial }
    }

    fn get(&self) -> i32 {
        self.value
    }

    fn set(&mut self, new_value: i32) {
        self.value = new_value;
    }

    fn increment(&mut self) {
        self.value += 1;
    }

    fn add(&self, amount: i32) -> i32 {
        self.value + amount
    }

    fn consume_and_return(self) -> i32 {
        self.value
    }
}

#[test]
fn test_leanclass_struct_compiles() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Test that we can create Counter instances
        let counter = Counter { value: 42 };
        let external = LeanExternal::new(lean, counter).unwrap();

        // Test that we can access the value
        let value_ref = external.get_ref();
        assert_eq!(value_ref.value, 42);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_leanclass_external_class_impl() {
    use leo3::external::ExternalClass;

    // Verify ExternalClass was implemented
    assert_eq!(Counter::class_name(), "Counter");
}

// Additional tests for Point struct
#[derive(Clone, Debug)]
#[leanclass]
struct Point {
    x: f64,
    y: f64,
}

#[leanclass]
impl Point {
    fn new(x: f64, y: f64) -> Self {
        Point { x, y }
    }

    fn get_x(&self) -> f64 {
        self.x
    }

    fn get_y(&self) -> f64 {
        self.y
    }

    fn distance(&self, other_x: f64, other_y: f64) -> f64 {
        let dx = self.x - other_x;
        let dy = self.y - other_y;
        (dx * dx + dy * dy).sqrt()
    }

    fn translate(&mut self, dx: f64, dy: f64) {
        self.x += dx;
        self.y += dy;
    }

    fn scale(&mut self, factor: f64) {
        self.x *= factor;
        self.y *= factor;
    }
}

#[test]
fn test_point_basic() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let point = Point { x: 3.0, y: 4.0 };
        let external = LeanExternal::new(lean, point).unwrap();

        let point_ref = external.get_ref();
        assert_eq!(point_ref.x, 3.0);
        assert_eq!(point_ref.y, 4.0);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_leanclass_ffi_functions_exist() {
    // This test just verifies that the FFI functions were generated and linked
    // We can't easily call them from Rust, but we can at least check they exist
    // by verifying the test compiles
}

// --- COW (Copy-on-Write) behavior tests ---

/// Helper: read the Counter value by borrowing the external object's inner data.
unsafe fn read_counter_value(ptr: *mut leo3::ffi::lean_object) -> i32 {
    let data_ptr = leo3::ffi::lean_get_external_data(ptr);
    (*(data_ptr as *const Counter)).value
}

#[test]
fn test_cow_exclusive_mutation_is_in_place() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create a Counter with value 5 — RC starts at 1 (exclusive)
        let counter = Counter { value: 5 };
        let external = LeanExternal::new(lean, counter).unwrap();
        let ptr = external.into_ptr();

        // Verify it's exclusive
        assert!(unsafe { leo3::ffi::object::lean_is_exclusive(ptr) });

        // Call increment via FFI — should mutate in place since RC == 1
        let result_ptr = unsafe { __lean_ffi_Counter_increment(ptr) };

        // For exclusive objects, the returned pointer should be the same object
        assert_eq!(
            ptr, result_ptr,
            "exclusive mutation must return the same object (in-place)"
        );

        // Read value directly from the external data
        let val = unsafe { read_counter_value(result_ptr) };
        assert_eq!(val, 6, "in-place mutation must update the value");

        // Clean up
        unsafe { leo3::ffi::object::lean_dec_ref(result_ptr) };

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_cow_shared_mutation_creates_copy() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create a Counter with value 10
        let counter = Counter { value: 10 };
        let external = LeanExternal::new(lean, counter).unwrap();
        let ptr = external.into_ptr();

        // Simulate sharing: bump refcount so lean_is_exclusive returns false
        unsafe { leo3::ffi::object::lean_inc_ref(ptr) };
        // ptr now has RC=2

        // Call increment via FFI — should COW-clone since RC > 1
        let new_ptr = unsafe { __lean_ffi_Counter_increment(ptr) };

        // The returned pointer must be a different object (a clone was made)
        assert_ne!(
            ptr, new_ptr,
            "shared mutation must return a new object, not mutate in place"
        );

        // Original should still have value 10
        let original_val = unsafe { read_counter_value(ptr) };
        assert_eq!(
            original_val, 10,
            "original object must be unchanged after COW"
        );

        // New object should have value 11
        let new_val = unsafe { read_counter_value(new_ptr) };
        assert_eq!(new_val, 11, "COW copy must reflect the mutation");

        // Clean up: we hold one extra ref on ptr (from inc_ref), and one on new_ptr
        unsafe {
            leo3::ffi::object::lean_dec_ref(ptr);
            leo3::ffi::object::lean_dec_ref(new_ptr);
        }

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_cow_multiple_shared_mutations_create_independent_copies() {
    use leo3::conversion::IntoLean;

    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create a Counter with value 0
        let counter = Counter { value: 0 };
        let external = LeanExternal::new(lean, counter).unwrap();
        let original_ptr = external.into_ptr();

        // Bump RC to 3 so it stays shared across two mutations
        unsafe {
            leo3::ffi::object::lean_inc_ref(original_ptr);
            leo3::ffi::object::lean_inc_ref(original_ptr);
        }
        // RC is now 3

        // First shared mutation: increment (0 -> 1)
        // This consumes one ref (RC 3→2 inside the wrapper's drop of borrowed)
        let copy1 = unsafe { __lean_ffi_Counter_increment(original_ptr) };

        // Second shared mutation: set(42)
        // original_ptr still has RC=2, so it's still shared.
        // inc_ref to give the FFI call a ref to consume
        unsafe { leo3::ffi::object::lean_inc_ref(original_ptr) };
        let copy2 = unsafe {
            // Create a proper LeanInt32 object for the i32 argument
            let lean_val = 42i32.into_lean(lean).unwrap();
            __lean_ffi_Counter_set(original_ptr, lean_val.into_ptr())
        };

        // All three should be different objects
        assert_ne!(original_ptr, copy1, "first COW must produce a new object");
        assert_ne!(original_ptr, copy2, "second COW must produce a new object");
        assert_ne!(copy1, copy2, "each COW must produce independent copies");

        // Verify values
        let orig_val = unsafe { read_counter_value(original_ptr) };
        let copy1_val = unsafe { read_counter_value(copy1) };
        let copy2_val = unsafe { read_counter_value(copy2) };

        assert_eq!(orig_val, 0, "original must remain 0");
        assert_eq!(copy1_val, 1, "first copy must be incremented to 1");
        assert_eq!(copy2_val, 42, "second copy must be set to 42");

        // Clean up remaining refs
        unsafe {
            leo3::ffi::object::lean_dec_ref(original_ptr);
            leo3::ffi::object::lean_dec_ref(copy1);
            leo3::ffi::object::lean_dec_ref(copy2);
        }

        Ok::<_, LeanError>(())
    })
    .unwrap();
}
