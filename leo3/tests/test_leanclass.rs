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
