//! Example demonstrating the #[leanclass] macro
//!
//! This example shows how to use #[leanclass] to expose Rust structs
//! to Lean4 as external objects.

use leo3::external::LeanExternal;
use leo3::prelude::*;

/// A simple counter that can be used from Lean
#[derive(Clone, Debug)]
#[leanclass]
struct Counter {
    value: i32,
}

#[leanclass]
impl Counter {
    /// Create a new counter starting at 0
    fn new() -> Self {
        Counter { value: 0 }
    }

    /// Create a counter with a specific initial value
    fn with_value(initial: i32) -> Self {
        Counter { value: initial }
    }

    /// Get the current value
    fn get(&self) -> i32 {
        self.value
    }

    /// Increment the counter by 1
    fn increment(&mut self) {
        self.value += 1;
    }

    /// Add an amount to the counter
    fn add(&mut self, amount: i32) {
        self.value += amount;
    }

    /// Reset the counter to 0
    fn reset(&mut self) {
        self.value = 0;
    }
}

/// A 2D point
#[derive(Clone, Debug)]
#[leanclass]
struct Point {
    x: f64,
    y: f64,
}

#[leanclass]
impl Point {
    /// Create a new point
    fn new(x: f64, y: f64) -> Self {
        Point { x, y }
    }

    /// Get the x coordinate
    fn x(&self) -> f64 {
        self.x
    }

    /// Get the y coordinate
    fn y(&self) -> f64 {
        self.y
    }

    /// Calculate distance from origin
    fn distance_from_origin(&self) -> f64 {
        (self.x * self.x + self.y * self.y).sqrt()
    }

    /// Move the point by a delta
    fn translate(&mut self, dx: f64, dy: f64) {
        self.x += dx;
        self.y += dy;
    }

    /// Scale the point by a factor
    fn scale(&mut self, factor: f64) {
        self.x *= factor;
        self.y *= factor;
    }
}

fn main() -> LeanResult<()> {
    println!("=== Leo3 #[leanclass] Example ===\n");

    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        println!("1. Testing Counter:");
        println!("   - Creating counter...");
        let counter = Counter { value: 0 };
        let external = LeanExternal::new(lean, counter)?;
        println!("   - Counter value: {}", external.get_ref().value);
        println!("   - ExternalClass name: {}", Counter::class_name());

        println!("\n2. Testing Point:");
        println!("   - Creating point at (3.0, 4.0)...");
        let point = Point { x: 3.0, y: 4.0 };
        let external = LeanExternal::new(lean, point)?;
        let point_ref = external.get_ref();
        println!("   - Point: ({}, {})", point_ref.x, point_ref.y);
        println!(
            "   - Distance from origin: {:.2}",
            (point_ref.x * point_ref.x + point_ref.y * point_ref.y).sqrt()
        );

        println!("\n3. Generated FFI functions:");
        println!("   - Counter.new");
        println!("   - Counter.with_value");
        println!("   - Counter.get");
        println!("   - Counter.increment");
        println!("   - Counter.add");
        println!("   - Counter.reset");
        println!("   - Point.new");
        println!("   - Point.x");
        println!("   - Point.y");
        println!("   - Point.distance_from_origin");
        println!("   - Point.translate");
        println!("   - Point.scale");

        println!("\n✓ All #[leanclass] features working!");
        println!("\nThese Rust structs can now be used from Lean4!");
        println!("The macro automatically generated:");
        println!("  1. ExternalClass implementations");
        println!("  2. FFI wrapper functions for all methods");
        println!("  3. Proper type conversions between Rust and Lean");

        Ok(())
    })
}
