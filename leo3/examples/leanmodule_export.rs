//! Example demonstrating the `#[leanmodule]` macro for module export.
//!
//! The `#[leanmodule]` macro generates a `#[no_mangle] extern "C"` initialization
//! function (`initialize_<Name>`) that Lean4 calls when loading a Rust-backed module.
//! Functions inside the module remain callable from Rust as usual.

use leo3::prelude::*;

// A module with an explicit Lean-side name.
// Generates: extern "C" fn initialize_MathLib(...)
#[leanmodule(name = "MathLib")]
mod math_lib {
    pub fn add(a: u64, b: u64) -> u64 {
        a + b
    }

    pub fn factorial(n: u64) -> u64 {
        (1..=n).product()
    }
}

// A module using a bare identifier as the name.
// Generates: extern "C" fn initialize_StringUtils(...)
#[leanmodule(StringUtils)]
mod string_utils {
    pub fn reverse(s: &str) -> String {
        s.chars().rev().collect()
    }

    pub fn is_palindrome(s: &str) -> bool {
        let lower: String = s
            .chars()
            .filter(|c| c.is_alphanumeric())
            .map(|c| c.to_ascii_lowercase())
            .collect();
        lower == lower.chars().rev().collect::<String>()
    }
}

// A module with nested items (sub-modules, structs).
// Generates: extern "C" fn initialize_Geometry(...)
#[leanmodule(name = "Geometry")]
mod geometry {
    pub mod shapes {
        pub fn circle_area(radius: f64) -> f64 {
            std::f64::consts::PI * radius * radius
        }
    }

    pub struct Point {
        pub x: f64,
        pub y: f64,
    }

    impl Point {
        pub fn distance_to(&self, other: &Point) -> f64 {
            ((self.x - other.x).powi(2) + (self.y - other.y).powi(2)).sqrt()
        }
    }
}

fn main() -> LeanResult<()> {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|_lean| {
        println!("=== leanmodule Export Example ===\n");

        // Module functions are still callable from Rust.
        println!("MathLib:");
        println!("  add(3, 4)      = {}", math_lib::add(3, 4));
        println!("  factorial(6)   = {}", math_lib::factorial(6));

        println!("\nStringUtils:");
        println!("  reverse(\"lean\") = {}", string_utils::reverse("lean"));
        println!(
            "  is_palindrome(\"racecar\") = {}",
            string_utils::is_palindrome("racecar")
        );

        println!("\nGeometry:");
        println!(
            "  circle_area(1.0) = {:.4}",
            geometry::shapes::circle_area(1.0)
        );
        let a = geometry::Point { x: 0.0, y: 0.0 };
        let b = geometry::Point { x: 3.0, y: 4.0 };
        println!("  distance (0,0)→(3,4) = {}", a.distance_to(&b));

        println!("\n=== Done ===");
        Ok(())
    })
}
