//! Basic Leo3 usage example
//!
//! This example demonstrates basic usage patterns for Leo3, including:
//! - Runtime initialization
//! - Working with natural numbers
//! - String operations
//! - Array manipulation
//!
//! Note: This example requires Lean4 to be properly linked to run.

use leo3::prelude::*;

fn main() -> LeanResult<()> {
    println!("=== Leo3 Basic Example ===\n");

    // Initialize the Lean runtime
    leo3::prepare_freethreaded_lean();
    println!("✓ Lean runtime initialized\n");

    // All Lean operations must happen within with_lean
    leo3::with_lean(|lean| {
        // ======================================
        // Natural Number Examples
        // ======================================
        println!("--- Natural Numbers ---");

        let a = LeanNat::from_usize(lean, 10)?;
        let b = LeanNat::from_usize(lean, 32)?;
        println!("Created nat a = 10, b = 32");

        let sum = LeanNat::add(a, b)?;
        println!("Sum: 10 + 32 = {}", LeanNat::to_usize(&sum)?);

        let x = LeanNat::from_usize(lean, 6)?;
        let y = LeanNat::from_usize(lean, 7)?;
        let product = LeanNat::mul(x, y)?;
        println!("Product: 6 * 7 = {}", LeanNat::to_usize(&product)?);

        let base = LeanNat::from_usize(lean, 2)?;
        let exp = LeanNat::from_usize(lean, 10)?;
        let power = LeanNat::pow(base, exp)?;
        println!("Power: 2^10 = {}", LeanNat::to_usize(&power)?);

        println!();

        // ======================================
        // String Examples
        // ======================================
        println!("--- Strings ---");

        let s1 = LeanString::new(lean, "Hello, ")?;
        let s2 = LeanString::new(lean, "Lean4!")?;
        println!("Created strings: '{}' and '{}'",
                 LeanString::to_str(&s1)?,
                 LeanString::to_str(&s2)?);

        let s3 = LeanString::append(s1, &s2)?;
        println!("Concatenated: '{}'", LeanString::to_str(&s3)?);
        println!("Length: {} characters", LeanString::len(&s3));

        let s4 = LeanString::new(lean, "Welcome")?;
        let s5 = LeanString::push(s4, '!' as u32)?;
        println!("After push: '{}'", LeanString::to_str(&s5)?);

        println!();

        // ======================================
        // Array Examples
        // ======================================
        println!("--- Arrays ---");

        let mut arr = LeanArray::new(lean)?;
        println!("Created empty array");

        // Push some numbers
        for i in 1..=5 {
            let n = LeanNat::from_usize(lean, i * 10)?;
            arr = LeanArray::push(arr, n.cast())?;
        }
        println!("Pushed 5 elements: [10, 20, 30, 40, 50]");
        println!("Array size: {}", LeanArray::size(&arr));

        // Pop an element
        arr = LeanArray::pop(arr)?;
        println!("After pop: size = {}", LeanArray::size(&arr));

        // Swap elements
        arr = LeanArray::swap(arr, 0, 3)?;
        println!("After swapping indices 0 and 3");

        println!();

        // ======================================
        // Mixed Type Array Example
        // ======================================
        println!("--- Mixed Type Array ---");

        let mut mixed = LeanArray::new(lean)?;

        // Arrays can hold different types
        let num = LeanNat::from_usize(lean, 42)?;
        let text = LeanString::new(lean, "Answer")?;

        mixed = LeanArray::push(mixed, num.cast())?;
        mixed = LeanArray::push(mixed, text.cast())?;

        println!("Created array with nat and string");
        println!("Array size: {}", LeanArray::size(&mixed));

        println!();

        // ======================================
        // Reference Counting Examples
        // ======================================
        println!("--- Reference Counting ---");

        let n1 = LeanNat::from_usize(lean, 100)?;
        println!("Created nat: {}", LeanNat::to_usize(&n1)?);

        // Clone increments reference count
        let n2 = n1.clone();
        println!("Cloned nat: {}", LeanNat::to_usize(&n2)?);

        // Unbind and rebind
        let n_ref = n1.unbind();
        println!("Unbound nat to LeanRef (can be stored/sent)");

        let n3 = n_ref.bind(lean);
        println!("Rebound nat: {}", LeanNat::to_usize(&n3)?);

        println!();

        // ======================================
        // Computation Example: Fibonacci
        // ======================================
        println!("--- Computing Fibonacci Numbers ---");

        let mut fib_prev = LeanNat::from_usize(lean, 0)?;
        let mut fib_curr = LeanNat::from_usize(lean, 1)?;

        print!("Fibonacci sequence: {} {} ",
               LeanNat::to_usize(&fib_prev)?,
               LeanNat::to_usize(&fib_curr)?);

        for _ in 0..8 {
            let fib_next = LeanNat::add(fib_prev.clone(), fib_curr.clone())?;
            print!("{} ", LeanNat::to_usize(&fib_next)?);
            fib_prev = fib_curr;
            fib_curr = fib_next;
        }
        println!("\n");

        // ======================================
        // Computation Example: GCD
        // ======================================
        println!("--- Computing GCD ---");

        let a = LeanNat::from_usize(lean, 48)?;
        let b = LeanNat::from_usize(lean, 18)?;
        let gcd = LeanNat::gcd(a, b)?;
        println!("GCD(48, 18) = {}", LeanNat::to_usize(&gcd)?);

        let a = LeanNat::from_usize(lean, 100)?;
        let b = LeanNat::from_usize(lean, 35)?;
        let gcd = LeanNat::gcd(a, b)?;
        println!("GCD(100, 35) = {}", LeanNat::to_usize(&gcd)?);

        Ok(())
    })?;

    println!("\n=== Example completed successfully ===");

    Ok(())
}
