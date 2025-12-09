//! Tests for derive macros: `#[derive(IntoLean, FromLean)]`

use leo3::ffi;
use leo3::prelude::*;

// Test 1: Simple struct with primitive fields
#[derive(Debug, PartialEq, IntoLean, FromLean)]
struct Point {
    x: u64,
    y: u64,
}

#[test]
fn test_simple_struct() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let original = Point { x: 10, y: 20 };

        // Convert to Lean
        let lean_obj = original.into_lean(lean)?;

        // Verify it's a constructor with tag 0
        unsafe {
            assert_eq!(ffi::lean_obj_tag(lean_obj.as_ptr()), 0);
        }

        // Convert back to Rust
        let restored = Point::from_lean(&lean_obj)?;

        // Verify equality
        assert_eq!(Point { x: 10, y: 20 }, restored);

        Ok(())
    });

    assert!(result.is_ok());
}

// Test 2: Tuple struct
#[derive(Debug, PartialEq, IntoLean, FromLean)]
struct Pair(u64, u64);

#[test]
fn test_tuple_struct() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let original = Pair(42, 84);
        let lean_obj = original.into_lean(lean)?;
        let restored = Pair::from_lean(&lean_obj)?;
        assert_eq!(Pair(42, 84), restored);
        Ok(())
    });

    assert!(result.is_ok());
}

// Test 3: Nested struct
#[derive(Debug, PartialEq, IntoLean, FromLean)]
struct Rectangle {
    top_left: Point,
    bottom_right: Point,
}

#[test]
fn test_nested_struct() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let original = Rectangle {
            top_left: Point { x: 0, y: 0 },
            bottom_right: Point { x: 100, y: 200 },
        };

        let lean_obj = original.into_lean(lean)?;
        let restored = Rectangle::from_lean(&lean_obj)?;

        assert_eq!(
            Rectangle {
                top_left: Point { x: 0, y: 0 },
                bottom_right: Point { x: 100, y: 200 },
            },
            restored
        );

        Ok(())
    });

    assert!(result.is_ok());
}

// Test 4: Unit enum
#[derive(Debug, PartialEq, IntoLean, FromLean)]
enum Color {
    Red,
    Green,
    Blue,
}

#[test]
fn test_unit_enum() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test Red (tag 0)
        let red = Color::Red;
        let lean_red = red.into_lean(lean)?;
        unsafe {
            assert_eq!(ffi::lean_obj_tag(lean_red.as_ptr()), 0);
        }
        let restored_red = Color::from_lean(&lean_red)?;
        assert_eq!(Color::Red, restored_red);

        // Test Green (tag 1)
        let green = Color::Green;
        let lean_green = green.into_lean(lean)?;
        unsafe {
            assert_eq!(ffi::lean_obj_tag(lean_green.as_ptr()), 1);
        }
        let restored_green = Color::from_lean(&lean_green)?;
        assert_eq!(Color::Green, restored_green);

        // Test Blue (tag 2)
        let blue = Color::Blue;
        let lean_blue = blue.into_lean(lean)?;
        unsafe {
            assert_eq!(ffi::lean_obj_tag(lean_blue.as_ptr()), 2);
        }
        let restored_blue = Color::from_lean(&lean_blue)?;
        assert_eq!(Color::Blue, restored_blue);

        Ok(())
    });

    assert!(result.is_ok());
}

// Test 5: Enum with tuple variants
#[derive(Debug, PartialEq, IntoLean, FromLean)]
enum Shape {
    Circle(u64),             // radius
    Rectangle(u64, u64),     // width, height
    Triangle(u64, u64, u64), // side1, side2, side3
}

#[test]
fn test_enum_with_tuple_variants() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test Circle
        let circle = Shape::Circle(10);
        let lean_circle = circle.into_lean(lean)?;
        unsafe {
            assert_eq!(ffi::lean_obj_tag(lean_circle.as_ptr()), 0);
        }
        let restored_circle = Shape::from_lean(&lean_circle)?;
        assert_eq!(Shape::Circle(10), restored_circle);

        // Test Rectangle
        let rect = Shape::Rectangle(20, 30);
        let lean_rect = rect.into_lean(lean)?;
        unsafe {
            assert_eq!(ffi::lean_obj_tag(lean_rect.as_ptr()), 1);
        }
        let restored_rect = Shape::from_lean(&lean_rect)?;
        assert_eq!(Shape::Rectangle(20, 30), restored_rect);

        // Test Triangle
        let tri = Shape::Triangle(3, 4, 5);
        let lean_tri = tri.into_lean(lean)?;
        unsafe {
            assert_eq!(ffi::lean_obj_tag(lean_tri.as_ptr()), 2);
        }
        let restored_tri = Shape::from_lean(&lean_tri)?;
        assert_eq!(Shape::Triangle(3, 4, 5), restored_tri);

        Ok(())
    });

    assert!(result.is_ok());
}

// Test 6: Enum with struct variants
#[derive(Debug, PartialEq, IntoLean, FromLean)]
enum Message {
    Quit,
    Move { x: u64, y: u64 },
    Write { text: String },
}

#[test]
fn test_enum_with_struct_variants() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test Quit
        let quit = Message::Quit;
        let lean_quit = quit.into_lean(lean)?;
        let restored_quit = Message::from_lean(&lean_quit)?;
        assert_eq!(Message::Quit, restored_quit);

        // Test Move
        let move_msg = Message::Move { x: 10, y: 20 };
        let lean_move = move_msg.into_lean(lean)?;
        let restored_move = Message::from_lean(&lean_move)?;
        assert_eq!(Message::Move { x: 10, y: 20 }, restored_move);

        // Test Write
        let write_msg = Message::Write {
            text: "Hello".to_string(),
        };
        let lean_write = write_msg.into_lean(lean)?;
        let restored_write = Message::from_lean(&lean_write)?;
        assert_eq!(
            Message::Write {
                text: "Hello".to_string()
            },
            restored_write
        );

        Ok(())
    });

    assert!(result.is_ok());
}

// Test 7: Generic struct
#[derive(Debug, PartialEq, IntoLean, FromLean)]
struct Wrapper<T> {
    value: T,
}

#[test]
fn test_generic_struct() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test with u64
        let original_u64 = Wrapper { value: 42u64 };
        let lean_u64 = original_u64.into_lean(lean)?;
        let restored_u64 = Wrapper::<u64>::from_lean(&lean_u64)?;
        assert_eq!(Wrapper { value: 42u64 }, restored_u64);

        // Test with bool
        let original_bool = Wrapper { value: true };
        let lean_bool = original_bool.into_lean(lean)?;
        let restored_bool = Wrapper::<bool>::from_lean(&lean_bool)?;
        assert_eq!(Wrapper { value: true }, restored_bool);

        Ok(())
    });

    assert!(result.is_ok());
}

// Test 8: Generic enum (Result-like)
#[derive(Debug, PartialEq, IntoLean, FromLean)]
enum MyResult<T, E> {
    Ok(T),
    Err(E),
}

#[test]
fn test_generic_enum() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test Ok variant
        let ok_val: MyResult<u64, String> = MyResult::Ok(42u64);
        let lean_ok = ok_val.into_lean(lean)?;
        unsafe {
            assert_eq!(ffi::lean_obj_tag(lean_ok.as_ptr()), 0);
        }
        let restored_ok = MyResult::<u64, String>::from_lean(&lean_ok)?;
        assert_eq!(MyResult::Ok(42u64), restored_ok);

        // Test Err variant
        let err_val: MyResult<u64, String> = MyResult::Err("error".to_string());
        let lean_err = err_val.into_lean(lean)?;
        unsafe {
            assert_eq!(ffi::lean_obj_tag(lean_err.as_ptr()), 1);
        }
        let restored_err = MyResult::<u64, String>::from_lean(&lean_err)?;
        assert_eq!(MyResult::Err("error".to_string()), restored_err);

        Ok(())
    });

    assert!(result.is_ok());
}

// Test 9: Unit struct
#[derive(Debug, PartialEq, IntoLean, FromLean)]
struct Unit;

#[test]
fn test_unit_struct() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let original = Unit;
        let lean_obj = original.into_lean(lean)?;
        let restored = Unit::from_lean(&lean_obj)?;
        assert_eq!(Unit, restored);
        Ok(())
    });

    assert!(result.is_ok());
}

// Test 10: Struct with all primitive types
#[derive(Debug, PartialEq, IntoLean, FromLean)]
struct AllPrimitives {
    a: u8,
    b: u16,
    c: u32,
    d: u64,
    e: usize,
    f: bool,
    g: String,
}

#[test]
fn test_all_primitives() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let original = AllPrimitives {
            a: 1,
            b: 2,
            c: 3,
            d: 4,
            e: 5,
            f: true,
            g: "test".to_string(),
        };

        let lean_obj = original.into_lean(lean)?;
        let restored = AllPrimitives::from_lean(&lean_obj)?;

        assert_eq!(
            AllPrimitives {
                a: 1,
                b: 2,
                c: 3,
                d: 4,
                e: 5,
                f: true,
                g: "test".to_string(),
            },
            restored
        );

        Ok(())
    });

    assert!(result.is_ok());
}
