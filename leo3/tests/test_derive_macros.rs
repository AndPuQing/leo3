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

// Test 11: Transparent newtype wrapper (tuple)
#[derive(Debug, PartialEq, IntoLean, FromLean)]
#[lean(transparent)]
struct UserId(u64);

#[test]
fn test_transparent_newtype() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let user_id = UserId(42);
        let lean_obj = user_id.into_lean(lean)?;
        let restored = UserId::from_lean(&lean_obj)?;
        assert_eq!(UserId(42), restored);
        Ok(())
    });

    assert!(result.is_ok());
}

// Test 12: Transparent newtype wrapper (named field)
#[derive(Debug, PartialEq, IntoLean, FromLean)]
#[lean(transparent)]
struct Email {
    address: String,
}

#[test]
fn test_transparent_named_field() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let email = Email {
            address: "test@example.com".to_string(),
        };
        let lean_obj = email.into_lean(lean)?;
        let restored = Email::from_lean(&lean_obj)?;
        assert_eq!(
            Email {
                address: "test@example.com".to_string()
            },
            restored
        );
        Ok(())
    });

    assert!(result.is_ok());
}

// Test 13: Transparent with generic type
#[derive(Debug, PartialEq, IntoLean, FromLean)]
#[lean(transparent)]
struct NewtypeWrapper<T>(T);

#[test]
fn test_transparent_generic() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test with u64
        let wrapper_u64 = NewtypeWrapper(100u64);
        let lean_u64 = wrapper_u64.into_lean(lean)?;
        let restored_u64 = NewtypeWrapper::<u64>::from_lean(&lean_u64)?;
        assert_eq!(NewtypeWrapper(100u64), restored_u64);

        // Test with String
        let wrapper_string = NewtypeWrapper("hello".to_string());
        let lean_string = wrapper_string.into_lean(lean)?;
        let restored_string = NewtypeWrapper::<String>::from_lean(&lean_string)?;
        assert_eq!(NewtypeWrapper("hello".to_string()), restored_string);

        Ok(())
    });

    assert!(result.is_ok());
}

// Test 14: Skip attribute - fields excluded from conversion
#[derive(Debug, PartialEq, IntoLean, FromLean)]
struct UserData {
    id: u64,
    name: String,
    #[lean(skip)]
    cached_hash: u64,
}

#[test]
fn test_skip_field() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let user = UserData {
            id: 42,
            name: "Alice".to_string(),
            cached_hash: 12345, // This will be ignored
        };
        let lean_obj = user.into_lean(lean)?;
        let restored = UserData::from_lean(&lean_obj)?;

        // cached_hash should be 0 (default) after round-trip
        assert_eq!(42, restored.id);
        assert_eq!("Alice", restored.name);
        assert_eq!(0, restored.cached_hash); // Default value
        Ok(())
    });

    assert!(result.is_ok());
}

// Test 15: Skip attribute with tuple struct
#[derive(Debug, PartialEq, IntoLean, FromLean)]
struct Point3D(u64, u64, #[lean(skip)] u64);

#[test]
fn test_skip_tuple_field() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let point = Point3D(10, 20, 30);
        let lean_obj = point.into_lean(lean)?;
        let restored = Point3D::from_lean(&lean_obj)?;

        assert_eq!(10, restored.0);
        assert_eq!(20, restored.1);
        assert_eq!(0, restored.2); // Skipped field gets default
        Ok(())
    });

    assert!(result.is_ok());
}

// Test 16: Default attribute - uses Default::default() on extraction failure
#[derive(Debug, PartialEq, IntoLean, FromLean)]
struct ConfigData {
    name: String,
    #[lean(default)]
    timeout: u64,
}

#[test]
fn test_default_field() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let config = ConfigData {
            name: "test".to_string(),
            timeout: 5000,
        };
        let lean_obj = config.into_lean(lean)?;
        let restored = ConfigData::from_lean(&lean_obj)?;

        assert_eq!("test", restored.name);
        assert_eq!(5000, restored.timeout);
        Ok(())
    });

    assert!(result.is_ok());
}

// Test 17: Skip the custom conversion test for now
// The 'with' attribute requires more complex setup that we'll handle in integration tests
// For now, we'll test that basic attribute combinations work

// Test 18: Rename attribute for better error messages
#[derive(Debug, PartialEq, IntoLean, FromLean)]
struct ApiResponse {
    #[lean(rename = "status_code")]
    status: u64,
    #[lean(rename = "response_body")]
    body: String,
}

#[test]
fn test_rename_attribute() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let response = ApiResponse {
            status: 200,
            body: "OK".to_string(),
        };
        let lean_obj = response.into_lean(lean)?;
        let restored = ApiResponse::from_lean(&lean_obj)?;

        assert_eq!(200, restored.status);
        assert_eq!("OK", restored.body);
        Ok(())
    });

    assert!(result.is_ok());
}

// Test 19: Multiple attributes combined
#[derive(Debug, PartialEq, IntoLean, FromLean)]
struct ComplexData {
    id: u64,
    #[lean(skip)]
    internal_cache: u64,
    #[lean(default)]
    optional_count: u64,
    #[lean(rename = "temperature")]
    temp: u64,
}

#[test]
fn test_multiple_attributes() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let data = ComplexData {
            id: 1,
            internal_cache: 999,
            optional_count: 42,
            temp: 25,
        };
        let lean_obj = data.into_lean(lean)?;
        let restored = ComplexData::from_lean(&lean_obj)?;

        assert_eq!(1, restored.id);
        assert_eq!(0, restored.internal_cache); // skipped, gets default
        assert_eq!(42, restored.optional_count);
        assert_eq!(25, restored.temp);
        Ok(())
    });

    assert!(result.is_ok());
}

// Test 20: Explicit tag attribute for enum variants
#[derive(Debug, PartialEq, IntoLean, FromLean)]
enum Protocol {
    #[lean(tag = 10)]
    Http,
    #[lean(tag = 20)]
    Https,
    #[lean(tag = 30)]
    Ftp(String),
}

#[test]
fn test_explicit_tags() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test Http with tag 10
        let http = Protocol::Http;
        let lean_http = http.into_lean(lean)?;
        let restored_http = Protocol::from_lean(&lean_http)?;
        assert_eq!(Protocol::Http, restored_http);

        // Test Https with tag 20
        let https = Protocol::Https;
        let lean_https = https.into_lean(lean)?;
        let restored_https = Protocol::from_lean(&lean_https)?;
        assert_eq!(Protocol::Https, restored_https);

        // Test Ftp with tag 30
        let ftp = Protocol::Ftp("server.com".to_string());
        let lean_ftp = ftp.into_lean(lean)?;
        let restored_ftp = Protocol::from_lean(&lean_ftp)?;
        assert_eq!(Protocol::Ftp("server.com".to_string()), restored_ftp);

        Ok(())
    });

    assert!(result.is_ok());
}
