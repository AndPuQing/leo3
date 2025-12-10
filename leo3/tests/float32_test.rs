use leo3::prelude::*;

#[test]
fn test_float32_creation() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> LeanResult<()> {
        let f = LeanFloat32::from_f32(lean, 3.14159)?;
        assert!((LeanFloat32::to_f32(&f) - 3.14159).abs() < 0.0001);
        Ok(())
    })
    .unwrap();
}

#[test]
fn test_float32_arithmetic() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanFloat32::from_f32(lean, 10.0)?;
        let b = LeanFloat32::from_f32(lean, 5.0)?;

        // Test addition
        let sum = LeanFloat32::add(lean, &a, &b)?;
        assert_eq!(LeanFloat32::to_f32(&sum), 15.0);

        // Test subtraction
        let diff = LeanFloat32::sub(lean, &a, &b)?;
        assert_eq!(LeanFloat32::to_f32(&diff), 5.0);

        // Test multiplication
        let prod = LeanFloat32::mul(lean, &a, &b)?;
        assert_eq!(LeanFloat32::to_f32(&prod), 50.0);

        // Test division
        let quot = LeanFloat32::div(lean, &a, &b)?;
        assert_eq!(LeanFloat32::to_f32(&quot), 2.0);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_float32_special_values() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test zero
        let zero = LeanFloat32::zero(lean)?;
        assert_eq!(LeanFloat32::to_f32(&zero), 0.0);

        // Test one
        let one = LeanFloat32::one(lean)?;
        assert_eq!(LeanFloat32::to_f32(&one), 1.0);

        // Test infinity
        let inf = LeanFloat32::infinity(lean)?;
        assert!(LeanFloat32::isInf(&inf));
        assert!(LeanFloat32::to_f32(&inf).is_infinite());

        // Test NaN
        let nan = LeanFloat32::nan(lean)?;
        assert!(LeanFloat32::isNaN(&nan));
        assert!(LeanFloat32::to_f32(&nan).is_nan());

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_float32_comparisons() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanFloat32::from_f32(lean, 5.0)?;
        let b = LeanFloat32::from_f32(lean, 10.0)?;
        let c = LeanFloat32::from_f32(lean, 5.0)?;

        // Test equality
        assert!(LeanFloat32::beq(&a, &c));
        assert!(!LeanFloat32::beq(&a, &b));

        // Test less than
        assert!(LeanFloat32::lt(&a, &b));
        assert!(!LeanFloat32::lt(&b, &a));

        // Test less than or equal
        assert!(LeanFloat32::le(&a, &b));
        assert!(LeanFloat32::le(&a, &c));
        assert!(!LeanFloat32::le(&b, &a));

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_float32_math_functions() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let x = LeanFloat32::from_f32(lean, 9.0)?;

        // Test square root
        let sqrt_x = LeanFloat32::sqrt(lean, x)?;
        assert_eq!(LeanFloat32::to_f32(&sqrt_x), 3.0);

        // Test absolute value
        let neg_x = LeanFloat32::from_f32(lean, -5.0)?;
        let abs_x = LeanFloat32::abs(lean, neg_x)?;
        assert_eq!(LeanFloat32::to_f32(&abs_x), 5.0);

        // Test floor
        let y = LeanFloat32::from_f32(lean, 3.7)?;
        let floor_y = LeanFloat32::floor(lean, y)?;
        assert_eq!(LeanFloat32::to_f32(&floor_y), 3.0);

        // Test ceil
        let ceil_y = LeanFloat32::ceil(lean, LeanFloat32::from_f32(lean, 3.2)?)?;
        assert_eq!(LeanFloat32::to_f32(&ceil_y), 4.0);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_float32_bits() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let f = LeanFloat32::from_f32(lean, 1.0)?;
        let bits = LeanFloat32::toBits(&f);

        // 1.0 in IEEE 754 binary32 is 0x3F800000
        assert_eq!(bits, 0x3F800000);

        // Test round trip
        let f2 = LeanFloat32::ofBits(lean, bits)?;
        assert_eq!(LeanFloat32::to_f32(&f2), 1.0);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_float32_to_float64_conversion() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let f32_val = LeanFloat32::from_f32(lean, 3.14)?;
        let f64_val = LeanFloat32::toFloat(&f32_val, lean)?;

        // Check that the conversion preserves the value (within f32 precision)
        assert!((LeanFloat::to_f64(&f64_val) - 3.14).abs() < 0.01);

        Ok(())
    })
    .unwrap();
}
