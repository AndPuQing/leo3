//! Lean signed integer type wrappers.
//!
//! Provides wrappers for Int8, Int16, Int32, Int64, and ISize types.
//!
//! In Lean4, these are structures that wrap UInt types using two's complement:
//! ```lean
//! structure Int8 where
//!   ofUInt8 :: toUInt8 : UInt8
//! ```

use crate::err::LeanResult;
use crate::ffi;
use crate::ffi::inline::*;
use crate::ffi::object::{
    lean_ctor_get_uint16, lean_ctor_get_uint32, lean_ctor_get_uint64, lean_ctor_get_uint8,
    lean_ctor_set_uint16, lean_ctor_set_uint32, lean_ctor_set_uint64, lean_ctor_set_uint8,
};
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::LeanChar;

// ============================================================================
// Int8
// ============================================================================

/// A Lean 8-bit signed integer.
///
/// In Lean4, this is represented as a structure wrapping UInt8 using two's complement.
pub struct LeanInt8 {
    _private: (),
}

#[allow(non_snake_case, missing_docs)]
impl LeanInt8 {
    /// The number of distinct values: 2^8 = 256.
    pub const SIZE: u32 = 256;

    /// The minimum value: -(2^7) = -128.
    pub const MIN: i8 = -128;

    /// The maximum value: 2^7 - 1 = 127.
    pub const MAX: i8 = 127;

    /// Create a Lean Int8 from a Rust i8.
    pub fn mk<'l>(lean: Lean<'l>, value: i8) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::lean_alloc_ctor(0, 0, 1);
            lean_ctor_set_uint8(ptr, 0, value as u8);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to Rust i8.
    pub fn to_i8<'l>(obj: &LeanBound<'l, Self>) -> i8 {
        unsafe { lean_ctor_get_uint8(obj.as_ptr(), 0) as i8 }
    }

    // Arithmetic operations

    /// Addition with wrapping semantics.
    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_add(Self::to_i8(a) as u8, Self::to_i8(b) as u8);
            Self::mk(lean, result as i8)
        }
    }

    /// Subtraction with wrapping semantics.
    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_sub(Self::to_i8(a) as u8, Self::to_i8(b) as u8);
            Self::mk(lean, result as i8)
        }
    }

    /// Multiplication with wrapping semantics.
    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_mul(Self::to_i8(a) as u8, Self::to_i8(b) as u8);
            Self::mk(lean, result as i8)
        }
    }

    /// Division. Returns 0 if divisor is 0.
    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_div(Self::to_i8(a) as u8, Self::to_i8(b) as u8);
            Self::mk(lean, result as i8)
        }
    }

    /// Modulo operation. Returns dividend if divisor is 0.
    pub fn mod_<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_mod(Self::to_i8(a) as u8, Self::to_i8(b) as u8);
            Self::mk(lean, result as i8)
        }
    }

    /// Negation with wrapping semantics.
    pub fn neg<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_neg(Self::to_i8(a) as u8);
            Self::mk(lean, result as i8)
        }
    }

    /// Absolute value with wrapping semantics.
    pub fn abs<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_abs(Self::to_i8(a) as u8);
            Self::mk(lean, result as i8)
        }
    }

    // Bitwise operations

    /// Bitwise AND.
    pub fn land<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_land(Self::to_i8(a) as u8, Self::to_i8(b) as u8);
            Self::mk(lean, result as i8)
        }
    }

    /// Bitwise OR.
    pub fn lor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_lor(Self::to_i8(a) as u8, Self::to_i8(b) as u8);
            Self::mk(lean, result as i8)
        }
    }

    /// Bitwise XOR.
    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_xor(Self::to_i8(a) as u8, Self::to_i8(b) as u8);
            Self::mk(lean, result as i8)
        }
    }

    /// Bitwise complement (NOT).
    pub fn complement<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_complement(Self::to_i8(a) as u8);
            Self::mk(lean, result as i8)
        }
    }

    /// Left shift (arithmetic).
    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_shift_left(Self::to_i8(a) as u8, Self::to_i8(b) as u8);
            Self::mk(lean, result as i8)
        }
    }

    /// Right shift (arithmetic - sign-extending).
    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int8_shift_right(Self::to_i8(a) as u8, Self::to_i8(b) as u8);
            Self::mk(lean, result as i8)
        }
    }

    // Comparison operations

    /// Check equality.
    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int8_dec_eq(Self::to_i8(a) as u8, Self::to_i8(b) as u8) }
    }

    /// Check if strictly less than.
    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int8_dec_lt(Self::to_i8(a) as u8, Self::to_i8(b) as u8) }
    }

    /// Check if less than or equal.
    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int8_dec_le(Self::to_i8(a) as u8, Self::to_i8(b) as u8) }
    }

    // Character operations

    /// Check if this value is a valid Unicode scalar.
    /// For signed integers, must be non-negative and valid Unicode.
    pub fn isValidChar<'l>(obj: &LeanBound<'l, Self>) -> bool {
        let val = Self::to_i8(obj);
        if val < 0 {
            return false;
        }
        let uval = val as u32;
        uval < 0xD800 || (0xE000..=0x10FFFF).contains(&uval)
    }

    /// Convert to LeanChar if valid Unicode scalar, otherwise return error.
    pub fn toChar<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanChar>> {
        let val = Self::to_i8(obj);
        if val < 0 {
            return Err(crate::err::LeanError::conversion(
                "Negative values cannot be converted to char",
            ));
        }
        let uval = val as u32;
        match char::from_u32(uval) {
            Some(c) => LeanChar::mk(lean, c),
            None => Err(crate::err::LeanError::conversion(
                "Invalid Unicode scalar value",
            )),
        }
    }

    // Conversions to/from arbitrary precision types

    /// Convert to LeanInt (arbitrary precision integer).
    pub fn toInt<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanInt>> {
        unsafe {
            let val = Self::to_i8(obj) as i64;
            let ptr = ffi::inline::lean_int64_to_int(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanInt (wrapping if out of range).
    pub fn ofInt<'l>(
        lean: Lean<'l>,
        int: &LeanBound<'l, crate::types::LeanInt>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let val = crate::types::LeanInt::to_i64(int).unwrap_or(0) as i8;
        Self::mk(lean, val)
    }

    /// Convert to LeanNat (fails for negative values).
    pub fn toNat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanNat>> {
        let val = Self::to_i8(obj);
        if val < 0 {
            return Err(crate::err::LeanError::conversion(
                "Negative values cannot be converted to Nat",
            ));
        }
        unsafe {
            let ptr = ffi::inline::lean_uint8_to_nat(val as u8);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanNat (wrapping if out of range).
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let val = ffi::inline::lean_uint8_of_nat(nat.as_ptr()) as i8;
            Self::mk(lean, val)
        }
    }

    // Float conversions

    /// Convert to LeanFloat (64-bit float).
    pub fn toFloat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat>> {
        unsafe {
            let val = Self::to_i8(obj) as f64;
            let ptr = ffi::inline::lean_box_float(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanInt8> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanInt8({})", LeanInt8::to_i8(self))
    }
}

// ============================================================================
// Int16
// ============================================================================

/// A Lean 16-bit signed integer.
pub struct LeanInt16 {
    _private: (),
}

#[allow(non_snake_case, missing_docs)]
impl LeanInt16 {
    /// The number of distinct values: 2^16 = 65536.
    pub const SIZE: u32 = 65536;

    /// The minimum value: -(2^15) = -32768.
    pub const MIN: i16 = -32768;

    /// The maximum value: 2^15 - 1 = 32767.
    pub const MAX: i16 = 32767;

    pub fn mk<'l>(lean: Lean<'l>, value: i16) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::lean_alloc_ctor(0, 0, 2);
            lean_ctor_set_uint16(ptr, 0, value as u16);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn to_i16<'l>(obj: &LeanBound<'l, Self>) -> i16 {
        unsafe { lean_ctor_get_uint16(obj.as_ptr(), 0) as i16 }
    }

    // Arithmetic operations

    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_add(Self::to_i16(a) as u16, Self::to_i16(b) as u16);
            Self::mk(lean, result as i16)
        }
    }

    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_sub(Self::to_i16(a) as u16, Self::to_i16(b) as u16);
            Self::mk(lean, result as i16)
        }
    }

    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_mul(Self::to_i16(a) as u16, Self::to_i16(b) as u16);
            Self::mk(lean, result as i16)
        }
    }

    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_div(Self::to_i16(a) as u16, Self::to_i16(b) as u16);
            Self::mk(lean, result as i16)
        }
    }

    pub fn mod_<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_mod(Self::to_i16(a) as u16, Self::to_i16(b) as u16);
            Self::mk(lean, result as i16)
        }
    }

    pub fn neg<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_neg(Self::to_i16(a) as u16);
            Self::mk(lean, result as i16)
        }
    }

    pub fn abs<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_abs(Self::to_i16(a) as u16);
            Self::mk(lean, result as i16)
        }
    }

    // Bitwise operations

    pub fn land<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_land(Self::to_i16(a) as u16, Self::to_i16(b) as u16);
            Self::mk(lean, result as i16)
        }
    }

    pub fn lor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_lor(Self::to_i16(a) as u16, Self::to_i16(b) as u16);
            Self::mk(lean, result as i16)
        }
    }

    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_xor(Self::to_i16(a) as u16, Self::to_i16(b) as u16);
            Self::mk(lean, result as i16)
        }
    }

    pub fn complement<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_complement(Self::to_i16(a) as u16);
            Self::mk(lean, result as i16)
        }
    }

    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_shift_left(Self::to_i16(a) as u16, Self::to_i16(b) as u16);
            Self::mk(lean, result as i16)
        }
    }

    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int16_shift_right(Self::to_i16(a) as u16, Self::to_i16(b) as u16);
            Self::mk(lean, result as i16)
        }
    }

    // Comparison operations

    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int16_dec_eq(Self::to_i16(a) as u16, Self::to_i16(b) as u16) }
    }

    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int16_dec_lt(Self::to_i16(a) as u16, Self::to_i16(b) as u16) }
    }

    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int16_dec_le(Self::to_i16(a) as u16, Self::to_i16(b) as u16) }
    }

    // Character operations

    pub fn isValidChar<'l>(obj: &LeanBound<'l, Self>) -> bool {
        let val = Self::to_i16(obj);
        if val < 0 {
            return false;
        }
        let uval = val as u32;
        uval < 0xD800 || (0xE000..=0x10FFFF).contains(&uval)
    }

    pub fn toChar<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanChar>> {
        let val = Self::to_i16(obj);
        if val < 0 {
            return Err(crate::err::LeanError::conversion(
                "Negative values cannot be converted to char",
            ));
        }
        let uval = val as u32;
        match char::from_u32(uval) {
            Some(c) => LeanChar::mk(lean, c),
            None => Err(crate::err::LeanError::conversion(
                "Invalid Unicode scalar value",
            )),
        }
    }

    // Conversions to/from arbitrary precision types

    /// Convert to LeanInt (arbitrary precision integer).
    pub fn toInt<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanInt>> {
        unsafe {
            let val = Self::to_i16(obj) as i64;
            let ptr = ffi::inline::lean_int64_to_int(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanInt (wrapping if out of range).
    pub fn ofInt<'l>(
        lean: Lean<'l>,
        int: &LeanBound<'l, crate::types::LeanInt>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let val = crate::types::LeanInt::to_i64(int).unwrap_or(0) as i16;
        Self::mk(lean, val)
    }

    /// Convert to LeanNat (fails for negative values).
    pub fn toNat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanNat>> {
        let val = Self::to_i16(obj);
        if val < 0 {
            return Err(crate::err::LeanError::conversion(
                "Negative values cannot be converted to Nat",
            ));
        }
        unsafe {
            let ptr = ffi::inline::lean_uint16_to_nat(val as u16);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanNat (wrapping if out of range).
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let val = ffi::inline::lean_uint16_of_nat(nat.as_ptr()) as i16;
            Self::mk(lean, val)
        }
    }

    // Float conversions

    /// Convert to LeanFloat (64-bit float).
    pub fn toFloat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat>> {
        unsafe {
            let val = Self::to_i16(obj) as f64;
            let ptr = ffi::inline::lean_box_float(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanInt16> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanInt16({})", LeanInt16::to_i16(self))
    }
}

// ============================================================================
// Int32
// ============================================================================

/// A Lean 32-bit signed integer.
pub struct LeanInt32 {
    _private: (),
}

#[allow(non_snake_case, missing_docs)]
impl LeanInt32 {
    /// The number of distinct values: 2^32 = 4294967296.
    pub const SIZE: u64 = 4294967296;

    /// The minimum value: -(2^31) = -2147483648.
    pub const MIN: i32 = -2147483648;

    /// The maximum value: 2^31 - 1 = 2147483647.
    pub const MAX: i32 = 2147483647;

    pub fn mk<'l>(lean: Lean<'l>, value: i32) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::lean_alloc_ctor(0, 0, 4);
            lean_ctor_set_uint32(ptr, 0, value as u32);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn to_i32<'l>(obj: &LeanBound<'l, Self>) -> i32 {
        unsafe { lean_ctor_get_uint32(obj.as_ptr(), 0) as i32 }
    }

    // Arithmetic operations

    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_add(Self::to_i32(a) as u32, Self::to_i32(b) as u32);
            Self::mk(lean, result as i32)
        }
    }

    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_sub(Self::to_i32(a) as u32, Self::to_i32(b) as u32);
            Self::mk(lean, result as i32)
        }
    }

    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_mul(Self::to_i32(a) as u32, Self::to_i32(b) as u32);
            Self::mk(lean, result as i32)
        }
    }

    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_div(Self::to_i32(a) as u32, Self::to_i32(b) as u32);
            Self::mk(lean, result as i32)
        }
    }

    pub fn mod_<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_mod(Self::to_i32(a) as u32, Self::to_i32(b) as u32);
            Self::mk(lean, result as i32)
        }
    }

    pub fn neg<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_neg(Self::to_i32(a) as u32);
            Self::mk(lean, result as i32)
        }
    }

    pub fn abs<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_abs(Self::to_i32(a) as u32);
            Self::mk(lean, result as i32)
        }
    }

    // Bitwise operations

    pub fn land<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_land(Self::to_i32(a) as u32, Self::to_i32(b) as u32);
            Self::mk(lean, result as i32)
        }
    }

    pub fn lor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_lor(Self::to_i32(a) as u32, Self::to_i32(b) as u32);
            Self::mk(lean, result as i32)
        }
    }

    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_xor(Self::to_i32(a) as u32, Self::to_i32(b) as u32);
            Self::mk(lean, result as i32)
        }
    }

    pub fn complement<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_complement(Self::to_i32(a) as u32);
            Self::mk(lean, result as i32)
        }
    }

    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_shift_left(Self::to_i32(a) as u32, Self::to_i32(b) as u32);
            Self::mk(lean, result as i32)
        }
    }

    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int32_shift_right(Self::to_i32(a) as u32, Self::to_i32(b) as u32);
            Self::mk(lean, result as i32)
        }
    }

    // Comparison operations

    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int32_dec_eq(Self::to_i32(a) as u32, Self::to_i32(b) as u32) }
    }

    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int32_dec_lt(Self::to_i32(a) as u32, Self::to_i32(b) as u32) }
    }

    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int32_dec_le(Self::to_i32(a) as u32, Self::to_i32(b) as u32) }
    }

    // Character operations

    pub fn isValidChar<'l>(obj: &LeanBound<'l, Self>) -> bool {
        let val = Self::to_i32(obj);
        if val < 0 {
            return false;
        }
        let uval = val as u32;
        uval < 0xD800 || (0xE000..=0x10FFFF).contains(&uval)
    }

    pub fn toChar<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanChar>> {
        let val = Self::to_i32(obj);
        if val < 0 {
            return Err(crate::err::LeanError::conversion(
                "Negative values cannot be converted to char",
            ));
        }
        let uval = val as u32;
        match char::from_u32(uval) {
            Some(c) => LeanChar::mk(lean, c),
            None => Err(crate::err::LeanError::conversion(
                "Invalid Unicode scalar value",
            )),
        }
    }

    // Conversions to/from arbitrary precision types

    /// Convert to LeanInt (arbitrary precision integer).
    pub fn toInt<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanInt>> {
        unsafe {
            let val = Self::to_i32(obj) as i64;
            let ptr = ffi::inline::lean_int64_to_int(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanInt (wrapping if out of range).
    pub fn ofInt<'l>(
        lean: Lean<'l>,
        int: &LeanBound<'l, crate::types::LeanInt>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let val = crate::types::LeanInt::to_i64(int).unwrap_or(0) as i32;
        Self::mk(lean, val)
    }

    /// Convert to LeanNat (fails for negative values).
    pub fn toNat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanNat>> {
        let val = Self::to_i32(obj);
        if val < 0 {
            return Err(crate::err::LeanError::conversion(
                "Negative values cannot be converted to Nat",
            ));
        }
        unsafe {
            let ptr = ffi::inline::lean_uint32_to_nat(val as u32);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanNat (wrapping if out of range).
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let val = ffi::inline::lean_uint32_of_nat(nat.as_ptr()) as i32;
            Self::mk(lean, val)
        }
    }

    // Float conversions

    /// Convert to LeanFloat (64-bit float).
    pub fn toFloat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat>> {
        unsafe {
            let val = Self::to_i32(obj) as f64;
            let ptr = ffi::inline::lean_box_float(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanInt32> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanInt32({})", LeanInt32::to_i32(self))
    }
}

// ============================================================================
// Int64
// ============================================================================

/// A Lean 64-bit signed integer.
pub struct LeanInt64 {
    _private: (),
}

#[allow(non_snake_case, missing_docs)]
impl LeanInt64 {
    /// The number of distinct values: 2^64.
    pub const SIZE: u128 = 18446744073709551616;

    /// The minimum value: -(2^63) = -9223372036854775808.
    pub const MIN: i64 = -9223372036854775808;

    /// The maximum value: 2^63 - 1 = 9223372036854775807.
    pub const MAX: i64 = 9223372036854775807;

    pub fn mk<'l>(lean: Lean<'l>, value: i64) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::lean_alloc_ctor(0, 0, 8);
            lean_ctor_set_uint64(ptr, 0, value as u64);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    pub fn to_i64<'l>(obj: &LeanBound<'l, Self>) -> i64 {
        unsafe { lean_ctor_get_uint64(obj.as_ptr(), 0) as i64 }
    }

    // Arithmetic operations

    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_add(Self::to_i64(a) as u64, Self::to_i64(b) as u64);
            Self::mk(lean, result as i64)
        }
    }

    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_sub(Self::to_i64(a) as u64, Self::to_i64(b) as u64);
            Self::mk(lean, result as i64)
        }
    }

    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_mul(Self::to_i64(a) as u64, Self::to_i64(b) as u64);
            Self::mk(lean, result as i64)
        }
    }

    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_div(Self::to_i64(a) as u64, Self::to_i64(b) as u64);
            Self::mk(lean, result as i64)
        }
    }

    pub fn mod_<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_mod(Self::to_i64(a) as u64, Self::to_i64(b) as u64);
            Self::mk(lean, result as i64)
        }
    }

    pub fn neg<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_neg(Self::to_i64(a) as u64);
            Self::mk(lean, result as i64)
        }
    }

    pub fn abs<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_abs(Self::to_i64(a) as u64);
            Self::mk(lean, result as i64)
        }
    }

    // Bitwise operations

    pub fn land<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_land(Self::to_i64(a) as u64, Self::to_i64(b) as u64);
            Self::mk(lean, result as i64)
        }
    }

    pub fn lor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_lor(Self::to_i64(a) as u64, Self::to_i64(b) as u64);
            Self::mk(lean, result as i64)
        }
    }

    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_xor(Self::to_i64(a) as u64, Self::to_i64(b) as u64);
            Self::mk(lean, result as i64)
        }
    }

    pub fn complement<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_complement(Self::to_i64(a) as u64);
            Self::mk(lean, result as i64)
        }
    }

    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_shift_left(Self::to_i64(a) as u64, Self::to_i64(b) as u64);
            Self::mk(lean, result as i64)
        }
    }

    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_int64_shift_right(Self::to_i64(a) as u64, Self::to_i64(b) as u64);
            Self::mk(lean, result as i64)
        }
    }

    // Comparison operations

    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int64_dec_eq(Self::to_i64(a) as u64, Self::to_i64(b) as u64) }
    }

    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int64_dec_lt(Self::to_i64(a) as u64, Self::to_i64(b) as u64) }
    }

    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_int64_dec_le(Self::to_i64(a) as u64, Self::to_i64(b) as u64) }
    }

    // Character operations

    pub fn isValidChar<'l>(obj: &LeanBound<'l, Self>) -> bool {
        let val = Self::to_i64(obj);
        if val < 0 || val > u32::MAX as i64 {
            return false;
        }
        let uval = val as u32;
        uval < 0xD800 || (0xE000..=0x10FFFF).contains(&uval)
    }

    pub fn toChar<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanChar>> {
        let val = Self::to_i64(obj);
        if val < 0 {
            return Err(crate::err::LeanError::conversion(
                "Negative values cannot be converted to char",
            ));
        }
        if val > u32::MAX as i64 {
            return Err(crate::err::LeanError::conversion(
                "Value out of range for Unicode scalar",
            ));
        }
        let uval = val as u32;
        match char::from_u32(uval) {
            Some(c) => LeanChar::mk(lean, c),
            None => Err(crate::err::LeanError::conversion(
                "Invalid Unicode scalar value",
            )),
        }
    }

    // Conversions to/from arbitrary precision types

    /// Convert to LeanInt (arbitrary precision integer).
    pub fn toInt<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanInt>> {
        unsafe {
            let val = Self::to_i64(obj);
            let ptr = ffi::inline::lean_int64_to_int(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanInt (wrapping if out of range).
    pub fn ofInt<'l>(
        lean: Lean<'l>,
        int: &LeanBound<'l, crate::types::LeanInt>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let val = crate::types::LeanInt::to_i64(int).unwrap_or(0);
        Self::mk(lean, val)
    }

    /// Convert to LeanNat (fails for negative values).
    pub fn toNat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanNat>> {
        let val = Self::to_i64(obj);
        if val < 0 {
            return Err(crate::err::LeanError::conversion(
                "Negative values cannot be converted to Nat",
            ));
        }
        unsafe {
            let ptr = ffi::inline::lean_uint64_to_nat(val as u64);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanNat (wrapping if out of range).
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let val = ffi::inline::lean_uint64_of_nat(nat.as_ptr()) as i64;
            Self::mk(lean, val)
        }
    }

    // Float conversions

    /// Convert to LeanFloat (64-bit float).
    pub fn toFloat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat>> {
        unsafe {
            let val = Self::to_i64(obj) as f64;
            let ptr = ffi::inline::lean_box_float(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanInt64> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanInt64({})", LeanInt64::to_i64(self))
    }
}

// ============================================================================
// ISize (platform-dependent)
// ============================================================================

/// A Lean platform-sized signed integer (ISize).
pub struct LeanISize {
    _private: (),
}

#[allow(non_snake_case, missing_docs)]
impl LeanISize {
    /// The number of distinct values (platform-dependent).
    #[cfg(target_pointer_width = "64")]
    pub const SIZE: u128 = 18446744073709551616; // 2^64

    #[cfg(target_pointer_width = "32")]
    pub const SIZE: u64 = 4294967296; // 2^32

    /// The minimum value (platform-dependent).
    #[cfg(target_pointer_width = "64")]
    pub const MIN: isize = -9223372036854775808; // -(2^63)

    #[cfg(target_pointer_width = "32")]
    pub const MIN: isize = -2147483648; // -(2^31)

    /// The maximum value (platform-dependent).
    #[cfg(target_pointer_width = "64")]
    pub const MAX: isize = 9223372036854775807; // 2^63 - 1

    #[cfg(target_pointer_width = "32")]
    pub const MAX: isize = 2147483647; // 2^31 - 1

    pub fn mk<'l>(lean: Lean<'l>, value: isize) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            if std::mem::size_of::<isize>() == 8 {
                let ptr = ffi::lean_alloc_ctor(0, 0, 8);
                lean_ctor_set_uint64(ptr, 0, value as u64);
                Ok(LeanBound::from_owned_ptr(lean, ptr))
            } else {
                let ptr = ffi::lean_alloc_ctor(0, 0, 4);
                lean_ctor_set_uint32(ptr, 0, value as u32);
                Ok(LeanBound::from_owned_ptr(lean, ptr))
            }
        }
    }

    pub fn to_isize<'l>(obj: &LeanBound<'l, Self>) -> isize {
        if std::mem::size_of::<isize>() == 8 {
            unsafe { lean_ctor_get_uint64(obj.as_ptr(), 0) as isize }
        } else {
            unsafe { lean_ctor_get_uint32(obj.as_ptr(), 0) as isize }
        }
    }

    // Arithmetic operations

    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_isize_add(Self::to_isize(a) as usize, Self::to_isize(b) as usize);
            Self::mk(lean, result as isize)
        }
    }

    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_isize_sub(Self::to_isize(a) as usize, Self::to_isize(b) as usize);
            Self::mk(lean, result as isize)
        }
    }

    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_isize_mul(Self::to_isize(a) as usize, Self::to_isize(b) as usize);
            Self::mk(lean, result as isize)
        }
    }

    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_isize_div(Self::to_isize(a) as usize, Self::to_isize(b) as usize);
            Self::mk(lean, result as isize)
        }
    }

    pub fn mod_<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_isize_mod(Self::to_isize(a) as usize, Self::to_isize(b) as usize);
            Self::mk(lean, result as isize)
        }
    }

    pub fn neg<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_isize_neg(Self::to_isize(a) as usize);
            Self::mk(lean, result as isize)
        }
    }

    pub fn abs<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_isize_abs(Self::to_isize(a) as usize);
            Self::mk(lean, result as isize)
        }
    }

    // Bitwise operations

    pub fn land<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_isize_land(Self::to_isize(a) as usize, Self::to_isize(b) as usize);
            Self::mk(lean, result as isize)
        }
    }

    pub fn lor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_isize_lor(Self::to_isize(a) as usize, Self::to_isize(b) as usize);
            Self::mk(lean, result as isize)
        }
    }

    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_isize_xor(Self::to_isize(a) as usize, Self::to_isize(b) as usize);
            Self::mk(lean, result as isize)
        }
    }

    pub fn complement<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_isize_complement(Self::to_isize(a) as usize);
            Self::mk(lean, result as isize)
        }
    }

    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result =
                lean_isize_shift_left(Self::to_isize(a) as usize, Self::to_isize(b) as usize);
            Self::mk(lean, result as isize)
        }
    }

    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result =
                lean_isize_shift_right(Self::to_isize(a) as usize, Self::to_isize(b) as usize);
            Self::mk(lean, result as isize)
        }
    }

    // Comparison operations

    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_isize_dec_eq(Self::to_isize(a) as usize, Self::to_isize(b) as usize) }
    }

    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_isize_dec_lt(Self::to_isize(a) as usize, Self::to_isize(b) as usize) }
    }

    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_isize_dec_le(Self::to_isize(a) as usize, Self::to_isize(b) as usize) }
    }

    // Character operations

    pub fn isValidChar<'l>(obj: &LeanBound<'l, Self>) -> bool {
        let val = Self::to_isize(obj);
        if val < 0 || val > u32::MAX as isize {
            return false;
        }
        let uval = val as u32;
        uval < 0xD800 || (0xE000..=0x10FFFF).contains(&uval)
    }

    pub fn toChar<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanChar>> {
        let val = Self::to_isize(obj);
        if val < 0 {
            return Err(crate::err::LeanError::conversion(
                "Negative values cannot be converted to char",
            ));
        }
        if val > u32::MAX as isize {
            return Err(crate::err::LeanError::conversion(
                "Value out of range for Unicode scalar",
            ));
        }
        let uval = val as u32;
        match char::from_u32(uval) {
            Some(c) => LeanChar::mk(lean, c),
            None => Err(crate::err::LeanError::conversion(
                "Invalid Unicode scalar value",
            )),
        }
    }

    // Conversions to/from arbitrary precision types

    /// Convert to LeanInt (arbitrary precision integer).
    pub fn toInt<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanInt>> {
        unsafe {
            let val = Self::to_isize(obj) as i64;
            let ptr = ffi::inline::lean_int64_to_int(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanInt (wrapping if out of range).
    pub fn ofInt<'l>(
        lean: Lean<'l>,
        int: &LeanBound<'l, crate::types::LeanInt>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let val = crate::types::LeanInt::to_i64(int).unwrap_or(0) as isize;
        Self::mk(lean, val)
    }

    /// Convert to LeanNat (fails for negative values).
    pub fn toNat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanNat>> {
        let val = Self::to_isize(obj);
        if val < 0 {
            return Err(crate::err::LeanError::conversion(
                "Negative values cannot be converted to Nat",
            ));
        }
        unsafe {
            let ptr = ffi::inline::lean_usize_to_nat(val as usize);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanNat (wrapping if out of range).
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let val = ffi::inline::lean_usize_of_nat(nat.as_ptr()) as isize;
            Self::mk(lean, val)
        }
    }

    // Float conversions

    /// Convert to LeanFloat (64-bit float).
    pub fn toFloat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat>> {
        unsafe {
            let val = Self::to_isize(obj) as f64;
            let ptr = ffi::inline::lean_box_float(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanISize> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanISize({})", LeanISize::to_isize(self))
    }
}
