//! Traits for converting between Rust and Lean types.
//!
//! This module provides traits for converting between Rust values and Lean objects.

use crate::err::LeanResult;
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;
use crate::types::{
    LeanArray, LeanBool, LeanByteArray, LeanExcept, LeanFloat, LeanFloat32, LeanISize, LeanInt16,
    LeanInt32, LeanInt64, LeanInt8, LeanOption, LeanString, LeanUInt16, LeanUInt32, LeanUInt64,
    LeanUInt8, LeanUSize,
};

/// Macro for automatic conversion dispatch. For `Vec<u8>` and `&[u8]`, uses optimized
/// bulk memcpy. For other types, delegates to IntoLean trait.
#[macro_export]
macro_rules! to_lean {
    ($vec:expr, $lean:expr, Vec<u8>) => {
        $crate::conversion::vec_u8_into_lean($vec, $lean)
    };
    ($slice:expr, $lean:expr, &[u8]) => {
        $crate::conversion::slice_u8_into_lean($slice, $lean)
    };
    ($value:expr, $lean:expr) => {
        $crate::conversion::IntoLean::into_lean($value, $lean)
    };
}

/// Macro for automatic conversion from Lean. For `Vec<u8>`, uses optimized conversion.
/// For other types, delegates to FromLean trait.
#[macro_export]
macro_rules! from_lean {
    ($obj:expr, Vec<u8>) => {
        Ok::<Vec<u8>, $crate::err::LeanError>($crate::conversion::vec_u8_from_lean($obj))
    };
    ($obj:expr, $ty:ty) => {
        <$ty as $crate::conversion::FromLean>::from_lean($obj)
    };
}

/// Trait for types that can be converted from Rust to Lean.
///
/// # Example
///
/// ```rust,ignore
/// impl<'l> IntoLean<'l> for u64 {
///     type Target = LeanNat;
///
///     fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
///         Ok(LeanNat::from_u64(lean, self))
///     }
/// }
/// ```
pub trait IntoLean<'l> {
    /// The target Lean type
    type Target;

    /// Convert this value into a Lean object.
    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>>;
}

/// Trait for types that can be converted from Lean to Rust.
///
/// # Example
///
/// ```rust,ignore
/// impl<'l> FromLean<'l> for u64 {
///     fn from_lean(obj: &LeanBound<'l, LeanNat>) -> LeanResult<Self> {
///         obj.to_u64()
///     }
/// }
/// ```
pub trait FromLean<'l>: Sized {
    /// The source Lean type
    type Source;

    /// Extract a Rust value from a Lean object.
    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self>;
}

// u64 ↔ LeanUInt64
impl<'l> IntoLean<'l> for u64 {
    type Target = LeanUInt64;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanUInt64::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for u64 {
    type Source = LeanUInt64;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanUInt64::to_u64(obj))
    }
}

// usize ↔ LeanUSize
impl<'l> IntoLean<'l> for usize {
    type Target = LeanUSize;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanUSize::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for usize {
    type Source = LeanUSize;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanUSize::to_usize(obj))
    }
}

// u32 ↔ LeanUInt32
impl<'l> IntoLean<'l> for u32 {
    type Target = LeanUInt32;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanUInt32::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for u32 {
    type Source = LeanUInt32;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanUInt32::to_u32(obj))
    }
}

// u16 ↔ LeanUInt16
impl<'l> IntoLean<'l> for u16 {
    type Target = LeanUInt16;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanUInt16::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for u16 {
    type Source = LeanUInt16;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanUInt16::to_u16(obj))
    }
}

// u8 ↔ LeanUInt8
impl<'l> IntoLean<'l> for u8 {
    type Target = LeanUInt8;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanUInt8::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for u8 {
    type Source = LeanUInt8;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanUInt8::to_u8(obj))
    }
}

// i8 ↔ LeanInt8
impl<'l> IntoLean<'l> for i8 {
    type Target = LeanInt8;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanInt8::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for i8 {
    type Source = LeanInt8;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanInt8::to_i8(obj))
    }
}

// i16 ↔ LeanInt16
impl<'l> IntoLean<'l> for i16 {
    type Target = LeanInt16;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanInt16::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for i16 {
    type Source = LeanInt16;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanInt16::to_i16(obj))
    }
}

// i32 ↔ LeanInt32
impl<'l> IntoLean<'l> for i32 {
    type Target = LeanInt32;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanInt32::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for i32 {
    type Source = LeanInt32;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanInt32::to_i32(obj))
    }
}

// i64 ↔ LeanInt64
impl<'l> IntoLean<'l> for i64 {
    type Target = LeanInt64;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanInt64::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for i64 {
    type Source = LeanInt64;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanInt64::to_i64(obj))
    }
}

// isize ↔ LeanISize
impl<'l> IntoLean<'l> for isize {
    type Target = LeanISize;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanISize::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for isize {
    type Source = LeanISize;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanISize::to_isize(obj))
    }
}

// f32 ↔ LeanFloat32
impl<'l> IntoLean<'l> for f32 {
    type Target = LeanFloat32;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanFloat32::from_f32(lean, self)
    }
}

impl<'l> FromLean<'l> for f32 {
    type Source = LeanFloat32;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanFloat32::to_f32(obj))
    }
}

// f64 ↔ LeanFloat
impl<'l> IntoLean<'l> for f64 {
    type Target = LeanFloat;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanFloat::from_f64(lean, self)
    }
}

impl<'l> FromLean<'l> for f64 {
    type Source = LeanFloat;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanFloat::to_f64(obj))
    }
}

// bool ↔ LeanBool
impl<'l> IntoLean<'l> for bool {
    type Target = LeanBool;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanBool::mk(lean, self)
    }
}

impl<'l> FromLean<'l> for bool {
    type Source = LeanBool;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        Ok(LeanBool::toBool(obj))
    }
}

// () ↔ Unit (Lean's Unit type)
// In Lean4, Unit is represented as a constructor with no data
impl<'l> FromLean<'l> for () {
    type Source = LeanAny;

    fn from_lean(_obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        // Unit has no data, just return ()
        Ok(())
    }
}

// String ↔ LeanString
impl<'l> IntoLean<'l> for String {
    type Target = LeanString;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanString::mk(lean, &self)
    }
}

impl<'l> FromLean<'l> for String {
    type Source = LeanString;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanString::cstr(obj).map(|s| s.to_string())
    }
}

// &str → LeanString (one-way conversion)
impl<'l> IntoLean<'l> for &str {
    type Target = LeanString;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanString::mk(lean, self)
    }
}

// Vec<T> ↔ LeanArray
impl<'l, T> IntoLean<'l> for Vec<T>
where
    T: IntoLean<'l> + 'l,
{
    type Target = LeanArray;

    /// Convert a `Vec<T>` to a `LeanArray`.
    ///
    /// Note: For `Vec<u8>`, consider using `vec_u8_into_lean()` or the `to_lean!` macro
    /// for better performance via bulk memcpy.
    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        // Optimized implementation: pre-allocate capacity to avoid reallocations
        let len = self.len();

        if len == 0 {
            return LeanArray::empty(lean);
        }

        // Pre-allocate array with exact capacity needed
        let mut arr = LeanArray::with_capacity(lean, len)?;

        // Use push_unchecked for better performance (no capacity checks)
        for item in self {
            let lean_item = item.into_lean(lean)?;
            let any_item: LeanBound<'l, LeanAny> = lean_item.cast();
            arr = unsafe { LeanArray::push_unchecked(arr, any_item)? };
        }

        Ok(arr)
    }
}

impl<'l, T> FromLean<'l> for Vec<T>
where
    T: FromLean<'l> + 'l,
{
    type Source = LeanArray;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        let size = LeanArray::size(obj);

        // Pre-allocate Vec with exact capacity
        let mut result = Vec::with_capacity(size);

        // Direct element access without intermediate allocations
        for i in 0..size {
            let elem = LeanArray::get(obj, i)
                .ok_or_else(|| crate::err::LeanError::runtime("Index out of bounds"))?;
            let typed_elem: LeanBound<'l, T::Source> = elem.cast();
            let rust_item = T::from_lean(&typed_elem)?;
            result.push(rust_item);
        }

        Ok(result)
    }
}

impl<'l, T> IntoLean<'l> for Option<T>
where
    T: IntoLean<'l> + 'l,
{
    type Target = LeanOption;

    /// Convert a Rust `Option<T>` to a Lean `Option`.
    ///
    /// Maps `None` to `Option.none` and `Some(value)` to `Option.some value`.
    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        match self {
            None => LeanOption::none(lean),
            Some(value) => {
                let lean_value = value.into_lean(lean)?;
                let any_value: LeanBound<'l, LeanAny> = lean_value.cast();
                LeanOption::some(any_value)
            }
        }
    }
}

impl<'l, T> FromLean<'l> for Option<T>
where
    T: FromLean<'l> + 'l,
{
    type Source = LeanOption;

    /// Convert a Lean `Option` to a Rust `Option<T>`.
    ///
    /// Maps `Option.none` to `None` and `Option.some value` to `Some(value)`.
    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        match LeanOption::get(obj) {
            None => Ok(None),
            Some(any_value) => {
                let typed_value: LeanBound<'l, T::Source> = any_value.cast();
                let rust_value = T::from_lean(&typed_value)?;
                Ok(Some(rust_value))
            }
        }
    }
}

impl<'l, T, E> IntoLean<'l> for Result<T, E>
where
    T: IntoLean<'l> + 'l,
    E: IntoLean<'l> + 'l,
{
    type Target = LeanExcept;

    /// Convert a Rust `Result<T, E>` to a Lean `Except`.
    ///
    /// Maps `Err(error)` to `Except.error` and `Ok(value)` to `Except.ok`.
    ///
    /// Note: Lean's `Except ε α` has the error type (ε) first, unlike Rust's `Result<T, E>`.
    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        match self {
            Err(error) => {
                let lean_error = error.into_lean(lean)?;
                let any_error: LeanBound<'l, LeanAny> = lean_error.cast();
                LeanExcept::error(any_error)
            }
            Ok(value) => {
                let lean_value = value.into_lean(lean)?;
                let any_value: LeanBound<'l, LeanAny> = lean_value.cast();
                LeanExcept::ok(any_value)
            }
        }
    }
}

impl<'l, T, E> FromLean<'l> for Result<T, E>
where
    T: FromLean<'l> + 'l,
    E: FromLean<'l> + 'l,
{
    type Source = LeanExcept;

    /// Convert a Lean `Except` to a Rust `Result<T, E>`.
    ///
    /// Maps `Except.error` to `Err(error)` and `Except.ok` to `Ok(value)`.
    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        match LeanExcept::toRustResult(obj) {
            Err(any_error) => {
                let typed_error: LeanBound<'l, E::Source> = any_error.cast();
                let rust_error = E::from_lean(&typed_error)?;
                Ok(Err(rust_error))
            }
            Ok(any_value) => {
                let typed_value: LeanBound<'l, T::Source> = any_value.cast();
                let rust_value = T::from_lean(&typed_value)?;
                Ok(Ok(rust_value))
            }
        }
    }
}

// Note: These are provided as helper functions instead of trait implementations
// to avoid trait specialization conflicts in stable Rust.

/// Optimized bulk conversion: `Vec<u8>` → LeanByteArray using single memcpy
///
/// This is ~100-1000x faster than element-by-element conversion for large arrays.
///
/// # Example
///
/// ```rust,ignore
/// let data = vec![1, 2, 3, 4, 5];
/// let ba = vec_u8_into_lean(data, lean)?;
/// ```
pub fn vec_u8_into_lean<'l>(
    vec: Vec<u8>,
    lean: Lean<'l>,
) -> LeanResult<LeanBound<'l, LeanByteArray>> {
    let len = vec.len();

    if len == 0 {
        return LeanByteArray::empty(lean);
    }

    unsafe {
        // Allocate byte array with exact capacity
        let ba = LeanByteArray::with_capacity(lean, len)?;
        let ptr = ba.as_ptr();

        // Get pointer to Lean's internal buffer
        let data_ptr = crate::ffi::inline::lean_sarray_cptr(ptr);

        // Bulk copy all bytes at once (single memcpy!)
        std::ptr::copy_nonoverlapping(vec.as_ptr(), data_ptr, len);

        // Update size
        let sarray = ptr as *mut crate::ffi::inline::lean_sarray_object;
        (*sarray).m_size = len;

        Ok(ba)
    }
}

/// Optimized bulk conversion: &[u8] → LeanByteArray using single memcpy
///
/// # Example
///
/// ```rust,ignore
/// let ba = slice_u8_into_lean(b"Hello, World!", lean)?;
/// ```
pub fn slice_u8_into_lean<'l>(
    slice: &[u8],
    lean: Lean<'l>,
) -> LeanResult<LeanBound<'l, LeanByteArray>> {
    let len = slice.len();

    if len == 0 {
        return LeanByteArray::empty(lean);
    }

    unsafe {
        // Allocate byte array with exact capacity
        let ba = LeanByteArray::with_capacity(lean, len)?;
        let ptr = ba.as_ptr();

        // Get pointer to Lean's internal buffer
        let data_ptr = crate::ffi::inline::lean_sarray_cptr(ptr);

        // Bulk copy all bytes at once (single memcpy!)
        std::ptr::copy_nonoverlapping(slice.as_ptr(), data_ptr, len);

        // Update size
        let sarray = ptr as *mut crate::ffi::inline::lean_sarray_object;
        (*sarray).m_size = len;

        Ok(ba)
    }
}

/// Optimized bulk conversion: LeanByteArray → `Vec<u8>` using single memcpy
///
/// This uses zero-copy slice access followed by a single memcpy.
///
/// # Example
///
/// ```rust,ignore
/// let vec = vec_u8_from_lean(&byte_array)?;
/// ```
pub fn vec_u8_from_lean<'l>(obj: &LeanBound<'l, LeanByteArray>) -> Vec<u8> {
    unsafe {
        // Zero-copy slice access, then clone with single memcpy
        let slice = LeanByteArray::as_slice(obj);
        slice.to_vec()
    }
}

/// Exception-safe array builder for constructing Lean arrays.
///
/// This builder ensures that partially constructed arrays are properly cleaned up
/// if a conversion fails or panics midway through construction.
///
/// # Example
///
/// ```rust,ignore
/// let mut builder = ArrayBuilder::with_capacity(lean, 100)?;
/// for item in items {
///     builder.push(item.into_lean(lean)?)?;
/// }
/// let array = builder.finish();
/// ```
pub struct ArrayBuilder<'l> {
    arr: Option<LeanBound<'l, LeanArray>>,
    count: usize,
}

impl<'l> ArrayBuilder<'l> {
    /// Create a new array builder with pre-allocated capacity.
    pub fn with_capacity(lean: Lean<'l>, capacity: usize) -> LeanResult<Self> {
        let arr = LeanArray::with_capacity(lean, capacity)?;
        Ok(Self {
            arr: Some(arr),
            count: 0,
        })
    }

    /// Push an element to the array.
    ///
    /// # Safety
    ///
    /// The builder must have sufficient capacity remaining.
    pub fn push(&mut self, elem: LeanBound<'l, LeanAny>) -> LeanResult<()> {
        let arr = self.arr.take().expect("ArrayBuilder already finished");
        self.arr = Some(unsafe { LeanArray::push_unchecked(arr, elem)? });
        self.count += 1;
        Ok(())
    }

    /// Get the current number of elements in the array.
    pub fn len(&self) -> usize {
        self.count
    }

    /// Check if the array is empty.
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Finish building and return the constructed array.
    ///
    /// After calling this, the builder is consumed and can't be used anymore.
    pub fn finish(mut self) -> LeanBound<'l, LeanArray> {
        self.arr.take().expect("ArrayBuilder already finished")
    }
}

// Drop implementation ensures cleanup on panic
impl<'l> Drop for ArrayBuilder<'l> {
    fn drop(&mut self) {
        // arr is automatically cleaned up via LeanBound's Drop
        // Nothing extra needed here
    }
}

/// Convert an ExactSizeIterator directly to a LeanArray without collecting to Vec first.
///
/// This is more efficient than first collecting to a Vec and then converting,
/// as it only allocates once.
///
/// # Example
///
/// ```rust,ignore
/// let arr = iter_into_lean((0..1000).map(|x| x * 2), lean)?;
/// ```
pub fn iter_into_lean<'l, T, I>(iter: I, lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanArray>>
where
    T: IntoLean<'l> + 'l,
    I: ExactSizeIterator<Item = T>,
{
    let len = iter.len();

    if len == 0 {
        return LeanArray::empty(lean);
    }

    let mut builder = ArrayBuilder::with_capacity(lean, len)?;

    for item in iter {
        let lean_item = item.into_lean(lean)?;
        builder.push(lean_item.cast())?;
    }

    Ok(builder.finish())
}

/// Convert a slice directly to a LeanArray.
///
/// This is a convenience function that uses the iterator-based conversion.
pub fn slice_into_lean<'l, T>(slice: &[T], lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanArray>>
where
    T: IntoLean<'l> + Clone + 'l,
{
    iter_into_lean(slice.iter().cloned(), lean)
}

// Tuple conversions

use crate::types::LeanProd;

// (A, B) ↔ LeanProd
impl<'l, A, B> IntoLean<'l> for (A, B)
where
    A: IntoLean<'l> + 'l,
    B: IntoLean<'l> + 'l,
{
    type Target = LeanProd;

    /// Convert a Rust tuple `(A, B)` to a Lean `Prod`.
    ///
    /// Maps `(a, b)` to `Prod.mk a b`.
    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        let lean_a = self.0.into_lean(lean)?;
        let lean_b = self.1.into_lean(lean)?;
        let any_a: LeanBound<'l, LeanAny> = lean_a.cast();
        let any_b: LeanBound<'l, LeanAny> = lean_b.cast();
        LeanProd::mk(any_a, any_b)
    }
}

impl<'l, A, B> FromLean<'l> for (A, B)
where
    A: FromLean<'l> + 'l,
    B: FromLean<'l> + 'l,
{
    type Source = LeanProd;

    /// Convert a Lean `Prod` to a Rust tuple `(A, B)`.
    ///
    /// Maps `Prod.mk a b` to `(a, b)`.
    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        let any_a = LeanProd::fst(obj);
        let any_b = LeanProd::snd(obj);
        let typed_a: LeanBound<'l, A::Source> = any_a.cast();
        let typed_b: LeanBound<'l, B::Source> = any_b.cast();
        let rust_a = A::from_lean(&typed_a)?;
        let rust_b = B::from_lean(&typed_b)?;
        Ok((rust_a, rust_b))
    }
}
