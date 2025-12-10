//! Traits for converting between Rust and Lean types.
//!
//! This module provides traits for converting between Rust values and Lean objects.

use crate::err::LeanResult;
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;
use crate::types::{LeanArray, LeanBool, LeanByteArray, LeanNat, LeanString};

/// Macro for automatic conversion dispatch. For Vec<u8> and &[u8], uses optimized
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

/// Macro for automatic conversion from Lean. For Vec<u8>, uses optimized conversion.
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

// =============================================================================
// Implementations for primitive types
// =============================================================================

// u64 ↔ LeanNat
impl<'l> IntoLean<'l> for u64 {
    type Target = LeanNat;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanNat::from_usize(lean, self as usize)
    }
}

impl<'l> FromLean<'l> for u64 {
    type Source = LeanNat;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanNat::to_usize(obj).map(|n| n as u64)
    }
}

// usize ↔ LeanNat
impl<'l> IntoLean<'l> for usize {
    type Target = LeanNat;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanNat::from_usize(lean, self)
    }
}

impl<'l> FromLean<'l> for usize {
    type Source = LeanNat;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanNat::to_usize(obj)
    }
}

// u32 ↔ LeanNat
impl<'l> IntoLean<'l> for u32 {
    type Target = LeanNat;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanNat::from_usize(lean, self as usize)
    }
}

impl<'l> FromLean<'l> for u32 {
    type Source = LeanNat;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanNat::to_usize(obj).and_then(|n| {
            u32::try_from(n).map_err(|_| crate::err::LeanError::conversion("Nat too large for u32"))
        })
    }
}

// u16 ↔ LeanNat
impl<'l> IntoLean<'l> for u16 {
    type Target = LeanNat;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanNat::from_usize(lean, self as usize)
    }
}

impl<'l> FromLean<'l> for u16 {
    type Source = LeanNat;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanNat::to_usize(obj).and_then(|n| {
            u16::try_from(n).map_err(|_| crate::err::LeanError::conversion("Nat too large for u16"))
        })
    }
}

// u8 ↔ LeanNat
impl<'l> IntoLean<'l> for u8 {
    type Target = LeanNat;

    fn into_lean(self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self::Target>> {
        LeanNat::from_usize(lean, self as usize)
    }
}

impl<'l> FromLean<'l> for u8 {
    type Source = LeanNat;

    fn from_lean(obj: &LeanBound<'l, Self::Source>) -> LeanResult<Self> {
        LeanNat::to_usize(obj).and_then(|n| {
            u8::try_from(n).map_err(|_| crate::err::LeanError::conversion("Nat too large for u8"))
        })
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
        let lean = obj.lean_token();
        let size = LeanArray::size(obj);

        // Pre-allocate Vec with exact capacity
        let mut result = Vec::with_capacity(size);

        // Direct element access without intermediate allocations
        for i in 0..size {
            let elem = LeanArray::get(obj, lean, i)
                .ok_or_else(|| crate::err::LeanError::runtime("Index out of bounds"))?;
            let typed_elem: LeanBound<'l, T::Source> = elem.cast();
            let rust_item = T::from_lean(&typed_elem)?;
            result.push(rust_item);
        }

        Ok(result)
    }
}

// Note: These are provided as helper functions instead of trait implementations
// to avoid trait specialization conflicts in stable Rust.

/// Optimized bulk conversion: Vec<u8> → LeanByteArray using single memcpy
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

/// Optimized bulk conversion: LeanByteArray → Vec<u8> using single memcpy
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
