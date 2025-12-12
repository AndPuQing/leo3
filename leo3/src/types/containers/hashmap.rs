//! HashMap type for Lean4's `Std.HashMap`.
//!
//! This module provides a Rust wrapper for Lean's HashMap type, which is
//! a hash table implementation with efficient lookup and insertion.
//!
//! **IMPORTANT**: This is currently a **placeholder implementation** with a simplified
//! linked-list structure. It does not use the actual Lean HashMap implementation.
//!
//! For the real Lean HashMap FFI bindings, see `leo3_ffi::hashmap`.
//! See `containers/README.md` for information on how to properly implement these using FFI.
//!
//! # Example
//!
//! ```rust,ignore
//! use leo3::prelude::*;
//! use leo3::types::LeanHashMap;
//!
//! leo3::with_lean(|lean| {
//!     // Create an empty HashMap
//!     let map = LeanHashMap::<LeanNat, LeanString>::empty(lean)?;
//!
//!     // Insert key-value pairs
//!     let key = LeanNat::from_usize(lean, 42)?;
//!     let value = LeanString::mk(lean, "hello")?;
//!     let map = map.insert(lean, key, value)?;
//!
//!     // Lookup a value
//!     let key = LeanNat::from_usize(lean, 42)?;
//!     if let Some(val) = map.find(lean, &key)? {
//!         println!("Found: {}", val.cstr()?);
//!     }
//!
//!     Ok::<_, LeanError>(())
//! })
//! ```

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::LeanList;
use std::marker::PhantomData;

/// A Lean HashMap type.
///
/// This is a wrapper around Lean's `Std.HashMap` type, which provides
/// efficient key-value storage using hash tables.
///
/// Note: This is represented as a Lean object. The actual implementation
/// uses Lean's internal HashMap structure.
pub struct LeanHashMapType<K, V> {
    _phantom: PhantomData<(K, V)>,
}

/// A bound Lean HashMap.
pub type LeanHashMap<'l, K, V> = LeanBound<'l, LeanHashMapType<K, V>>;

impl<'l, K, V> LeanHashMap<'l, K, V> {
    /// Create an empty HashMap.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let map = LeanHashMap::empty(lean)?;
    /// ```
    pub fn empty(lean: Lean<'l>) -> LeanResult<Self> {
        // Create an empty array to represent an empty HashMap
        // In practice, this would be a proper Std.HashMap.empty call
        // For now, we'll use an array as a simple backing store
        unsafe {
            let empty_array = ffi::lean_alloc_ctor(0, 0, 0);
            Ok(LeanBound::from_owned_ptr(lean, empty_array))
        }
    }

    /// Insert a key-value pair into the HashMap.
    ///
    /// Returns a new HashMap with the key-value pair inserted.
    /// Due to Lean's pure functional semantics, this creates a new map
    /// rather than modifying the existing one.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let key = 1u64.into_lean(lean)?;
    /// let value = "one".into_lean(lean)?;
    /// let map = map.insert(lean, key, value)?;
    /// ```
    pub fn insert(
        self,
        lean: Lean<'l>,
        key: LeanBound<'l, K>,
        value: LeanBound<'l, V>,
    ) -> LeanResult<Self> {
        // Create a pair (key, value) as a constructor with 2 fields
        unsafe {
            let pair = ffi::lean_alloc_ctor(0, 2, 0);
            ffi::object::lean_ctor_set(pair, 0, key.into_ptr());
            ffi::object::lean_ctor_set(pair, 1, value.into_ptr());

            // For simplicity, create a new array with the pair appended
            // In a real implementation, this would use Std.HashMap.insert
            let old_ptr = self.into_ptr();
            let new_map = ffi::lean_alloc_ctor(1, 2, 0);
            ffi::object::lean_ctor_set(new_map, 0, pair);
            ffi::object::lean_ctor_set(new_map, 1, old_ptr);

            Ok(LeanBound::from_owned_ptr(lean, new_map))
        }
    }

    /// Look up a value by key in the HashMap.
    ///
    /// Returns `Some(value)` if the key exists, or `None` if it doesn't.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let key = 1u64.into_lean(lean)?;
    /// if let Some(value) = map.find(lean, &key)? {
    ///     println!("Found: {:?}", value);
    /// }
    /// ```
    pub fn find(
        &self,
        _lean: Lean<'l>,
        _key: &LeanBound<'l, K>,
    ) -> LeanResult<Option<LeanBound<'l, V>>> {
        // In a real implementation, this would call Std.HashMap.find
        // For now, we'll return None as a placeholder
        // This would involve iterating through the structure to find the key
        Ok(None)
    }

    /// Check if the HashMap contains a key.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let key = 1u64.into_lean(lean)?;
    /// if map.contains(lean, &key)? {
    ///     println!("Map contains the key");
    /// }
    /// ```
    pub fn contains(&self, lean: Lean<'l>, key: &LeanBound<'l, K>) -> LeanResult<bool> {
        Ok(self.find(lean, key)?.is_some())
    }

    /// Get the number of key-value pairs in the HashMap.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let size = map.size()?;
    /// println!("HashMap has {} entries", size);
    /// ```
    pub fn size(&self) -> LeanResult<usize> {
        // Count the elements in the linked list structure
        let mut count = 0;
        let mut current = self.as_ptr();

        unsafe {
            while !current.is_null() && ffi::object::lean_obj_tag(current) == 1 {
                count += 1;
                // Get the tail (second field)
                current = ffi::object::lean_ctor_get(current, 1) as *mut ffi::lean_object;
            }
        }

        Ok(count)
    }

    /// Check if the HashMap is empty.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// if map.is_empty()? {
    ///     println!("HashMap is empty");
    /// }
    /// ```
    pub fn is_empty(&self) -> LeanResult<bool> {
        Ok(self.size()? == 0)
    }

    /// Convert the HashMap to a list of key-value pairs.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let pairs = map.to_list(lean)?;
    /// // Process the pairs...
    /// ```
    pub fn to_list(&self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanList>> {
        // Return the internal representation as a list
        unsafe {
            ffi::object::lean_inc(self.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, self.as_ptr()))
        }
    }

    /// Create a HashMap from a list of key-value pairs.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let list = LeanList::nil(lean)?;
    /// let map = LeanHashMap::from_list(lean, list)?;
    /// ```
    pub fn from_list(lean: Lean<'l>, list: LeanBound<'l, LeanList>) -> LeanResult<Self> {
        // Use the list directly as our internal representation
        unsafe {
            let ptr = list.into_ptr();
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conversion::IntoLean;
    use crate::types::{LeanString, LeanUInt64};
    use crate::LeanError;

    #[test]
    fn test_hashmap_empty() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let map = LeanHashMap::<LeanUInt64, LeanString>::empty(lean)?;
            assert!(map.is_empty()?);
            assert_eq!(map.size()?, 0);
            Ok::<_, LeanError>(())
        })
        .unwrap();
    }

    #[test]
    fn test_hashmap_insert() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let map = LeanHashMap::<LeanUInt64, LeanString>::empty(lean)?;

            let key = 42u64.into_lean(lean)?;
            let value = "hello".into_lean(lean)?;
            let map = map.insert(lean, key, value)?;

            assert!(!map.is_empty()?);
            assert_eq!(map.size()?, 1);

            Ok::<_, LeanError>(())
        })
        .unwrap();
    }

    #[test]
    fn test_hashmap_multiple_inserts() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let mut map = LeanHashMap::<LeanUInt64, LeanString>::empty(lean)?;

            for i in 1..=3 {
                let key = (i as u64).into_lean(lean)?;
                let value = format!("value{}", i).into_lean(lean)?;
                map = map.insert(lean, key, value)?;
            }

            assert_eq!(map.size()?, 3);

            Ok::<_, LeanError>(())
        })
        .unwrap();
    }
}
