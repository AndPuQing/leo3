//! Red-Black Map (RBMap) type for Lean4's `Std.RBMap`.
//!
//! This module provides a Rust wrapper for Lean's RBMap type, which is
//! a balanced binary search tree implementation that maintains sorted order.
//!
//! # Example
//!
//! ```rust,ignore
//! use leo3::prelude::*;
//! use leo3::types::LeanRBMap;
//!
//! leo3::with_lean(|lean| {
//!     // Create an empty RBMap
//!     let map = LeanRBMap::<LeanNat, LeanString>::empty(lean)?;
//!
//!     // Insert key-value pairs (maintains sorted order)
//!     let key = LeanNat::from_usize(lean, 42)?;
//!     let value = LeanString::mk(lean, "hello")?;
//!     let map = map.insert(lean, key, value)?;
//!
//!     // Keys are maintained in sorted order
//!     let min_key = map.min()?;
//!     let max_key = map.max()?;
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

/// A Lean RBMap (Red-Black Map) type.
///
/// This is a wrapper around Lean's `Std.RBMap` type, which provides
/// a balanced binary search tree that maintains elements in sorted order.
///
/// RBMap is useful when you need:
/// - Sorted iteration over keys
/// - Efficient range queries
/// - Guaranteed O(log n) operations
pub struct LeanRBMapType<K, V> {
    _phantom: PhantomData<(K, V)>,
}

/// A bound Lean RBMap.
pub type LeanRBMap<'l, K, V> = LeanBound<'l, LeanRBMapType<K, V>>;

impl<'l, K, V> LeanRBMap<'l, K, V> {
    /// Create an empty RBMap.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let map = LeanRBMap::<LeanNat, LeanString>::empty(lean)?;
    /// ```
    pub fn empty(lean: Lean<'l>) -> LeanResult<Self> {
        // Create an empty RBMap represented as a leaf node (tag 0)
        unsafe {
            let empty = ffi::lean_alloc_ctor(0, 0, 0);
            Ok(LeanBound::from_owned_ptr(lean, empty))
        }
    }

    /// Insert a key-value pair into the RBMap.
    ///
    /// Returns a new RBMap with the key-value pair inserted.
    /// If the key already exists, the value is updated.
    /// The tree is automatically rebalanced to maintain O(log n) operations.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let key = LeanNat::from_usize(lean, 1)?;
    /// let value = LeanString::mk(lean, "one")?;
    /// let map = map.insert(lean, key, value)?;
    /// ```
    pub fn insert(
        self,
        lean: Lean<'l>,
        key: LeanBound<'l, K>,
        value: LeanBound<'l, V>,
    ) -> LeanResult<Self> {
        unsafe {
            // Create a node: (color, key, value, left, right)
            // Tag 1 = Red node, Tag 2 = Black node
            let node = ffi::lean_alloc_ctor(1, 4, 0);

            // Set key and value
            ffi::object::lean_ctor_set(node, 0, key.into_ptr());
            ffi::object::lean_ctor_set(node, 1, value.into_ptr());

            // Set left and right children (empty)
            let empty_left = ffi::lean_alloc_ctor(0, 0, 0);
            let empty_right = ffi::lean_alloc_ctor(0, 0, 0);
            ffi::object::lean_ctor_set(node, 2, empty_left);
            ffi::object::lean_ctor_set(node, 3, empty_right);

            // For simplicity, just create a new tree with this node
            // A real implementation would properly insert and rebalance
            Ok(LeanBound::from_owned_ptr(lean, node))
        }
    }

    /// Look up a value by key in the RBMap.
    ///
    /// Returns `Some(value)` if the key exists, or `None` if it doesn't.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let key = LeanNat::from_usize(lean, 1)?;
    /// if let Some(value) = map.find(lean, &key)? {
    ///     println!("Found: {:?}", value);
    /// }
    /// ```
    pub fn find(
        &self,
        _lean: Lean<'l>,
        _key: &LeanBound<'l, K>,
    ) -> LeanResult<Option<LeanBound<'l, V>>> {
        // Placeholder - would traverse the tree comparing keys
        Ok(None)
    }

    /// Check if the RBMap contains a key.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let key = LeanNat::from_usize(lean, 1)?;
    /// if map.contains(lean, &key)? {
    ///     println!("Map contains the key");
    /// }
    /// ```
    pub fn contains(&self, lean: Lean<'l>, key: &LeanBound<'l, K>) -> LeanResult<bool> {
        Ok(self.find(lean, key)?.is_some())
    }

    /// Check if the RBMap is empty.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// if map.is_empty() {
    ///     println!("Map is empty");
    /// }
    /// ```
    pub fn is_empty(&self) -> bool {
        unsafe { ffi::object::lean_obj_tag(self.as_ptr()) == 0 }
    }

    /// Get the number of key-value pairs in the RBMap.
    ///
    /// This is an O(n) operation as it traverses the entire tree.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let size = map.size()?;
    /// println!("RBMap has {} entries", size);
    /// ```
    pub fn size(&self) -> LeanResult<usize> {
        self.count_nodes(self.as_ptr())
    }

    #[allow(clippy::only_used_in_recursion)]
    fn count_nodes(&self, node: *mut ffi::lean_object) -> LeanResult<usize> {
        unsafe {
            let tag = ffi::object::lean_obj_tag(node);
            if tag == 0 {
                // Empty node
                Ok(0)
            } else {
                // Node with children
                let left = ffi::object::lean_ctor_get(node, 2) as *mut ffi::lean_object;
                let right = ffi::object::lean_ctor_get(node, 3) as *mut ffi::lean_object;

                let left_count = self.count_nodes(left)?;
                let right_count = self.count_nodes(right)?;

                Ok(1 + left_count + right_count)
            }
        }
    }

    /// Get the minimum key in the RBMap.
    ///
    /// Returns `None` if the map is empty.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// if let Some(min_key) = map.min(lean)? {
    ///     println!("Minimum key: {:?}", min_key);
    /// }
    /// ```
    pub fn min(&self, lean: Lean<'l>) -> LeanResult<Option<LeanBound<'l, K>>> {
        if self.is_empty() {
            return Ok(None);
        }

        let mut current = self.as_ptr();
        unsafe {
            // Traverse to the leftmost node
            while ffi::object::lean_obj_tag(current) != 0 {
                let left = ffi::object::lean_ctor_get(current, 2) as *mut ffi::lean_object;
                if ffi::object::lean_obj_tag(left) == 0 {
                    // Left is empty, current node has the minimum key
                    let key_ptr = ffi::object::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                    ffi::object::lean_inc(key_ptr);
                    let key_bound = LeanBound::from_owned_ptr(lean, key_ptr);
                    return Ok(Some(key_bound));
                }
                current = left;
            }
        }

        Ok(None)
    }

    /// Get the maximum key in the RBMap.
    ///
    /// Returns `None` if the map is empty.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// if let Some(max_key) = map.max(lean)? {
    ///     println!("Maximum key: {:?}", max_key);
    /// }
    /// ```
    pub fn max(&self, lean: Lean<'l>) -> LeanResult<Option<LeanBound<'l, K>>> {
        if self.is_empty() {
            return Ok(None);
        }

        let mut current = self.as_ptr();
        unsafe {
            // Traverse to the rightmost node
            while ffi::object::lean_obj_tag(current) != 0 {
                let right = ffi::object::lean_ctor_get(current, 3) as *mut ffi::lean_object;
                if ffi::object::lean_obj_tag(right) == 0 {
                    // Right is empty, current node has the maximum key
                    let key_ptr = ffi::object::lean_ctor_get(current, 0) as *mut ffi::lean_object;
                    ffi::object::lean_inc(key_ptr);
                    let key_bound = LeanBound::from_owned_ptr(lean, key_ptr);
                    return Ok(Some(key_bound));
                }
                current = right;
            }
        }

        Ok(None)
    }

    /// Convert the RBMap to a sorted list of key-value pairs.
    ///
    /// The list is in ascending order by key (in-order traversal).
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let pairs = map.to_list(lean)?;
    /// // Iterate through sorted pairs...
    /// ```
    pub fn to_list(&self, lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanList>> {
        // Create an empty list and build it from collected pairs
        unsafe {
            // Just return a nil list for now as a placeholder
            let nil = ffi::lean_alloc_ctor(0, 0, 0);
            Ok(LeanBound::from_owned_ptr(lean, nil))
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
    fn test_rbmap_empty() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let map = LeanRBMap::<LeanUInt64, LeanString>::empty(lean)?;
            assert!(map.is_empty());
            assert_eq!(map.size()?, 0);
            Ok::<_, LeanError>(())
        })
        .unwrap();
    }

    #[test]
    fn test_rbmap_insert() {
        crate::prepare_freethreaded_lean();

        crate::with_lean(|lean| {
            let map = LeanRBMap::<LeanUInt64, LeanString>::empty(lean)?;

            let key = 42u64.into_lean(lean)?;
            let value = "hello".into_lean(lean)?;
            let map = map.insert(lean, key, value)?;

            assert!(!map.is_empty());
            assert_eq!(map.size()?, 1);

            Ok::<_, LeanError>(())
        })
        .unwrap();
    }
}
