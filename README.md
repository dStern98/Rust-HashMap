# About

This is an implementation of the Rust HashMap, essentially copying the API from
`std::collections::HashMap`. While the methods are taken from the Rust standard library, the implementation was written without any reference to how the Rust standard library actually implements a HashMap. The HashMap uses Open Addressing, and Linear Probing. That means that if the initial hash location is occupied, then we increment the location by 1 continuously until we find an empty spot.
The HashMap at its core in this implementation is a struct that contains a field buckets, which is a Vector of the enum `BucketOccupied` shown below.

```
pub enum BucketOccupied<K, V> {
Occupied((K, V)),
Vacant,
Deleted,
}
```

The HashMap begins with all of the elements set to `BucketOccupied::Vacant`. When a (key,value) pair is inserted, the vector element is changed to `BucketOccupied::Occupied(K,V)`,
containing the Key, Value pair in question. When a field is deleted, the deletion is lazy, so the enum in question is replaced with `BucketOccipied::Deleted`. The HashMap ignores deleted fields for the purpose of search, but will allow a new insertion to replace a deleted field.
Deleted fields are cleaned up only when the array is resized. The trade-off is therefore faster deletion but more frequent array resizes. The HashMap vector is sparse, and could be optimizted in terms of memory and iteration by using the Python dictionary design shown [here](https://mail.python.org/pipermail/python-dev/2012-December/123028.html) in a blog by Raymond Hettinger. At the current time, this has not been implemented.

## Basic Usage

Basic HashMap usage is as follows:

1. `pub fn new() -> Self`: Creates a new empty HashMap. No allocations occur
   until the first insertion.
2. `pub fn insert(&mut self, key: K, value: V) -> Option<V>`: Inserts the key-value pair (key, value). If the key was already in the HashMap, the old value is returned as an option. If the key did not previously exist in the HashMap, None is returned.
3. `pub fn remove<Q>(&mut self, key: &Q) -> Option<V>`: Remove the key from
   the HashMap, if it exists. If it does, the deleted value is returned as an
   Some(value), otherwise None is returned.
4. `pub fn get<Q>(&self, key: &Q) -> Option<&V>`/`pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>`: Obtain an immutable or mutable reference to the value corresponding to key, if it exists in the HashMap. None is returned if the key does not exist.
5. `pub fn clear(&mut self)`: Clears the HashMap, but keeps the same memory allocation.
6. `pub fn contains_key<Q>(&self, key: &Q) -> bool`: Whether or not the key
   exists in the HashMap.
7. `pub fn is_empty(&self) -> bool `/ `pub fn len(&self) -> usize`: Whether the HashMap is empty and the number of key/value pairs currently in the HashMap.

## Iteration

`IntoIterator` is implemented for both the borrowed `&'a HashMap<K, V>` and owned `HashMap<K, V>` HashMaps. Therefore, both versions can be iterated over in a for loop, with each iteration returning the (key, value) pairs in the HashMap with type dependent on whether the HashMap is borrowed or owned. The methods `iter_mut` and `iter` allow for iteration over the HashMap with a mutable/immutable reference to the value, with the Iterator Item: `(&'a K, &'a mut V)/(&'a K, &'a V)` respectively. Finally, the method `from` allows a new HashMap to be built from an array `[(K, V); N]`. In addition, the methods `keys()` and `values()` allow for convenient iteration over the HashMap's keys or values. All Iterator structs can be found in the file `iterators.rs`. All iterators move through the underlying HashMap's vector from front to back, and therefore does not
preserve insertion order.

## PartialEq

The method `eq` is defined for the HashMap as well, to allow for HashMap equality comparison.
