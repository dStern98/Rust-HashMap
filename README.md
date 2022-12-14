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
Deleted fields are cleaned up only when the array is resized. The trade-off is therefore faster deletion but more frequent array resizes.

## Iteration

`IntoIterator` is implemented for both the borrowed `&'a HashMap<K, V>` and owned `HashMap<K, V>` HashMaps. Therefore, both versions can be iterated over in a for loop, with each iteration returning the (key, value) pairs in the HashMap with type dependent on whether the HashMap is borrowed or owned. The method `iter_mut` allows for iteration over the HashMap with a mutable reference to the value, with the Iterator Item: `(&'a K, &'a mut V)`. Finally, the method `from` allows a new HashMap to be built from an array `[(K, V); N]`.

## PartialEq

The function `eq` is defined for the HashMap as well, to allow for HashMap equality comparison.
