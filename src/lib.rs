use std::borrow::Borrow;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::mem;
mod iterators;
use iterators::{IntoIter, Iter, IterMut, Keys, Values};
use std::fmt;

#[derive(Debug)]
pub enum Bucket<K, V> {
    ///Every Bucket in this scheme can either be either:
    /// 1. Occupied (with a key,value pair)
    /// 2. Vacant (no value)
    /// 3. Deleted (Lazy Deletion Scheme, removed when hashmap resized)
    Occupied((K, V)),
    Vacant,
    Deleted,
}

#[derive(Debug)]
pub struct HashMap<K, V> {
    ///Vec Storing the actual HashMap items
    buckets: Vec<Bucket<K, V>>,
    ///number of elements in the Vector that are not BucketOccupied::Vacant
    not_vacant_count: usize,
    ///number of elements in the Vector that are BucketOccupied::Deleted
    deleted_count: usize,
}

impl<K, V> fmt::Display for HashMap<K, V>
where
    K: fmt::Display,
    V: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //! JSON-like display for a HashMap.
        write!(f, "{{")?;
        for (key, value) in self.iter() {
            write!(f, "{}: {}, ", key, value)?;
        }
        write!(f, "}}")
    }
}

impl<K, V> Default for HashMap<K, V>
where
    K: Hash + Eq,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> HashMap<K, V>
where
    K: Hash + Eq,
{
    pub fn new() -> Self {
        //! Builds an empty HashMap with zero capacity.
        HashMap {
            buckets: Vec::new(),
            not_vacant_count: 0,
            deleted_count: 0,
        }
    }

    fn bucket<Q>(&self, key: &Q) -> usize
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        //! Given a key, determine the intial hash location.

        if self.buckets.is_empty() {
            panic!("bucket method called with HashMap length 0.");
        }
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        (hasher.finish() % self.buckets.len() as u64) as usize
    }

    fn lookup_key<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        //! Given a Key, find the location of the key in the HashMap. If
        //! not in the HashMap, then return None. This method is integral to
        //! getting, updating, and deleting items for the HashMap.

        //The logic of Open Addressing for finding a key in the HashMap
        //First, determine the original hash location
        let mut hash_location = self.bucket(key);
        loop {
            //Now iterate, starting at the initial hash location
            if let Some(vec_item) = self.buckets.get(hash_location) {
                match vec_item {
                    //If we reach a Vacant, then the key is not in the hashmap
                    Bucket::Vacant => return None,
                    //Skip over Deleted values
                    Bucket::Deleted => {
                        hash_location += 1;
                    }
                    //If the Bucket is Occupied, then we need to check if the key is equal
                    //to the search key
                    Bucket::Occupied((ref ekey, _)) => {
                        if key == ekey.borrow() {
                            return Some(hash_location);
                        }
                        hash_location += 1;
                    }
                }
            } else {
                //If we reach the end of the array, then
                //we wrap back around to the beginning of the array
                hash_location = 0;
            };
        }
    }

    fn find_key_insert_location<Q>(&self, key: &Q) -> usize
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        //! Find a key insert location in the HashMap.
        //!The loop only terminates when a Vacant, Deleted, or Occupied
        //! space is found with the same key as the search key. This means
        //! that great care must be taken on designing the HashMap to prevent
        //! an infinite loop. If the HashMap ever were to fill up completely without
        //! resizing, this loop would never exit (in most cases).

        //Finding where to insert a Key in the HashMap
        let mut hash_location = self.bucket(key);
        loop {
            if let Some(bucket) = self.buckets.get(hash_location) {
                match bucket {
                    //If we reach a Vacant, then that is where the insert location is
                    Bucket::Vacant | Bucket::Deleted => return hash_location,
                    //If the Bucket is Occupied, then we need to check if the key is equal
                    //to the search key. Return the hash_location if the key == the current occupied key.
                    Bucket::Occupied((ref ekey, _)) => {
                        if key == ekey.borrow() {
                            return hash_location;
                        }
                        hash_location += 1;
                    }
                }
            } else {
                //If we go off the map so to speak,
                // wrap back around to the front of the array
                hash_location = 0;
            }
        }
    }

    fn resize(&mut self) {
        //! Resize the HashMap. This MUST be triggered before
        //! the HashMap runs out of empty spaces.
        //! Doubles the array size if the array is non-empty.
        //! If the array is empty, sets the size to 2.

        //Double the Array Size
        let new_array_size = match self.buckets.len() {
            0 => 2,
            n => 2 * n,
        };
        //Create a new HashMap filled initially with Vacants
        let mut new_buckets: Vec<Bucket<K, V>> = Vec::with_capacity(new_array_size);
        for _ in 0..new_array_size {
            new_buckets.push(Bucket::Vacant);
        }

        //Drain the contents of the old hashmap.
        let old_buckets: Vec<Bucket<K, V>> = self.buckets.drain(..).collect();
        self.buckets = new_buckets;
        self.deleted_count = 0;
        self.not_vacant_count = 0;

        for old_bucket_item in old_buckets {
            if let Bucket::Occupied((key, value)) = old_bucket_item {
                self.insert(key, value);
            }
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        //! Insert the Key Pair (key, value). The HashMap is resized if
        //! the map is empty or the map is 3/4 full. If the insertion kicks out
        //! an old value, then the old value is returned.
        if self.buckets.is_empty() || (self.not_vacant_count + 1) >= 3 * self.buckets.len() / 4 {
            self.resize();
        };
        //Find the Insert Index for the Item.
        let hash_location = self.find_key_insert_location(&key);

        //Swap the new_item with the old_item from the HashMap.
        let current_item = self.buckets.get_mut(hash_location)?;
        let old_item = mem::replace(current_item, Bucket::Occupied((key, value)));

        //new_item is now the old_item.
        match old_item {
            Bucket::Occupied((_, value)) => Some(value),
            _ => {
                //Only increment the count if there is nothing to return (meaning)
                // a brand new item has been added to the HashMap. Otherwise,
                // an old value was overwritten, and the count should stay the same.
                self.not_vacant_count += 1;
                None
            }
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        //! Delete the item with key.
        //! If it existed, Some(old_value) is returned.

        if self.buckets.is_empty() {
            return None;
        }

        if let Some(key_location) = self.lookup_key(key) {
            self.deleted_count += 1;

            //Swap the item currently at the deletion location with a Deleted Enum variant.
            let current_item = self.buckets.get_mut(key_location)?;
            let deleted_item = mem::replace(current_item, Bucket::Deleted);

            match deleted_item {
                Bucket::Occupied((_, old_value)) => return Some(old_value),

                // The find_key_location method only returns Some when it found
                //a matching key in the HashMap. It should be guranteed that the deleted_item
                //is of type BucketOccupied::Occupied. The unreachable here is only to help with
                //debugging if a fatal bug is introducted into the code.
                _ => unreachable!(),
            };
        };

        None
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        //! get the value with key. If it does not exist,
        //! then None is returned.
        if self.buckets.is_empty() {
            return None;
        }

        if let Some(key_location) = self.lookup_key(key) {
            //Inside this block key_location is guranteed to be a valid
            // array index so the below index action is safe from a panic.
            match self.buckets[key_location] {
                Bucket::Occupied((_, ref value)) => return Some(value),
                _ => unreachable!(),
            }
        }
        None
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        //! Same as get, but returns a Mutable reference to the value.
        if self.buckets.is_empty() {
            return None;
        }

        if let Some(key_location) = self.lookup_key(key) {
            match self.buckets[key_location] {
                Bucket::Occupied((_, ref mut value)) => return Some(value),
                _ => unreachable!(),
            }
        }
        None
    }

    pub fn is_empty(&self) -> bool {
        //!Due to lazy deletion, we need to subtract deleted_count
        //!from not_vacant_count to get the number of occupied items that are
        //! in the HashMap.
        self.len() == 0
    }

    pub fn len(&self) -> usize {
        //! Same as is_empty impl.
        self.not_vacant_count - self.deleted_count
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        //!Returns True if the Key is in the HashMap
        self.get(key).is_some()
    }

    pub fn clear(&mut self) {
        //!Clear the HashMap by setting everything to vacant.
        for index in 0..self.buckets.len() {
            self.buckets[index] = Bucket::Vacant;
        }
        self.not_vacant_count = 0;
        self.deleted_count = 0;
    }
}

impl<'a, K, V> IntoIterator for &'a HashMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        //!The IntoIter Struct will only contain the Occupied (key,value) pairs,
        //! specifically an immutable reference to both key and value.
        Iter::new(&self.buckets)
    }
}

impl<K, V> IntoIterator for HashMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        //! into_iter consumes self, so we can take ownership of anything in self.
        //!The IntoIter Struct will only contain the Occupied (key,value) pairs
        IntoIter::new(self.buckets)
    }
}

impl<'a, K, V> HashMap<K, V> {
    pub fn keys(&'a self) -> Keys<'a, K, V> {
        //!Allow for mutable iteration of the values in the HashMap
        Keys::new(&self.buckets)
    }

    pub fn values(&'a self) -> Values<'a, K, V> {
        //!Allow for immutable iteration of the HashMap Values
        Values::new(&self.buckets)
    }

    pub fn iter_mut(
        &'a mut self,
    ) -> IterMut<impl Iterator<Item = (&'a K, &'a mut V)>, (&'a K, &'a mut V)> {
        //!Allow for mutable iteration of the values in the HashMap

        let mutable_bucket_iterator = self.buckets.iter_mut().filter_map(|bucket_item| {
            if let Bucket::Occupied((ref key, value)) = bucket_item {
                return Some((key, value));
            }
            None
        });

        IterMut {
            buckets: mutable_bucket_iterator,
        }
    }

    pub fn iter(&'a self) -> Iter<'a, K, V> {
        //! Allow for immutable iteration of items in HashMap.
        Iter::new(&self.buckets)
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for HashMap<K, V>
where
    K: Hash + Eq,
{
    fn from(arr: [(K, V); N]) -> Self {
        //!Builds and returns a New HashMap from an array of Tuples.
        let mut new_hashmap = HashMap::new();
        for (key, value) in arr {
            new_hashmap.insert(key, value);
        }
        new_hashmap
    }
}

impl<K, V> PartialEq<HashMap<K, V>> for HashMap<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    //!We define how to determine if two HashMaps are equal
    fn eq(&self, other: &HashMap<K, V>) -> bool {
        //First check the length. If length is not equal, return false
        if self.len() != other.len() {
            return false;
        }
        //If the len is equal, then we just have to iterate over one of the maps,
        //and check that the value in the other hashmap is the same
        for (key, value) in self {
            if let Some(other_value) = other.get(key) {
                //If a key in self is in other but with a different
                //value, then the HashMaps are not equal.
                if value != other_value {
                    return false;
                }
            } else {
                // If any key in self is not in other,
                //then the HashMaps are not equal.
                return false;
            }
        }
        //If we finish iterating without returning, then the maps are identical
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert() {
        //!Test Basic Insertion of a key.
        let mut dictionary: HashMap<&str, i32> = HashMap::new();
        assert!(dictionary.is_empty());
        assert_eq!(dictionary.len(), 0);
        //Insert foo
        dictionary.insert("foo", 45);
        assert_eq!(dictionary.get(&"foo"), Some(&45));
        assert_eq!(dictionary.len(), 1);
        //Insert bar
        dictionary.insert("bar", 46);
        assert_eq!(dictionary.get(&"bar"), Some(&46));
        assert_eq!(dictionary.len(), 2);
        //Insert baz
        dictionary.insert("baz", 47);
        assert_eq!(dictionary.get(&"baz"), Some(&47));
        assert_eq!(dictionary.get(&"sad"), None);
        assert_eq!(dictionary.insert("baz", 75), Some(47));
    }

    #[test]
    fn test_insert_already_exists() {
        //!Test that if a key already exists, the old value
        //! is returned
        let mut dictionary: HashMap<&str, i32> = HashMap::new();
        dictionary.insert("foo", 532);
        let insert_return = dictionary.insert("foo", 533);
        assert_eq!(insert_return.unwrap(), 532);
    }

    #[test]
    fn test_get() {
        //! Test Basic gets of a key.
        let mut dictionary: HashMap<&str, i32> = HashMap::new();
        //Insert foo, first checking that get returns None
        assert_eq!(dictionary.get(&"foo"), None);
        dictionary.insert("foo", 45);
        assert_eq!(dictionary.get(&"foo"), Some(&45));
        //Insert Bar, first checking that get returns None
        assert_eq!(dictionary.get(&"bar"), None);
        dictionary.insert("bar", 46);
        assert_eq!(dictionary.get(&"bar"), Some(&46));
        //Insert Baz, first checking that get returns None
        assert_eq!(dictionary.get(&"baz"), None);
        dictionary.insert("baz", 49);
        assert_eq!(dictionary.get(&"baz"), Some(&49));
    }

    #[test]
    fn test_remove() {
        //! Test removing a key from the HashMap.
        let mut dictionary: HashMap<&str, i32> = HashMap::new();
        //Insert foo, bar, and baz
        dictionary.insert("foo", 45);
        dictionary.insert("bar", 46);
        dictionary.insert("baz", 47);
        assert_eq!(dictionary.len(), 3);
        //First Delete Foo
        assert_eq!(dictionary.get(&"foo"), Some(&45));
        dictionary.remove(&"foo");
        assert_eq!(dictionary.len(), 2);
        assert_eq!(dictionary.get(&"foo"), None);
        //Then Delete bar
        assert_eq!(dictionary.get(&"bar"), Some(&46));
        dictionary.remove(&"bar");
        assert_eq!(dictionary.len(), 1);
        assert_eq!(dictionary.get(&"bar"), None);
        //Then delete baz
        assert_eq!(dictionary.get(&"baz"), Some(&47));
        dictionary.remove(&"baz");
        assert_eq!(dictionary.get(&"baz"), None);
        //Verify that the HashMap is now empty
        assert!(dictionary.is_empty());
        assert_eq!(dictionary.len(), 0);
    }

    #[test]
    fn test_remove_already_exists() {
        //! Test that if a key is deleted that already existed,
        //! the value is returned.
        let mut dictionary: HashMap<&str, f32> = HashMap::new();
        dictionary.insert("delete_me", 2.71828);
        let delete_return = dictionary.remove("delete_me");
        assert_eq!(delete_return.unwrap(), 2.71828);
    }

    #[test]
    fn test_clear() {
        //!Test clearing the HashMap.
        let mut dictionary: HashMap<&str, i32> = HashMap::new();
        //Insert foo, bar, and baz
        dictionary.insert("foo", 45);
        dictionary.insert("bar", 46);
        dictionary.insert("baz", 47);

        //Now Clear the HashMap
        dictionary.clear();
        assert!(dictionary.is_empty());
        assert_eq!(dictionary.len(), 0);
    }

    #[test]
    fn test_has_key() {
        let mut dictionary: HashMap<&str, i32> = HashMap::new();
        //Insert foo, check if key in HashMap
        assert!(!dictionary.contains_key(&"foo"));
        dictionary.insert("foo", 45);
        assert!(dictionary.contains_key(&"foo"));
        //Insert Bar, check if key in HashMap
        assert!(!dictionary.contains_key(&"bar"));
        dictionary.insert("bar", 46);
        assert!(dictionary.contains_key(&"bar"));
        //Insert Baz, check if key in HashMap
        assert!(!dictionary.contains_key(&"baz"));
        dictionary.insert("baz", 49);
        assert!(dictionary.contains_key(&"baz"));
    }

    #[test]
    fn test_into_iter_borrowed() {
        //Test into_iter with the borrowed hashmap
        let mut dictionary: HashMap<&str, i32> = HashMap::new();
        //Insert foo, bar, and baz
        dictionary.insert("foo", 45);
        dictionary.insert("bar", 46);
        dictionary.insert("baz", 47);

        for (key, value) in &dictionary {
            match *key {
                "foo" => assert_eq!(value, &45),
                "bar" => assert_eq!(value, &46),
                "baz" => assert_eq!(value, &47),
                _ => unreachable!(),
            }
        }

        println!("{}", dictionary);
        //dictionary has not been consumed, so this
        //print is valid.
    }

    #[test]
    fn test_into_iter_owned() {
        //test into_iter for the owned version, which consumes the hashmap
        let mut dictionary: HashMap<&str, i32> = HashMap::new();
        //Insert foo, bar, and baz
        dictionary.insert("foo", 45);
        dictionary.insert("bar", 46);
        dictionary.insert("baz", 47);

        for (key, value) in dictionary {
            match key {
                "foo" => assert_eq!(value, 45),
                "bar" => assert_eq!(value, 46),
                "baz" => assert_eq!(value, 47),
                _ => unreachable!(),
            }
        }
    }
    #[test]
    fn test_borrow_str() {
        //test the hashmap where K: String and we use get and remove with type &str
        let mut dictionary = HashMap::new();
        //Insert foo, bar, and baz
        dictionary.insert("foo".to_string(), 45);
        dictionary.insert("bar".to_string(), 46);
        dictionary.insert("baz".to_string(), 47);

        //Because get and remove take &Q where K: Borrow<Q>,
        //We can get and remove the Strings using an &str as input
        assert_eq!(dictionary.len(), 3);
        assert_eq!(dictionary.get("foo"), Some(&45));
        dictionary.remove("foo");
        assert_eq!(dictionary.len(), 2);
        assert_eq!(dictionary.get("foo"), None);
    }

    #[test]
    fn test_iter_mut() {
        //! Test mutating the HashMap contents using a loop.
        let mut dictionary = HashMap::new();
        dictionary.insert("a", 1);
        dictionary.insert("b", 2);
        dictionary.insert("c", 3);

        // Double all of the values
        for (_, val) in dictionary.iter_mut() {
            *val *= 2;
        }

        //Check that all of the values got doubled
        assert_eq!(dictionary.get(&"a"), Some(&2));
        assert_eq!(dictionary.get(&"b"), Some(&4));
        assert_eq!(dictionary.get(&"c"), Some(&6));
    }

    #[test]
    fn test_iter() {
        //! Test a loop where the key, value pairs are immutable
        //! references.
        let mut dictionary = HashMap::new();
        dictionary.insert("a".to_owned(), 1.3);
        dictionary.insert("b".to_owned(), 2.7);
        dictionary.insert("c".to_owned(), 3.9);

        for (key, value) in dictionary.iter() {
            match key.as_str() {
                "a" => assert_eq!(value, &1.3),
                "b" => assert_eq!(value, &2.7),
                "c" => assert_eq!(value, &3.9),
                _ => unreachable!(),
            }
        }
    }

    #[test]
    fn test_from() {
        //Check that we can build a HashMap from an array of tuples
        let dictionary = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);
        assert_eq!(dictionary.get(&"a"), Some(&1));
        assert_eq!(dictionary.get(&"b"), Some(&2));
        assert_eq!(dictionary.get(&"c"), Some(&3));
    }

    #[test]
    fn test_eq_lengths_unequal() {
        //! Check that the eq logic works where lengths are unequal.
        let mut dictionary = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);
        let mut dictionary2 = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);
        assert_eq!(dictionary == dictionary2, true);
        dictionary2.remove("a");
        assert_eq!(dictionary == dictionary2, false);
        dictionary.remove("a");
        assert_eq!(dictionary == dictionary2, true);
    }

    #[test]
    fn test_eq_lengths_equal() {
        //! Check that the eq logic works where lengths are equal.
        let mut dictionary = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);
        let mut dictionary2 = HashMap::from([("a", 1), ("b", 3), ("c", 3)]);

        assert_eq!(dictionary == dictionary2, false);
        dictionary2.insert("b", 2);
        assert_eq!(dictionary == dictionary2, true);

        dictionary.insert("c", 4);
        assert_eq!(dictionary == dictionary2, false);
    }

    #[test]
    fn test_keys_iterator() {
        //! Test Keys Iterator by collecting into a vec.
        let dictionary = HashMap::from([("a", vec![1]), ("b", vec![2, 3]), ("c", vec![10, 11])]);
        let dict_keys: Vec<_> = dictionary.keys().map(|&key| key).collect();
        assert_eq!(vec!["b", "a", "c"], dict_keys);
    }

    #[test]
    fn test_values_iterator() {
        //! Test Values Iterator by collecting into a vec.
        let dictionary = HashMap::from([("a", vec![1]), ("b", vec![2, 3])]);
        let dict_values: Vec<_> = dictionary.values().collect();
        assert_eq!(vec![&vec![2, 3], &vec![1]], dict_values);
    }

    #[test]
    fn test_bulk_remove() {
        let mut new_hash = HashMap::new();
        for (i, j) in (0..100_000).zip(100_000..200_000) {
            new_hash.insert(i, j);
        }
        for i in 0..100_000 {
            new_hash.remove(&i);
        }
        assert_eq!(new_hash.deleted_count, 100_000);
        new_hash.insert(5, 7);
        assert_eq!(new_hash.len(), 1);
    }
}
