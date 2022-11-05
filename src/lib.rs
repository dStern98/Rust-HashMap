use std::borrow::Borrow;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

pub enum BucketOccupied<K, V> {
    //Every Bucket in this scheme can either be either:
    // 1. Occupied (with a key,value pair)
    // 2. Vacant (no value)
    // 3. Deleted (Lazy Deletion Scheme, removed when hashmap resized)
    Occupied((K, V)),
    Vacant,
    Deleted,
}

pub struct HashMap<K, V> {
    buckets: Vec<BucketOccupied<K, V>>,
    //number of elements in the Vector that are not BucketOccupied::Vacant
    item_count: usize,
    //number of elements in the Vector that are BucketOccupied::Deleted
    deleted_count: usize,
}

impl<K, V> HashMap<K, V>
where
    K: Hash + Eq,
{
    pub fn new() -> Self {
        HashMap {
            buckets: Vec::new(),
            item_count: 0,
            deleted_count: 0,
        }
    }

    fn bucket<Q>(&self, key: &Q) -> usize
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        //Determine the initial hash location
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        return (hasher.finish() % self.buckets.len() as u64) as usize;
    }

    fn find_key_location<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        //The logic of Open Addressing for finding a key in the HashMap
        //First, determine the original hash location
        let mut hash_location = self.bucket(key);
        loop {
            //Now iterate, starting at the initial hash location
            if let Some(vec_value) = self.buckets.get(hash_location) {
                match vec_value {
                    //If we reach a Vacant, then the key is not in the hashmap
                    BucketOccupied::Vacant => return None,
                    //Skip over Deleted values
                    BucketOccupied::Deleted => {
                        hash_location += 1;
                    }
                    //If the Bucket is Occupied, then we need to check if the key is equal
                    //to the search key
                    BucketOccupied::Occupied((ref ekey, _)) => {
                        if key == ekey.borrow() {
                            return Some(hash_location);
                        } else {
                            hash_location += 1;
                        }
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
        //Finding where to insert a Key in the HashMap
        let mut hash_location = self.bucket(key);
        loop {
            if let Some(vec_value) = self.buckets.get(hash_location) {
                match vec_value {
                    //If we reach a Vacant, then that is where the insert location is
                    BucketOccupied::Vacant => return hash_location,
                    //Same with Deleted
                    BucketOccupied::Deleted => return hash_location,
                    //If the Bucket is Occupied, then we need to check if the key is equal
                    //to the search key. Return the hash_location if the key == the current occupied key.
                    BucketOccupied::Occupied((ref ekey, _)) => {
                        if key == ekey.borrow() {
                            return hash_location;
                        } else {
                            hash_location += 1;
                        }
                    }
                }
            } else {
                //If we go off the map so to speak, wrap back around to the front of the array
                hash_location = 0;
            }
        }
    }

    fn resize(&mut self) {
        //Double the Array Size
        let new_array_size = match self.buckets.len() {
            0 => 2,
            n => 2 * n,
        };
        //Create a new HashMap filled initially with Vacants
        let mut new_buckets: Vec<BucketOccupied<K, V>> = Vec::with_capacity(new_array_size);
        for _ in 0..new_array_size {
            new_buckets.push(BucketOccupied::Vacant);
        }

        let mut number_of_inserts = 0;

        for bucket_enum in self.buckets.drain(..) {
            if let BucketOccupied::Occupied((key, value)) = bucket_enum {
                let mut hasher = DefaultHasher::new();
                key.hash(&mut hasher);
                let mut hash_location = (hasher.finish() % new_buckets.len() as u64) as usize;
                let hash_location = loop {
                    if let Some(vec_value) = new_buckets.get(hash_location) {
                        match vec_value {
                            //If we reach a Vacant, then that is where the insert location is
                            BucketOccupied::Vacant => break hash_location,
                            //Same with Deleted
                            BucketOccupied::Deleted => break hash_location,
                            //If the Bucket is Occupied, then we need to check if the key is equal
                            //to the search key
                            BucketOccupied::Occupied((ref ekey, _)) => {
                                if &key == ekey {
                                    break hash_location;
                                } else {
                                    hash_location += 1;
                                }
                            }
                        }
                    } else {
                        //If we go off the map so to speak, wrap back around to the front of the array
                        hash_location = 0;
                    };
                };
                new_buckets[hash_location] = BucketOccupied::Occupied((key, value));
                number_of_inserts += 1;
            };
        }
        //Set self.buckets to the new_buckets vec
        self.buckets = new_buckets;
        self.deleted_count = 0;
        self.item_count = number_of_inserts;
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.buckets.is_empty() || (self.item_count + 1) >= 3 * self.buckets.len() / 4 {
            self.resize();
        };
        self.item_count += 1;
        let hash_location = self.find_key_insert_location(&key);
        self.buckets.push(BucketOccupied::Occupied((key, value)));
        let current_location_enum = self.buckets.swap_remove(hash_location);
        match current_location_enum {
            BucketOccupied::Occupied((_, value)) => return Some(value),
            _ => return None,
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(key_location) = self.find_key_location(key) {
            self.deleted_count += 1;
            self.buckets.push(BucketOccupied::Deleted);
            let old_enum = self.buckets.swap_remove(key_location);
            match old_enum {
                BucketOccupied::Occupied((_, value)) => return Some(value),
                _ => unreachable!(),
            };
        };

        return None;
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if self.buckets.len() == 0 {
            return None;
        }

        if let Some(key_location) = self.find_key_location(key) {
            match self.buckets[key_location] {
                BucketOccupied::Occupied((_, ref value)) => return Some(value),
                _ => unreachable!(),
            }
        }
        None
    }

    pub fn is_empty(&self) -> bool {
        //Due to lazy deletion, we need to subtract deleted count
        //from item_count
        self.item_count - self.deleted_count == 0
    }

    pub fn len(&self) -> usize {
        self.item_count - self.deleted_count
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        //Returns True if the Key is in the HashMap
        self.get(key).is_some()
    }

    pub fn clear(&mut self) {
        //Clear the HashMap, set everything to vacant
        let current_bucket_length = self.buckets.len();
        for index in 0..current_bucket_length {
            self.buckets.push(BucketOccupied::Vacant);
            self.buckets.swap_remove(index);
        }
        self.item_count = 0;
        self.deleted_count = 0;
    }
}

pub struct Iter<'a, K, V> {
    //Struct to Implement as an Iterator
    vec_of_occupied: Vec<(&'a K, &'a V)>,
}

pub struct IntoIter<K, V> {
    //Owned Version of the Struct Iter, this will consume the HashMap
    vec_of_occupied: Vec<(K, V)>,
}

pub struct IterMut<'a, K, V> {
    //Version of Iter struct where Values are mutable
    vec_of_occupied: Vec<(&'a K, &'a mut V)>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(inner_tuple) = self.vec_of_occupied.pop() {
            return Some(inner_tuple);
        }
        return None;
    }
}
impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        //Because the IntoIter struct was already built with the occupied (K,V) only,
        //we simply iterator one by one over the vec until we reach the end
        if let Some(inner_tuple) = self.vec_of_occupied.pop() {
            return Some(inner_tuple);
        }
        return None;
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    //Exact same logic as the borrowed version, without lifetimes or borrowing
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(inner_tuple) = self.vec_of_occupied.pop() {
            return Some(inner_tuple);
        }
        return None;
    }
}

impl<K, V> IntoIterator for HashMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        //The IntoIter Struct will only contain the Occupied (key,value) pairs
        let mut outbound_vector = Vec::new();
        let mut buckets_vec = self.buckets;
        //Iterate over the HashMap, and fill the IntoIter struct with the pairs
        for _ in 0..buckets_vec.len() {
            if let Some(bucket_occupied_enum) = buckets_vec.pop() {
                if let BucketOccupied::Occupied((key, value)) = bucket_occupied_enum {
                    outbound_vector.push((key, value));
                }
            }
        }
        IntoIter {
            vec_of_occupied: outbound_vector,
        }
    }
}

impl<'a, K, V> HashMap<K, V> {
    fn iter_mut(&'a mut self) -> IterMut<'a, K, V> {
        //Allow for mutable iteration of the values in the HashMap
        let mut outbound_vector = Vec::new();
        for item in self.buckets.iter_mut() {
            if let BucketOccupied::Occupied((key, value)) = item {
                //Dereference key and then reference to ensure that its reference is immutable
                outbound_vector.push((&*key, value));
            }
        }
        return IterMut {
            vec_of_occupied: outbound_vector,
        };
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for HashMap<K, V>
where
    K: Hash + Eq,
{
    fn from(arr: [(K, V); N]) -> Self {
        //Allows the building of a new HashMap from an Array of Tuples
        let mut new_hashmap = HashMap::new();
        for (key, value) in arr {
            new_hashmap.insert(key, value);
        }
        return new_hashmap;
    }
}

impl<'a, K, V> IntoIterator for &'a HashMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        //The IntoIter Struct will only contain the Occupied (key,value) pairs
        let mut outbound_vector = Vec::new();

        //Iterate over the HashMap, and fill the IntoIter struct with the pairs
        for item in self.buckets.iter() {
            if let BucketOccupied::Occupied((key, value)) = item {
                outbound_vector.push((key, value));
            }
        }
        Iter {
            vec_of_occupied: outbound_vector,
        }
    }
}

impl<K, V> PartialEq<HashMap<K, V>> for HashMap<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    //We define how to determine if two HashMaps are equal
    fn eq(&self, other: &HashMap<K, V>) -> bool {
        //First check the length. If length is not equal, return false
        if self.len() != other.len() {
            return false;
        }
        //If the len is equal, then we just have to iterate over one of the maps,
        //and check that the value in the other hashmap is the same
        for (key, value) in self {
            if let Some(other_value) = other.get(key) {
                if value != other_value {
                    return false;
                }
            }
        }
        //If we finish iterating without returning, then the maps are identical
        return true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert() {
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
    fn get() {
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
    fn remove() {
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
    fn clear() {
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
    fn has_key() {
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
    fn into_iter_borrowed() {
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
    }

    #[test]
    fn into_iter_owned() {
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
    fn test_from() {
        //Check that we can build a HashMap from an array of tuples
        let dictionary = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);
        assert_eq!(dictionary.get(&"a"), Some(&1));
        assert_eq!(dictionary.get(&"b"), Some(&2));
        assert_eq!(dictionary.get(&"c"), Some(&3));
    }

    #[test]
    fn test_eq() {
        //Check that the eq logic works
        let mut dictionary = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);
        let mut dictionary2 = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);
        assert_eq!(dictionary == dictionary2, true);
        dictionary2.remove("a");
        assert_eq!(dictionary == dictionary2, false);
        dictionary.remove("a");
        assert_eq!(dictionary == dictionary2, true);
    }
}
