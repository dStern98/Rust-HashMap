use std::collections::hash_map::DefaultHasher;
use std::hash::Hash;
use std::hash::{BuildHasher, Hasher};

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
    item_count: usize,
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

    pub fn bucket(&self, key: &K) -> usize
    where
        K: Hash + Eq,
    {
        //Determine the initial hash location
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        (hasher.finish() % self.buckets.len() as u64) as usize
    }

    pub fn find_key_location(&self, key: &K) -> Option<usize> {
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
                        if key == ekey {
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

    pub fn find_key_insert_location(&self, key: &K) -> usize {
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
                        if key == ekey {
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

    pub fn remove(&mut self, key: &K) -> Option<V>
    where
        V: Hash + Eq,
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

    pub fn get(&self, key: &K) -> Option<&V>
    where
        K: Hash + Eq,
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

    pub fn contains_key(&self, key: &K) -> bool {
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
}
