use super::BucketOccupied;

pub struct Keys<'a, K, V> {
    //Stores an iterator_position
    iterator_position: usize,
    //buckets: immutable reference to the buckets vec
    //from the HashMap.
    pub buckets: &'a Vec<BucketOccupied<K, V>>,
}

impl<'a, K, V> Keys<'a, K, V> {
    pub fn new(buckets: &'a Vec<BucketOccupied<K, V>>) -> Self {
        //Returns a new empty Keys struct.
        Keys {
            iterator_position: 0,
            buckets,
        }
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let current_item = self.buckets.get(self.iterator_position)?;
            self.iterator_position += 1;
            if let BucketOccupied::Occupied((key, _)) = current_item {
                return Some(key);
            }
        }
    }
}

pub struct Values<'a, K, V> {
    //Iterator that stores the values of the HashMap.
    //iterator_position stores the current place in the iterator.
    iterator_position: usize,
    //buckets stores a reference to the HashMap buckets.
    pub buckets: &'a Vec<BucketOccupied<K, V>>,
}

impl<'a, K, V> Values<'a, K, V> {
    pub fn new(buckets: &'a Vec<BucketOccupied<K, V>>) -> Self {
        //Initialize a new Values iterator.
        Values {
            iterator_position: 0,
            buckets,
        }
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            //If the current_index is valid, unwrap the value, otherwise
            //terminate the iterator.
            let current_item = self.buckets.get(self.iterator_position)?;
            self.iterator_position += 1;
            //If current_item is Occupied, return it as an option.
            //Otherwise, simply continue the loop.
            if let BucketOccupied::Occupied((_, value)) = current_item {
                return Some(value);
            }
        }
    }
}

pub struct IterMut<I, P>
where
    I: Iterator<Item = P>,
{
    //For IterMut, we put an iterator
    //straight into the buckets field.
    pub buckets: I,
}

impl<I, P> Iterator for IterMut<I, P>
where
    I: Iterator<Item = P>,
{
    // Since I is already the desired iterator, just call next.
    type Item = P;
    fn next(&mut self) -> Option<Self::Item> {
        self.buckets.next()
    }
}

pub struct IntoIter<K, V> {
    //Owned Version of the Struct Iter, this will consume the HashMap
    pub buckets: Vec<BucketOccupied<K, V>>,
}

impl<K, V> IntoIter<K, V> {
    pub fn new(buckets: Vec<BucketOccupied<K, V>>) -> Self {
        IntoIter { buckets }
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        //Here we drain one item at a time from the vec, always
        //at the front, until the vec is empty.
        while !self.buckets.is_empty() {
            let next_item = self.buckets.drain(0..1).next()?;
            if let BucketOccupied::Occupied((key, value)) = next_item {
                return Some((key, value));
            }
        }
        None
    }
}

pub struct Iter<'a, K, V> {
    //Struct to Implement as an Iterator
    // for immutable iteration of Key, Value pairs.
    iterator_position: usize,
    pub buckets: &'a Vec<BucketOccupied<K, V>>,
}

impl<'a, K, V> Iter<'a, K, V> {
    pub fn new(buckets: &'a Vec<BucketOccupied<K, V>>) -> Self {
        //Create a new Iter starting at position 0.
        Iter {
            iterator_position: 0,
            buckets,
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            //if current_item exists and it is Occupied, return
            //the key, value pair, after advancing the iterator position.
            let current_item = self.buckets.get(self.iterator_position)?;
            self.iterator_position += 1;
            if let BucketOccupied::Occupied((key, value)) = current_item {
                return Some((key, value));
            }
        }
    }
}
