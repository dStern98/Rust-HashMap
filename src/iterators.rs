pub struct Iter<'a, K, V> {
    //Struct to Implement as an Iterator
    // for immutable iteration.
    pub occupied_items: Vec<(&'a K, &'a V)>,
}

pub struct IntoIter<K, V> {
    //Owned Version of the Struct Iter, this will consume the HashMap
    pub occupied_items: Vec<(K, V)>,
}

pub struct IterMut<'a, K, V> {
    //Version of Iter struct where Values are mutable
    pub occupied_items: Vec<(&'a K, &'a mut V)>,
}

pub struct Keys<'a, K> {
    //Iterator that stores the keys of the HashMap.
    pub keys: Vec<&'a K>,
}

pub struct Values<'a, V> {
    //Iterator that stores the values of the HashMap.
    pub values: Vec<&'a V>,
}

impl<'a, K> Iterator for Keys<'a, K> {
    type Item = &'a K;
    fn next(&mut self) -> Option<Self::Item> {
        return self.keys.pop();
    }
}

impl<'a, V> Iterator for Values<'a, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        return self.values.pop();
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        return self.occupied_items.pop();
    }
}
impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        //Because the IntoIter struct was already built with the occupied (K,V) only,
        //we simply iterator one by one over the vec until we reach the end
        return self.occupied_items.pop();
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    //Exact same logic as the borrowed version, without lifetimes or borrowing
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        return self.occupied_items.pop();
    }
}
