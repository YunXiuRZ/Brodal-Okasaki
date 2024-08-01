-- Entirely from Chris Okasaki's Purely Functional Programming Language
module PriorityQueue (PriorityQueue(..)) where
    class PriorityQueue pq where
        empty       :: Ord a => pq a
        isEmpty     :: Ord a => pq a -> Bool
        insert      :: Ord a => a -> pq a -> pq a
        merge       :: Ord a => pq a -> pq a -> pq a
        findMin     :: Ord a => pq a -> Maybe a
        deleteMin   :: Ord a => pq a -> pq a

