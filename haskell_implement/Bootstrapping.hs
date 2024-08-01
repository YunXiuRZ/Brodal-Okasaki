module Bootstrapping where
import PriorityQueue

-- We expect queue to be a priority queue
data R queue a = Root a (queue (R queue a))
data BP queue a = Empty | BS (R queue a)

instance (Eq a) => Eq (R queue a) where
    (==) :: Eq a => R queue a -> R queue a -> Bool
    (Root x _) == (Root y _) = x == y

instance (Ord a) => Ord (R queue a) where
    (<=) :: Ord a => R queue a -> R queue a -> Bool
    (Root x _) <= (Root y _) = x <= y

instance (PriorityQueue queue) => PriorityQueue (BP queue) where

    empty :: (PriorityQueue queue, Ord a) => BP queue a
    empty = Empty

    isEmpty :: (PriorityQueue queue, Ord a) => BP queue a -> Bool
    isEmpty Empty = True
    isEmpty (BS _) = False

    merge :: (PriorityQueue queue, Ord a) => BP queue a -> BP queue a -> BP queue a
    merge Empty xs = xs
    merge xs Empty = xs
    merge (BS r1@(Root x1 q1)) (BS r2@(Root x2 q2))
        | x1 <= x2  = BS (Root x1 $ insert r2 q1)   -- the "insert" is owned by queue not BP
        | otherwise = BS (Root x2 $ insert r1 q2)   -- the "insert" is owned by queue not BP

    insert :: (PriorityQueue queue, Ord a) => a -> BP queue a -> BP queue a
    insert x = merge (BS (Root x empty))

    findMin :: (PriorityQueue queue, Ord a) => BP queue a -> Maybe a
    findMin Empty = Nothing
    findMin (BS (Root x q)) = Just x

    deleteMin :: (PriorityQueue queue, Ord a) => BP queue a -> BP queue a
    deleteMin Empty = Empty
    deleteMin (BS (Root x q)) = case findMin q of
        Nothing             -> Empty
        Just (Root y q1)    -> let q2 = deleteMin q
                                in BS (Root y $ merge q1 q2)


