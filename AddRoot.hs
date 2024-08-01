module AddRoot (RQ) where
import PriorityQueue

-- Rooted Queue, we expect q to be an instance of PriorityQueue
data RQ queue a = Empty | Root a (queue a)

instance (PriorityQueue queue) => PriorityQueue (RQ queue) where
    
    empty :: (PriorityQueue queue, Ord a) => RQ queue a
    empty = Empty
    
    isEmpty :: (PriorityQueue queue, Ord a) => RQ queue a -> Bool
    isEmpty Empty = True
    isEmpty (Root _ _) = False

    insert :: (PriorityQueue queue, Ord a) => a -> RQ queue a -> RQ queue a
    insert y Empty = Root y empty
    insert y (Root x q)
        | y <= x    = Root y (insert x q)
        | otherwise = Root x (insert y q)

    merge :: (PriorityQueue queue, Ord a) => RQ queue a -> RQ queue a -> RQ queue a
    merge Empty rq = rq
    merge rq Empty = rq
    merge (Root x1 q1) (Root x2 q2) 
        | x1 <= x2  = Root x1 (insert x2 $ merge q1 q2)
        | otherwise = Root x2 (insert x1 $ merge q1 q2)
    
    findMin :: (PriorityQueue queue, Ord a) => RQ queue a -> Maybe a
    findMin Empty = Nothing
    findMin (Root x q) = Just x

    deleteMin :: (PriorityQueue queue, Ord a) => RQ queue a -> RQ queue a
    deleteMin Empty = Empty
    deleteMin (Root x q) = case findMin q of
        Nothing   -> Empty
        Just v    -> Root v (deleteMin q) 
    


