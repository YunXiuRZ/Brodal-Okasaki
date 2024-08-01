module SkewBinomialHeap 
( Ts
, isEmpty
, insert
, merge
, findMin
, deleteMin
, size) where
import PriorityQueue

type Rank = Int
-- we should maintain the invariant that root is the 
-- minimum element of the tree
data STree a = Node a Rank [STree a] 
newtype Ts a = Build [STree a]


root :: STree a -> a
root (Node x r c) = x

rank :: STree a -> Int
rank (Node x r c) = r

-- helping function that wasn't included in Brodal and Okasaki's paper
size :: Ts a -> Int
size (Build []) = 0
size (Build (Node x r c:ts)) = length c + size (Build ts) + 1

-- We assume that r1 = r2
link :: Ord a => STree a -> STree a -> STree a
link t1@(Node x1 r1 c1) t2@(Node x2 r2 c2)  
    | x1 <= x2   = Node x1 (r1+1) (t2:c1)
    | otherwise  = Node x2 (r2+1) (t1:c2)

-- We assume that r0 = 0, i.e. t0 is a rank 0 skew binomial tree
--            and r1 = r2
skewLink :: Ord a => STree a -> STree a -> STree a -> STree a
skewLink t0@(Node x0 r0 _) t1@(Node x1 r1 c1) t2@(Node x2 r2 c2) 
    | x1 <= x0 && x1 <= x2 = Node x1 (r1+1) (t0:t2:c1)
    | x2 <= x0 && x2 <= x1 = Node x2 (r2+1) (t0:t1:c2)
    | otherwise            = Node x0 (r1+1) [t1,t2]

-- We assume that rank t <= tank t'
insertTree :: Ord a => STree a -> Ts a -> Ts a
insertTree t [] = [t]
insertTree t (t':ts)
    | rank t < rank t' = t:t':ts
    | otherwise        = insertTree (link t t') ts

-- Link them if there are two lowest-rank tree
uniqify :: Ord a => Ts a -> Ts a
uniqify [] = []
uniqify (t:ts) = insertTree t ts

meldUniq :: Ord a => Ts a -> Ts a -> Ts a
meldUniq [] ts = ts
meldUniq ts [] = ts
meldUniq (t1:ts1) (t2:ts2)
    | rank t1 < rank t2 = t1:meldUniq ts1 (t2:ts2)
    | rank t2 < rank t1 = t2:meldUniq (t1:ts1) ts2
    | otherwise         = insertTree (link t1 t2) (meldUniq ts1 ts2)

instance PriorityQueue Ts where
    empty = []

    isEmpty :: Ts a -> Bool
    isEmpty = null

    insert :: Ord a => a -> Ts a -> Ts a
    insert x ts@(t1:t2:tss)
        | rank t1 == rank t2 = skewLink (Node x 0 []) t1 t2 : tss
        | otherwise          = Node x 0 [] : ts
    insert x ts = Node x 0 [] : ts

    merge :: Ord a => Ts a -> Ts a -> Ts a
    merge ts ts' = meldUniq (uniqify ts) (uniqify ts')

    -- I don't want to deal with side effect in agda so I use "Nothing" rather than exception
    findMin :: Ord a => Ts a -> Maybe a
    findMin [] = Nothing
    findMin (t:ts) = case findMin ts of
        Nothing              -> Just (root t)
        Just v | root t <= v -> Just (root t)
        Just v | otherwise   -> Just v

    -- "getMin" find the subtree containing the minimum element 
    -- "split" split the subtrees of the given tree into two groups by 
    -- their rank. The former group contains subtrees with rank > 0 
    -- while the latter contains subtrees with rank = 0.
    deleteMin :: Ord a => Ts a -> Ts a
    deleteMin [] = []
    deleteMin ts = foldr insert (meld tss ts') xs'
        where   getMin :: Ord a => Ts a -> (STree a, Ts a)
                getMin [t] = (t, [])
                getMin (t:ts)
                    | root t <= root t' = (t, ts)
                    | otherwise         = (t', t:ts')
                    where (t', ts') = getMin ts
                split :: Ts a -> [a] -> Ts a -> (Ts a, [a])
                split ts xs [] = (ts, xs)
                split ts xs (t:c)
                    | rank t == 0 = split ts (root t : xs) c
                    | otherwise   = split (t:ts) xs c
                (Node x r c, tss) = getMin ts
                (ts', xs')        = split [] [] c


