module SkewBinomialHeap 
( Ts
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
insertTree t (Build []) = Build [t]
insertTree t (Build (t':ts))
    | rank t < rank t' = Build (t:t':ts)
    | otherwise        = insertTree (link t t') (Build ts)

-- Link them if there are two lowest-rank tree
uniqify :: Ord a => Ts a -> Ts a
uniqify (Build []) = Build []
uniqify (Build (t:ts)) = insertTree t (Build ts)

meldUniq :: Ord a => Ts a -> Ts a -> Ts a
meldUniq (Build []) ts = ts
meldUniq ts (Build []) = ts
meldUniq ts1@(Build (t1:tss1)) ts2@(Build (t2:tss2))
    | rank t1 < rank t2 = let (Build ts') = meldUniq (Build tss1) ts2
                            in Build (t1:ts')
    | rank t2 < rank t1 = let (Build ts') = meldUniq ts1 (Build tss2)
                            in Build (t2:ts')
    | otherwise         = insertTree (link t1 t2) (meldUniq (Build tss1) (Build tss2))

instance PriorityQueue Ts where
    empty = Build []

    isEmpty :: Ts a -> Bool
    isEmpty (Build ts) = null ts

    insert :: Ord a => a -> Ts a -> Ts a
    insert x ts@(Build (t1:t2:tss))
        | rank t1 == rank t2 = Build (skewLink (Node x 0 []) t1 t2 : tss)
        | otherwise          = Build (Node x 0 [] : (t1:t2:tss))
    insert x (Build ts) = Build (Node x 0 [] : ts)

    merge :: Ord a => Ts a -> Ts a -> Ts a
    merge ts ts' = meldUniq (uniqify ts) (uniqify ts')

    -- I don't want to deal with side effect in agda so I use "Nothing" rather than exception
    findMin :: Ord a => Ts a -> Maybe a
    findMin (Build []) = Nothing
    findMin (Build (t:ts)) = case findMin (Build ts) of
        Nothing              -> Just (root t)
        Just v | root t <= v -> Just (root t)
        Just v | otherwise   -> Just v

    -- "getMin" find the subtree containing the minimum element 
    -- "split" split the subtrees of the given tree into two groups by 
    -- their rank. The former group contains subtrees with rank > 0 
    -- while the latter contains subtrees with rank = 0.
    deleteMin :: Ord a => Ts a -> Ts a
    deleteMin (Build []) = empty
    deleteMin ts = foldr insert (merge tss ts') xs'
        where   getMin :: Ord a => Ts a -> (STree a, Ts a)
                getMin (Build [t]) = (t, empty)
                getMin (Build (t:ts))
                    | root t <= root t' = (t, Build ts)
                    | otherwise         = (t', Build (t:ts'))
                    where (t', Build ts') = getMin (Build ts)
                split :: Ts a -> [a] -> Ts a -> (Ts a, [a])
                split ts xs (Build []) = (ts, xs)
                split (Build ts) xs (Build (t:c))
                    | rank t == 0 = split (Build ts) (root t : xs) (Build c)
                    | otherwise   = split (Build (t:ts)) xs (Build c)
                (Node x r c, tss) = getMin ts
                (ts', xs')        = split empty [] (Build c)


