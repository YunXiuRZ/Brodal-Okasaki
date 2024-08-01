import PriorityQueue 
import SkewBinomialHeap 
import AddRoot 

toHeap :: Ord a => [a] -> RQ Ts a
toHeap = foldr insert empty

heap = toHeap [4, 8, 7, 6, 3]



