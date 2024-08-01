import PriorityQueue
import SkewBinomialHeap
import AddRoot
import Bootstrapping

toHeap :: Ord a => [a] -> BP (RQ Ts) a
toHeap = foldr insert empty

heap = toHeap [4, 8, 7, 6, 3]


