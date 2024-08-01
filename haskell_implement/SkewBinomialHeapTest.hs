import PriorityQueue
import SkewBinomialHeap

toSkewBinomialHeap :: Ord a => [a] -> Ts a
toSkewBinomialHeap = foldr insert empty

heap :: Ts Integer
heap = toSkewBinomialHeap [4, 8, 7, 6, 3]

