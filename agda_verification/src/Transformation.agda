{-# OPTIONS --rewriting #-}
open import Examples.Sorting.Sequential.Comparable
open import PriorityQueue 
open import Calf hiding (A)
open import Calf.Data.Bool
open import Calf.Data.Maybe

module Transformation (M : Comparable) (PQ : PriorityQueue M) where
open Comparable M

-- Rooted Queue
data RQ : Set where
  empty : RQ

  root : val A
       → val (PriorityQueue.Q PQ)
        --------------------------
       → RQ
rq : tp⁺
rq = meta⁺ RQ

emp : val rq
emp = empty

postulate
  isEmpty : cmp (Π rq λ _ → F bool)
  insert : cmp (Π A λ _ → Π rq λ _ → F rq)
  merge : cmp (Π rq λ _ → Π rq λ _ → F rq)
  findMin : cmp (Π rq λ _ → F (maybe A))
  deleteMin : cmp (Π rq λ _ → F rq)
 

