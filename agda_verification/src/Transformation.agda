{-# OPTIONS --rewriting #-}
open import Preorder as P
open import PriorityQueue as PQ
open import Calf hiding (A)
open import Calf.Data.Bool
open import Calf.Data.Maybe

module Transformation (M : Preorder) (PQ : PriorityQueue M) where
  open Preorder M
  module PQM = PQ M

  module AddRoot where
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

    RootedSBH : PQM.PriorityQueue
    RootedSBH = record { Q = rq;
                         emp = emp;
                         isEmpty = isEmpty;
                         insert = insert;
                         merge = merge;
                         findMin = findMin;
                         deleteMin = deleteMin}

