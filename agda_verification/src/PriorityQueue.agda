{-# OPTIONS --rewriting #-}
open import Calf.Data.Bool
open import Examples.Sorting.Sequential.Comparable
open import Calf hiding (A)
open import Calf.Data.Maybe

module PriorityQueue (M : Comparable)  where

record PriorityQueue (A : tp⁺) : Set where
  field
    Q : tp⁺
    emp : val Q
    isEmpty : cmp (Π Q λ _ → F bool)
    insert : cmp (Π A λ _ → Π Q λ _ → F Q)
    merge : cmp (Π Q λ _ → Π Q λ _ → F Q)
    findMin : cmp (Π Q λ _ → F (maybe A))
    deleteMin : cmp (Π Q λ _ → F Q)
    

