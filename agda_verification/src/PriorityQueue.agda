{-# OPTIONS --rewriting #-}
open import Calf.Data.Bool
open import Preorder as P
open import Calf hiding (A)
open import Calf.Data.Maybe

module PriorityQueue where

record PriorityQueue (M : Preorder) : Set where
  field
    Q : tp⁺
    emp : val Q
    isEmpty : cmp (Π Q λ _ → F bool)
    insert : cmp (Π (getᴬ M) λ _ → Π Q λ _ → F Q)
    merge : cmp (Π Q λ _ → Π Q λ _ → F Q)
    findMin : cmp (Π Q λ _ → F (maybe (getᴬ M)))
    deleteMin : cmp (Π Q λ _ → F Q)

PQFunctor : Set₁
PQFunctor = (M : Preorder) → PriorityQueue M


