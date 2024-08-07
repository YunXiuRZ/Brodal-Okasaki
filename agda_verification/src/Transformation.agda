{-# OPTIONS --rewriting #-}
open import Preorder as P
open import PriorityQueue as PQ
open import Calf hiding (A)
open import Calf.Data.Bool hiding (_≤_)
open import Calf.Data.Maybe

open import Relation.Binary hiding (Preorder)

module Transformation (M : Preorder) (Queue : PriorityQueue M) where
  open Preorder M
  module PQM = PQ M

  module AddRoot where
    -- Rooted Queue
    data RQ : Set where
      empty : RQ

      root : val A
           → val (PriorityQueue.Q Queue)
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
{-
  module Bootstrapping where
    mutual 
      data R : Set where
        empty : val A
               -------
              → R

        {-rec : val A
            → val (PriorityQueue.Q PQR.PriorityQueue)
            ---------------------------
            → R-}
      r : tp⁺
      r = meta⁺ R

      _≤ᵣ_ : val r → val r → Set
      (empty a₁) ≤ᵣ (empty a₂) = a₁ ≤ a₂
      {-(empty a₁) ≤ᵣ (rec a₂ _) = a₁ ≤ a₂
      (rec a₁ _) ≤ᵣ (empty a₂) = a₁ ≤ a₂
      (rec a₁ _) ≤ᵣ (rec a₂ _) = a₁ ≤ a₂-}

      ≤ᵣ-refl : Reflexive _≤ᵣ_
      ≤ᵣ-refl = {!!} 

      ≤ᵣ-trans : Transitive _≤ᵣ_
      ≤ᵣ-trans = {!!}

      ≤ᵣ-total : Total _≤ᵣ_
      ≤ᵣ-total = {!!}
      
      instance
        preorderR : Preorder
        preorderR = record
          { A = r
          ; _≤_ = _≤ᵣ_
          ; ≤-refl = ≤ᵣ-refl
          ; ≤-trans = ≤ᵣ-trans
          ; ≤-total = ≤ᵣ-total
          }

      open module PQR = PQ preorderR

-}
