{-# OPTIONS --rewriting #-}
open import Preorder as P
open import PriorityQueue as PQ
open import Calf hiding (A)
open import Calf.Data.Bool hiding (_≤_)
open import Calf.Data.Maybe

open import Relation.Binary hiding (Preorder)


module Transformation where
  variable
    M : Preorder
    Q : PQFunctor

  module AddRoot where
    -- Rooted Queue
    data RQ (M : Preorder) (Queue : PQFunctor) : Set where
      empty : RQ M Queue

      root : val (getᴬ M)
           → val (PriorityQueue.Q (Queue M))
           --------------------------
           → RQ M Queue
    rq : Preorder → PQFunctor → tp⁺
    rq M Queue = meta⁺ (RQ M Queue)

    emp : val (rq M Q)
    emp = empty

    postulate
      isEmpty : cmp (Π (rq M Q) λ _ → F bool)
      insert : cmp (Π (getᴬ M) λ _ → Π (rq M Q) λ _ → F (rq M Q))
      merge : cmp (Π (rq M Q) λ _ → Π (rq M Q) λ _ → F (rq M Q))
      findMin : cmp (Π (rq M Q) λ _ → F (maybe (getᴬ M)))
      deleteMin : cmp (Π (rq M Q) λ _ → F (rq M Q))

    RootedSBH : PQFunctor → PQFunctor
    RootedSBH Q M = record { Q = rq M Q
                           ; emp = emp
                           ; isEmpty = isEmpty
                           ; insert = insert
                           ; merge = merge
                           ; findMin = findMin
                           ; deleteMin = deleteMin}

-- I temporarily give up this part due to the difficulty of defining Bootstrapping, but I have some maybe useful idea. I'll try to implement it if time permits
{-
  module Bootstrapping where
    mutual 
      data R (M : Preorder) (Queue : PQFunctor) : Set where
        empty : val (getᴬ M)
               -------
              → R M Queue

        rec : val (getᴬ M)
            → val (PriorityQueue.Q (Queue (preorderR M Queue)))
            ---------------------------
            → R M Queue
      r : Preorder → PQFunctor → tp⁺
      r M Q = meta⁺ (R M Q)

      
      _≤ᵣ_ : (M : Preorder) → (Q : PQFunctor) → val (r M Q) → val (r M Q) → Set
      _≤ᵣ_ M Q (empty a₁) (empty a₂) = {!!}
      _≤ᵣ_ M Q (empty a₁) (rec a₂ _) = {!!}
      _≤ᵣ_ M Q(rec a₁ _) (empty a₂) = {!!}
      _≤ᵣ_ M Q(rec a₁ _) (rec a₂ _) = {!!}

      ≤ᵣ-refl : (M : Preorder) → (Q : PQFunctor) → Reflexive (_≤ᵣ_ M Q)
      ≤ᵣ-refl M Q = {!!} 

      ≤ᵣ-trans : (M : Preorder) → (Q : PQFunctor) → Transitive (_≤ᵣ_ M Q)
      ≤ᵣ-trans M Q = {!!}
 
      ≤ᵣ-total : (M : Preorder) → (Q : PQFunctor) → Total (_≤ᵣ_ M Q)
      ≤ᵣ-total M Q = {!!}
      

      preorderR : Preorder → PQFunctor → Preorder
      preorderR M Q = record
        { A = r M Q
        ; _≤_ = _≤ᵣ_ M Q
        ; ≤-refl = ≤ᵣ-refl M Q
        ; ≤-trans = ≤ᵣ-trans M Q
        ; ≤-total = ≤ᵣ-total M Q
        }


-}
