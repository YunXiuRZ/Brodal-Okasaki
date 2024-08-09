{-# OPTIONS --prop --rewriting #-}
open import Preorder as P 

module SkewBinomialHeap where

open import Calf hiding (A)
open import Calf.Data.Nat hiding (_≤?_) renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_)
open import Calf.Data.List hiding (merge; and)
open import Calf.Data.Maybe
open import Calf.Data.Bool hiding (_≤_; _<_; _≤?_)

open import Agda.Builtin.Unit

open import PriorityQueue
open import Extend

open import Function
open import Data.Sum
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Negation using (¬_)

variable
  M : Preorder

-- Skew Binomial Tree
-- When linking two SBT, we set the root of the resulting SBT to be the root of
-- the former one
data SBT (M : Preorder) : val nat → Set where
  leaf : val (getᴬ M)
        -------------------
       → SBT M zero
  
  simple : ∀ {r}
         → SBT M r
         → SBT M r
          --------------
         →  SBT M (suc r)

  skewA : ∀ {r}
        → val (getᴬ M)
        → SBT M r
        → SBT M r
         ---------------
        → SBT M (suc r)

  skewB : ∀ {r}
        → SBT M r
        → val (getᴬ M)
        → SBT M r
         ---------------
        → SBT M (suc r)

sbt : Preorder → val nat → tp⁺
sbt M r = meta⁺ (SBT M r)

_≤ⁿn_ : val nat → val (maybe nat) → Set
n ≤ⁿn (just m) = n ≤ⁿ m
n ≤ⁿn nothing = ⊤

_<ⁿn_ : val nat → val (maybe nat) → Set
n <ⁿn (just m) = n <ⁿ m
n <ⁿn nothing = ⊤

-- Monotonic List of Skew Binomial Trees
data SBML (M : Preorder) : val (maybe nat) → Set where
  empty : SBML M nothing

  cons : ∀ {r mr}
       → r <ⁿn mr
       → SBT M r
       → SBML M mr
       ----------
       → SBML M (just r)

-- true → uniqified
data SBH (M : Preorder) : val bool → val (maybe nat) → Set where
  unique : ∀ {mr}
         → SBML M mr
         ---------
         → SBH M true mr

  skew : ∀ {r}
       → SBT M r
       → SBML M (just r)
       ----------------
       → SBH M false (just r)
       
sbh : Preorder → val bool → val (maybe nat) → tp⁺
sbh M b mr = meta⁺ (SBH M b mr)

root : {M : Preorder} → {r : val nat} → val (sbt M r) → val (getᴬ M)
--Π nat λ r → Π (sbt M r) λ _ → F (getᴬ M)
root (leaf x) = x
root (simple t₁ t₂) = root t₁
root (skewA x t₁ t₂) = x
root (skewB t₁ x t₂) = x

rank : {M : Preorder} → {r : val nat} → val (sbt M r) → val nat
rank {M} {r} t = r

link : cmp (Π nat λ r → Π (sbt M r) λ _ → Π (sbt M r) λ _ → F (sbt M (suc r)))
link {M} r t₁ t₂ = branch (x₁ ≤? x₂)
   (λ x≤y → ret (simple t₁ t₂))
   (λ x≰y → ret (simple t₂ t₁))
   where
   open Preorder M
   x₁ = root t₁
   x₂ = root t₂

skewLink : cmp (Π (sbt M 0) λ _ → Π nat λ r → Π (sbt M r) λ _ → Π (sbt M r) λ _ → F (sbt M (suc r)))
skewLink {M} t₀ r t₁ t₂ = branch (x₁ ≤? x₂ ×-dec x₁ ≤? x₀)
  (λ _ → ret (skewB t₁ x₀ t₂))
  (λ _ → branch ((x₂ ≤? x₁) ×-dec (x₂ ≤? x₀))
         (λ _ → ret (skewB t₂ x₀ t₁))
         (λ _ → ret (skewA x₀ t₁ t₂) ))
  where
  open Preorder M
  x₀ = root t₀
  x₁ = root t₁
  x₂ = root t₂


postulate
  --we assume that r' ≤ r or r' is nothing 
  insertTree : cmp (Π nat λ r → Π (sbt M r) λ _
                  → Π (maybe nat) λ mr → Π (Σ⁺ bool (λ b → sbh M b mr)) λ _
                  → Π (meta⁺ (r ≤ⁿn mr)) λ _ 
                  → F (Σ⁺ bool (λ b → (Σ⁺ nat (λ i → sbh M b (just i))))))
  uniqify : cmp (Π bool λ b → Π (maybe nat) λ mr → Π (sbh M b mr) λ _
               → F (Σ⁺ nat (λ r → sbh M true (just r))))
  meldUniq : cmp (Π (maybe nat) λ mr₁ → Π (sbh M true mr₁) λ _
                → Π (maybe nat) λ mr₂ → Π (sbh M true mr₂) λ _
                → F (Σ⁺ bool (λ b → Σ⁺ (maybe nat) λ mr → sbh M b mr)))


queue : Preorder → tp⁺
queue M = Σ⁺ bool λ b → Σ⁺ (maybe nat) λ mr → sbh M b mr

emp : val (queue M)
emp = (true , (nothing , unique empty))

postulate
  isEmpty : cmp (Π (queue M) λ _ → F bool)
  insert : cmp (Π (getᴬ M) λ _ → Π (queue M) λ _ → F (queue M))
  merge : cmp (Π (queue M) λ _ → Π (queue M) λ _ → F (queue M))
  findMin : cmp (Π (queue M) λ _ → F (maybe (getᴬ M)))
  deleteMin : cmp(Π (queue M) λ _ → F (queue M))


skewBinomialHeap : PQFunctor
skewBinomialHeap M = record { Q = queue M
                            ; emp = emp
                            ; isEmpty = isEmpty
                            ; insert = insert
                            ; merge = merge
                            ; findMin = findMin
                            ; deleteMin = deleteMin
                            }


