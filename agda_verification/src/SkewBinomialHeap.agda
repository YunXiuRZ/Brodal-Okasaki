{-# OPTIONS --prop --rewriting #-}
open import Preorder as P

module SkewBinomialHeap where

open import Calf hiding (A)
open import Calf.Data.Nat 
open import Calf.Data.List hiding (merge)
open import Calf.Data.Maybe
open import Calf.Data.Bool hiding (_≤_; _<_)

open import Agda.Builtin.Unit

open import PriorityQueue 

open import Function
open import Data.Sum

variable
  M : Preorder

-- Skew Binomial Tree
data SBT (M : Preorder) : val nat → Set where
  leaf : val (getᴬ M)
        -------------------
       → SBT M zero
  
  simple : ∀ r
         → SBT M r
         → SBT M r
          --------------
         →  SBT M (suc r)

  skewA : ∀ r
        → val (getᴬ M)
        → SBT M r
        → SBT M r
         ---------------
        → SBT M (suc r)

  skewB : ∀ r
        → val (getᴬ M)
        → SBT M r
        → SBT M r
         ---------------
        → SBT M (suc r)

sbt : Preorder → val nat → tp⁺
sbt M r = meta⁺ (SBT M r)

_≤n_ : val nat → val (maybe nat) → Set
n ≤n (just m) = n ≤ m
n ≤n nothing = ⊤

_<n_ : val nat → val (maybe nat) → Set
n <n (just m) = n < m
n <n nothing = ⊤

-- Monotonic List of Skew Binomial Trees
data SBML (M : Preorder) : val (maybe nat) → Set where
  empty : SBML M nothing

  cons : ∀ {r mr}
       → r <n mr
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

root : cmp (Π nat λ r → Π (sbt M r) λ _ → F (getᴬ M))
root .zero (leaf x) = ret x
root .(suc r) (simple r t₁ t₂) = root r t₁
root .(suc r) (skewA r x t₁ t₂) = ret x
root .(suc r) (skewB r x t₁ t₂) = ret x

rank : cmp (Π nat λ r → Π (sbt M r) λ _ → F nat)
rank r t = ret r

-- test how to use comparable
{-
ctest : cmp (Π A λ _ → Π A λ _ → F A)
ctest x y = bind (F _) (x ≤ᴬ? y) $ case-≤
    (λ x≤y → ret {!!})
    (λ x≰y → ret {!!})
-}

postulate
  link : cmp (Π nat λ r → Π (sbt M r) λ _ → Π (sbt M r) λ _ → F (sbt M (suc r)))
  skewLink : cmp (Π (sbt M 0) λ _ → Π nat λ r → Π (sbt M r) λ _ → Π (sbt M r) λ _ → F (sbt M (suc r)))
  --we assume that r' ≤ r or r' is nothing 
  insertTree : cmp (Π nat λ r → Π (sbt M r) λ _
                  → Π (maybe nat) λ mr → Π (Σ⁺ bool (λ b → sbh M b mr)) λ _
                  → Π (meta⁺ (r ≤n mr)) λ _ 
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


