{-# OPTIONS --prop --rewriting #-}
open import Examples.Sorting.Sequential.Comparable

module SkewBinomialHeap (M : Comparable)  where

open import Calf hiding (A)
open import Calf.Data.Nat 
open import Calf.Data.List hiding (merge)
open import Calf.Data.Maybe
open import Calf.Data.Bool hiding (_≤_; _<_)

open import Agda.Builtin.Unit


open Comparable M renaming (_≤?_ to _≤ᴬ?_; _≤_ to _≤ᴬ_)
open import Examples.Sorting.Sequential.Core M
open import Function
open import Data.Sum

-- Skew Binomial Tree
data SBT : val nat → Set where
  leaf : val A
        -------------
       → SBT zero
  
  simple : ∀ r
         → SBT r
         → SBT r
          --------------
         →  SBT (suc r)

  skewA : ∀ r
        → val A
        → SBT r
        → SBT r
         ---------------
        → SBT (suc r)

  skewB : ∀ r
        → val A
        → SBT r
        → SBT r
         ---------------
        → SBT (suc r)
sbt : val nat → tp⁺
sbt r = meta⁺ (SBT r)

{-
data SBH : val (maybe nat) → Set where
  empty : SBH nothing

  LSB : ∀ r
      → SBT r
       ---------------
      → SBH (just r)

  sLSB : ∀ r
       → SBT r
       → SBT r
        ---------------
       → SBH (just r)

  cons : ∀ {r r'}
       → r < r'
       → SBH (just r)
       → SBT r'
        ----------------
       → SBH (just r')
-}

_≤n_ : val nat → val (maybe nat) → Set
n ≤n (just m) = n ≤ m
n ≤n nothing = ⊤

_<n_ : val nat → val (maybe nat) → Set
n <n (just m) = n < m
n <n nothing = ⊤

-- Monotonic List of Skew Binomial Trees
data SBML : val (maybe nat) → Set where
  empty : SBML nothing

  cons : ∀ {r mr}
       → r <n mr
       → SBT r
       → SBML mr
       ----------
       → SBML (just r)

-- true → uniqified
data SBH : val bool → val (maybe nat) → Set where
  unique : ∀ {mr}
         → SBML mr
         ---------
         → SBH true mr

  skew : ∀ {r}
       → SBT r
       → SBML (just r)
       ----------------
       → SBH false (just r)
       
sbh : val bool → val (maybe nat) → tp⁺
sbh b mr = meta⁺ (SBH b mr)

root : cmp (Π nat λ r → Π (sbt r) λ _ → F A)
root .zero (leaf x) = ret x
root .(suc r) (simple r sbt₁ sbt₂) = root r sbt₁
root .(suc r) (skewA r x sbt₁ sbt₂) = ret x
root .(suc r) (skewB r x sbt₁ sbt₂) = ret x

rank : cmp (Π nat λ r → Π (sbt r) λ _ → F nat)
rank r sbt = ret r

-- test how to use comparable
{-
ctest : cmp (Π A λ _ → Π A λ _ → F A)
ctest x y = bind (F _) (x ≤ᴬ? y) $ case-≤
    (λ x≤y → ret {!!})
    (λ x≰y → ret {!!})
-}

postulate
  link : cmp (Π nat λ r → Π (sbt r) λ _ → Π (sbt r) λ _ → F (sbt (suc r)))

  skewLink : cmp (Π (sbt 0) λ _ → Π nat λ r → Π (sbt r) λ _ → Π (sbt r) λ _ → F (sbt (suc r)))

  --we assume that r' ≤ r or r' is nothing later
  insertTree : cmp (Π nat λ r → Π (sbt r) λ _
                  → Π (maybe nat) λ mr → Π (Σ⁺ bool (λ b → sbh b mr)) λ _
                  → Π (meta⁺ (r ≤n mr)) λ _ 
                  → F (Σ⁺ bool (λ b → (Σ⁺ nat (λ i → sbh b (just i))))))

  uniqify : cmp (Π bool λ b → Π (maybe nat) λ mr → Π (sbh b mr) λ _
               → F (Σ⁺ nat (λ r → sbh true (just r))))

  meldUniq : cmp (Π (maybe nat) λ mr₁ → Π (sbh true mr₁) λ _
                → Π (maybe nat) λ mr₂ → Π (sbh true mr₂) λ _
                → F (Σ⁺ bool (λ b → Σ⁺ (maybe nat) λ mr → sbh b mr)))

  emp : val (sbh true nothing)

  isEmpty : cmp (Π bool λ b → Π (maybe nat) λ mr → Π (sbh b mr) λ _
               → F bool)

  insert : cmp (Π A λ _
              → Π bool λ b → Π (maybe nat) λ mr → Π (sbh b mr) λ _
              → F (Σ⁺ bool λ b' → Σ⁺ (maybe nat) λ mr' → sbh b' mr'))

  merge : cmp (Π bool λ b₁ → Π (maybe nat) λ mr₁ → Π (sbh b₁ mr₁) λ _
             → Π bool λ b₂ → Π (maybe nat) λ mr₂ → Π (sbh b₂ mr₂) λ _
             → F (Σ⁺ bool λ b → Σ⁺ (maybe nat) λ mr → sbh b mr))

  findMin : cmp (Π bool λ b → Π (maybe nat) λ mr → Π (sbh b mr) λ _
               → F A)

  deleteMin : cmp (Π bool λ b → Π (maybe nat) λ mr → Π (sbh b mr) λ _
                 → F (maybe A))

--uniqify cmp (Π nat λ _ → Π (sbh A r) → Π (sbh
{-
   emp : val Q
   isEmpty : cmp (Π Q λ _ → F bool)
   insert : cmp (Π A λ _ → Π Q λ _ → F Q)
   merge : cmp (Π Q λ _ → Π Q λ _ → F Q)
   findMin : cmp (Π Q λ _ → F (maybe A))
   deleteMin : cmp (Π Q λ _ → F Q)
-}







