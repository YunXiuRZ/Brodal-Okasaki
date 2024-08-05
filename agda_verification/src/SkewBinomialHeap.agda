{-# OPTIONS --prop --rewriting #-}
open import Examples.Sorting.Sequential.Comparable

module SkewBinomialHeap (M : Comparable)  where

open import Calf hiding (A)
open import Calf.Data.Nat 
open import Calf.Data.List
open import Calf.Data.Maybe


open Comparable M renaming (_≤?_ to _≤ᴬ?_; _≤_ to _≤ᴬ_)
open import Examples.Sorting.Sequential.Core M
open import Function
open import Data.Sum


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
sbh : val (maybe nat) → tp⁺
sbh r = meta⁺ (SBH r)


root : cmp (Π nat λ r → Π (sbt r) λ _ → F A)
root .zero (leaf x) = ret x
root .(suc r) (simple r sbt₁ sbt₂) = root r sbt₁
root .(suc r) (skewA r x sbt₁ sbt₂) = ret x
root .(suc r) (skewB r x sbt₁ sbt₂) = ret x

rank : cmp (Π nat λ r → Π (sbt r) λ _ → F nat)
rank r sbt = ret r

-- test how to use comparable
ctest : cmp (Π A λ _ → Π A λ _ → F A)
ctest x y = bind (F _) (x ≤ᴬ? y) $ case-≤
    (λ x≤y → ret {!!})
    (λ x≰y → ret {!!})

postulate
  link : cmp (Π nat λ r → Π (sbt r) λ _ → Π (sbt r) λ _ → F (sbt (suc r)))

  skewLink : cmp (Π (sbt 0) λ _ → Π nat λ r → Π (sbt r) λ _ → Π (sbt r) λ _ → F (sbt (suc r)))

  -- we assume that r' ≤ r or r' is nothing
  {-insertTree : cmp (Π nat λ r → Π (sbt r) λ _
                  → Π (maybe nat) λ r' → Π (sbh r') λ _
                  → F (sbh ))-}

--uniqify cmp (Π nat λ _ → Π (sbh A r) → Π (sbh










