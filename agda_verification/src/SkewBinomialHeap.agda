{-# OPTIONS --prop --rewriting #-}
open import Examples.Sorting.Sequential.Comparable

module SkewBinomialHeap (M : Comparable)  where

open import Calf hiding (A)
open import Calf.Data.Nat hiding (_≤?_)
open import Calf.Data.List


open Comparable M
open import Examples.Sorting.Sequential.Core M
open import Function


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

data SBH : val nat → Set where
  LSB : ∀ r
      → SBT r
       ---------------
      → SBH r

  sLSB : ∀ r
       → SBT r
       → SBT r
        ---------------
       → SBH r

  cons : ∀ {r r'}
       → r < r'
       → SBH r
       → SBT r'
        ----------------
       → SBH r'


root : cmp (Π nat λ r → Π (sbt r) λ _ → F A)
root .zero (leaf x) = ret x
root .(suc r) (simple r sbt₁ sbt₂) = root r sbt₁
root .(suc r) (skewA r x sbt₁ sbt₂) = ret x
root .(suc r) (skewB r x sbt₁ sbt₂) = ret x

rank : cmp (Π nat λ r → Π (sbt r) λ _ → F nat)
rank r sbt = ret r

link : cmp (Π nat λ r → Π (sbt r) λ _ → Π (sbt r) λ _ → F (sbt (suc r)))
link r sbt₁ sbt₂ = {!!}

skewLink : cmp (Π (sbt 0) λ _ → Π nat λ r → Π (sbt r) λ _ → Π (sbt r) λ _ → F (sbt (suc r)))
skewLink sbt₀ r sbt₁ sbt₂ = {!!}


-- test how to use comparable
ctest : cmp (Π A λ _ → Π A λ _ → F A)
ctest x y = bind (F _) (x ≤? y) $ case-≤
    (λ x≤y → ret {!!})
    (λ x≰y → ret {!!})


--insertTree : cmp (Π nat λ _ → Π)

--uniqify cmp (Π nat λ _ → Π (sbh A r) → Π (sbh










