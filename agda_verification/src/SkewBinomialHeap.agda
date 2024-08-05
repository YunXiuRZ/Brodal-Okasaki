{-# OPTIONS --prop --rewriting #-}
open import Examples.Sorting.Sequential.Comparable

module SkewBinomialHeap (M : Comparable)  where

open import Calf hiding (A)
open import Calf.Data.Nat 
open import Calf.Data.List


open Comparable M
open import Examples.Sorting.Sequential.Core M
open import Function


data SBT (A : tp⁺) : val nat → Set where
  leaf : val A
        -------------
       → SBT A zero
  
  simple : ∀ r
         → SBT A r
         → SBT A r
          --------------
         →  SBT A (suc r)

  skewA : ∀ r
        → val A
        → SBT A r
        → SBT A r
         ---------------
        → SBT A (suc r)

  skewB : ∀ r
        → val A
        → SBT A r
        → SBT A r
         ---------------
        → SBT A (suc r)
sbt : (A : tp⁺) → val nat → tp⁺
sbt A r = meta⁺ (SBT A r)

data SBH (A : tp⁺) : val nat → Set where
  LSB : ∀ r
      → SBT A r
       ---------------
      → SBH A r

  sLSB : ∀ r
       → SBT A r
       → SBT A r
        ---------------
       → SBH A r

  cons : ∀ {r r'}
       → r < r'
       → SBH A r
       → SBT A r'
        ----------------
       → SBH A r'


root : cmp (Π nat λ r → Π (sbt A r) λ _ → F A)
root .zero (leaf x) = ret x
root .(suc r) (simple r sbt₁ sbt₂) = root r sbt₁
root .(suc r) (skewA r x sbt₁ sbt₂) = ret x
root .(suc r) (skewB r x sbt₁ sbt₂) = ret x

rank : cmp (Π nat λ r → Π (sbt A r) λ _ → F nat)
rank r sbt = ret r

link : cmp (Π nat λ r → Π (sbt A r) λ _ → Π (sbt A r) λ _ → F (sbt A (suc r)))
link r sbt₁ sbt₂ = {!!}

skewLink : cmp (Π (sbt A 0) λ _ → Π nat λ r → Π (sbt A r) λ _ → Π (sbt A r) λ _ → F (sbt A (suc r)))
skewLink sbt₀ r sbt₁ sbt₂ = ?

{-
ctest : cmp (Π A λ _ → Π A λ _ → F A)
ctest x y = bind (F _) (x ≤? y) $ case-≤
    (λ x≤y → ret ?)
    (λ x≰y → ret ?)
-}

--insertTree : cmp (Π nat λ _ → Π)

--uniqify cmp (Π nat λ _ → Π (sbh A r) → Π (sbh










