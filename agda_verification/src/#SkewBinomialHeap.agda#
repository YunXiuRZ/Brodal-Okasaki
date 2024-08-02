{-# OPTIONS --prop --rewriting #-}

module SkewBinomialHeap  where

open import Calf
open import Calf.Data.Nat
open import Calf.Data.List


data SBT (A : tp⁺) : val nat → Set where
  leaf : (a : val A)
        -------------
       → SBT A zero
  
  simple : ∀ r
         → (t1 : SBT A r)
         → (t2 : SBT A r)
          --------------
         →  SBT A (suc r)

  skewA : ∀ r
        →  (a : val A)
        → (t1 : SBT A r)
        → (t2 : SBT A r)
         ---------------
        → SBT A (suc r)

  skewB : ∀ r
        →  (a : val A)
        → (t1 : SBT A r)
        → (t2 : SBT A r)
         ---------------
        → SBT A (suc r)


data SBH (A : tp⁺) : val nat → Set where
  LSB : ∀ r
      → (t : SBT A r)
       ---------------
      → SBH A r

  sLSB : ∀ r
       → (t1 : SBT A r)
       → (t2 : SBT A r)
        ---------------
       → SBH A r

  cons : ∀ {r r'}
       → (r<r' : r < r')
       → (h : SBH A r)
       → (t : SBT A r')
        ----------------
       → SBH A r'
       











