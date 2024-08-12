{-# OPTIONS --rewriting #-}
module Extend where

open import Calf.Prelude
open import Calf.CBPV
open import Relation.Nullary
open import Calf.Data.Nat hiding (_≤?_) renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_)
open import Calf.Data.Maybe
open import Data.Nat.Properties using (≤-refl)


postulate
  bind2 : (X : tp⁻) → cmp (F A) → cmp (F B) → (val A → val B → cmp X) → cmp X


branch : {S E : Set} → (Dec E) → (E → S) → (¬ E → S) → S
branch {S} (yes proof) true-branch false-branch = true-branch proof
branch {S} (no proof) true-branch false-branch = false-branch proof

data _≤ⁿn_ : val nat → val (maybe nat) → Set where
  just : ∀ {n m}
       → n ≤ⁿ m
        ----------------
       → n ≤ⁿn (just m)

  nothing : ∀ {n}
           ---------------
          → n ≤ⁿn nothing

data _<ⁿn_ : val nat → val (maybe nat) → Set where
  just : ∀ {n m}
       → n <ⁿ m
        ----------------
       → n <ⁿn (just m)

  nothing : ∀ {n}
           ----------------
          → n <ⁿn nothing

<ⁿn→s≤ⁿn : ∀ {n m} → n <ⁿn m → (suc n) ≤ⁿn m
<ⁿn→s≤ⁿn (just x) = just x
<ⁿn→s≤ⁿn nothing = nothing

n≤ⁿnn : ∀ {n} → n ≤ⁿn just n
n≤ⁿnn = just ≤-refl
