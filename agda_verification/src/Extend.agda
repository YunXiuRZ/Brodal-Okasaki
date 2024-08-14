{-# OPTIONS --rewriting #-}
module Extend where

open import Calf.Prelude
open import Calf.CBPV
open import Relation.Nullary
open import Calf.Data.Nat hiding (_≤?_) 
open import Calf.Data.Maybe
open import Data.Nat.Properties using (≤-refl; <-≤-trans; <⇒≤; n≤1+n; ≤-trans)
open import Relation.Binary.PropositionalEquality


branch : {S E : Set} → (Dec E) → (E → S) → (¬ E → S) → S
branch {S} (yes proof) true-branch false-branch = true-branch proof
branch {S} (no proof) true-branch false-branch = false-branch proof

postulate
  branch-yes : {S E : Set} {exp : Dec E} {tb : E → S} {fb : ¬ E → S} {proof : E}
             → branch exp tb fb ≡ tb proof
  branch-no : {S E : Set} {exp : Dec E} {tb : E → S} {fb : ¬ E → S} {proof : ¬ E}
            → branch exp tb fb ≡ fb proof


data _≤ⁿ_ : val nat → val (maybe nat) → Set where
  just : ∀ {n m}
       → n ≤ m
        ----------------
       → n ≤ⁿ (just m)

  nothing : ∀ {n}
           ---------------
          → n ≤ⁿ nothing

data _<ⁿ_ : val nat → val (maybe nat) → Set where
  just : ∀ {n m}
       → n < m
        ----------------
       → n <ⁿ (just m)

  nothing : ∀ {n}
           ----------------
          → n <ⁿ nothing

<ⁿ→s≤ⁿ : ∀ {n m} → n <ⁿ m → (suc n) ≤ⁿ m
<ⁿ→s≤ⁿ (just x) = just x
<ⁿ→s≤ⁿ nothing = nothing


s≤ⁿ→≤ⁿ : ∀ {n mr} → suc n ≤ⁿ mr → n ≤ⁿ mr
s≤ⁿ→≤ⁿ {n} {mr = just r} (just sn≤r) = just (≤-trans (n≤1+n n) sn≤r)
s≤ⁿ→≤ⁿ {mr = nothing} sn≤ⁿmr = nothing

n≤ⁿn : ∀ {n} → n ≤ⁿ just n
n≤ⁿn = just ≤-refl

data _≤ᵐ_ : val (maybe nat) → val (maybe nat) → Set where
  just : ∀ {n m}
       → n ≤ⁿ m
        ----------------
       → (just n) ≤ᵐ m

  nothing : 
           -------------
          nothing ≤ᵐ nothing

≤ᵐ-refl : ∀ {n} → n ≤ᵐ n
≤ᵐ-refl {just x} = just n≤ⁿn
≤ᵐ-refl {nothing} = nothing


<-≤ᵐ→<ⁿ : ∀ {n m mr} → n < m → (just m) ≤ᵐ mr → n <ⁿ mr
<-≤ᵐ→<ⁿ {mr = just r} n<m (just (just m≤r)) = just (<-≤-trans n<m m≤r)
<-≤ᵐ→<ⁿ {mr = nothing} n<m (just m≤ⁿmr) = nothing


<ⁿ-≤ᵐ→<ⁿ : ∀ {n mr mr'} → n <ⁿ mr → mr ≤ᵐ mr' → n <ⁿ mr'
<ⁿ-≤ᵐ→<ⁿ {mr = just r} {mr' = just r'} (just n<r) (just (just r≤r')) = just (<-≤-trans n<r r≤r')
<ⁿ-≤ᵐ→<ⁿ {mr' = nothing} n<ⁿmr mr≤ᵐmr' = nothing

<ⁿ-≤ᵐ→≤ᵐ : ∀ {n mr mr'} → n <ⁿ mr → mr ≤ᵐ mr' → just n ≤ᵐ mr'
<ⁿ-≤ᵐ→≤ᵐ {mr' = just r'} (just n<m) (just (just m≤r')) = just (just (<⇒≤ (<-≤-trans n<m m≤r')))
<ⁿ-≤ᵐ→≤ᵐ {mr' = nothing} n<ⁿmr mr≤ᵐmr' = just nothing



