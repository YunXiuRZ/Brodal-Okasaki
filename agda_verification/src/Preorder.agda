{-# OPTIONS --prop --rewriting #-}

open import Calf.CBPV hiding (A)

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Reflects
open import Relation.Binary hiding (Preorder)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Sum
open import Function

Π' : (A : Set) → (A → Set) → Set
Π' A B = (x : A) → B x

record Preorder : Set₁ where
  field
    A : tp⁺
    _≤_ : val A → val A → Set
    ≤-refl : Reflexive _≤_
    ≤-trans : Transitive _≤_
    ≤-total : Total _≤_
    _≤?_ : Π' (val A) λ x → Π' (val A) λ y → Dec (x ≤ y)

  _≥_ : val A → val A → Set
  x ≥ y = y ≤ x

  _≰_ : val A → val A → Set
  x ≰ y = ¬ x ≤ y

  ≰⇒≥ : _≰_ ⇒ _≥_
  ≰⇒≥ ¬x≤y with ≤-total _ _
  ... | inj₁ x≤y = contradiction x≤y ¬x≤y
  ... | inj₂ y≤x = y≤x

  case-≤ : {S : Set} {x y : val A} → (x ≤ y → S) → (x ≰ y → S) → Dec (x ≤ y) → S
  case-≤ {S} {x} {y} yes-branch no-branch (yes x≤y) = yes-branch x≤y
  case-≤ {S} {x} {y} yes-branch no-branch (no ¬x≤y) = no-branch ¬x≤y

  bind/case-≤ : {x y : val A} {f : val B → cmp X} (yes-branch : x ≤ y → cmp (F B)) (no-branch : x ≰ y → cmp (F B)) (d : Dec (x ≤ y)) →
    bind X (case-≤ yes-branch no-branch d) f ≡ case-≤ (λ h → bind X (yes-branch h) f) (λ h → bind X (no-branch h) f) d
  bind/case-≤ yes-branch no-branch (yes x≤y) = refl
  bind/case-≤ yes-branch no-branch (no ¬x≤y) = refl

  case-≤/idem : {S : Set} {x y : val A} (branch : S) (d : Dec (x ≤ y)) →
    case-≤ {S} {x} {y} (λ _ → branch) (λ _ → branch) d ≡ branch
  case-≤/idem branch (yes x≤y) = refl
  case-≤/idem branch (no ¬x≤y) = refl

getᴬ : Preorder → tp⁺
getᴬ M = Preorder.A M

-- Example of construction of preorder
NatPreorder : Preorder
NatPreorder = record
  { A = nat
  ; _≤_ = _≤_
  ; ≤-refl = ≤-refl
  ; ≤-trans = ≤-trans
  ; ≤-total = ≤-total
  ;_≤?_ = λ x y → (x ≤? y)
  }
  where
    open import Calf.Data.Nat
    open import Data.Nat.Properties
