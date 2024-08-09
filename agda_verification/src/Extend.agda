{-# OPTIONS --rewriting #-}
module Extend where

open import Calf.Prelude
open import Calf.CBPV
open import Relation.Nullary



postulate
  bind2 : (X : tp⁻) → cmp (F A) → cmp (F B) → (val A → val B → cmp X) → cmp X


branch : {S E : Set} → (Dec E) → (E → S) → (¬ E → S) → S
branch {S} (yes proof) true-branch false-branch = true-branch proof
branch {S} (no proof) true-branch false-branch = false-branch proof
