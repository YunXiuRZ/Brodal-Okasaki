{-# OPTIONS --prop --rewriting #-}
open import Preorder as P 

module SkewBinomialHeap where

open import Algebra.Cost.Instances using (ℕ-CostMonoid)
costMonoid = ℕ-CostMonoid

open import Calf costMonoid hiding (A)
open import Calf.Data.Nat hiding (_≤?_)
open import Calf.Data.List hiding (merge; and)
open import Calf.Data.Maybe
open import Calf.Data.Bool hiding (_≤_; _<_; _≤?_; _≟_)

{-open import Algebra.Cost.Instances using (ℕ-CostMonoid)
costMonoid = ℕ-CostMonoid
open import Calf.Step costMonoid
open import Calf.Data.BigO costMonoid
-}
open import Calf.Data.IsBounded costMonoid

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

open import PriorityQueue
open import Extend

open import Function
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat using (_+_)
open import Data.Nat.Properties using (≤∧≢⇒<; <-cmp; +-identityʳ; _≟_)
open import Data.Sum
open import Data.Product using (Σ; _×_)
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality as Eq using (subst; sym)
open import Relation.Binary.Definitions using (Tri; Trichotomous; tri<; tri≈; tri>)


variable
  M : Preorder

-- Skew Binomial Tree
-- When linking two SBT, we set the root of the resulting SBT to be the root of
-- the former one
data SBT (M : Preorder) : val nat → Set where
  leaf : val (getᴬ M)
        -------------------
       → SBT M zero
  
  simple : ∀ {r}
         → SBT M r
         → SBT M r
          --------------
         →  SBT M (suc r)

  skewA : ∀ {r}
        → val (getᴬ M)
        → SBT M r
        → SBT M r
         ---------------
        → SBT M (suc r)

  skewB : ∀ {r}
        → SBT M r
        → val (getᴬ M)
        → SBT M r
         ---------------
        → SBT M (suc r)

sbt : Preorder → val nat → tp⁺
sbt M r = meta⁺ (SBT M r)

-- Monotonic List of Skew Binomial Trees
data SBML (M : Preorder) : val (maybe nat) → Set where
  empty : SBML M nothing

  cons : ∀ {r mr}
       → SBT M r
       → SBML M mr
       → r <ⁿ mr
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

unique⁻¹ : ∀ {mr} → SBH M true mr → SBML M mr
unique⁻¹ (unique x) = x

len-sbml : ∀ {mr} → SBML M mr → ℕ
len-sbml empty = zero
len-sbml (cons t ts r<ⁿmr) = suc (len-sbml ts)

len-sbh : ∀ {b mr} → SBH M b mr → ℕ
len-sbh (unique ts) = len-sbml ts
len-sbh (skew t ts) = suc (len-sbml ts)


root : {M : Preorder} → {r : val nat} → val (sbt M r) → val (getᴬ M)
--Π nat λ r → Π (sbt M r) λ _ → F (getᴬ M)
root (leaf x) = x
root (simple t₁ t₂) = root t₁
root (skewA x t₁ t₂) = x
root (skewB t₁ x t₂) = x

rank : {M : Preorder} → {r : val nat} → val (sbt M r) → val nat
rank {M} {r} t = r

splitˢᵇʰ : {b : val bool} {r : val nat} → val (sbh M b (just r)) → (val (sbt M r)) × (Σ (val (maybe nat)) λ mr → val (sbh M true mr))
splitˢᵇʰ (unique (cons {r} {mr} t sbml r<ⁿnmr)) = t , (mr , unique sbml)
splitˢᵇʰ (skew {r} t sbml) = t , (just r , unique sbml)

headˢᵇʰ : {b : val bool} {r : val nat} → val (sbh M b (just r)) → val (sbt M r)
headˢᵇʰ sbh = proj₁ (splitˢᵇʰ sbh)

tailˢᵇʰ : {b : val bool} {r : val nat} → val (sbh M b (just r)) → (Σ (val (maybe nat)) λ mr → val (sbh M true mr))
tailˢᵇʰ sbh = proj₂ (splitˢᵇʰ sbh)


link : cmp (Π nat λ r → Π (sbt M r) λ _ → Π (sbt M r) λ _ → F (sbt M (suc r)))
link {M} r t₁ t₂ = branch (x₁ ≤? x₂)
   (λ x≤y → ret (simple t₁ t₂))
   (λ x≰y → ret (simple t₂ t₁))
   where
   open Preorder M
   x₁ = root t₁
   x₂ = root t₂

-- link has no cost
link/is-bounded : ∀ {M} r t₁ t₂
                → IsBounded (sbt M (suc r)) (link {M} r t₁ t₂) zero
link/is-bounded {M} r t₁ t₂ = branch (x₁ ≤? x₂)
  (λ x≤y → subst (λ x → (IsBounded (sbt M (suc r)) x zero)) (sym (branch-yes {exp = x₁ ≤? x₂} {proof = x≤y})) (bound/ret {sbt M (suc r)} (simple t₁ t₂)))
  (λ x≰y → subst (λ x → (IsBounded (sbt M (suc r)) x zero)) (sym (branch-no {exp = x₁ ≤? x₂} {proof = x≰y})) (bound/ret {sbt M (suc r)} (simple t₂ t₁)))
  where
  open Preorder M 
  x₁ = root t₁
  x₂ = root t₂

skewLink : cmp (Π (sbt M 0) λ _ → Π nat λ r → Π (sbt M r) λ _ → Π (sbt M r) λ _ → F (sbt M (suc r)))
skewLink {M} t₀ r t₁ t₂ = branch (x₁ ≤? x₂ ×-dec x₁ ≤? x₀)
  (λ x₁-min → ret (skewB t₁ x₀ t₂))
  (λ x₁-not-min → branch ((x₂ ≤? x₁) ×-dec (x₂ ≤? x₀))
    (λ x₂-min → ret (skewB t₂ x₀ t₁))
    (λ x₀-min → ret (skewA x₀ t₁ t₂)))
  where
  open Preorder M
  x₀ = root t₀
  x₁ = root t₁
  x₂ = root t₂
  
-- skewLink has no cost
skewLink/is-bounded : ∀ {M} t₀ r t₁ t₂
                    → IsBounded (sbt M (suc r)) (skewLink {M} t₀ r t₁ t₂) zero
skewLink/is-bounded {M} t₀ r t₁ t₂ = branch x₁-min?
  (λ x₁-min → (subst (λ x → IsBounded (sbt M (suc r)) x zero) (sym (branch-yes {exp = x₁-min?} {proof = x₁-min}))) $
              bound/ret {sbt M (suc r)} (skewB t₁ x₀ t₂))
  (λ x₁-not-min → branch x₂-min?
    (λ x₂-min → (subst (λ x → IsBounded (sbt M (suc r)) x zero) (sym (branch-no {exp = x₁-min?} {proof = x₁-not-min}))) $
                (subst (λ y → IsBounded (sbt M (suc r)) y zero) (sym (branch-yes {exp = x₂-min?} {proof = x₂-min})) $
                bound/ret {sbt M (suc r)} (skewB t₂ x₀ t₁)))
    (λ x₀-min → (subst (λ x → IsBounded (sbt M (suc r)) x zero) (sym (branch-no {exp = x₁-min?} {proof = x₁-not-min}))) $
                (subst (λ y → IsBounded (sbt M (suc r)) y zero) (sym (branch-no {exp = x₂-min?} {proof = x₀-min})) $
                bound/ret {sbt M (suc r)} (skewA x₀ t₁ t₂)))
  )
  where
  open Preorder M
  x₀ = root t₀
  x₁ = root t₁
  x₂ = root t₂
  x₁-min? = x₁ ≤? x₂ ×-dec x₁ ≤? x₀
  x₂-min? = x₂ ≤? x₁ ×-dec x₂ ≤? x₀

insertTree' : cmp (Π nat λ r → Π (sbt M r) λ _
                  → Π (maybe nat) λ mr → Π (sbh M true mr) λ _
                  → Π (meta⁺ (r ≤ⁿ mr)) λ _ 
                  → F ((Σ⁺ (maybe nat) λ mr' → Σ⁺ (sbh M true mr') λ _ → (meta⁺ (r ≤ⁿ mr')))))
insertTree' r t nothing ts n≤ⁿmr = ret (just r , unique (cons t empty nothing) , n≤ⁿn)
insertTree' {M} r t (just n) (unique sbml) (just r≤n) with r ≟ n
...                                      | no r≢n = 
  ret (just r , unique (cons t sbml (just (≤∧≢⇒< r≤n r≢n))) , n≤ⁿn)
...                                      | yes r≡n with sbml
...                                                   | cons {r'} {mr} t' ts n<ⁿmr = 
  bind (F _) (link n (subst (SBT M) r≡n t) t') λ sbt → 
  step (F _) 1 $
  bind (F _) (insertTree' (suc n) sbt mr (unique ts) (<ⁿ→s≤ⁿ n<ⁿmr)) λ (mr' , ts' , sn≤ⁿmr') → 
  ret (mr' , ts' , subst (λ a → a ≤ⁿ mr') (sym r≡n) (s≤ⁿ→≤ⁿ sn≤ⁿmr'))

-- The cost of insertTree' is bounded by the length of the target heap 
insertTree'/is-bounded : ∀ {M} r t mr sbh₁ r≤ⁿmr 
                      → IsBounded ((Σ⁺ (maybe nat) λ mr' → Σ⁺ (sbh M true mr') λ _ → (meta⁺ (r ≤ⁿ mr')))) (insertTree' {M} r t mr sbh₁ r≤ⁿmr) (len-sbh sbh₁)
insertTree'/is-bounded {M} r t nothing (unique empty) r≤ⁿmr = 
  bound/ret {Σ⁺ (maybe nat) λ mr' → Σ⁺ (sbh M true mr') λ _ → (meta⁺ (r ≤ⁿ mr'))} (just r , unique (cons t empty nothing) , n≤ⁿn)
insertTree'/is-bounded {M} r t (just n) (unique ts) (just r≤n) with r ≟ n
...   | no r≢n = 
  (bound/relax {A = Σ⁺ (maybe nat) λ mr' → Σ⁺ (sbh M true mr') λ _ → (meta⁺ (r ≤ⁿ mr'))} {c' = len-sbml ts} z≤n {ret (just r , unique (cons t ts (just (≤∧≢⇒< r≤n r≢n))) , n≤ⁿn)}) 
  (bound/ret {Σ⁺ (maybe nat) λ mr' → Σ⁺ (sbh M true mr') λ _ → (meta⁺ (r ≤ⁿ mr'))} (just r , unique (cons t ts (just (≤∧≢⇒< r≤n r≢n))) , n≤ⁿn))
...   | yes r≡n with ts
...     | cons {r'} {mr} t' tss n<ⁿmr = 
  (subst (λ x → IsBounded A (bind (F _)
    (link n (subst (SBT M) r≡n t) t') λ sbt → 
     step (F _) 1 $
     bind (F _) (insertTree' (suc n) sbt mr (unique tss) (<ⁿ→s≤ⁿ n<ⁿmr)) λ (mr' , ts' , sn≤ⁿmr') → 
     ret (mr' , ts' , subst (λ a → a ≤ⁿ mr') (sym r≡n) (s≤ⁿ→≤ⁿ sn≤ⁿmr'))) (1 + x)) 
     (+-identityʳ (len-sbml tss)) )
  (bound/bind/const
    {e = link {M} n (subst (SBT M) r≡n t) t'}
    {f = λ sbt → 
         step (F _) 1 $
         bind (F _) (insertTree' (suc n) sbt mr (unique tss) (<ⁿ→s≤ⁿ n<ⁿmr)) λ (mr' , ts' , sn≤ⁿmr') → 
         ret {A = A} (mr' , ts' , subst (λ a → a ≤ⁿ mr') (sym r≡n) (s≤ⁿ→≤ⁿ sn≤ⁿmr'))} zero ( 1 + (len-sbml tss + 0) ) (link/is-bounded {M} n (subst (SBT M) r≡n t) t') λ sbt → 
  bound/step 1 (bind (F A) (insertTree' (suc n) sbt mr (unique tss) (<ⁿ→s≤ⁿ n<ⁿmr)) λ (mr' , ts' , sn≤ⁿmr') → 
                ret (mr' , ts' , subst (λ a → a ≤ⁿ mr') (sym r≡n) (s≤ⁿ→≤ⁿ sn≤ⁿmr'))) 
  (bound/bind/const
    {e = insertTree' (suc n) sbt mr (unique tss) (<ⁿ→s≤ⁿ n<ⁿmr)}
    {f = λ (mr' , ts' , sn≤ⁿmr') → ret {A = A} (mr' , ts' , subst (λ a → a ≤ⁿ mr') (sym r≡n) (s≤ⁿ→≤ⁿ sn≤ⁿmr'))}
  (len-sbml tss) 0 (insertTree'/is-bounded (suc n) sbt mr (unique tss) (<ⁿ→s≤ⁿ n<ⁿmr)) (λ (mr' , ts' , sn≤ⁿmr') → 
  bound/ret {A = A} ( mr' , ts' , subst (λ a → a ≤ⁿ mr') (sym r≡n) (s≤ⁿ→≤ⁿ sn≤ⁿmr')  ))))
  where 
  A = Σ⁺ (maybe nat) λ mr' → Σ⁺ (sbh M true mr') λ _ → (meta⁺ (r ≤ⁿ mr'))

--we assume that r' ≤ r or r' is nothing and the skew binomial heap is uniqified
insertTree : cmp (Π nat λ r → Π (sbt M r) λ _
                  → Π (maybe nat) λ mr → Π (sbh M true mr) λ _
                  → Π (meta⁺ (r ≤ⁿ mr)) λ _ 
                  → F ((Σ⁺ (maybe nat) (λ mr' → sbh M true mr'))))
insertTree r t mr sbh r≤ⁿmr = 
  bind (F _) (insertTree' r t mr sbh r≤ⁿmr) λ (mr' , sbh' , _) → 
  ret (mr' , sbh')

insertTree/is-bounded : ∀ {M} r t mr sbh₁ r≤ⁿmr 
                      → IsBounded (Σ⁺ (maybe nat) (λ mr' → sbh M true mr')) (insertTree r t mr sbh₁ r≤ⁿmr ) (len-sbh sbh₁)
insertTree/is-bounded {M} r t mr sbh₁ r≤ⁿmr = 
  (subst 
    (λ x → (IsBounded A (insertTree r t mr sbh₁ r≤ⁿmr) x)) 
    (+-identityʳ (len-sbh sbh₁)) 
    (bound/bind/const 
      {e = insertTree' r t mr sbh₁ r≤ⁿmr} 
      {f = λ (mr' , sbh' , _) → ret {A = A} (mr' , sbh')} 
      (len-sbh sbh₁) 
      0 
      (insertTree'/is-bounded r t mr sbh₁ r≤ⁿmr) (λ (mr' , sbh' , _) → 
    bound/ret {A = A} ((mr' , sbh')))))
  where A = Σ⁺ (maybe nat) (λ mr' → sbh M true mr')


uniqify : cmp (Π bool λ b → Π (maybe nat) λ mr → Π (sbh M b mr) λ _
               → F (Σ⁺ (maybe nat) (λ mr' → sbh M true mr')))
uniqify .true nothing (unique ts) = ret (nothing , unique ts)
uniqify .true (just r) (unique ts) = ret (just r , unique ts)
uniqify .false (just r) (skew t ts) = insertTree r t (just r) (unique ts) n≤ⁿn 

{-# TERMINATING #-}
meldUniq' : cmp (Π (maybe nat) λ mr₁ → Π (sbh M true mr₁) λ _
              → Π (maybe nat) λ mr₂ → Π (sbh M true mr₂) λ _
              → F (Σ⁺ (maybe nat) λ mr → Σ⁺ (sbh M true mr) λ _ → (meta⁺ (mr₁ ≤ᵐ mr ⊎ mr₂ ≤ᵐ mr))))
meldUniq' nothing sbh₁ mr₂ sbh₂ = 
  ret (mr₂ , sbh₂ , inj₂ ≤ᵐ-refl)
meldUniq' (just r₁) sbh₁ nothing sbh₂ = 
  ret (just r₁ , sbh₁ , inj₁ ≤ᵐ-refl)
meldUniq' {M} (just r₁) sbh₁@(unique (cons {r₁} {mr₁} t₁ tss₁ r₁<ⁿmr₁))
         (just r₂) sbh₂@(unique (cons {r₂} {mr₂} t₂ tss₂ r₂<ⁿmr₂)) with <-cmp r₁ r₂
...    | tri< r₁<r₂ _ _ = 
  bind (F _) (meldUniq' mr₁ (unique tss₁) (just r₂) sbh₂) λ { 
    (mr' , ts' , inj₁ mr₁≤ᵐmr') → 
      ret (just r₁ , unique (cons t₁ (unique⁻¹ ts') (<ⁿ-≤ᵐ→<ⁿ r₁<ⁿmr₁ mr₁≤ᵐmr')) , inj₁ ≤ᵐ-refl)
  ; (mr' , ts' , inj₂ r₂≤ᵐmr')  → 
      ret (just r₁ , unique (cons t₁ (unique⁻¹ ts') (<-≤ᵐ→<ⁿ r₁<r₂ r₂≤ᵐmr')) , inj₁ ≤ᵐ-refl)}
...    | tri> _ _ r₁>r₂ = 
  bind (F _) (meldUniq' mr₂ (unique tss₂) (just r₁) sbh₁) λ { 
    (mr' , ts' , inj₂ r₁≤ᵐmr') → 
      ret (just r₂ , unique (cons t₂ (unique⁻¹ ts') (<-≤ᵐ→<ⁿ r₁>r₂ r₁≤ᵐmr')) , inj₂ ≤ᵐ-refl)
  ; (mr' , ts' , inj₁ mr₂≤ᵐmr')  → 
      ret (just r₂ , unique (cons t₂ (unique⁻¹ ts') (<ⁿ-≤ᵐ→<ⁿ r₂<ⁿmr₂ mr₂≤ᵐmr')) , inj₂ ≤ᵐ-refl)}
...    | tri≈ _ r₁≡r₂ _ = 
  bind (F _) (link r₂ (subst (SBT M) r₁≡r₂ t₁) t₂) λ t' → 
  bind (F _) (meldUniq' mr₁ (unique tss₁) mr₂ (unique tss₂)) λ {
    (mr' , tss' , inj₁ mr₁≤ᵐmr') → 
      bind (F _) (insertTree' (suc r₂) t' mr' tss' (subst (λ n → suc n ≤ⁿ mr') r₁≡r₂ (<ⁿ→s≤ⁿ (<ⁿ-≤ᵐ→<ⁿ r₁<ⁿmr₁ mr₁≤ᵐmr')))) λ (mr'' , ts' , sr₂≤ⁿmr'') → 
      ret (mr'' , ts' , inj₂ (just (s≤ⁿ→≤ⁿ sr₂≤ⁿmr'')))
  ; (mr' , tss' , inj₂ mr₂≤ᵐmr') → 
      bind (F _) (insertTree' (suc r₂) t' mr' tss' ((<ⁿ→s≤ⁿ (<ⁿ-≤ᵐ→<ⁿ r₂<ⁿmr₂ mr₂≤ᵐmr')))) λ (mr'' , ts' , sr₂≤ⁿmr'') → 
      ret (mr'' , ts' , inj₂ (just (s≤ⁿ→≤ⁿ sr₂≤ⁿmr''))) }

meldUniq : cmp (Π (maybe nat) λ mr₁ → Π (sbh M true mr₁) λ _
              → Π (maybe nat) λ mr₂ → Π (sbh M true mr₂) λ _
              → F (Σ⁺ (maybe nat) λ mr → sbh M true mr))
meldUniq mr₁ sbh₁ mr₂ sbh₂ = bind (F _) (meldUniq' mr₁ sbh₁ mr₂ sbh₂) λ (mr' , sbh' , x) → ret (mr' , sbh')

queue : Preorder → tp⁺
queue M = Σ⁺ bool λ b → Σ⁺ (maybe nat) λ mr → sbh M b mr

emp : val (queue M)
emp = (true , (nothing , unique empty))


insert : cmp (Π (getᴬ M) λ _ → Π (queue M) λ _ → F (queue M))
insert x (true , just zero , unique ts@(cons t tss z<ⁿmr)) = ret (false , just zero , skew (leaf x) ts)
insert x (true , just (suc r) , unique ts) = ret (true , just zero , unique (cons (leaf x) ts (just z<s)))
insert {M} x (false , just r , skew t₁ (cons {mr = mr} t₂ ts r<ⁿmr)) with (≡-dec _≟_) (just (suc r)) mr
...   | yes sr≡mr = 
        bind (F (queue M)) (skewLink (leaf x) r t₁ t₂) λ t' → 
        ret (false , just (suc r) , skew t' (subst (SBML M) (sym sr≡mr) ts))
...   | no sr≢mr = 
        bind (F (queue M)) (skewLink (leaf x) r t₁ t₂) λ t' → 
        ret (true , just (suc r) , unique (cons t' ts (<ⁿ∧s≢→s<ⁿ r<ⁿmr sr≢mr)))
insert x (true , nothing , unique empty) = ret (true , just zero , unique (cons (leaf x) empty nothing))

-- The insert operation of Skew Binomial Heap take constant time!!!!!
insert/is-bounded : ∀ {M} x b mr sbh₁
                 → IsBounded (queue M) (insert {M} x (b , mr , sbh₁)) zero
insert/is-bounded {M} x true (just zero) (unique ts@(cons t tss z<ⁿmr)) = 
  (bound/ret {A = queue M} (false , just zero , skew (leaf x) ts))
insert/is-bounded {M} x true (just (suc r)) (unique ts) = 
  (bound/ret {A = queue M} (true , just zero , unique (cons (leaf x) ts (just z<s))))
insert/is-bounded {M} x false (just r) (skew t₁ (cons {mr = mr} t₂ ts r<ⁿmr)) with (≡-dec _≟_) (just (suc r)) mr
...   | yes sr≡mr = 
        (bound/bind/const
          {A = sbt M (suc r)}
          {B = queue M}
          {e = skewLink (leaf x) r t₁ t₂}
          {f = λ t' → ret (false , just (suc r) , skew t' (subst (SBML M) (sym sr≡mr) ts))}
          zero 
          zero 
          (skewLink/is-bounded {M} (leaf x) r t₁ t₂) λ t' →
        bound/ret {A = queue M} (false , just (suc r) , skew t' (subst (SBML M) (sym sr≡mr) ts)))
...   | no sr≢mr = 
        bound/bind/const
          {A = sbt M (suc r)}
          {B = queue M}
          {e = skewLink (leaf x) r t₁ t₂}
          {f = λ t' → ret (true , just (suc r) , unique (cons t' ts (<ⁿ∧s≢→s<ⁿ r<ⁿmr sr≢mr)))}
          zero
          zero
          (skewLink/is-bounded {M} (leaf x) r t₁ t₂) (λ t' →
        bound/ret {A = queue M} (true , just (suc r) , unique (cons t' ts (<ⁿ∧s≢→s<ⁿ r<ⁿmr sr≢mr))))
insert/is-bounded {M} x true nothing (unique empty) = bound/ret {A = queue M} (true , just zero , unique (cons (leaf x) empty nothing))

postulate
  isEmpty : cmp (Π (queue M) λ _ → F bool)
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


