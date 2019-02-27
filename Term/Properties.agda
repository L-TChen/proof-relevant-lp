open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Term.Properties (Atom : Set)(_≟A_ : Decidable {A = Atom} _≡_ ) where

open import Relation.Nullary public
open import Data.Fin
open import Data.Fin.Properties hiding (_≟_)
open import Data.Nat
import Data.Nat.Properties as ℕₚ
open import Data.Empty
open import Data.List
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties

open import Term.Base Atom _≟A_
open import Term.Freshness Atom _≟A_
--open import Distinct
--open Permutation Atom _≟A_

subst-fvar-≡ : ∀ x {n xs} {u : RawTm n xs} → [ u / x ] (fvar x) ≡ u
subst-fvar-≡ x with x ≟A x
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

subst-fvar-≢ : ∀ {x y n xs} ⦃ _ : y ∈ xs ⦄ {u : RawTm n xs}
            → x ≢ y → [ u / x ] (fvar y) ≡ fvar y
subst-fvar-≢ {x} {y} x≢y with x ≟A y
... | yes p = ⊥-elim (x≢y p)
... | no ¬p = refl

close-fvar-≡ : ∀ x {n xs}
               → bvar fromℕ n ≡ abs {n} {xs} x (fvar x)
close-fvar-≡ x with x ≟A x
... | yes p = refl
... | no ¬p = ⊥-elim (¬p refl)

close-fvar-≢ : ∀ {x y xs} n ⦃ _ : y ∈ xs ⦄
               → x ≢ y
               → abs {n} {xs} x (fvar y) ≡ fvar y
close-fvar-≢ {x} {y} k x≢y with x ≟A y
... | yes p = ⊥-elim (x≢y p)
... | no ¬p = refl

-- Additional Properties regarding _⁺
{-
⁺-opening  : ∀ {n} (x : Atom) {xs} ⦃ _ : x ∈ xs ⦄ (t : RawTm n xs)
          → inst x (t ⁺) ≡ t
⁺-opening  {k} u (bvar i) with k ≟A toℕ (inject₁ i)
... | yes p rewrite toℕ-inject₁ i        =  ⊥-elim (ℕₚ.<-irrefl (sym p) (toℕ<n i))
... | no ¬p rewrite lower₁-inject₁′ i ¬p = refl
⁺-opening  u (fvar x) = refl
⁺-opening  u (t₁ · t₂)
  rewrite ⁺-opening  u t₁
        | ⁺-opening  u t₂ = refl
⁺-opening  u (ƛ t)
  rewrite ⁺-opening (u ⁺) t = refl
-}

⁺-closing : ∀ {x n xs}{t : RawTm n (x ∷ xs)} → x # t
          → {!!} ≡ abs {n} x t
⁺-closing x#t = {!!}

-- ⁺-distrib-subst : ∀ k x (u t : RawTm k)
--                 → ([ u / x ]ᵣ t) ⁺ ≡ [ u ⁺ / x ]ᵣ t ⁺
-- ⁺-distrib-subst k x u (bvar i) = refl
-- ⁺-distrib-subst k x u (fvar y) with x ≟S y
-- ... | yes p = refl
-- ... | no ¬p = refl
-- ⁺-distrib-subst k x u (t₁ · t₂)
--   rewrite ⁺-distrib-subst k x u t₁
--         | ⁺-distrib-subst k x u t₂ = refl
-- ⁺-distrib-subst k x u (ƛ t) rewrite ⁺-distrib-subst (suc k) x (u ⁺) t = refl

-- #-⁺ : ∀ {x k}{t : RawTm k} → x # t → x # t ⁺
-- #-⁺ bv         = bv
-- #-⁺ (fv x≢y) = fv x≢y
-- #-⁺ (app z z₁) = app (#-⁺ z) (#-⁺ z₁)
-- #-⁺ (lam z)    = lam (#-⁺ z)

-- close-fresh : ∀ {y k u} → y # u → ⟦ k ↤ y ⟧ u ≡ u ⁺
-- close-fresh bv = refl
-- close-fresh {y} {k} (fv x≢y) = close-fvar′ k x≢y
-- close-fresh (app y#u₁ y#u₂)
--   rewrite close-fresh y#u₁
--         | close-fresh y#u₂ = refl
-- close-fresh (lam y#u)
--   rewrite close-fresh y#u = refl

-- -- Sec 3.2 Opening is the inverse of the closing operation.
-- close-open-var : ∀ {x k t} → x # t → ⟦ k ↤ x ⟧ ⟦ k ↦ x ⟧₀ t ≡ t
-- close-open-var {x} {k} (bv {i}) with k ≟ℕ (toℕ i)
-- ... | no ¬p rewrite inject₁-lower₁ i ¬p = refl
-- ... | yes p rewrite sym (close-fvar x k)
--                   | cong bvar_ (toℕ-injective  (trans (toℕ-fromℕ k) p)) = refl
-- close-open-var (fv x≢y) = close-fvar′ _ x≢y
-- close-open-var (app x#t x#t₁)
--   rewrite close-open-var x#t
--         | close-open-var x#t₁ = refl
-- close-open-var (lam x#t)
--   rewrite close-open-var x#t = refl
  
-- close-open-var₀ : ∀ {x t} → x # t → abs x (inst x t) ≡ t
-- close-open-var₀ = close-open-var

-- -- Sec 3.2
-- open-close-var : ∀ k x t → ⟦ k ↦ x ⟧₀ ⟦ k ↤ x ⟧ t ≡ t
-- open-close-var k x (bvar i) with k ≟ℕ toℕ (inject₁ i)
-- ... | yes p rewrite toℕ-inject₁ i = ⊥-elim (ℕₚ.<-irrefl (sym p) (toℕ<n i))
-- ... | no ¬p rewrite lower₁-inject₁′ i ¬p = refl
-- open-close-var k x (fvar y) with x ≟S y
-- ... | no ¬p = refl
-- ... | yes p with k ≟ℕ (toℕ (fromℕ k))
-- open-close-var k x (fvar y) | yes p | yes q rewrite p = refl
-- open-close-var k x (fvar y) | yes p | no ¬q = ⊥-elim (¬q (sym (toℕ-fromℕ k)))
-- open-close-var k x (t · t₁) rewrite open-close-var k x t | open-close-var k x t₁ = refl
-- open-close-var k x (ƛ t)    rewrite open-close-var (suc k) x t = refl

-- open-close-var₀ : ∀ x (t : Tm) → inst x (abs x t) ≡ t
-- open-close-var₀ = open-close-var 0

-- -- Sec 3.5
-- open-var-fv : ∀ {k x y t} → x ≢ y → x # t → x # ⟦ k ↦ y ⟧₀ t
-- open-var-fv {k} x≢y (bv {i}) with k ≟ℕ (toℕ i)
-- ... | yes p = fv x≢y
-- ... | no ¬p = bv
-- open-var-fv x≢y (fv x≢t)      = fv x≢t
-- open-var-fv x≢y (app x#t₁ x#t₂) = app (open-var-fv x≢y x#t₁) (open-var-fv x≢y x#t₂)
-- open-var-fv x≢y (lam x#t)       = lam (open-var-fv x≢y x#t)

-- open-var-fv₀ : ∀ {x y t} → x ≢ y → x # t → x # inst y t
-- open-var-fv₀ = open-var-fv

-- --
-- close-var-fv : ∀ {x k} (t : RawTm k) → x # ⟦ k ↤ x ⟧ t
-- close-var-fv (bvar i) = bv
-- close-var-fv {x} (fvar y) with x ≟S y
-- ... | yes p = bv
-- ... | no ¬p = fv ¬p
-- close-var-fv (t₁ · t₂) = app (close-var-fv t₁) (close-var-fv t₂)
-- close-var-fv (ƛ t)     = lam (close-var-fv t)

-- -- Sec 3.5
-- subst-open-var : ∀ {k x y} (u : RawTm k) (t : RawTm (suc k)) → x ≢ y
--                → [ u / x ]ᵣ (⟦ k ↦ y ⟧₀ t) ≡ ⟦ k ↦ y ⟧₀ [ u ⁺ / x ]ᵣ t 
-- subst-open-var {k} {x} {y} _ (bvar i)  x≢y with k ≟ℕ (toℕ i)
-- ... | no ¬p = refl
-- ... | yes p = subst-fvar′ x≢y
-- subst-open-var {_} {x} {y} u (fvar z) x≢y with x ≟S z
-- ... | yes p rewrite ⁺-opening (fvar y) u = refl
-- ... | no ¬p = refl
-- subst-open-var u (t₁ · t₂) x≢y
--   rewrite subst-open-var u t₁ x≢y
--         | subst-open-var u t₂ x≢y = refl
-- subst-open-var u (ƛ t) x≢y
--   rewrite subst-open-var (u ⁺) t x≢y = refl

-- subst-open-var₀ : ∀ {x y} u t → x ≢ y
--                 → [ u / x ] (inst y t) ≡ inst y ([ u ⁺ / x ]ᵣ t)
-- subst-open-var₀ = subst-open-var

-- -- Sec 3.5
-- subst-close-var : ∀ {k x y u} (t : RawTm k) → x ≢ y → y # u 
--                   → [ u ⁺ / x ]ᵣ ⟦ k ↤ y ⟧ t  ≡ ⟦ k ↤ y ⟧ [ u / x ]ᵣ t
-- subst-close-var (bvar i) x≢y y#u = refl
-- subst-close-var {k} {x} {y} {u} (fvar z) x≢y y#u with x ≟S z
-- ... | yes refl
--   rewrite close-fresh y#u
--         | close-fvar′ k (λ y≢z → x≢y (sym y≢z)) = subst-fvar z
-- ... | no  x≢z with y ≟S z
-- ... | yes y≡z = refl
-- ... | no y≢z  = subst-fvar′ x≢z
-- subst-close-var (t₁ · t₂) x≢y y#u
--   rewrite subst-close-var t₁ x≢y y#u
--         | subst-close-var t₂ x≢y y#u = refl
-- subst-close-var (ƛ t) x≢y y#u
--   rewrite subst-close-var t x≢y (#-⁺ y#u) = refl

-- -- Sec 3.5
-- subst-fresh : ∀ {x k t} (u : RawTm k) → x # t → [ u / x ]ᵣ t ≡ t
-- subst-fresh _ bv = refl
-- subst-fresh {x} _ (fv x≢y) = subst-fvar′ x≢y
-- subst-fresh u (app x#t x#t₁)
--   rewrite subst-fresh u x#t
--         | subst-fresh u x#t₁ = refl
-- subst-fresh u (lam x#t)
--   rewrite subst-fresh (u ⁺) x#t = refl
  
-- -- Sec 3.7

-- subst-open : ∀ k x u v t
--            → [ u / x ]ᵣ ⟦ k ↦ v ⟧ t ≡ ⟦ k ↦ [ u / x ]ᵣ v ⟧ [ u ⁺ / x ]ᵣ t
-- subst-open k x u v (bvar i) with k ≟ℕ toℕ i
-- ... | yes p = refl
-- ... | no ¬p = refl
-- subst-open k x u v (fvar y) with x ≟S y
-- ... | yes p = sym (⁺-opening ([ u / x ]ᵣ v) u) 
-- ... | no ¬p = refl
-- subst-open k x u v (t₁ · t₂)
--   rewrite subst-open k x u v t₁
--         | subst-open k x u v t₂ = refl
-- subst-open k x u v (ƛ t)
--   rewrite subst-open (suc k) x (u ⁺) (v ⁺) t
--         | ⁺-distrib-subst k x u v = refl

-- -- Sec 3.7
-- subst-intro : ∀ {x} u t → x # t → [ u / x ] (inst x t) ≡ ⟦ 0 ↦ u ⟧ t
-- subst-intro {x} u t x#t = begin
--   [ u / x ] (inst x t)                        ≡⟨ subst-open 0 x u (fvar x) t ⟩
--   ⟦ 0 ↦ [ u / x ] (fvar x) ⟧ ([ u ⁺ / x ]ᵣ t) ≡⟨ cong (⟦ 0 ↦ ([ u / x ] (fvar x)) ⟧_)(subst-fresh (u ⁺) x#t) ⟩
--   ⟦ 0 ↦ [ u / x ] (fvar x) ⟧ t               ≡⟨ cong (λ u → ⟦ 0 ↦ u ⟧ t) (subst-fvar x) ⟩ 
--   ⟦ 0 ↦ u ⟧ t                                  ∎
--   where
--     open ≡-Reasoning

-- -- Sec 3.7
-- close-var-rename : ∀ x {y k t}
--                  → y # t → ⟦ k ↤ x ⟧ t ≡ ⟦ k ↤ y ⟧ [ fvar y / x ]ᵣ t
-- close-var-rename x bv = refl
-- close-var-rename x {y} {k} (fv {z} y≢z) with x ≟S z
-- ... | yes refl rewrite close-fvar y k               = refl
-- ... | no ¬p    rewrite close-fresh {y} {k} (fv y≢z) = refl
-- close-var-rename x (app y#t y#t₁)
--   rewrite close-var-rename x y#t
--         | close-var-rename x y#t₁ = refl
-- close-var-rename x (lam y#t)
--   rewrite close-var-rename x y#t = refl

-- -- Sec 3.7
-- subst-as-close-open : ∀ {x} t u → [ u / x ] t ≡ ⟦ 0 ↦ u ⟧ (abs x t)
-- subst-as-close-open {x} t u = begin
--   [ u / x ] t                   ≡⟨ cong ([ u / x ]_) (sym (open-close-var₀ x t)) ⟩
--   [ u / x ] (inst x (abs x t))  ≡⟨ subst-intro u (abs x t) (close-var-fv t) ⟩
--   ⟦ 0 ↦ u ⟧ (abs x t)           ∎
--   where open ≡-Reasoning
