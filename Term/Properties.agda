{-# OPTIONS --with-K #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Term.Properties (Atom : Set)(_≟A_ : Decidable {A = Atom} _≡_ ) where

open import Relation.Nullary public
open import Data.Fin
open import Data.Fin.Properties hiding (_≟_)
open import Data.Nat renaming (_≟_ to _≟ℕ_)
import Data.Nat.Properties as ℕₚ
open import Data.Empty
open import Data.List
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties

open import Term.Base Atom _≟A_
open import Term.Freshness Atom _≟A_

subst-fvar-≡ : ∀ x {n xs} {u : RawTm n xs} → [ u / x ] (fvar x) ≡ u
subst-fvar-≡ x with x ≟A x
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

subst-fvar-≢ : ∀ {x y n xs} ⦃ _ : y ∈ xs ⦄ {u : RawTm n xs}
            → x ≢ y → [ u / x ] (fvar y) ≡ fvar y
subst-fvar-≢ {x} {y} x≢y with x ≟A y
... | yes p = ⊥-elim (x≢y p)
... | no ¬p = refl

close-fvar-≡ : ∀ x {xs n}
               → bvar fromℕ n ≡ abs {xs} x (fvar x)
close-fvar-≡ x with x ≟A x
... | yes p = refl
... | no ¬p = ⊥-elim (¬p refl)

close-fvar-≢ : ∀ {x y n xs} ⦃ _ : y ∈ xs ⦄
               → x ≢ y
               → abs {xs} {n} x (fvar y) ≡ fvar y
close-fvar-≢ {x} {y} x≢y with x ≟A y
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

⁺-closing : ∀ {x n xs}{t : RawTm n xs} → x ∉ xs
          → (t ⁺) ≡ abs x (t ⁺Cxt)
⁺-closing x∉xs = {!!}

⁺-dist-subst : ∀ {n} x {xs} (u : RawTm n xs) (t : RawTm n (x ∷ xs))
             → ([ u / x ] t) ⁺ ≡ [ (u ⁺) / x ] (t ⁺)
⁺-dist-subst x u (bvar i)  = refl
⁺-dist-subst x u (fvar y)  with x ≟A y
... | yes p = refl
... | no ¬p = refl
⁺-dist-subst x u (t₁ · t₂) = cong₂ _·_ (⁺-dist-subst x u t₁) (⁺-dist-subst x u t₂)
⁺-dist-subst x u (ƛ t)     = cong ƛ_ (⁺-dist-subst x (u ⁺) t)

#-⁺ : ∀ {x n xs}{t : RawTm n xs} → x ∉ xs → x # t ⁺
#-⁺ {t = t} x∉xs = x∉xs⇒x#t (t ⁺) λ x∈xs → x∉xs x∈xs

close-fresh : ∀ {x n xs}(t : RawTm n xs)
            → x ∉ xs
            → (abs x (t ⁺Cxt)) ≡ (t ⁺) 
close-fresh (bvar i) _ = refl
close-fresh {x} (fvar_ y ⦃ y∈xs ⦄) x∉xs with x ≟A y
... | yes refl = ⊥-elim (x∉xs y∈xs)
... | no ¬p    = refl
close-fresh (t₁ · t₂) x∉xs = cong₂ _·_ (close-fresh t₁ x∉xs) (close-fresh t₂ x∉xs)
close-fresh (ƛ t)     x∉xs = cong ƛ_ (close-fresh t x∉xs)

-- Sec 3.2 Opening is the inverse of the closing operation.
close-open-var : ∀ {n x xs}(t : RawTm (suc n) xs)
               → x ∉ xs → abs x (inst x t) ≡ t
close-open-var {n} (bvar i) x∉xs with n ≟ℕ (toℕ i)
close-open-var {n} (bvar i) x∉xs | no ¬p = cong bvar_ (inject₁-lower₁ i ¬p)
close-open-var {n} {x} (bvar i) x∉xs | yes p = begin
  abs x (fvar x) ≡⟨ sym (close-fvar-≡ x) ⟩
  bvar (fromℕ n) ≡⟨ cong bvar_ (toℕ-injective (trans (toℕ-fromℕ n) p)) ⟩ 
  bvar i ∎
  where open ≡-Reasoning
close-open-var (fvar_ y ⦃ y∈xs ⦄) x∉xs = close-fvar-≢ λ { refl → x∉xs y∈xs }
close-open-var (t₁ · t₂) x∉xs =
  cong₂ _·_ (close-open-var t₁ x∉xs) (close-open-var t₂ x∉xs)
close-open-var (ƛ t) x∉xs = cong ƛ_ (close-open-var t x∉xs)

-- Sec 3.2
open-close-var : ∀ {n x xs} (t : RawTm n (x ∷ xs)) → inst x (abs x t) ≡ t
open-close-var {n} (bvar i) with n ≟ℕ toℕ (inject₁ i)
... | yes p rewrite toℕ-inject₁ i = ⊥-elim (ℕₚ.<-irrefl (sym p) (toℕ<n i))
... | no ¬p = cong bvar_ (lower₁-inject₁′ i ¬p)
open-close-var {n} {x} (fvar y) with x ≟A y
... | no ¬p = {!!} -- it requires truncated type
... | yes p with n ≟ℕ (toℕ (fromℕ n))
... | yes q = {!!}
... | no ¬q = ⊥-elim (¬q (sym (toℕ-fromℕ n)))
open-close-var (t · t₁) = cong₂ _·_ (open-close-var t) (open-close-var t₁)
open-close-var (ƛ t)    = cong ƛ_ (open-close-var t)

-- Sec 3.5
open-var-fv : ∀ {n x xs y}{t : RawTm (suc n) xs}
            → x ≢ y → x ∉ xs → x # inst y t
open-var-fv {y = y} {t} x≢y x∉xs =
  x∉xs⇒x#t (inst y t) λ { (here px) → x≢y px ; (there p) → x∉xs p}

close-var-fv : ∀ {x n xs} (t : RawTm n (x ∷ xs)) → x # abs x t
close-var-fv (bvar i) = bvar inject₁ i
close-var-fv {x} {n} (fvar y) with x ≟A y
... | yes p = bvar fromℕ n
... | no ¬p = fvar ¬p
close-var-fv (t₁ · t₂) = (close-var-fv t₁) · (close-var-fv t₂)
close-var-fv (ƛ t)     = ƛ (close-var-fv t)

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
