
open import Data.Nat

module SystemH.Type.Properties (Op At : ℕ → Set) where

open import Data.Fin

open import Axiom.Extensionality.Propositional 
open import Relation.Binary.PropositionalEquality
  hiding (Extensionality) -- using (_≡_; refl; _≗_; cong; cong₂)
open import Function

open import SystemH.Type.Base Op At

private
  variable
    m₁ m₂ : ℕ

import Data.Fin.Properties as Fₚ

postulate
  fun-ext : ∀ {a b} → Extensionality a b
  -- TODO: replace it
------------------------------------------------------------------------
-- injectivity of ↑, map-↑, ↑-ty
------------------------------------------------------------------------

-- module _ where
--   open import Data.Vec
--   import Data.Vec.Properties as Vₚ
--   open import Data.Fin
--   import Data.Fin.Properties as Fₚ

--   ↑-injective : {t u : Tm Ξ}
--     → ↑₁-tm t ≡ ↑₁-tm u
--     → t ≡ u
    
--   map-↑-injective : {xs ys : Tms Ξ n}
--     → ↑₁-tm ∘ xs ≗ ↑₁-tm ∘ ys
--     → xs ≗ ys

--   ↑-ty-injective : {σ τ : Ty Ξ}
--     → ↑₁-ty σ ≡ ↑₁-ty τ
--     → σ ≡ τ

--   map-↑-ty-injective : {τs σs : Tys Ξ n}
--     → ↑₁-ty ∘ τs ≗ ↑₁-ty ∘ σs
--     → τs ≗ σs

--   private
--     ⇒₀ : ∀ {τs : Tys Ξ n}{σs : Tys Ξ m} {τ σ} → σs ⇒ σ ≡ τs ⇒ τ → n ≡ m
--     ⇒₀ refl = refl
    
--     ⇒₁ : ∀ {σs τs : Tys Ξ n}{σ τ} → σs ⇒ σ ≡ τs ⇒ τ → σs ≡ τs
--     ⇒₁ refl = refl

--     ⇒₂ : ∀ {σs τs : Tys Ξ n}{σ τ} → σs ⇒ σ ≡ τs ⇒ τ → σ ≡ τ
--     ⇒₂ refl = refl

--     at₀ : {xs : Tms Ξ n} {ys : Tms Ξ m} {ψ : At n} {φ : At m}
--       → at ψ xs ≡ at φ ys → n ≡ m
--     at₀ refl = refl

--     at₁ : {xs ys : Tms Ξ n} {ψ φ : At n}
--       → at ψ xs ≡ at φ ys → ψ ≡ φ
--     at₁ refl = refl

--     at₂ : {xs ys : Tms Ξ n} {ψ φ : At n}
--       → at ψ xs ≡ at φ ys → xs ≡ ys
--     at₂ refl = refl

--     var₁ : ∀ {x y} → var {n} x ≡ var {n} y → x ≡ y
--     var₁ refl = refl

--     op₀ : {σ₁ : Op m₁} {σ₂ : Op m₂} {xs : Tms Ξ m₁} {ys : Tms Ξ m₂}
--       → op σ₁ xs ≡ op σ₂ ys → m₁ ≡ m₂
--     op₀ refl = refl

--     op₁ : {σ₁ σ₂ : Op n} {xs ys : Tms Ξ n}
--       → op σ₁ xs ≡ op σ₂ ys → σ₁ ≡ σ₂
--     op₁ refl = refl

--     op₂ : {σ₁ σ₂ : Op n} {xs ys : Tms Ξ n}
--       → op σ₁ xs ≡ op σ₂ ys → xs ≡ ys
--     op₂ refl = refl

--   ↑-injective {t = var x}    {var y}    eq = cong var (Fₚ.suc-injective (var₁ eq))
--     -- (Fₚ.inject₁-injective (var₁ eq))
--   ↑-injective {t = op σ₁ xs} {op σ₂ ys} eq with op₀ eq
--   ↑-injective {t = op σ₁ xs} {op σ₂ ys} eq | refl =
--     cong₂ op (op₁ eq) {!!}
-- --    cong₂ op (op₁ eq) (map-↑-injective (op₂ eq))
    
--   map-↑-injective eq i = ↑-injective (eq i)

--   ↑-ty-injective {σ = at ψ xs} {at φ ys} eq with at₀ eq
--   ... | refl = cong₂ at (at₁ eq) {!!}
--   ↑-ty-injective {σ = σs ⇒ σ₂} {τs ⇒ τ₂} eq with ⇒₀ eq
--   ... | refl = cong₂ _⇒_ {!!} (↑-ty-injective (⇒₂ eq))

--   map-↑-ty-injective eq = {!!}

--   ------------------------------------------------------------------------
--   -- subst-↑ 
--   ------------------------------------------------------------------------

--   subst-↑-tm : ∀ {d} (t : Tm Ξ) (u : Tm (suc Ξ) {d}) 
--     → [ ↑₁-tm t ]tm (↑₁-tm u) ≡ ↑₁-tm ([ t ]tm u)

--   subst-map-↑-tm : ∀ {d} (t : Tm Ξ ) (xs : Tms (suc Ξ) {d} n)
--     → ([ ↑₁-tm t ]tm_) ∘ (↑₁-tm ∘ xs) ≡ ↑₁-tm ∘ ([ t ]tm_ ∘ xs)

--   subst-↑-ty : ∀ {d} (t : Tm Ξ) (τ : Ty (suc Ξ) {d}) 
--     → ([ ↑₁-tm t ]ty (↑₁-ty τ)) ≡ ↑₁-ty ([ t ]ty τ)

--   subst-map-↑-ty : ∀ {d} (t : Tm Ξ) (τs : Tys (suc Ξ) {d} n)
--     → ([ ↑₁-tm t ]ty_) ∘ (↑₁-ty ∘ τs) ≡ ↑₁-ty ∘ ([ t ]ty_ ∘ τs)
--  {-   
--   subst-↑-tm t (var zero)    = refl
--   subst-↑-tm t (var (suc x)) = refl
--   subst-↑-tm t (op σ xs)     = cong (op σ) (subst-map-↑-tm t xs)

--   subst-map-↑-tm t xs = begin
--     map [ ↑₁-tm t ]tm_ (map ↑-tm xs)
--       ≡⟨ sym (Vₚ.map-∘ ([ ↑-tm t ]tm_) ↑-tm xs) ⟩
--     map ([ ↑-tm t ]tm_ ∘ ↑-tm) xs
--       ≡⟨ Vₚ.map-cong (subst-↑-tm t) xs ⟩
--     map (↑-tm ∘ [ t ]tm_) xs
--       ≡⟨ Vₚ.map-∘ ↑-tm [ t ]tm_ xs  ⟩
--     map ↑-tm (map [ t ]tm_ xs)
--       ∎ 
--     where open ≡-Reasoning

--   subst-↑-ty t (at φ xs) = cong (at φ) (subst-map-↑-tm t xs)
--   subst-↑-ty t (τs ⇒ τ) =
--     cong₂ _⇒_ (subst-map-↑-ty t τs) (subst-↑-ty t τ)

--   subst-map-↑-ty t τs = begin
--     map ([ ↑-tm t ]ty_) (map ↑-ty τs)
--       ≡⟨ sym (Vₚ.map-∘ _ _ _) ⟩
--     map ([ ↑-tm t ]ty_ ∘ ↑-ty) τs
--       ≡⟨ Vₚ.map-cong (subst-↑-ty t) τs ⟩
--     map (↑-ty ∘ [ t ]ty_) τs
--       ≡⟨ Vₚ.map-∘ _ _ τs ⟩ 
--     map ↑-ty (map ([ t ]ty_) τs)
--       ∎
--     where open ≡-Reasoning 
-- -}
