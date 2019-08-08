open import Data.Nat

module SystemH.Type.Properties (Op At : ℕ → Set) where

open import Relation.Binary.PropositionalEquality
open import Function

open import SystemH.Type.Base Op At

private
  variable
    n m m₁ m₂ : ℕ

------------------------------------------------------------------------
-- injectivity of ↑, map-↑, ↑-ty
------------------------------------------------------------------------

module _ where
  open import Data.Vec
  import Data.Vec.Properties as Vₚ
  open import Data.Fin
  import Data.Fin.Properties as Fₚ

  ↑-injective : {t u : Tm Ξ}
    → ↑-tm t ≡ ↑-tm u
    → t ≡ u

  map-↑-injective : {xs ys : Tms Ξ n}
    → map ↑-tm xs ≡ map ↑-tm ys
    → xs ≡ ys

  ↑-ty-injective : {σ τ : Ty Ξ}
    → ↑-ty σ ≡ ↑-ty τ
    → σ ≡ τ

  private
    ∀₁₁ : {σ τ : Ty (suc Ξ)} → ∀₁ σ ≡ ∀₁ τ → σ ≡ τ
    ∀₁₁ refl = refl

    ⇒₁ : ∀ {σ₁ σ₂ : Ty Ξ} {τ₁ τ₂} → σ₁ ⇒ σ₂ ≡ τ₁ ⇒ τ₂ → σ₁ ≡ τ₁
    ⇒₁ refl = refl

    ⇒₂ : ∀ {σ₁ σ₂ : Ty Ξ} {τ₁ τ₂} → σ₁ ⇒ σ₂ ≡ τ₁ ⇒ τ₂ → σ₂ ≡ τ₂
    ⇒₂ refl = refl

    at₀ : {xs : Tms Ξ n} {ys : Tms Ξ m} {ψ : At n} {φ : At m}
      → at ψ xs ≡ at φ ys → n ≡ m
    at₀ refl = refl

    at₁ : {xs ys : Tms Ξ n} {ψ φ : At n}
      → at ψ xs ≡ at φ ys → ψ ≡ φ
    at₁ refl = refl

    at₂ : {xs ys : Tms Ξ n} {ψ φ : At n}
      → at ψ xs ≡ at φ ys → xs ≡ ys
    at₂ refl = refl

    var₁ : ∀ {x y} → var {n} x ≡ var {n} y → x ≡ y
    var₁ refl = refl

    op₀ : {σ₁ : Op m₁} {σ₂ : Op m₂} {xs : Tms Ξ m₁} {ys : Tms Ξ m₂}
      → op σ₁ xs ≡ op σ₂ ys → m₁ ≡ m₂
    op₀ refl = refl

    op₁ : {σ₁ σ₂ : Op n} {xs ys : Tms Ξ n}
      → op σ₁ xs ≡ op σ₂ ys → σ₁ ≡ σ₂
    op₁ refl = refl

    op₂ : {σ₁ σ₂ : Op n} {xs ys : Tms Ξ n}
      → op σ₁ xs ≡ op σ₂ ys → xs ≡ ys
    op₂ refl = refl

  ↑-injective {t = var x}    {var y}    eq = cong var (Fₚ.inject₁-injective (var₁ eq))
  ↑-injective {t = op σ₁ xs} {op σ₂ ys} eq with op₀ eq
  ↑-injective {t = op σ₁ xs} {op σ₂ ys} eq | refl =
    cong₂ op (op₁ eq) (map-↑-injective (op₂ eq))

  map-↑-injective {xs = []}      {[]}     refl = refl
  map-↑-injective {xs = x ∷ xs'} {y ∷ ys} eq   =
    cong₂ _∷_ (↑-injective (Vₚ.∷-injectiveˡ eq)) (map-↑-injective (Vₚ.∷-injectiveʳ eq))

  ↑-ty-injective {σ = at ψ xs} {at φ ys} eq with at₀ eq
  ... | refl = cong₂ at (at₁ eq) (map-↑-injective (at₂ eq))
  ↑-ty-injective {σ = σ₁ ⇒ σ₂} {τ₁ ⇒ τ₂} eq =
    cong₂ _⇒_ (↑-ty-injective (⇒₁ eq)) (↑-ty-injective (⇒₂ eq))
  ↑-ty-injective {σ = ∀₁ σ'}    {∀₁ τ}   eq =
    cong ∀₁ (↑-ty-injective (∀₁₁ eq))

  ------------------------------------------------------------------------
  -- subst-↑ 
  ------------------------------------------------------------------------

  subst-↑-tm : (t : Tm Ξ) (u : Tm (suc Ξ)) 
    → [ ↑-tm t ]tm (↑-tm u) ≡ ↑-tm ([ t ]tm u)

  {-# TERMINATING #-}
  subst-map-↑-tm : (t : Tm Ξ) (xs : Tms (suc Ξ) n)
    → map ([ ↑-tm t ]tm_) (map ↑-tm xs) ≡ map ↑-tm (map ([ t ]tm_) xs)

  subst-↑-tm t (var zero)    = refl
  subst-↑-tm t (var (suc x)) = refl
  subst-↑-tm t (op σ xs)     = cong (op σ) (subst-map-↑-tm t xs)

  subst-map-↑-tm t xs = begin
    map [ ↑-tm t ]tm_ (map ↑-tm xs)
      ≡⟨ sym (Vₚ.map-∘ ([ ↑-tm t ]tm_) ↑-tm xs) ⟩
    map ([ ↑-tm t ]tm_ ∘ ↑-tm) xs
      ≡⟨ Vₚ.map-cong (subst-↑-tm t) xs ⟩
    map (↑-tm ∘ [ t ]tm_) xs
      ≡⟨ Vₚ.map-∘ ↑-tm [ t ]tm_ xs  ⟩
    map ↑-tm (map [ t ]tm_ xs)                     ∎ 
    where open ≡-Reasoning

  subst-↑-ty : (t : Tm Ξ) (τ : Ty (suc Ξ)) 
    → ([ ↑-tm t ]ty (↑-ty τ)) ≡ ↑-ty ([ t ]ty τ)
  subst-↑-ty t (at φ xs) = cong (at φ) (subst-map-↑-tm t xs)
  subst-↑-ty t (τ₁ ⇒ τ₂) = cong₂ _⇒_ (subst-↑-ty t τ₁) (subst-↑-ty t τ₂)
  subst-↑-ty t (∀₁ τ)    = cong ∀₁ (subst-↑-ty (↑-tm t) τ)

------------------------------------------------------------------------
-- Context properties 
------------------------------------------------------------------------

module _ where
  open import Data.List
  open import Data.List.Membership.Propositional
  open import Data.List.Membership.Propositional.Properties
  open import Data.List.Relation.Unary.Any
    using (here; there)
  open import Data.Product
    using (proj₁; proj₂)

  open import SystemH.Type.Context Op At

  ↑-∈-↑ : {τ : Ty Ξ} → τ ∈ Γ → ↑-ty τ ∈ ↑ Γ
  ↑-∈-↑ = ∈-map⁺ ↑-ty

  lower₁-∈-↑ : {τ : Ty Ξ} → ↑-ty τ ∈ (↑ Γ) → τ ∈ Γ
  lower₁-∈-↑ {Γ = _ ∷ Γ} (here px)  = here (↑-ty-injective px)
  lower₁-∈-↑ {Γ = _ ∷ Γ} (there px) = there (lower₁-∈-↑ px)

  ext : (∀ {τ} → τ ∈ Γ → τ ∈ Δ)
    → (∀ {τ σ} → τ ∈ (σ ∷ Γ) → τ ∈ σ ∷ Δ)
  ext ρ (here px) = here  px
  ext ρ (there p) = there (ρ p)

  ext-↑ : (∀ {τ : Ty Ξ} → τ ∈ Γ → τ ∈ Δ)
    → {τ : Ty (suc Ξ)} → τ ∈ ↑ Γ → τ ∈ ↑ Δ
  ext-↑ {Ξ = Ξ} {Γ} {Δ} ρ {τ} px =
    subst (λ τ → τ ∈ (↑ Δ)) (sym τ=σ) (↑-∈-↑ (ρ σ∈Γ))
    where
      pf = ∈-map⁻ ↑-ty px    
      σ∈Γ = proj₁ (proj₂ pf)
      τ=σ = proj₂ (proj₂ pf) 
