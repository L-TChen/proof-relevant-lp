open import Data.Nat

module SystemH.Type.Properties (Op At : ℕ → Set) where

open import Relation.Binary.PropositionalEquality
open import Function

open import SystemH.Type.Base Op At

private
  variable
    n m m₁ m₂ : ℕ

------------------------------------------------------------------------
-- injectivity of inject₁, map-inject₁, inject₁-ty
------------------------------------------------------------------------

module _ where
  open import Data.Vec
  import Data.Vec.Properties as Vₚ
  open import Data.Fin
  import Data.Fin.Properties as Fₚ

  inject₁-injective : {t u : Tm Ξ}
    → inject₁-tm t ≡ inject₁-tm u
    → t ≡ u

  map-inject₁-injective : {xs ys : Tms Ξ n}
    → map inject₁-tm xs ≡ map inject₁-tm ys
    → xs ≡ ys

  inject₁-ty-injective : {σ τ : Ty Ξ}
    → inject₁-ty σ ≡ inject₁-ty τ
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

  inject₁-injective {t = var x}      {var y}      eq = cong var (Fₚ.inject₁-injective (var₁ eq))
  inject₁-injective {t = op σ₁ xs} {op σ₂ ys} eq with op₀ eq
  inject₁-injective {t = op σ₁ xs} {op σ₂ ys} eq | refl =
    cong₂ op (op₁ eq) (map-inject₁-injective (op₂ eq))

  map-inject₁-injective {xs = []}     {[]}     refl = refl
  map-inject₁-injective {xs = x ∷ xs'} {y ∷ ys} eq   =
    cong₂ _∷_ (inject₁-injective (Vₚ.∷-injectiveˡ eq)) (map-inject₁-injective (Vₚ.∷-injectiveʳ eq))

  inject₁-ty-injective {σ = at ψ xs} {at φ ys} eq with at₀ eq
  ... | refl = cong₂ at (at₁ eq) (map-inject₁-injective (at₂ eq))
  inject₁-ty-injective {σ = σ₁ ⇒ σ₂} {τ₁ ⇒ τ₂} eq =
    cong₂ _⇒_ (inject₁-ty-injective (⇒₁ eq)) (inject₁-ty-injective (⇒₂ eq))
  inject₁-ty-injective {σ = ∀₁ σ'}    {∀₁ τ}    eq =
    cong ∀₁ (inject₁-ty-injective (∀₁₁ eq))

  ------------------------------------------------------------------------
  -- subst-inject₁ 
  ------------------------------------------------------------------------

  subst-inject₁-tm : (t : Tm Ξ) (u : Tm (suc Ξ)) 
    → [0↦ inject₁-tm t ]tm (inject₁-tm u) ≡ inject₁-tm ([0↦ t ]tm u)

  {-# TERMINATING #-}
  subst-map-inject₁-tm : (t : Tm Ξ) (xs : Tms (suc Ξ) n)
    → map ([0↦ inject₁-tm t ]tm_) (map inject₁-tm xs) ≡ map inject₁-tm (map ([0↦ t ]tm_) xs)

  subst-inject₁-tm t (var zero)    = refl
  subst-inject₁-tm t (var (suc x)) = refl
  subst-inject₁-tm t (op σ xs)     = cong (op σ) (subst-map-inject₁-tm t xs)

  subst-map-inject₁-tm t xs = begin
    map [0↦ inject₁-tm t ]tm_ (map inject₁-tm xs)
      ≡⟨ sym (Vₚ.map-∘ ([0↦ inject₁-tm t ]tm_) inject₁-tm xs) ⟩
    map ([0↦ inject₁-tm t ]tm_ ∘ inject₁-tm) xs
      ≡⟨ Vₚ.map-cong (subst-inject₁-tm t) xs ⟩
    map (inject₁-tm ∘ [0↦ t ]tm_) xs
      ≡⟨ Vₚ.map-∘ inject₁-tm [0↦ t ]tm_ xs  ⟩
    map inject₁-tm (map [0↦ t ]tm_ xs)
      ∎ 
    where open ≡-Reasoning

  subst-inject₁-ty : (t : Tm Ξ) (τ : Ty (suc Ξ)) 
    → ([0↦ inject₁-tm t ]ty (inject₁-ty τ)) ≡ inject₁-ty ([0↦ t ]ty τ)
  subst-inject₁-ty t (at φ xs) = cong (at φ) (subst-map-inject₁-tm t xs)
  subst-inject₁-ty t (τ₁ ⇒ τ₂) = cong₂ _⇒_ (subst-inject₁-ty t τ₁) (subst-inject₁-ty t τ₂)
  subst-inject₁-ty t (∀₁ τ)    = cong ∀₁ (subst-inject₁-ty (inject₁-tm t) τ)

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

  inject₁-∈-↑ : {τ : Ty Ξ} → τ ∈ Γ → inject₁-ty τ ∈ ↑ Γ
  inject₁-∈-↑ = ∈-map⁺ inject₁-ty

  lower₁-∈-↑ : {τ : Ty Ξ} → inject₁-ty τ ∈ (↑ Γ) → τ ∈ Γ
  lower₁-∈-↑ {Γ = _ ∷ Γ} (here px)  = here (inject₁-ty-injective px)
  lower₁-∈-↑ {Γ = _ ∷ Γ} (there px) = there (lower₁-∈-↑ px)

  ext : (∀ {τ} → τ ∈ Γ → τ ∈ Δ)
    → (∀ {τ σ} → τ ∈ (σ ∷ Γ) → τ ∈ σ ∷ Δ)
  ext ρ (here px) = here  px
  ext ρ (there p) = there (ρ p)

  ext-↑ : (∀ {τ : Ty Ξ} → τ ∈ Γ → τ ∈ Δ)
    → {τ : Ty (suc Ξ)} → τ ∈ ↑ Γ → τ ∈ ↑ Δ
  ext-↑ {Ξ = Ξ} {Γ} {Δ} ρ {τ} px =
    subst (λ τ → τ ∈ (↑ Δ)) (sym τ=σ) (inject₁-∈-↑ (ρ σ∈Γ))
    where
      pf = ∈-map⁻ inject₁-ty px    
      σ  = proj₁ pf
      σ∈Γ = proj₁ (proj₂ pf)
      τ=σ = proj₂ (proj₂ pf) 
