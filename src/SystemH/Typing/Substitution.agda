open import Data.Nat

module SystemH.Typing.Substitution (Op At : ℕ → Set) where

open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
  using (here; there)
open import Relation.Binary.PropositionalEquality
  renaming (subst to ≡-subst)
  
open import SystemH.Type        Op At
open import SystemH.Typing.Base Op At

rename : {Γ Δ : Cxt Ξ}
  → (∀ {τ} → τ ∈ Γ → τ ∈ Δ)
    ------------------------------------------------  
  → ∀ {τ : Ty Ξ} → [ Ξ , Ψ ] Γ ⊢ τ → [ Ξ , Ψ ] Δ ⊢ τ
rename ρ (ax ψ)   = ax ψ
rename ρ (var x)  = var (ρ x)
rename ρ (ƛ M)    = ƛ rename (ext ρ) M
rename ρ (M · N)  = rename ρ M · rename ρ N
rename ρ (M ∙ t)  = rename ρ M ∙ t
rename ρ (∀₀ M)   = ∀₀ (rename (ext-↑ ρ) M)

↑-⊢ : {Γ Ψ : Cxt Ξ} 
  → [ Ξ , Ψ ] Γ ⊢ τ
    ----------------------------------
  → [ suc Ξ , ↑ Ψ ] ↑ Γ ⊢ ↑-ty τ
↑-⊢ (ax ψ)   = ax  (↑-∈-↑ ψ)
↑-⊢ (var x)  = var (↑-∈-↑ x)
↑-⊢ (ƛ M)    = ƛ ↑-⊢ M
↑-⊢ (M · M₁) = ↑-⊢ M · ↑-⊢ M₁
↑-⊢ (∀₀ M)   = ∀₀ (↑-⊢ M)
↑-⊢ (M ∙ t)  = ≡-subst (λ τ → [ _ , _ ] _ ⊢ τ)
  (subst-↑-ty t _) (↑-⊢ M ∙ ↑-tm t)

exts : (∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] Δ ⊢ τ)
    -----------------------------------------
  → ∀ {τ σ} → τ ∈ σ ∷ Γ → [ Ξ , Ψ ] σ ∷ Δ ⊢ τ 
exts ρ (here refl) = var (here refl)
exts ρ (there px)  = rename there (ρ px)

exts-↑ : (∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] Δ ⊢ τ)
    -----------------------------------------
  → ∀ {τ} → τ ∈ ↑ Γ → [ suc Ξ , ↑ Ψ ] ↑ Δ ⊢ τ
exts-↑ ρ τ∈Γ = ≡-subst ([ _ , _ ] _ ⊢_) (sym τ=τ′) (↑-⊢ (ρ τ′∈Γ))
  where
    pf   = ∈-map⁻ ↑-ty τ∈Γ    
    τ′∈Γ = proj₁ (proj₂ pf)
    τ=τ′ = proj₂ (proj₂ pf) 

subst : {Γ Δ : Cxt Ξ}
      → (∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] Δ ⊢ τ)
        -------------------------------------------
      → (∀ {τ} → [ Ξ , Ψ ] Γ ⊢ τ → [ Ξ , Ψ ] Δ ⊢ τ)
subst ρ (ax x)   = ax x
subst ρ (var x)  = ρ x
subst ρ (ƛ M)    = ƛ subst (exts ρ) M
subst ρ (M · N)  = subst ρ M · subst ρ N
subst ρ (∀₀ M)   = ∀₀ (subst (exts-↑ ρ) M)
subst ρ (M ∙ t)  = subst ρ M ∙ t

exts-comp : {E : Cxt Ξ}
  → (∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] Δ ⊢ τ)
  → (∀ {σ} → σ ∈ Δ → [ Ξ , Ψ ] E ⊢ σ)
  → ∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] E ⊢ τ
exts-comp ρ₁ ρ₂ x = subst ρ₂ (ρ₁ x)

_[_] : {τ₁ τ₂ : Ty Ξ}
     → [ Ξ , Ψ ] (τ₁ ∷ Γ) ⊢ τ₂
     → [ Ξ , Ψ ] Γ ⊢ τ₁
       --------------------
     → [ Ξ , Ψ ] Γ ⊢ τ₂
_[_] {Γ = Γ} N M = subst ρ N
  where 
    ρ : τ ∈ _ ∷ Γ → [ _ , _ ] _ ⊢ τ
    ρ (here refl) = M
    ρ (there p)   = var p
