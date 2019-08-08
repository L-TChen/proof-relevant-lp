open import Data.Nat

module SystemH.Typing.Base (Op At : ℕ → Set) where

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
  using (here; there)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import SystemH.Type Op At

-- Proof Evidence (Expression)
-- `Ψ` is the context for axioms
-- `Γ` is the context for variables

data [_,_]_⊢_ (Ξ : VCxt) (Ψ Γ : Cxt Ξ) : (τ : Ty Ξ) → Set where
  ax  : τ ∈ Ψ
        --------------- Axiom
      → [ Ξ , Ψ ] Γ ⊢ τ

  var : τ ∈ Γ
      ----------------- Var
      → [ Ξ , Ψ ] Γ ⊢ τ

  ƛ_  : ∀ {σ}
      → [ Ξ , Ψ ] τ ∷ Γ ⊢ σ
        --------------------------- Abs
      → [ Ξ , Ψ ] Γ ⊢ τ ⇒ σ

  _·_ : ∀ {σ}
      → [ Ξ , Ψ ] Γ ⊢ τ ⇒ σ
      → [ Ξ , Ψ ] Γ ⊢ τ
        ------------------- App
      → [ Ξ , Ψ ] Γ ⊢ σ

  ∀₀  : [ suc Ξ , ↑ Ψ ] ↑ Γ ⊢ τ
        ----------------------- Gen
      → [ Ξ , Ψ ] Γ ⊢ ∀₁ τ

  _∙_ : [ Ξ , Ψ ] Γ ⊢ ∀₁ τ
      → (t : Tm Ξ)
        ----------------------------------- Inst
      → [ Ξ , Ψ ] Γ ⊢ [0↦ t ]ty τ

infix 10  [_,_]_⊢_

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

inject₁-⊢ : {Γ Ψ : Cxt Ξ} 
  → [ Ξ , Ψ ] Γ ⊢ τ
    ----------------------------------
  → [ suc Ξ , ↑ Ψ ] ↑ Γ ⊢ inject₁-ty τ
inject₁-⊢ (ax ψ)   = ax  (inject₁-∈-↑ ψ)
inject₁-⊢ (var x)  = var (inject₁-∈-↑ x)
inject₁-⊢ (ƛ M)    = ƛ inject₁-⊢ M
inject₁-⊢ (M · M₁) = inject₁-⊢ M · inject₁-⊢ M₁
inject₁-⊢ (∀₀ M)   = ∀₀ (inject₁-⊢ M)
inject₁-⊢ (M ∙ t)  = subst (λ τ → [ _ , _ ] _ ⊢ τ)
  (subst-inject₁-ty t _) (inject₁-⊢ M ∙ inject₁-tm t)
  where open import Relation.Binary.PropositionalEquality

exts : (∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] Δ ⊢ τ)
    -----------------------------------------
  → ∀ {τ σ} → τ ∈ σ ∷ Γ → [ Ξ , Ψ ] σ ∷ Δ ⊢ τ 
exts σ (here refl) = var (here refl)
exts σ (there px)  = rename there (σ px)

exts-↑ : (∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] Δ ⊢ τ)
    -----------------------------------------
  → ∀ {τ} → τ ∈ ↑ Γ → [ suc Ξ , ↑ Ψ ] ↑ Δ ⊢ τ
exts-↑ σ τ∈Γ = {!!}

subst : {Γ Δ : Cxt Ξ}
      → (∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] Δ ⊢ τ)
        -------------------------------------------
      → (∀ {τ} → [ Ξ , Ψ ] Γ ⊢ τ → [ Ξ , Ψ ] Δ ⊢ τ)
subst σ (ax x)   = ax x
subst σ (var x)  = σ x
subst σ (ƛ M)    = ƛ subst (exts σ) M
subst σ (M · N)  = subst σ M · subst σ N
subst σ (∀₀ M)   = ∀₀ (subst (exts-↑ σ) M)
subst σ (M ∙ t)  = subst σ M ∙ t

_[_] : {τ₁ : Ty Ξ} {τ₂ : Ty Ξ}
     → [ Ξ , Ψ ] (τ₁ ∷ Γ) ⊢ τ₂
     → [ Ξ , Ψ ] Γ ⊢ τ₁
       --------------------
     → [ Ξ , Ψ ] Γ ⊢ τ₂
_[_] {Ξ = Ξ} {Ψ = Ψ} {Γ = Γ} {τ₁} {τ₂} N M = subst σ N
  where 
    σ : {τ : Ty Ξ} → τ ∈ τ₁ ∷ Γ → [ Ξ , Ψ ] Γ ⊢ τ
    σ (here refl) = M
    σ (there p)   = var p
