open import Data.Nat

module SystemH.Typing.Base (Op At : ℕ → Set) where

open import Data.Vec
open import Data.Fin

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality
  hiding (subst)

open import SystemH.Type Op At

-- Proof Evidence (Expression)
-- `Ψ` is the context for axioms
-- `Γ` is the context for variables

data _,_,_⊢_ (Ξ : VCxt) (Ψ Γ : Cxt Ξ) : (τ : Ty Ξ) → Set where
  ax  : ∀ {τ} (ψ : τ ∈ Ψ)
        ------------- Axiom
      → Ξ , Ψ , Γ ⊢ τ

  var : ∀ {τ} → τ ∈ Γ
      --------------- Var
      → Ξ , Ψ , Γ ⊢ τ

  ƛ_  : {τ σ : Ty Ξ} (e : Ξ , Ψ , τ ∷ Γ ⊢ σ)
        ------------------------- Abs
      → Ξ , Ψ , Γ ⊢ (τ ⇒ σ)

  _·_ : ∀ {τ σ} (e₁ : Ξ , Ψ , Γ ⊢ τ ⇒ σ) (e₂ : Ξ , Ψ , Γ ⊢ τ)
        ----------------------------------------------------- App
      → Ξ , Ψ , Γ ⊢ σ

  ∀₀  : ∀ {τ} (e : suc Ξ , ↑ Ψ , ↑ Γ ⊢ τ)
        ----------------------------------- Gen
      → Ξ , Ψ , Γ ⊢ ∀₁ τ

  _∙_  : ∀ {τ} (e : Ξ , Ψ , Γ ⊢ ∀₁ τ) (t : Tm Ξ)
          -------------------------------- Inst
        → Ξ , Ψ , Γ ⊢ [ Ξ ↦ t ]ty τ

infix 10  _,_,_⊢_

_ : (ψ : At 0) (φ : At 1) (k : Op 0)
  → 0 , ∀₁ (at φ (var zero ∷ [])) ∷ [] , at ψ [] ∷ [] ⊢ at φ (tm k [] ∷ [])
_ = λ ψ φ k → ax (here refl) ∙ tm k []

ext : (∀ {τ} → τ ∈ Γ → τ ∈ Δ)
  → (∀ {τ σ} → τ ∈ (σ ∷ Γ) → τ ∈ σ ∷ Δ)
ext ρ (here px) = here  px
ext ρ (there p) = there (ρ p)

ext-↑ : (∀ {τ : Ty Ξ} → τ ∈ Γ → τ ∈ Δ)
  → ∀ {τ} → inject₁-ty τ ∈ (↑ Γ) → inject₁-ty τ ∈ (↑ Δ)
ext-↑ ρ px = {!ρ !}

rename : (∀ {τ} → τ ∈ Γ → τ ∈ Δ)
  → ∀ {τ} → (Ξ , Ψ , Γ ⊢ τ) → (Ξ , Ψ , Δ ⊢ τ)
rename ρ (ax ψ)   = ax ψ
rename ρ (var x)  = var (ρ x)
rename ρ (ƛ M)    = ƛ rename (ext ρ) M
rename ρ (M · N)  = rename ρ M · rename ρ N
rename ρ (M ∙ t)  = rename ρ M ∙ t
rename ρ (∀₀ M)   = ∀₀ (rename {!!} M)

exts : (∀ {τ} → τ ∈ Γ → Ξ , Ψ , Δ ⊢ τ)
  → ∀ {τ σ} → τ ∈ σ ∷ Γ → Ξ , Ψ , σ ∷ Δ ⊢ τ 
exts = {!!}

subst : (∀ {τ} → τ ∈ Γ → Ξ , Ψ , Δ ⊢ τ)
      → (∀ {τ} → Ξ , Ψ , Γ ⊢ τ → Ξ , Ψ , Δ ⊢ τ)
subst σ (ax x)   = ax x
subst σ (var x)  = σ x
subst σ (ƛ M)    = ƛ subst (exts σ) M
subst σ (M · N)  = subst σ M · subst σ N
subst σ (∀₀ M)   = ∀₀ (subst {!!} M)
subst σ (M ∙ t)  = subst σ M ∙ t 

_[_] : {τ₁ τ₂ : Ty Ξ}
     → Ξ , Ψ , (τ₁ ∷ Γ) ⊢ τ₂
     → Ξ , Ψ , Γ ⊢ τ₁
       -------------
     → Ξ , Ψ , Γ ⊢ τ₂
_[_] {Ξ} {Ψ} {Γ} {τ₁} {τ₂} N M = subst σ N
  where 
    σ : ∀ {τ} → τ ∈ τ₁ ∷ Γ → Ξ , Ψ , Γ ⊢ τ
    σ (here refl) = M
    σ (there p)   = var p
