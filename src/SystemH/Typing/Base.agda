open import Data.Nat

module SystemH.Typing.Base (Op At : ℕ → Set) where

open import Data.List
open import Data.List.Membership.Propositional
  using (_∈_) public
  
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

  ƛ_  : [ Ξ , Ψ ] τ ∷ Γ ⊢ σ
        ------------------- Abs
      → [ Ξ , Ψ ] Γ ⊢ τ ⇒ σ

  _·_ : [ Ξ , Ψ ] Γ ⊢ τ ⇒ σ
      → [ Ξ , Ψ ] Γ ⊢ τ
        ------------------- App
      → [ Ξ , Ψ ] Γ ⊢ σ

  ∀₀  : [ suc Ξ , ↑ Ψ ] ↑ Γ ⊢ τ
        ----------------------- Gen
      → [ Ξ , Ψ ] Γ ⊢ ∀₁ τ

  _∙_ : [ Ξ , Ψ ] Γ ⊢ ∀₁ τ  → (t : Tm Ξ)
        -------------------------------- Inst
      → [ Ξ , Ψ ] Γ ⊢ [ t ]ty τ

infix 6 [_,_]_⊢_
infix 14 _·_
infix 16 _∙_
