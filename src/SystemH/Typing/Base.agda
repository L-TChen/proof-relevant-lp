{-# OPTIONS --rewriting #-}
open import Data.Nat

module SystemH.Typing.Base (Op At : ℕ → Set) where

open import Agda.Builtin.Equality
open import Data.Nat.Properties

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE +-identityʳ #-}

open import Data.Fin
  hiding (_+_)
open import Data.Vec
  using (_∷_; _++_)
open import Data.Vec.Membership.Propositional
  using (_∈_)
open import Data.Vec.Relation.Unary.All
  using (All)
open import Size

open import SystemH.Type Op At

-- Proof Evidence (Expression)
-- `Ψ` is the context for axioms
-- `Γ` is the context for variables

data [_,_]_⊢_ (Ψ : Context n) : (d : Size) (Γ : Context m) (τ : Type) → Set where
  ax  : τ ∈ Ψ
        --------------- Axiom
      → [ Ψ , d ] Γ ⊢ τ

  var : τ ∈ Γ
      ----------------- Var
      → [ Ψ , d ] Γ ⊢ τ

  ƛ_  : [ Ψ , d ] (τ₁ ∷ Δ) ++ Γ ⊢ τ
        ---------------------------- Abs
      → [ Ψ , ↑ d ] Γ ⊢ (τ₁ ∷ Δ) ⇒ τ

  _·_ : [ Ψ , d ] Γ ⊢ (τ₁ ∷ Δ) ⇒ τ₂
      → All [ Ψ , d ] Γ ⊢_ (τ₁ ∷ Δ)
        ---------------------------- App
      → [ Ψ , ↑ d ] Γ ⊢ τ₂

  _∙₀_ : [ Ψ , d ] Γ ⊢ ∀₁ Ξ τ
      → (σ : Fin (suc Ξ) → Tm 0)
        ---------------------------------- Inst₀
      → [ Ψ , ↑ d ] Γ ⊢ [ σ ]ty τ

  _∙₁_ : [ Ψ , d ] Γ ⊢ ∀₁ Ξ₁ τ
      → (σ : Fin (suc Ξ₁) → Tm (suc Ξ₂))
        ---------------------------------- Inst₁
      → [ Ψ , ↑ d ] Γ ⊢ ∀₁ Ξ₂ ([ σ ]ty τ)

infix 6 [_,_]_⊢_

infix 14 _·_
infix 16 _∙₁_
infix 16 _∙₀_
