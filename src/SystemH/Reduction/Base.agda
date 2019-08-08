open import Data.Nat

module SystemH.Reduction.Base (Op At : ℕ → Set) where

open import SystemH.Type   Op At
open import SystemH.Typing Op At

data _⟶_ {Ξ : _} {Ψ Γ : Cxt Ξ} {τ : Ty Ξ} : (t u : [ Ξ , Ψ ] Γ ⊢ τ) → Set where
  β-ƛ : {σ : Ty Ξ} {e : _} {t : [ Ξ , Ψ ] Γ ⊢ σ}
      → ƛ e · t ⟶ e [ t ]

infix 8 _⟶_ 
