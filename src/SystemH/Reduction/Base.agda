open import Data.Nat

module SystemH.Reduction.Base (Op At : ℕ → Set) where

open import Data.List
  hiding ([_])

open import SystemH.Type   Op At
open import SystemH.Typing Op At

data Value {Ξ : VCxt} {Ψ Γ : Cxt Ξ} : [ Ξ , Ψ ] Γ ⊢ τ → Set where
  V-ax :
      {τ∈Ψ : τ ∈ Ψ}
      --------------
    → Value (ax τ∈Ψ)

  V-ƛ :
      {N : [ Ξ , Ψ ] τ ∷ Γ ⊢ σ}
      -------------------------
    → Value (ƛ N)

  V-inst :
      {M : [ suc Ξ , ↑ Ψ ] ↑ Γ ⊢ τ} {t : Tm Ξ}
    → Value M
      -------------
    → Value (M ∙ t)

data _-→_ {Ξ} {Ψ Γ : Cxt Ξ} {τ} : (t u : [ Ξ , Ψ ] Γ ⊢ τ) → Set where
  β-ƛ : ∀ {M} {N : [ _ , _ ] Γ ⊢ σ}
--      → Value N -- with this condition it becomes call-by-value
        -----------------------------
      → ƛ M · N -→ [ N ] M

  ξ-·₁ : ∀ {L L′} {M : [ Ξ , Ψ ] Γ ⊢ σ}
    → L -→ L′
      -----------------
    → L · M -→ L′ · M

  ξ-·₂ : ∀ {V} {M M′ : [ Ξ , Ψ ] Γ ⊢ σ}
    → M -→ M′
      -----------------
    → V · M -→ V · M′   

infix 8 _-→_ 
