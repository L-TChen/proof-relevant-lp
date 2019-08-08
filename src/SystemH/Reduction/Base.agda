open import Data.Nat

module SystemH.Reduction.Base (Op At : ℕ → Set) where

open import Data.List
  hiding ([_])

open import SystemH.Type   Op At
open import SystemH.Typing Op At

data Value {Ξ : VCxt} {Ψ Γ : Cxt Ξ} : [ Ξ , Ψ ] Γ ⊢ τ → Set where
  V-ƛ : {N : [ Ξ , Ψ ] τ ∷ Γ ⊢ σ}
        -------------------------
      → Value (ƛ N)

  V-ax : {τ∈Ψ : τ ∈ Ψ}
         --------------
       → Value (ax τ∈Ψ)

  V-∀₀ : {M : [ suc Ξ , ↑ Ψ ] ↑ Γ ⊢ τ}
       → Value M
         -----------------------------
       → Value (∀₀ M)

  V-inst : {M : [ Ξ , Ψ ] Γ ⊢ ∀₁ τ} {t : Tm Ξ}
       → Value M
         -------------------------------------
       → Value (M ∙ t)

data _-→_ {Ξ : VCxt} {Ψ Γ : Cxt Ξ} {τ : Ty Ξ} : (t u : [ Ξ , Ψ ] Γ ⊢ τ) → Set where
  ξ-·₁ : {L L′ : [ Ξ , Ψ ] Γ ⊢ σ ⇒ τ} {M : [ Ξ , Ψ ] Γ ⊢ σ}
    → L -→ L′
      -----------------
    → L · M -→ L′ · M

  ξ-·₂ : {V : [ Ξ , Ψ ] Γ ⊢ σ ⇒ τ} {M M′ : [ Ξ , Ψ ] Γ ⊢ σ}
    → Value V
    → M -→ M′
      --------------
    → V · M -→ V · M′


  β-ƛ : {M : [ Ξ , Ψ ] (σ ∷ Γ) ⊢ τ} {N : [ _ , _ ] Γ ⊢ σ}
    → Value N
      -------------------
    → ƛ M · N -→ M [ N ]

infix 8 _-→_ 
