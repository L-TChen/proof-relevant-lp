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
         -----------------------------
       → Value (∀₀ M)

data _-→_ {Ξ : VCxt} {Ψ Γ : Cxt Ξ} {τ : Ty Ξ} : (t u : [ Ξ , Ψ ] Γ ⊢ τ) → Set where
  β-ƛ : {M : [ Ξ , Ψ ] (σ ∷ Γ) ⊢ τ} {N : [ _ , _ ] Γ ⊢ σ}
      → Value N
        -----------------------------
      → ƛ M · N -→ M [ N ]

infix 8 _-→_ 
