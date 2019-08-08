open import Data.Nat

module SystemH.Type.Context (Op At : ℕ → Set) where

open import Data.List

open import SystemH.Type.Base Op At

Cxt : VCxt → Set
Cxt Ξ = List (Ty Ξ)

variable
  Ψ Γ Δ : Cxt Ξ

↑_ : Cxt Ξ → Cxt (suc Ξ)
↑ Γ = map inject₁-ty Γ

-- simultaneous substitution
[0↦_]cxt_ : {Ξ : VCxt} → Tm Ξ → Cxt (suc Ξ) → Cxt Ξ 
[0↦ t ]cxt Γ = map ([0↦ t ]ty_) Γ

infix 10 [0↦_]cxt_
