open import Data.Nat

module SystemH.Type.Context (Op At : ℕ → Set) where

open import Data.List
open import Size using (Size)

open import SystemH.Type.Base Op At

Cxt : VCxt → Set
Cxt Ξ = List (Ty Ξ)

variable
  Ψ Γ Δ : Cxt Ξ

↑_ : Cxt Ξ → Cxt (suc Ξ)
↑ Γ = map inject₁-ty Γ

-- simultaneous substitution
[_↦_]cxt_ : (Ξ : VCxt) → Tm Ξ → Cxt (suc Ξ) → Cxt Ξ
[ Ξ ↦ t ]cxt Γ = map ([ Ξ ↦ t ]ty_) Γ

infix 10 [_↦_]cxt_
