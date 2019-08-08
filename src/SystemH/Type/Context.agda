open import Data.Nat

module SystemH.Type.Context (Op At : ℕ → Set) where

open import Data.List

open import SystemH.Type.Base Op At

Cxt : VCxt → Set
Cxt Ξ = List (Ty Ξ)

variable
  Ψ Γ Δ : Cxt Ξ

↑_ : Cxt Ξ → Cxt (suc Ξ)
↑ Γ = map ↑-ty Γ

-- simultaneous substitution
[_]cxt_ : {Ξ : VCxt} → Tm Ξ → Cxt (suc Ξ) → Cxt Ξ 
[ t ]cxt Γ = map ([ t ]ty_) Γ

infix 8 [_]cxt_

