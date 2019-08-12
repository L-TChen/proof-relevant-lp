open import Data.Nat

module SystemH.Type.Context (Op At : ℕ → Set) where

open import Data.Vec
open import Data.Fin

open import SystemH.Type.Base Op At

Cxt : VCxt → ℕ → Set
Cxt Ξ n = Vec (Ty Ξ) n

Context : ℕ → Set
Context n = Cxt 0 n

--variable
--  Ψ Γ Δ : Cxt Ξ n
--  Γ₁ Γ₂ Δ₁ Δ₂ : Cxt Ξ n
variable
  Ψ Γ Δ : Context n
  Γ₁ Γ₂ Δ₁ Δ₂ : Context n

↑₁_ : Cxt Ξ n → Cxt (suc Ξ) n
↑₁ Γ = map ↑₁-ty Γ

------------------------------------------------------------------------
-- Simultaneous Substitution
------------------------------------------------------------------------
[_]cxt_ : (Fin Ξ₁ → Tm Ξ₂)
  → Cxt Ξ₁ n → Cxt Ξ₂ n
[ σ ]cxt Γ = map [ σ ]ty_ Γ

------------------------------------------------------------------------
-- Single Substitution
------------------------------------------------------------------------
[_]₁cxt_ : Tm Ξ
  → Cxt (suc Ξ) n → Cxt Ξ n
[ t ]₁cxt Γ = [ single t ]cxt_ Γ

infix 8 [_]cxt_
infix 8 [_]₁cxt_

