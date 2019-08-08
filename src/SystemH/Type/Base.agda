{-# OPTIONS --without-K #-}

open import Data.Nat

module SystemH.Type.Base (Op At : ℕ → Set) where

-- TODO:
-- Use sized types
-- Problem: `substTm` requres addition for size,
-- otherwise it would cause some problem when proving properties of `substTm`

open import Data.Vec 
open import Data.Fin as F
  using (Fin; zero; suc)

private
  variable
    n m : ℕ

VCxt : Set
VCxt = ℕ

variable
  Ξ Ξ₁ Ξ₂ : VCxt

data Tm  (Ξ : ℕ) : Set

Tms : VCxt → ℕ → Set
Tms Ξ n = Vec (Tm Ξ) n

data Tm Ξ where
  -- de Bruijn level variable (count from the outermost binder)
  var : (x : Fin Ξ) → Tm Ξ
  -- m-ary operation symbols
  op  : (σ : Op n) → (xs : Tms Ξ n) → Tm Ξ

-- `Term` stands for closed terms 
Term : Set
Term = Tm 0

-- Formula
data Ty (Ξ : VCxt) : Set where
  -- n-ary atomic formulas
  at  : (φ : At n) → (xs : Tms Ξ n) → Ty Ξ
  -- implication
  _⇒_ : (τ₁ τ₂ : Ty Ξ) → Ty Ξ
  ∀₁  : (τ : Ty (suc Ξ)) → Ty Ξ
  -- ∀₁ for first-order universal quantifier
  
variable
  τ : Ty Ξ
  
{-# TERMINATING #-}
inject₁-tm : Tm Ξ → Tm (suc Ξ)
inject₁-tm (var x)  = var  (F.inject₁ x)
inject₁-tm (op σ xs) = op σ (map inject₁-tm xs)

private
  {-# TERMINATING #-}
  substTm : Tm Ξ → Tm (suc Ξ) → Tm Ξ
  substTm u (var zero)    = u
  substTm u (var (suc x)) = var x
  substTm u (op σ xs)     = op σ (map (substTm u) xs)

  substTy : Tm Ξ → Ty (suc Ξ) → Ty Ξ
  substTy t (at φ xs) = at φ (map (substTm t) xs)
  substTy t (τ₁ ⇒ τ₂) = substTy t τ₁ ⇒ substTy t τ₂
  substTy t (∀₁ τ)    = ∀₁ (substTy (inject₁-tm t) τ)

[0↦_]tm_ : Tm Ξ → Tm (suc Ξ) → Tm Ξ
[0↦ u ]tm t = substTm u t

[0↦_]ty_ : Tm Ξ → Ty (suc Ξ) → Ty Ξ
[0↦ t ]ty u = substTy t u

-- `Type` stands for types without free variables
Type : Set
Type = Ty 0

inject₁-ty : Ty Ξ → Ty (suc Ξ)
inject₁-ty (at φ xs) = at φ (map inject₁-tm xs)
inject₁-ty (τ ⇒ τ₁)  = inject₁-ty τ ⇒ inject₁-ty τ₁
inject₁-ty (∀₁ τ)    = ∀₁ (inject₁-ty τ)
