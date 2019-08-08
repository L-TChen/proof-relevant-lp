{-# OPTIONS --without-K #-}

open import Data.Nat

module SystemH.Type.Base (Op At : ℕ → Set) where

-- TODO:
-- Use sized types
-- Problem: `substTm` requres addition for size,
-- otherwise it would cause some problem when proving properties of `substTm`

open import Data.Vec as V
open import Data.Fin as F

private
  variable
    n m : ℕ

VCxt : Set
data Tm  (Ξ : ℕ) : Set
Tms : VCxt → ℕ → Set

VCxt = ℕ
Tms Ξ n = Vec (Tm Ξ) n

data Tm Ξ where
  -- de Bruijn level variable (count from the outermost binder)
  var : (x : Fin Ξ) → Tm Ξ
  -- m-ary operation symbols
  op  : (σ : Op n) → (xs : Tms Ξ n) → Tm Ξ

data Ty (Ξ : VCxt) : Set where
  -- n-ary atomic formulas
  at  : (φ : At n) → (xs : Tms Ξ n) → Ty Ξ
  -- implication
  _⇒_ : (τ₁ τ₂ : Ty Ξ) → Ty Ξ
  ∀₁  : (τ : Ty (suc Ξ)) → Ty Ξ
  -- ∀₁ for first-order universal quantifier
  
variable
  Ξ Ξ₁ Ξ₂ : VCxt
  τ τ₁ τ₂ σ σ₁ σ₂ : Ty Ξ

-- `Term` stands for closed terms 
Term : Set
Term = Tm 0

-- `Type` stands for types without free variables
Type : Set
Type = Ty 0
  
------------------------------------------------------------------------
-- Weakening variable context
------------------------------------------------------------------------

{-# TERMINATING #-}
↑-tm : Tm Ξ → Tm (suc Ξ)
↑-tm (var x)  = var  (F.inject₁ x)
↑-tm (op σ xs) = op σ (map ↑-tm xs)

↑-ty : Ty Ξ → Ty (suc Ξ)
↑-ty (at φ xs) = at φ (map ↑-tm xs)
↑-ty (τ ⇒ τ₁)  = ↑-ty τ ⇒ ↑-ty τ₁
↑-ty (∀₁ τ)    = ∀₁ (↑-ty τ)

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------
{-# TERMINATING #-}
substTm : Tm Ξ → Tm (suc Ξ) → Tm Ξ
substTm u (var zero)    = u
substTm u (var (suc x)) = var x
substTm u (op σ xs)     = op σ (map (substTm u) xs)

substTy : Tm Ξ → Ty (suc Ξ) → Ty Ξ
substTy t (at φ xs) = at φ (map (substTm t) xs)
substTy t (τ₁ ⇒ τ₂) = substTy t τ₁ ⇒ substTy t τ₂
substTy t (∀₁ τ)    = ∀₁ (substTy (↑-tm t) τ)

[_]tm_ : Tm Ξ → Tm (suc Ξ) → Tm Ξ
[ u ]tm t = substTm u t

[_]ty_ : Tm Ξ → Ty (suc Ξ) → Ty Ξ
[ t ]ty u = substTy t u

------------------------------------------------------------------------
-- Horn Clause
------------------------------------------------------------------------

open import Data.Product
  hiding (map)

Horn : ℕ → Set
Horn n = Vec (∃ At) (suc n) 

to∀s : Ty n → Ty 0
to∀s τ = {!!}

toTy : At n → Ty n
toTy ψ = at ψ (map var (allFin _))

to⇒ : Vec (Ty Ξ) (suc n) → Ty Ξ
to⇒ (τ ∷ [])          = τ
to⇒ (τ ∷ τs@(_ ∷ _)) = to⇒ τs ⇒ τ

⟦_⟧ : Horn n → Ty 0
⟦ B ∷ [] ⟧     = {!!}
⟦ B ∷ x ∷ As ⟧ = {!!}
