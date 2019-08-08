{-# OPTIONS --without-K #-}

open import Data.Nat

module SystemH.Type.Base (Op At : ℕ → Set) where

open import Data.Vec as V
open import Data.Fin as F
  hiding (_+_)
open import Size

private
  variable
    n m : ℕ
    d   : Size

VCxt : Set
data Tm  (Ξ : ℕ) : {depth : Size} → Set
Tms : VCxt → {d : Size} → ℕ → Set

VCxt = ℕ
Tms Ξ {d} n = Vec (Tm Ξ {d}) n

data Tm Ξ where
  -- de Bruijn level variable (count from the outermost binder)
  var : (x : Fin Ξ) → Tm Ξ {d}
  -- m-ary operation symbols
  op  : (σ : Op n) → (xs : Tms Ξ {d} n) → Tm Ξ {↑ d}

data Ty (Ξ : VCxt) : Set where
  -- n-ary atomic formulas
  at  : (φ : At n) → (xs : Tms Ξ n) → Ty Ξ
  -- implication
  _⇒_ : (τ₁ τ₂ : Ty Ξ) → Ty Ξ
  ∀₁  : (τ : Ty (suc Ξ)) → Ty Ξ
  -- ∀₁ for first-order universal quantifier
  
variable
  Ξ Ξ₁ Ξ₂ Ξ₃ : VCxt
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

↑-tm : Tm Ξ {d} → Tm (suc Ξ) {d}
↑-tm (var x)   = var  (inject₁ x)
↑-tm (op σ xs) = op σ (map ↑-tm xs)

↑-ty : Ty Ξ → Ty (suc Ξ)
↑-ty (at φ xs) = at φ (map ↑-tm xs)
↑-ty (τ ⇒ τ₁)  = ↑-ty τ ⇒ ↑-ty τ₁
↑-ty (∀₁ τ)    = ∀₁ (↑-ty τ)

------------------------------------------------------------------------
-- Simultaneous Substitution
------------------------------------------------------------------------

rename-tm : (Fin Ξ₁ → Fin Ξ₂)
  → Tm Ξ₁ {d} → Tm Ξ₂ {d}
rename-tm ρ (var x)   = var (ρ x)
rename-tm ρ (op σ xs) = op σ (map (rename-tm ρ) xs)

rename-ty : (Fin Ξ₁ → Fin Ξ₂)
  → Ty Ξ₁ → Ty Ξ₂
rename-ty ρ (at φ xs) = at φ (map (rename-tm ρ) xs)
rename-ty ρ (τ ⇒ τ₁)  = rename-ty ρ τ ⇒ rename-ty ρ τ₁
rename-ty ρ (∀₁ τ)    = ∀₁ (rename-ty (F.lift 1 ρ) τ)

exts-tm : (Fin Ξ₁ → Tm Ξ₂)
  → Fin (suc Ξ₁) → Tm (suc Ξ₂)
exts-tm ρ 0F      = var 0F
exts-tm ρ (suc x) = rename-tm suc (ρ x)

subst-tm : (Fin Ξ₁ → Tm Ξ₂)
  → Tm Ξ₁ {d} → Tm Ξ₂
subst-tm ρ (var x)   = ρ x
subst-tm ρ (op σ xs) = op σ (map (subst-tm ρ) xs)

subst-ty : (Fin Ξ₁ → Tm Ξ₂)
  → Ty Ξ₁ → Ty Ξ₂
subst-ty ρ (at φ xs) = at φ (map (subst-tm ρ) xs)
subst-ty ρ (τ ⇒ τ₁)  = subst-ty ρ τ ⇒ subst-ty ρ τ₁
subst-ty ρ (∀₁ τ)    = ∀₁ (subst-ty (exts-tm ρ) τ)

exts-tm-∘ : (Fin Ξ₁ → Tm Ξ₂)
  → (Fin Ξ₂ → Tm Ξ₃)
  → (Fin Ξ₁ → Tm Ξ₃)
exts-tm-∘ ρ₁ ρ₂ x = subst-tm ρ₂ (ρ₁ x)

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------
substTm : Tm Ξ → Tm (suc Ξ) {d} → Tm Ξ
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
{-
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
-}
