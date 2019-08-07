{-# OPTIONS --without-K #-}

open import Data.Nat
  renaming (_≟_ to _≟ℕ_)

module SystemH.Type.Base (Op : ℕ → Set) (At : ℕ → Set) where

open import Data.Vec 
open import Data.Fin as F
  using (Fin; toℕ; lower₁)

open import Relation.Nullary

open import Size

private
  variable
    n m : ℕ

VCxt : Set
VCxt = ℕ

variable
  Ξ Ξ₁ Ξ₂ : VCxt
  i j k   : Size

data Tm  (Ξ : ℕ) {depth : Size} : Set where
  -- variable
  var : (x : Fin Ξ) → Tm Ξ
  -- m-ary operation symbols
  tm  : {i : Size< depth} (k : Op m) → (xs : Vec (Tm Ξ {i}) m) → Tm Ξ

-- `Term` stands for closed terms 
Term : Set
Term = Tm 0

Tms : VCxt → {i : Size} → ℕ → Set
Tms Ξ {i} n = Vec (Tm Ξ {i}) n

-- Formula
data Ty (Ξ : VCxt) : Set where
  -- n-ary atomic formulas
  at  : (φ : At n) → (xs : Tms Ξ n) → Ty Ξ
  -- implication
  _⇒_ : (τ₁ : Ty Ξ) (τ₂ : Ty Ξ) → Ty Ξ
  ∀₁  : (τ : Ty (suc Ξ)) → Ty Ξ
  -- ∀₁ for first-order universal quantifier

inject₁ : Tm Ξ {i} → Tm (suc Ξ) {i}
inject₁ (var x)  = var  (F.inject₁ x)
inject₁ (tm k x) = tm k (map inject₁ x)

private
  substTm : {Ξ : VCxt} → Tm Ξ → Tm (suc Ξ) {j} → Tm Ξ
  substTm {Ξ = Ξ} u (var x) with Ξ ≟ℕ toℕ x
  ... | yes _ = u
  ... | no  p = var (lower₁ x p)
  substTm u (tm k xs) = tm k (map (substTm u) xs)

  substTy : {Ξ : VCxt} → Tm Ξ → Ty (suc Ξ) → Ty Ξ
  substTy t (at φ xs) = at φ (map (substTm t) xs)
  substTy t (τ₁ ⇒ τ₂) = substTy t τ₁ ⇒ substTy t τ₂
  substTy t (∀₁ τ)    = ∀₁ (substTy (inject₁ t) τ)

[_↦_]tm_ : (Ξ : VCxt) → Tm Ξ → Tm (suc Ξ) → Tm Ξ
[ Ξ ↦ u ]tm t = substTm {Ξ = Ξ} u t

[_↦_]ty_ : (Ξ : VCxt) → Tm Ξ → Ty (suc Ξ) → Ty Ξ
[ Ξ ↦ t ]ty u = substTy {Ξ} t u

-- `Type` stands for types without free variables
Type : Set
Type = Ty 0 

inject₁-ty : Ty Ξ → Ty (suc Ξ)
inject₁-ty (at φ xs) = at φ (map inject₁ xs)
inject₁-ty (τ ⇒ τ₁)  = inject₁-ty τ ⇒ inject₁-ty τ₁
inject₁-ty (∀₁ τ)    = ∀₁ (inject₁-ty τ)
