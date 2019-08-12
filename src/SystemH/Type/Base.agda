{-# OPTIONS --without-K #-}

open import Data.Nat as N

module SystemH.Type.Base (Op At : ℕ → Set) where

open import Data.Nat.Properties as Nₚ
open import Data.Vec as V
open import Data.Fin as F
  hiding (_+_)
open import Data.Empty

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function
open import Size

variable
  n m : ℕ

-- variable context x₁, x₂, ⋯ , xₙ 
VCxt : Set
VCxt = ℕ

data Tm (Ξ : VCxt) : {depth : Size} → Set
data Ty (Ξ : VCxt) : {depth : Size} → Set 
Tms Tys : VCxt → {d : Size} → ℕ → Set

Tms Ξ {d} n = Fin n → Tm Ξ {d}
Tys Ξ {d} n = Vec (Ty Ξ {d}) n

Term Type : {depth : Size} → Set
Term {d} = Tm 0 {d}
Type {d} = Ty 0 {d}

variable
  d   : Size
  Ξ Ξ₁ Ξ₂ Ξ₃ : VCxt
  τ τ₁ τ₂    : Ty Ξ
  τs τs₁ τs₂ : Tys Ξ {d} n

data Tm Ξ where
  -- de Bruijn level variable (count from the outermost binder)
  var : (x : Fin Ξ) → Tm Ξ {d}
  -- n-ary operation symbols
  op  : (K : Op n) → (xs : Tms Ξ {d} n) → Tm Ξ {↑ d}

data Ty Ξ where
  -- n-ary atomic formulas
  at  : (φ : At n) (xs : Tms Ξ n) → Ty Ξ {d}
  -- implication
  _⇒_ : (τs : Tys Ξ {d} m) (τ : Ty Ξ {d}) → Ty Ξ {↑ d}
  -- the first-order universal quantifier ∀₁ bind m+1 many variables
  ∀₁  : (m : ℕ) (τ : Ty (suc m + Ξ) {d}) → Ty Ξ {↑ d}

infix 16 _⇒_
  
------------------------------------------------------------------------
-- Weakening variable context
------------------------------------------------------------------------

private
  n+m+l=m+n+l : ∀ n m l → n + (m + l) ≡ m + (n + l)
  n+m+l=m+n+l n m l = begin
    n + (m + l)
      ≡⟨ sym (+-assoc n m l) ⟩
    (n + m) + l
      ≡⟨ cong (_+ l) (+-comm n m) ⟩
    (m + n) + l
      ≡⟨ +-assoc m n l ⟩
    m + (n + l)
      ∎
    where open ≡-Reasoning

↑-tm : (n : ℕ) → Tm Ξ {d} → Tm (n + Ξ) {d}
↑-tm n (var x)   = var (raise n x)
↑-tm n (op K xs) = op K (↑-tm n ∘ xs)

↑-ty : (n : ℕ) → Ty Ξ {d} → Ty (n + Ξ) {d}
↑-ty n (at φ xs) = at φ (↑-tm n ∘ xs)
↑-ty n (τs ⇒ τ)  = (map (↑-ty n) τs) ⇒ ↑-ty n τ
↑-ty {Ξ} n (∀₁ m τ) with ↑-ty n τ
... | ↑τ rewrite n+m+l=m+n+l n (suc m) Ξ = ∀₁ m ↑τ

↑₁-tm : Tm Ξ {d} → Tm (suc Ξ) {d}
↑₁-tm = ↑-tm 1 

↑₁-ty : Ty Ξ {d} → Ty (suc Ξ) {d}
↑₁-ty = ↑-ty 1 

------------------------------------------------------------------------
-- Renaming
------------------------------------------------------------------------

rename-tm : (Fin Ξ₁ → Fin Ξ₂)
  → Tm Ξ₁ {d} → Tm Ξ₂ {d}
rename-tm ρ (var x)   = var (ρ x)
rename-tm ρ (op K xs) = op K (rename-tm ρ ∘ xs)

rename-ty : (Fin Ξ₁ → Fin Ξ₂)
  → Ty Ξ₁ {d} → Ty Ξ₂ {d}
rename-ty ρ (at φ xs) = at φ (rename-tm ρ ∘ xs)
rename-ty ρ (τs ⇒ τ)  = map (rename-ty ρ) τs ⇒ rename-ty ρ τ
rename-ty ρ (∀₁ m τ)  = ∀₁ m (rename-ty (lift (suc m) ρ) τ)

exts-tm : (m : ℕ) → (Fin Ξ₁ → Tm Ξ₂)
  → Fin (m + Ξ₁) → Tm (m + Ξ₂)
exts-tm m σ i with toℕ i ≥? m
exts-tm _ σ i | yes p = ↑-tm _ (σ (reduce≥ i p))
exts-tm _ σ i | no ¬p = var (embed i ¬p)
  where
    embed : {m n l : ℕ} → (i : Fin (m + n))
      → ¬ m N.≤ toℕ i → Fin (m + l)
    embed {0F} 0F      leq    = ⊥-elim (leq z≤n)
    embed {0F} (suc i) leq    = ⊥-elim (leq z≤n)
    embed {suc m} 0F  _       = 0F
    embed {suc m} (suc i) leq = suc (embed i λ m≤i → leq (s≤s m≤i))

------------------------------------------------------------------------
-- Decidable Equality for Substitution
------------------------------------------------------------------------

_≗-sub_ : (σ₁ σ₂ : Fin Ξ₁ → Tm Ξ₂) → Set
σ₁ ≗-sub σ₂ = ∀ x → σ₁ x ≡ σ₂ x


------------------------------------------------------------------------
-- Simultaneous Substitution
------------------------------------------------------------------------

[_]tm_ : (Fin Ξ₁ → Tm Ξ₂)
  → Tm Ξ₁ {d} → Tm Ξ₂
[ σ ]tm (var x)   = σ x
[ σ ]tm (op K xs) = op K ([ σ ]tm_ ∘ xs)

[_]ty_ : (Fin Ξ₁ → Tm Ξ₂)
  → Ty Ξ₁ {d} → Ty Ξ₂
[ σ ]ty (at φ xs) = at φ ([ σ ]tm_ ∘ xs)
[ σ ]ty (τs ⇒ τ)  = map ([ σ ]ty_ ) τs ⇒ [ σ ]ty τ
[ σ ]ty (∀₁ m τ)  = ∀₁ m ([ exts-tm (suc m) σ ]ty τ)

------------------------------------------------------------------------
-- Substitution Composition
------------------------------------------------------------------------

_◇_ : ∀ {n m l}
  → (Fin m → Tm n)
  → (Fin l → Tm m)
  → Fin l → Tm n
(σ₂ ◇ σ₁) x = [ σ₂ ]tm (σ₁ x)

------------------------------------------------------------------------
-- Single Substitution
------------------------------------------------------------------------
single : Tm Ξ
  → (Fin (suc Ξ) → Tm Ξ)
single u 0F      = u
single u (suc t) = var t

[_]₁tm_ : Tm Ξ → Tm (suc Ξ) {d} → Tm Ξ
[_]₁tm_ u = [ single u ]tm_

[_]₁ty_ : Tm Ξ → Ty (suc Ξ) {d} → Ty Ξ
[_]₁ty_ u = [ single u ]ty_

------------------------------------------------------------------------
-- Horn Clause
------------------------------------------------------------------------

open import Data.Product

Horn : ℕ → Set
Horn n = Fin n → ∃ At

toTy : At n → Ty n
toTy ψ = at ψ var

{-
⟦_⟧ : Horn n → Ty 0
⟦ B ∷ As ⟧     = {!!}
-}
