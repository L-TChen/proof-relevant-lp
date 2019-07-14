{-# OPTIONS --cubical #-}

module Typing where

open import Data.Nat
open import Data.String using (String) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_)

open import FiniteSets.Kuratowski
import Cubical.Foundations.Logic as L

open import Assoc
open import Exp

Cxt : Set
Cxt = Assoc FName (Typ 0)

Cxt₁ : Set
Cxt₁ = K FName

private
  variable
    n m : ℕ
    Γ : Cxt
    Δ Θ : Cxt₁
    σ τ : Typ n
    x : FName
    e e₁ e₂ : Exp n m
    
data _⊢₁_ : Cxt₁ → Typ 0 → Set where
  var : L.[ x ∈ Δ ] → Δ ⊢₁ fv x
  _⇒_ : Δ ⊢₁ σ → Δ ⊢₁ τ
      → Δ ⊢₁ (σ ⇒ τ)
  Ȧ : (L : FNames)
    → (∀ x → L.[ x ∉ L ] → ([ x ] ∪ Δ) ⊢₁ instVar₁ x τ)
    → Δ ⊢₁ Ȧ τ 

data _,_⊢_∶_ : Cxt₁ → Cxt → Expr → Typ 0 → Set where
  var : L.[ (x , τ) ∈ Γ ] → Θ , Γ ⊢ fv x ∶ τ
  ⇒-intro : Θ ⊢₁ σ
          → (L : FNames)
          → (∀ x → L.[ x ∉ L ] → Θ , ([ x , σ ] ∪ Γ) ⊢ instVar x e ∶ τ)
          → Θ , Γ ⊢ (ƛ σ e) ∶ (σ ⇒ τ)
  ⇒-elim  : Θ , Γ ⊢ e₁ ∶ (σ ⇒ τ)
          → Θ , Γ ⊢ e₂ ∶ σ
          → Θ , Γ ⊢ (e₁ · e₂) ∶ τ
  Ȧ-intro : (L : FNames)
          → (∀ x → L.[ x ∉ L ] → ([ x ] ∪  Θ) , Γ ⊢ (instVarτ x e) ∶ instVar₁ x τ)  
          → Θ , Γ ⊢ Λ e ∶ Ȧ τ 
  Ȧ-elim  : Θ , Γ ⊢ e ∶ Ȧ σ
          → Θ ⊢₁ τ
          → Θ , Γ ⊢ e ⋆ τ ∶ inst₁ τ σ 

substCxt₁ : FName → Typ 0 → Cxt → Cxt 
substCxt₁ x τ = mapK (λ yσ → (proj₁ yσ , [ x ↝ τ ]₁ (proj₂ yσ)))

postulate
 substCxt₁-∈ : ∀ {Γ} x σ y τ
               → L.[ (x , σ) ∈ Γ ]
               → L.[ (x , [ y ↝ τ ]₁ σ) ∈ substCxt₁ y τ Γ ]
