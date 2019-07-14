{-# OPTIONS --cubical #-}

module Assoc where 

open import Data.Product hiding (map)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (map)

open import FiniteSets.Kuratowski

private
  variable
    A : Set

Assoc : Set → Set → Set
Assoc A B = K (A × B)

dom : ∀ {A B} → Assoc A B → K A
dom = mapK proj₁

-- postulate
--  assoc-≠ : ∀ {A B} (Γ : Assoc A B) x Δ y {σ τ} 
--            → DomDist (Γ ++ [ x , τ ] ++ Δ) → ¬ (x ≡ y)
--            → (y , σ) ∈ (Γ ++ [ x , τ ] ++ Δ) 
--            → (y , σ) ∈ (Γ ++ Δ)
--  assoc-≡ : ∀ {A B} (Γ : Assoc A B) x Δ {σ τ} 
--            → DomDist (Γ ++ [ x , τ ] ++ Δ)
--            → (x , σ) ∈ (Γ ++ [ x , τ ] ++ Δ) 
--            → σ ≡ τ
