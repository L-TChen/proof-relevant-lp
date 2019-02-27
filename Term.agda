open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Term (Atom : Set)(_≟S_ : Decidable {A = Atom} _≡_ ) where

open import Data.List
open import Data.Fin

open import Term.Base       Atom _≟S_ public

Ex₁ : CTm
Ex₁ = ƛ ƛ (bvar (# 0))
-- λ x . λ y . x
Ex₂ : CTm
Ex₂ = ƛ ƛ (bvar (# 1))

Ex₃ : CTm
Ex₃ = Ex₁ · Ex₂

