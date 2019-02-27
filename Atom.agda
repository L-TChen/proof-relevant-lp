module Atom where

open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

record Name : Set₁ where
  field
    Atom      : Set
    _≟A_      : Decidable {A = Atom} _≡_
    fresh-gen : ∀ xs → Σ[ x ∈ Atom ] x ∉ xs

  Atoms : Set
  Atoms = List Atom

open Name public
