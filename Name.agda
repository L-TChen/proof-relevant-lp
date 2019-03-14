module Name where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.Product hiding (map)
open import Data.Char
open import Data.List
open import Data.List.Membership.Propositional

open import Data.List.Relation.Binary.Lexicographical strictTotalOrder public
open StrictTotalOrder lexicographical                                  public

Name : Set
Name = List Char

postulate
  fresh-gen : ∀ (xs : List Name) → ∃[ x ] (x ∉ xs)
