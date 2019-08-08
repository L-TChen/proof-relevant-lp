open import Data.Nat

module SystemH.Typing (Op At : ℕ → Set) where

open import SystemH.Typing.Base         Op At public
open import SystemH.Typing.Substitution Op At public
