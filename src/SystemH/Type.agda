open import Data.Nat

module SystemH.Type (Op At : ℕ → Set) where

open import SystemH.Type.Base       Op At public
open import SystemH.Type.Context    Op At public
open import SystemH.Type.Properties Op At public
