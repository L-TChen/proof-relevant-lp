

module Term  where

open import Data.Fin
open import Term.Base public

Ex₁ : CTm
Ex₁ = ƛ ƛ (bvar (# 0))
-- λ x . λ y . x
Ex₂ : CTm
Ex₂ = ƛ ƛ (bvar (# 1))

Ex₃ : CTm
Ex₃ = Ex₁ · Ex₂

