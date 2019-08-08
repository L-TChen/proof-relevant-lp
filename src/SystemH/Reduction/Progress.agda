open import Data.Nat

module SystemH.Reduction.Progress (Op At : ℕ → Set) where

open import SystemH.Type           Op At
open import SystemH.Typing         Op At
open import SystemH.Reduction.Base Op At

{-
progress : ∀ {e : Expr} {τ}
           → ∅ , ∅ ⊢ e ∶ τ 
           → ¬ (Val e)
           → ∃ (λ e' → e ⟼ e')
progress = {!!}
-}
