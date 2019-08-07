open import Data.Nat

module SystemH.Typing.Reduction (Op At : ℕ → Set) where

open import SystemH.Type Op At
open import SystemH.Typing.Base Op At

data _⟶_ {Ξ : _} : {Δ Γ : Cxt Ξ} (t u : Ξ , Δ , Γ ⊢ τ) → Set where
  β-ƛ : ∀ {e t}
      → ((ƛ e) · t) ⟶ {!e!}
