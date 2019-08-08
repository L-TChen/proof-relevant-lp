open import Data.Nat

module SystemH.Typing.Reduction (Op At : ℕ → Set) where

open import SystemH.Type Op At
open import SystemH.Typing.Base Op At

data _⟶_ {Ξ : _} : {Ψ Γ : Cxt Ξ} (t u : [ Ξ , Ψ ] Γ ⊢ τ) → Set where
  β-ƛ : ∀ {e t}
      → ((ƛ e) · t) ⟶ {!e!}
