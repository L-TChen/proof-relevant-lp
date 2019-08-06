open import Data.Nat
  renaming (_≟_ to _≟ℕ_)

module SystemH.Type.Base.Properties (Op : ℕ → Set) (At : ℕ → Set) where

open import Relation.Binary.PropositionalEquality
open import Size

open import SystemH.Type.Base Op At

∀₁₁ : {σ τ : Ty (suc Ξ) {i}} → ∀₁ σ ≡ ∀₁ τ → σ ≡ τ
∀₁₁ refl = refl

inject₁-ty-injective : (σ τ : Ty Ξ) → inject₁-ty σ ≡ inject₁-ty τ → σ ≡ τ
inject₁-ty-injective (at ψ xs) (at φ ys) eq = {!!}
inject₁-ty-injective (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) eq = {!!}
inject₁-ty-injective (∀₁ {j} σ) (∀₁ τ) eq   = {!!}
