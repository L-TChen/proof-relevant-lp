open import Data.Nat
  renaming (_≟_ to _≟ℕ_)

module SystemH.Type.Base.Properties (Op : ℕ → Set) (At : ℕ → Set) where

open import Data.Vec using ([]; _∷_; map)
import Data.Vec.Properties as Vₚ

open import Data.Fin using (Fin)
import Data.Fin.Properties as Fₚ

open import Relation.Binary.PropositionalEquality
open import Size

open import SystemH.Type.Base Op At

∀₁₁ : {σ τ : Ty (suc Ξ)} → ∀₁ σ ≡ ∀₁ τ → σ ≡ τ
∀₁₁ refl = refl

⇒₁ : ∀ {σ₁ σ₂ : Ty Ξ} {τ₁ τ₂} → σ₁ ⇒ σ₂ ≡ τ₁ ⇒ τ₂ → σ₁ ≡ τ₁
⇒₁ refl = refl

⇒₂ : ∀ {σ₁ σ₂ : Ty Ξ} {τ₁ τ₂} → σ₁ ⇒ σ₂ ≡ τ₁ ⇒ τ₂ → σ₂ ≡ τ₂
⇒₂ refl = refl

at₀ : ∀ {n m} {xs : Tms Ξ n} {ys : Tms Ξ m} {ψ : At n} {φ : At m}
  → at ψ xs ≡ at φ ys → n ≡ m
at₀ refl = refl

at₁ : ∀ {n} {xs ys : Tms Ξ n} {ψ φ : At n}
  → at ψ xs ≡ at φ ys → ψ ≡ φ
at₁ refl = refl

at₂ : ∀ {n} {xs ys : Tms Ξ n} {ψ φ : At n}
  → at ψ xs ≡ at φ ys → xs ≡ ys
at₂ refl = refl

var₁ : {n : ℕ} {x y : Fin n} → var x ≡ var y → x ≡ y
var₁ refl = refl

tm₀ : ∀ {m₁ m₂ j₁ j₂} {φ : Op m₁} {ψ : Op m₂} {xs : Tms Ξ {j₁} m₁} {ys : Tms Ξ {j₂} m₂}
  → tm {i = j₁} φ xs ≡ tm {i = j₂} ψ ys → m₁ ≡ m₂
tm₀ refl = refl

tm₁ : ∀ {n j₁ j₂} {φ ψ : Op n} {xs : Tms Ξ {j₁} n} {ys : Tms Ξ {j₂} n}
  → tm {i = j₁} φ xs ≡ tm {i = j₂} ψ ys → j₁ ≡ j₂
tm₁ refl = refl

tm₂ : ∀ {n j} {φ ψ : Op n} {xs : Tms Ξ {j} n} {ys : Tms Ξ {j} n}
  → tm {i = j} φ xs ≡ tm {i = j} ψ ys → φ ≡ ψ
tm₂ refl = refl

tm₃ : ∀ {n} {φ ψ : Op n} {xs ys : Tms Ξ n}
  → tm φ xs ≡ tm ψ ys → xs ≡ ys
tm₃ refl = refl

inj∞ : Tm Ξ {i} → Tm Ξ {∞}
inj∞ (var x)   = var x
inj∞ (tm k xs) = tm k (map inj∞ xs)

mutual
  inject₁-injective : (t u : Tm Ξ) → inject₁ t ≡ inject₁ u → t ≡ u
  inject₁-injective (var x) (var y) eq       = cong var (Fₚ.inject₁-injective (var₁ eq))
  inject₁-injective (tm ψ xs) (tm φ ys) eq with tm₀ eq
  inject₁-injective (tm ψ xs) (tm φ ys) eq | refl with tm₁ eq
  inject₁-injective (tm ψ xs) (tm φ ys) eq | refl | refl = cong₂ tm {!!} {!!}

  map-inject₁-injective : ∀ {n} (xs ys : Tms Ξ n) → map inject₁ xs ≡ map inject₁ ys → xs ≡ ys
  map-inject₁-injective [] [] refl = refl
  map-inject₁-injective (x ∷ xs) (y ∷ ys) eq =
    cong₂ _∷_ (inject₁-injective _ _ (Vₚ.∷-injectiveˡ eq)) (map-inject₁-injective xs ys (Vₚ.∷-injectiveʳ eq))

inject₁-ty-injective : (σ τ : Ty Ξ) → inject₁-ty σ ≡ inject₁-ty τ → σ ≡ τ
inject₁-ty-injective (at ψ xs) (at φ ys) eq with at₀ eq
... | refl = cong₂ at (at₁ eq) (map-inject₁-injective xs ys (at₂ eq))
inject₁-ty-injective (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) eq =
  cong₂ _⇒_ (inject₁-ty-injective σ₁ τ₁ (⇒₁ eq)) (inject₁-ty-injective σ₂ τ₂ (⇒₂ eq))
inject₁-ty-injective (∀₁ σ) (∀₁ τ) eq =
  cong ∀₁ (inject₁-ty-injective σ τ (∀₁₁ eq))
