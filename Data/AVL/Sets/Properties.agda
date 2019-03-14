open import Relation.Binary using (StrictTotalOrder)

module Data.AVL.Sets.Properties
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Bool
open import Data.AVL.Sets strictTotalOrder

open StrictTotalOrder strictTotalOrder

infix 4 _∈_
infix 4 _∉_

_∈_ : _ → ⟨Set⟩ → Set
x ∈ xs = (x ∈? xs) ≡ true

_∉_ : _ → ⟨Set⟩ → Set 
x ∉ xs = (x ∈? xs) ≡ false

∉-¬∈ : ∀ {x xs} → x ∉ xs → ¬ (x ∈ xs)
∉-¬∈ {x} {xs} x∉xs with x ∈? xs
∉-¬∈ {x} {xs} refl | false = λ ()


postulate 
  ∈-insert : ∀ {x y} t → x ∈ t → x ∈ insert y t
  ∈-insert-= : ∀ {x} t → x ∈ insert x t
  ∈-≉-insert : ∀ {x y} t  → ¬ x ≈ y → y ∈ insert x t → y ∈ t 
  ∈-≉-delete : ∀ {x y} t → ¬ x ≈ y → y ∈ t → y ∈ delete x t 
