open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

module Term.Freshness (Atom : Set)(_≟A_ : Decidable {A = Atom} (_≡_)) where

open import Data.Fin
open import Data.List.Membership.Propositional
open import Term Atom _≟A_

data _#_ (x : Atom) {n xs} : RawTm n xs → Set where
  instance
    fvar_ : ∀ {y} ⦃ y∈xs : y ∈ xs ⦄ → x ≢ y     → x # fvar y
    bvar_ : ∀                     (i : Fin n)   → x # bvar i
    _·_   : ∀ {t₁ t₂}         → x # t₁ → x # t₂ → x # t₁ · t₂
    ƛ_    : ∀ {t}                      → x # t  → x # ƛ t 
infix 5 _#_

x∉xs⇒x#t : ∀ {x xs n} → (t : RawTm n xs) → x ∉ xs → x # t
x∉xs⇒x#t (fvar_ y ⦃ y∈xs ⦄) x∉xs = fvar λ { refl → x∉xs y∈xs }
x∉xs⇒x#t (bvar i) x∉xs = bvar i
x∉xs⇒x#t (t · t₁) x∉xs = x∉xs⇒x#t t x∉xs · x∉xs⇒x#t t₁ x∉xs
x∉xs⇒x#t (ƛ t) x∉xs    = ƛ x∉xs⇒x#t t x∉xs
