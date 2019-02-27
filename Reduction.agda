open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Reduction (Atom : Set)(_≟A_ : Decidable {A = Atom} _≡_ ) where
open import Data.List
open import Term  Atom _≟A_
private
  Atoms : Set
  Atoms = List Atom

data _↝_ {xs : Atoms} : Tm xs → Tm xs → Set where
  app  : ∀ {t : Body xs}{u : Tm xs}
         ----------------------------
         → (ƛ t) · u ↝ [ u /] t
  appL : ∀ {t₁ t₂ u}
         → t₁ ↝ t₂
         -----------------
         → t₁ · u ↝ t₂ · u
  appR : ∀ {t u₁ u₂}
         → u₁ ↝ u₂
         -----------------
         → t · u₁ ↝ t · u₂

infix 5 _↝_ 
