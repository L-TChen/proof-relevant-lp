open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Typing (Atom : Set)(_≟A_ : Decidable {A = Atom} _≡_ ) where
open import Data.List
open import Data.Product hiding (map)
open import Data.List.Membership.Propositional

open import Term    Atom _≟A_
open import Type    Atom _≟A_
open import Context Atom _≟A_

private
  Atoms : Set
  Atoms = List Atom

data _⊢_∶_ : (Γ : Cxt) → Tm (dom Γ) → Typ → Set where
  ⊢var : ∀ {Γ x τ}
         → (x∈Γ : (x , τ) ∈ Γ)
         ---------------------------------
         → Γ ⊢ fvar_ x ⦃ ∈-Cxt x∈Γ ⦄ ∶ τ

  ⊢·   : ∀ {Γ ys e₁ e₂} {F₁} {F₂ : Ty ys}
        → Γ ⊢ e₁ ∶ (_ , F₁ ⇒̇ F₂)     → Γ ⊢ e₂ ∶ (_ , F₁)
        ------------------------------------
        → Γ ⊢ e₁ · e₂ ∶ (_ , F₂)

  ⊢ƛ   : ∀ {x ys F₁ Γ e}{F₂ : Ty ys}
        → (x , (_ , F₁)) ∷  Γ ⊢ e ∶ (_ , F₂)
        ---------------------------------
        → Γ ⊢ ƛ (abs x e) ∶ ((_ , F₁ ⇒̇ F₂))

  ⊢∀-intro : ∀ {Γ e y ys F}
       → Γ ⊢ e ∶ (y ∷ ys , F)
       → Γ ⊢ e ∶ (ys , ∀̇ T.abs y F)
         
  ⊢∀-elim  : ∀ {Γ e ys t}{F : TyBody ys}
       → Γ ⊢ e ∶ (_ , ∀̇ F)
       → Γ ⊢ e ∶ (_ , let z = proj₁ (fresh-gen ys) in T.[_/_] t z (T.inst z F))

infix 4 _⊢_∶_
