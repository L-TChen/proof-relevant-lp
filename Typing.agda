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

data _⊢_∶_ (Γ : Cxt) : Tm (dom Γ) → Typ → Set where
  ⊢var : ∀ {x F}
         → (x∈Γ : (x , F) ∈ Γ)
         ---------------------------------
         → Γ ⊢ fvar_ x ⦃ ∈-Cxt x∈Γ ⦄ ∶ F

  ⊢app : ∀ {ys e₁ e₂} {F₁} {F₂ : Ty ys}
        → Γ ⊢ e₁ ∶ -, F₁ ⇒̇ F₂     → Γ ⊢ e₂ ∶ -, F₁
        ------------------------------------
        → Γ ⊢ e₁ · e₂ ∶ -, F₂

  ⊢abs : ∀ {x ys F₁ e}{F₂ : Ty ys}
        → (x , -, F₁) ∷  Γ ⊢ e ∶ -, F₂
        ---------------------------------
        → Γ ⊢ ƛ (abs x e) ∶ -, F₁ ⇒̇ F₂

  ⊢∀-intro : ∀ {e y ys}{F : Ty (y ∷ ys)}
       → Γ ⊢ e ∶ -, F
       → Γ ⊢ e ∶ -, ∀̇ T.abs y F
         
  ⊢∀-elim  : ∀ {e ys t}{F : TyBody ys}
       → Γ ⊢ e ∶ -, ∀̇ F
       → Γ ⊢ e ∶ -, T.[ t /] F

infix 3 _⊢_∶_
