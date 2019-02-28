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


open import Reduction Atom _≟A_
{-
substitution : ∀ {Γ F t u} → Γ ⊢ t ∶ F → Γ ⊢ [ u /] t ∶ F
substitution = ?
-}
preservation : ∀ {Γ F e e′} → Γ ⊢ e ∶ F → e ↝ e′ → Γ ⊢ e′ ∶ F
preservation (⊢var x∈Γ) ()
preservation (⊢app Γ⊢e∶F Γ⊢e∶F₁) app         = {!!}
preservation (⊢app Γ⊢e₁∶F₁⇒F₂ Γ⊢u₁∶F₁) (appR u₁↝u₂) =
  ⊢app  Γ⊢e₁∶F₁⇒F₂ (preservation Γ⊢u₁∶F₁ u₁↝u₂)
preservation (⊢abs Γ⊢e∶F) ()
preservation (⊢∀-intro Γ⊢e∶F) app = {!!}
preservation (⊢∀-intro (⊢app Γ⊢t·u₁∶F Γ⊢t·u₁∶F₁)) (appR e↝e′) =
  ⊢∀-intro (⊢app Γ⊢t·u₁∶F (preservation Γ⊢t·u₁∶F₁ e↝e′))
preservation (⊢∀-intro (⊢∀-intro Γ⊢t·u₁∶F))       (appR e↝e′) =
  ⊢∀-intro (⊢∀-intro (preservation Γ⊢t·u₁∶F (appR e↝e′)))
preservation (⊢∀-intro (⊢∀-elim Γ⊢t·u₁∶F))        (appR e↝e′) =
  ⊢∀-intro (⊢∀-elim (preservation Γ⊢t·u₁∶F (appR e↝e′)))
preservation (⊢∀-elim Γ⊢e∶F) app = {!!}
preservation (⊢∀-elim Γ⊢e∶F) (appR e↝e′) =
  ⊢∀-elim (preservation Γ⊢e∶F (appR e↝e′))
