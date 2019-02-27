open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Typing (Atom : Set)(_≟A_ : Decidable {A = Atom} _≡_ ) where
open import Data.List
open import Data.Product hiding (map)
open import Data.List.Membership.Propositional

open import Term    Atom _≟A_
open import Type    Atom _≟A_

open import Context Atom Ty

data _⊢_∶_ {ys : Atoms} : (Γ : Cxt ys) → Tm (dom ys Γ) → Ty ys → Set where
  ⊢var : ∀ {Γ x τ}
         → (x∈Γ : (x , τ) ∈ Γ)
         ---------------------------------
         → Γ ⊢ fvar_ x ⦃ ∈-Cxt ys  x∈Γ ⦄ ∶ τ

  ⊢·   : ∀ {Γ e₁ e₂ F₁ F₂}
        → Γ ⊢ e₁ ∶ F₁ ⇒̇ F₂     → Γ ⊢ e₂ ∶ F₁
        ------------------------------------
        → Γ ⊢ e₁ · e₂ ∶ F₂

  ⊢ƛ   : ∀ {x F₁ Γ F₂ e}
        → (x , F₁) ∷ Γ ⊢ e ∶ F₂
        ---------------------------------
        → Γ ⊢ ƛ (abs x e) ∶ F₁ ⇒̇ F₂

  ⊢Gen : ∀ {Γ e y}{ F : Ty (y ∷ ys) }
         → {!!} ⊢ {!!} ∶ F            -- Γ ⊢ t : F
         → Γ ⊢ e ∶ ∀̇ T.abs y F
         
  ⊢∀  : ∀ {Γ e F}
      → Γ ⊢ e ∶ ∀̇ F
      → Γ ⊢ e ∶ {!T.inst ? F!}        -- Γ ⊢ e ∶ [ t / x ] F 

infix 4 _⊢_∶_
