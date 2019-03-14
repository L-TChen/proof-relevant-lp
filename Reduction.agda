module Reduction where

open import Term
open import Name
open import Data.AVL.Sets            lexicographical
open import Data.AVL.Sets.Properties lexicographical

data _↝_ {xs : Names} : Tm xs → Tm xs → Set where
  app  : ∀ {t : Body xs}{u : Tm xs}
         ----------------------------
         → (ƛ t) · u ↝ subst u t
         
  appL : ∀ {t₁ t₂ u}
         → t₁ ↝ t₂
         -----------------
         → t₁ · u ↝ t₂ · u

  appR : ∀ {t u₁ u₂}
         → u₁ ↝ u₂
         -----------------
         → t · u₁ ↝ t · u₂

infix 5 _↝_ 
