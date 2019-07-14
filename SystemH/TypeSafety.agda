{-# OPTIONS --cubical #-}

module TypeSafety where

open import Data.Empty using (⊥-elim)
open import Data.String using (String) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_; yes; no)
open import Data.Nat using (_+_)

open import FiniteSets.Kuratowski

open import Exp
open import Typing
open import Assoc
open import Infrastructure

open import FVars

open import Reduction

preservation : ∀ {e e' : Expr} {τ}
                → ∅ , ∅ ⊢ e ∶ τ 
                → e ⟼ e'
                → ∅ , ∅ ⊢ e' ∶ τ
preservation = {!!}

progress : ∀ {e : Expr} {τ}
           → ∅ , ∅ ⊢ e ∶ τ 
           → ¬ (Val e)
           → ∃ (λ e' → e ⟼ e')
progress = {!!}
