{-# OPTIONS --without-K #-}

module SystemH.Safety where

{-
open import Type
open import Typing
open import Reduction
-}
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
