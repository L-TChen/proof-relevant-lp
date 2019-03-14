{-# OPTIONS --without-K --safe #-}
module Sets where

open import Relation.Binary using (StrictTotalOrder)
open import Data.Bool
open import Data.List.Base as List using (List)
open import Data.Maybe.Base as Maybe
open import Data.Product as Prod using (_×_; _,_; proj₁)
open import Data.Unit
open import Function
open import Level

import Data.AVL

⟨Set⟩ : ∀ {a ℓ₁ ℓ₂} → StrictTotalOrder a ℓ₁ ℓ₂ → Set (a ⊔ ℓ₂)
⟨Set⟩ A = Data.AVL.Tree A (Data.AVL.const A ⊤)

------------------------------------------------------------------------
-- Repackaged functions

module _ {a ℓ₁ ℓ₂} {A≤ : StrictTotalOrder a ℓ₁ ℓ₂} where
  open StrictTotalOrder A≤ renaming (Carrier to A)
  
  module AVL = Data.AVL A≤

  empty : ⟨Set⟩ A≤
  empty = AVL.empty

  singleton : A → ⟨Set⟩ A≤
  singleton k = AVL.singleton k _

  insert : A → ⟨Set⟩ A≤ → ⟨Set⟩ A≤
  insert k = AVL.insert  k _

  delete : A → ⟨Set⟩ A≤ → ⟨Set⟩ A≤
  delete = AVL.delete  

  infix 4 _∈?_

  _∈?_ : A → ⟨Set⟩ A≤ → Bool
  _∈?_ = AVL._∈?_ 

  headTail : ⟨Set⟩ A≤ → Maybe (A × ⟨Set⟩ A≤)
  headTail s = Maybe.map (Prod.map₁ proj₁) (AVL.headTail  s)

  initLast : ⟨Set⟩ A≤ → Maybe (⟨Set⟩ A≤ × A)
  initLast s = Maybe.map (Prod.map₂ proj₁) (AVL.initLast  s)

  fromList : List A → ⟨Set⟩ A≤
  fromList = AVL.fromList  ∘ List.map (_, _)

  toList : ⟨Set⟩ A≤ → List A
  toList = List.map proj₁ ∘ AVL.toList  
