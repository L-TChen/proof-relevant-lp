{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Lexicographical
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Empty
open import Data.List

open import Level

open StrictTotalOrder strictTotalOrder
  renaming (Carrier to A; _≈_ to _∼_; _<_ to _≺_; compare to compareA)

data _≈_ : Rel (List A) (a ⊔ ℓ₁) where
  []  : [] ≈ []
  _∷_ : ∀ {x y xs ys} → (x∼y : x ∼ y) → (xs≈ys : xs ≈ ys) → (x ∷ xs) ≈ (y ∷ ys)

data _<_ : Rel (List A) (a ⊔ ℓ₂) where
  here  : ∀ {x y xs ys} → (x ≺ y) → (x ∷ xs) < (y ∷ ys)
  there : ∀ {x xs ys} → xs < ys → (x ∷ xs) < (x ∷ ys)
  empty : ∀ {x xs} → [] < (x ∷ xs)

private
  ≈-refl : Reflexive _≈_
  ≈-refl {[]} = []
  ≈-refl {x ∷ xs} = refl ∷ ≈-refl {xs}
    where open IsEquivalence isEquivalence

  ≈-sym : Symmetric _≈_
  ≈-sym [] = []
  ≈-sym (x∼y ∷ xs≈ys) = sym x∼y ∷ ≈-sym xs≈ys
    where open IsEquivalence isEquivalence

  ≈-trans : Transitive _≈_
  ≈-trans [] [] = []
  ≈-trans (x∼y ∷ xs≈ys) (y∼z ∷ ys≈zs) =
    IsEquivalence.trans isEquivalence x∼y y∼z ∷ ≈-trans xs≈ys ys≈zs
  
  ≈-isEquivalence : IsEquivalence _≈_
  ≈-isEquivalence =
    record
      { refl  = ≈-refl
      ; sym   = ≈-sym
      ; trans = ≈-trans
      }
    where open IsEquivalence isEquivalence 

  <-transitive : Transitive _<_
  <-transitive (here x≺y) (here y≺z) = here (trans x≺y y≺z)
  <-transitive (here x) (there _) = here x
  <-transitive (there _) (here x) = here x
  <-transitive (there xs) (there ys) = there (<-transitive xs ys)
  <-transitive empty (here x) = empty
  <-transitive empty (there ys) = empty

  compare : Trichotomous _≈_ _<_
  compare [] [] = tri≈ (λ ()) [] λ ()
  compare [] (x ∷ ys) = tri< empty (λ ()) (λ ())
  compare (x ∷ xs) [] = tri> (λ ()) (λ ()) empty
  compare (x ∷ xs) (y ∷ ys) with compareA x y
  compare (x ∷ xs) (y ∷ ys) | tri< a ¬b ¬c = tri< (here a) {!!} {!!}
  compare (x ∷ xs) (y ∷ ys) | tri≈ ¬a b ¬c = {!!} -- compare xs ys
  compare (x ∷ xs) (y ∷ ys) | tri> ¬a ¬b c = tri> {!!} {!!} (here c)

lexicographical : StrictTotalOrder a (a ⊔ ℓ₁) (a ⊔ ℓ₂)
lexicographical =
  record
    { Carrier = List A
    ; _≈_ = _≈_
    ; _<_ = _<_
    ; isStrictTotalOrder = record
        { isEquivalence = ≈-isEquivalence
        ; trans         = <-transitive
        ; compare       = compare
        }
    }
