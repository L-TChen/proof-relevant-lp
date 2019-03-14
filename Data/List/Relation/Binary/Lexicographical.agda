{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Lexicographical
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Relation.Nullary
open import Data.Empty
open import Data.List

open import Level

open StrictTotalOrder strictTotalOrder
  renaming (Carrier to A; _≈_ to _∼_; _<_ to _≺_; compare to compareA)

private

  data _≈_ : Rel (List A) (a ⊔ ℓ₁) where
    []  : [] ≈ []
    _∷_ : ∀ {x y xs ys} → (x∼y : x ∼ y) → (xs≈ys : xs ≈ ys) → (x ∷ xs) ≈ (y ∷ ys)

  data _<_ : Rel (List A) (a ⊔  ℓ₁ ⊔ ℓ₂) where
    empty : ∀ {x xs} → [] < (x ∷ xs)
    here  : ∀ {x y xs ys} → (x ≺ y) → (x ∷ xs) < (y ∷ ys)
    there : ∀ {x y xs ys} → x ∼ y → xs < ys → (x ∷ xs) < (y ∷ ys)

  _>_ : Rel (List A) _
  xs > ys = ys < xs

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
  <-transitive (here x<y) (there y∼z ys<zs) = here (<-respʳ-≈ y∼z x<y)
  <-transitive (there x∼y xs<ys) (here y<x)  =
    here (<-respˡ-≈ (IsEquivalence.sym isEquivalence x∼y) y<x)
  <-transitive (there x∼y xs<ys) (there y∼x ys<zs) =
    there (IsEquivalence.trans isEquivalence x∼y y∼x) (<-transitive xs<ys ys<zs)
  <-transitive empty (here _)    = empty
  <-transitive empty (there _ _) = empty

  ∼-∷ : ∀ {x y xs ys}
        → ¬ (x ≺ y) → x ∼ y → ¬ (y ≺ x)
        → Tri (xs < ys) (xs ≈ ys) (xs > ys)
        → Tri ((x ∷ xs) < (y ∷ ys)) ((x ∷ xs) ≈ (y ∷ ys)) ((x ∷ xs) > (y ∷ ys))
  ∼-∷ ¬x≺y x∼y ¬y≺x (tri< a ¬b ¬c) =
    tri< (there x∼y a) (λ { (x∼y ∷ xs≈ys) → ¬b xs≈ys })
      λ { (here y≺x) → ¬y≺x y≺x ; (there _ xs>ys) → ¬c xs>ys }
  ∼-∷ ¬x≺y x∼y ¬y≺x (tri≈ ¬a b ¬c) =
    tri≈ (λ { (here x<y) → ¬x≺y x<y ; (there _ xs<ys) → ¬a xs<ys }) (x∼y ∷ b)
      λ { (here x>y) → ¬y≺x x>y ; (there _ xs>ys) → ¬c xs>ys }
  ∼-∷ ¬x≺y x∼y ¬y≺x (tri> ¬a ¬b c) =
    tri> (λ { (here x≺y) → ¬x≺y x≺y ; (there _ xs<ys) → ¬a xs<ys })
      (λ { (x∼y ∷ xs≈ys) → ¬b xs≈ys }) (there (IsEquivalence.sym isEquivalence x∼y) c)
  
  compare : Trichotomous _≈_ _<_
  compare [] [] = tri≈ (λ ()) [] λ ()
  compare [] (y ∷ ys) = tri< empty (λ ()) λ ()
  compare (x ∷ xs) [] = tri> (λ ()) (λ ()) empty
  compare (x ∷ xs) (y ∷ ys) with compareA x y
  compare (x ∷ xs) (y ∷ ys) | tri< a ¬b ¬c = tri< (here a) (λ { (x∼y ∷ p) → ¬b x∼y })
    λ { (here x≻y) → ¬c x≻y ; (there y∼x _) → ¬b (IsEquivalence.sym isEquivalence y∼x) }
  compare (x ∷ xs) (y ∷ ys) | tri> ¬a ¬b c =
    tri> (λ { (here x≺y) → ¬a x≺y ; (there x∼y _) → ¬b x∼y }) (λ { (x∼y ∷ p) → ¬b x∼y } ) (here c)
  compare (x ∷ xs) (y ∷ ys) | tri≈ ¬a b ¬c = ∼-∷ ¬a b ¬c (compare xs ys) 

lexicographical : StrictTotalOrder a (a ⊔ ℓ₁) (a ⊔ ℓ₁ ⊔ ℓ₂)
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
