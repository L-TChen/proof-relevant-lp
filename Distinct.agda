module Distinct where 

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Empty
open import Data.Sum hiding (map)
open import Data.List
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties

module _ {A : Set} where

  data Dist : List A → Set where
    []  : Dist []
    _∷_ : ∀ {x xs} (x∉xs : x ∉ xs) → Dist xs → Dist (x ∷ xs)

  [-]-dist : ∀ {x : A} → Dist (x ∷ [])
  [-]-dist = (λ ()) ∷ []

  ∈-++-ins : ∀ {xs ys} {x z : A} → x ∈ xs ++ ys  →  x ∈ xs ++ (z ∷ ys)
  ∈-++-ins {xs} x∈xs++ys with ∈-++⁻ xs x∈xs++ys
  ... | inj₁ x∈xs = ∈-++⁺ˡ x∈xs
  ... | inj₂ x∈ys = ∈-++⁺ʳ xs (there x∈ys)

  ∈-++-≢ : ∀ xs {x : A}{z ys}
         → x ≢ z → x ∈ xs ++ z ∷ ys
         → x ∈ xs ++ ys
  ∈-++-≢ xs x≢z x∈xs++z∷ys with ∈-++⁻ xs x∈xs++z∷ys
  ... | inj₁ x∈xs           = ∈-++⁺ˡ x∈xs
  ... | inj₂ (here px)      = ⊥-elim (x≢z px)
  ... | inj₂ (there x∈z∷ys) = ∈-++⁺ʳ xs x∈z∷ys

  ∈-∷-≢ : ∀ {xs} {x z : A}
         → x ≢ z → x ∈ z ∷ xs
         → x ∈ xs
  ∈-∷-≢ x≢z x∈z∷xs = ∈-++-≢ [] x≢z x∈z∷xs
  
  Dist-rm : ∀ xs {ys}{x : A}
            → Dist (xs ++ x ∷ ys) → Dist (xs ++ ys)
  Dist-rm []        (_ ∷ p) = p
  Dist-rm (_ ∷ xs)  (x∉xs++z∷ys ∷ p) =
    (λ x∈xs++ys → x∉xs++z∷ys (∈-++-ins x∈xs++ys)) ∷ Dist-rm xs p

  Dist-ins : ∀ xs {ys}{z : A}
           → Dist (xs ++ ys) → z ∉ (xs ++ ys)
           → Dist (xs ++ z ∷ ys)
  Dist-ins [] p z∉xs++ys = z∉xs++ys ∷ p
  Dist-ins (x ∷ xs) (x∉xs++ys ∷ p) z∉xs++ys =
    (λ x∈xs++z∷ys → x∉xs++ys (∈-++-≢ xs (λ x≡z → z∉xs++ys (here (sym x≡z)) ) x∈xs++z∷ys))
      ∷ Dist-ins xs p λ z∈xs++ys → z∉xs++ys (there z∈xs++ys)
