open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module Permutation (Atom : Set)( _≟A_ : Decidable {A = Atom} (_≡_)) where

open import Data.List
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Empty

open import Distinct

⦅_·_⦆_ : Atom → Atom → Atom → Atom
⦅ a · b ⦆ x with a ≟A x
... | yes p = b
... | no ¬p with b ≟A x
... | yes q = a
... | no ¬q = x

infixr 20 ⦅_·_⦆_

⦅a·b⦆a=b : ∀ {a b} → ⦅ a · b ⦆ a ≡ b
⦅a·b⦆a=b {a} {b} with a ≟A a
... | yes p = refl
... | no ¬p = ⊥-elim (¬p refl)

⦅a·b⦆b=a : ∀ {a b} → ⦅ a · b ⦆ b ≡ a
⦅a·b⦆b=a {a} {b} with a ≟A b
... | yes refl = refl
... | no ¬p with b ≟A b
... | yes q = refl
... | no ¬q = ⊥-elim (¬q refl)

⦅a·b⦆x=x : ∀ {a b x} → a ≢ x → b ≢ x → ⦅ a · b ⦆ x ≡ x
⦅a·b⦆x=x {a} {b} {x} a≢x b≢x with a ≟A x
... | yes p = ⊥-elim (a≢x p)
... | no ¬p with b ≟A x
... | yes q = ⊥-elim (b≢x q)
... | no ¬q = refl

perm-bijection : ∀ {a b} x → ⦅ a · b ⦆ ⦅ a · b ⦆ x ≡ x
perm-bijection {a} {b} x with a ≟A x
... | yes refl rewrite ⦅a·b⦆a=b {a} {b} | ⦅a·b⦆b=a {a} {b} = refl
... | no ¬p with b ≟A x
... | yes refl rewrite ⦅a·b⦆b=a {a} {b} | ⦅a·b⦆a=b {a} {b} = refl
... | no ¬q = ⦅a·b⦆x=x ¬p ¬q

map-perm-bijection : ∀ {a b} xs → map ⦅ a · b ⦆_ (map ⦅ a · b ⦆_ xs) ≡ xs
map-perm-bijection [] = refl
map-perm-bijection (x ∷ xs) = cong₂ _∷_ (perm-bijection x) (map-perm-bijection xs)

map-perm-∈⁻ : ∀ {a b x xs} → ⦅ a · b ⦆ x ∈ map ⦅ a · b ⦆_ xs → x ∈ xs
map-perm-∈⁻ {a} {b} {x} {[]} ()
map-perm-∈⁻ {a} {b} {x} {y ∷ xs} (there x∈xs) = there (map-perm-∈⁻ x∈xs)
map-perm-∈⁻ {a} {b} {x} {y ∷ xs} (here px) = here (begin
  x                        ≡⟨ sym (perm-bijection x) ⟩
  ⦅ a · b ⦆ ⦅ a · b ⦆ x ≡⟨ cong ⦅ a · b ⦆_ px ⟩
  ⦅ a · b ⦆ ⦅ a · b ⦆ y ≡⟨ perm-bijection y ⟩
  y                        ∎)
  where open ≡-Reasoning

map-perm-∈⁺ : ∀ {xs a b x} → x ∈ xs → ⦅ a · b ⦆ x ∈ map ⦅ a · b ⦆_ xs
map-perm-∈⁺ {[]} ()
map-perm-∈⁺ {y ∷ xs} (there x∈xs)      = there (map-perm-∈⁺ x∈xs)
map-perm-∈⁺ {y ∷ xs} {a} {b} (here px) = here (cong ⦅ a · b ⦆_ px)

perm-dist : ∀ {a b xs} → Dist xs → Dist (map ⦅ a · b ⦆_ xs)
perm-dist [] = []
perm-dist (x∉xs ∷ xs) =
  (λ ⦅ab⦆x∈map⦅ab⦆xs → x∉xs (map-perm-∈⁻ ⦅ab⦆x∈map⦅ab⦆xs) ) ∷ perm-dist xs
