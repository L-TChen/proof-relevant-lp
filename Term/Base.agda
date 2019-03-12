open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

module Term.Base (Atom : Set)(_≟A_ : Decidable {A = Atom} (_≡_)) where

open import Relation.Nullary
open import Data.Nat renaming (_≟_ to _≟ℕ_) 
open import Data.Fin renaming (_≟_ to _≟F_) -- hiding (_+_; compare)
open import Data.Product hiding (map)
open import Data.AVL.Sets
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)

open import Distinct

private 
  Atoms : Set
  Atoms = List Atom
  
data RawTm (n : ℕ) : (xs : Atoms) → Dist xs → Set where
  bvar : ∀ {xs p}  (i : Fin n)              → RawTm n xs p
  fvar : ∀ {xs ys} x {p}                    → RawTm n (xs ++ x ∷ ys) p
  _·_  : ∀ {xs p}  (t₁ t₂ : RawTm n xs p)   → RawTm n xs p
  ƛ_   : ∀ {xs p}  (t : RawTm (suc n) xs p) → RawTm n xs p

infixl 15 _·_
infixr 15 ƛ_

Tm : ∀ (xs : Atoms) → Set
Tm xs = ∀ {p} → RawTm 0 xs p

Body : ∀ (xs : Atoms) → Set
Body xs = ∀ {p} → RawTm 1 xs p

CTm : Set
CTm = Tm []

--module _ {xs : Atoms} where 

--  inst : ∀ {n} x → RawTm (suc n) xs → RawTm n (x ∷ xs) 
--  inst x t = ?

  -- abs : ∀ {n} x → RawTm n (x ∷ xs) → RawTm (suc n) xs
  -- abs x (bvar i) = bvar inject₁ i
  -- abs {n} x (fvar_ y ⦃ y∈xs++x∷ys ⦄) with x ≟A y
  -- ... | yes _ = bvar fromℕ n
  -- ... | no ¬p = fvar_ y ⦃ ∈-∷-≢ (λ {refl → ¬p refl}) y∈xs++x∷ys ⦄
  -- abs x (t₁ · t₂) = abs x t₁ · abs x t₂
  -- abs x (ƛ t)     = ƛ abs x t

  -- _⁺ : ∀ {n} → RawTm n xs → RawTm (suc n) xs
  -- (bvar i)  ⁺ = bvar (inject₁ i)
  -- (fvar x)  ⁺ = fvar x
  -- (t₁ · t₂) ⁺ = (t₁ ⁺) · (t₂ ⁺)
  -- (ƛ t) ⁺     = ƛ (t ⁺)

  -- [_/_] : ∀ {n} → RawTm n xs
  --       → ∀ x → RawTm n (x ∷ xs) → RawTm n xs
  -- [ u / x ] (bvar i) = bvar i
  -- [ u / x ] (fvar_ y ⦃ y∈x∷xs ⦄) with x ≟A y
  -- ... | yes _ = u
  -- ... | no ¬p = fvar_ y ⦃ ∈-∷-≢ (λ { refl → ¬p refl}) y∈x∷xs ⦄
  -- [ u / x ] (t₁ · t₂) = [ u / x ] t₁ · [ u / x ] t₂
  -- [ u / x ] (ƛ t)     = ƛ [ u ⁺ / x ] t

  -- [_/] : Tm xs → Body xs → Tm xs
  -- [_/] u t =  [ u / proj₁ z ] (inst (proj₁ z) t)
  --   where
  --     postulate fresh-gen : (xs : Atoms) → Σ[ x ∈ Atom ] (x ∉ xs)
  --     z = fresh-gen xs

  -- _⁺Cxt : ∀ {x n} → RawTm n xs → RawTm n (x ∷ xs)
  -- (fvar y) ⁺Cxt  = fvar y
  -- (bvar i) ⁺Cxt  = bvar i
  -- (t₁ · t₂) ⁺Cxt = (t₁ ⁺Cxt) · (t₂ ⁺Cxt)
  -- (ƛ t)     ⁺Cxt = ƛ t ⁺Cxt

  -- {-
  -- Tm-perm : ∀ {a b n xs}
  --         → RawTm n xs → RawTm n (map ⦅ a · b ⦆_ xs)
  -- Tm-perm {a} {b} (fvar x) = fvar ⦅ a · b ⦆ x
  -- Tm-perm (bvar i)         = bvar i
  -- Tm-perm (t₁ · t₂)        = Tm-perm t₁ · Tm-perm t₂
  -- Tm-perm (ƛ t)            = ƛ Tm-perm t
  -- -}
