module Term.Base where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_]; subst)

open import Data.Nat renaming (_≟_ to _≟ℕ_) 
open import Data.Fin renaming (_≟_ to _≟F_) -- hiding (_+_; compare)
open import Data.Product hiding (map)
open import Data.Bool renaming (_≟_ to _≟B_)

open import Name

open import Data.AVL.Sets            lexicographical
open import Data.AVL.Sets.Properties lexicographical

Names : Set
Names = ⟨Set⟩

data RawTm (n : ℕ) (xs : Names) : Set where
  bvar : (i : Fin n)              → RawTm n xs
  fvar : ∀ x (x∈xs : x ∈ xs)      → RawTm n xs
  _·_  : (t₁ t₂ : RawTm n xs  )   → RawTm n xs
  ƛ_   : (t : RawTm (suc n) xs)   → RawTm n xs

infixl 15 _·_
infixr 15 ƛ_

Tm : Names → Set
Tm xs = RawTm 0 xs

Body : Names → Set
Body xs = RawTm 1 xs

CTm : Set
CTm = Tm empty

module _ {xs : Names} where 

  inst : ∀ {n} x (x∉xs : x ∉ xs) → RawTm (suc n) xs → RawTm n (insert x xs)
  inst {n} x x∉xs (bvar i) with n ≟ℕ (toℕ i)
  ... | yes p = fvar x (∈-insert-= xs)
  ... | no ¬p = bvar   (lower₁ i ¬p)
  inst x x∉xs (fvar y y∈xs) = fvar y (∈-insert xs y∈xs)
  inst x x∉xs (t · t₁)      = inst x x∉xs t · inst x x∉xs t₁
  inst x x∉xs (ƛ t)         = ƛ inst x x∉xs t

  abs : ∀ {n} x → RawTm n (insert x xs) → RawTm (suc n) xs
  abs x (bvar i) = bvar (inject₁ i)
  abs {n} x (fvar y y∈xs) with x ≟ y
  ... | yes _ = bvar (fromℕ n)
  ... | no ¬p = fvar y (∈-≉-insert xs ¬p y∈xs)
  abs x (t₁ · t₂) = abs x t₁ · abs x t₂
  abs x (ƛ t)     = ƛ abs x t

  _⁺ : ∀ {n} → RawTm n xs → RawTm (suc n) xs
  (bvar i)  ⁺ = bvar (inject₁ i)
  (fvar x x∈xs) ⁺ = fvar x x∈xs
  (t₁ · t₂) ⁺ = (t₁ ⁺) · (t₂ ⁺)
  (ƛ t) ⁺     = ƛ (t ⁺)

  _⁺Cxt : ∀ {x n} → RawTm n xs → RawTm n (insert x xs)
  (fvar y y∈xs) ⁺Cxt = fvar y (∈-insert xs y∈xs)
  (bvar i) ⁺Cxt  = bvar i
  (t₁ · t₂) ⁺Cxt = (t₁ ⁺Cxt) · (t₂ ⁺Cxt)
  (ƛ t)     ⁺Cxt = ƛ t ⁺Cxt
  
  subst : ∀ {n} → RawTm n xs → RawTm (suc n) xs → RawTm n xs 
  subst {n} u (bvar i)  with n ≟ℕ (toℕ i)
  ... | yes p = u
  ... | no ¬p = bvar (lower₁ i ¬p)
  subst u (fvar x x∈xs) = fvar x x∈xs
  subst u (t · t₁)      = subst u t · subst u t₁
  subst u (ƛ t)         = ƛ subst (u ⁺) t
  
  -- [_/_] : ∀ {n} → RawTm n xs
  --       → ∀ x → RawTm n (x ∷ xs) → RawTm n xs
  -- [ u / x ] (bvar i) = bvar i
  -- [ u / x ] (fvar_ y ⦃ y∈x∷xs ⦄) with x ≟A y
  -- ... | yes _ = u
  -- ... | no ¬p = fvar_ y ⦃ ∈-∷-≢ (λ { refl → ¬p refl}) y∈x∷xs ⦄
  -- [ u / x ] (t₁ · t₂) = [ u / x ] t₁ · [ u / x ] t₂
  -- [ u / x ] (ƛ t)     = ƛ [ u ⁺ / x ] t


  {-
  Tm-perm : ∀ {a b n xs}
          → RawTm n xs → RawTm n (map ⦅ a · b ⦆_ xs)
  Tm-perm {a} {b} (fvar x) = fvar ⦅ a · b ⦆ x
  Tm-perm (bvar i)         = bvar i
  Tm-perm (t₁ · t₂)        = Tm-perm t₁ · Tm-perm t₂
  Tm-perm (ƛ t)            = ƛ Tm-perm t
  -}
