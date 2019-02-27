open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

module Type (Atom : Set)(_≟A_ : Decidable {A = Atom} (_≡_)) where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)

open import Distinct

private
  Atoms : Set
  Atoms = List Atom

Const : Set
Const = Atom

-- the type of terms (inside formulae)
mutual
  RawArgs : ℕ → Atoms → Set
  RawArgs n xs = List (RawArg n xs)
  
  data RawArg (n : ℕ)(xs : Atoms) : Set where
    bvar_ : (i : Fin n)                      → RawArg n xs
    fvar_ : (x : Atom) ⦃ _ : x ∈ xs ⦄        → RawArg n xs 
    Con   : (K : Const) → (as : RawArgs n xs) → RawArg n xs

-- the type of formulae
data RawTy (n : ℕ)(xs : Atoms) : Set where
  At  : (P : Atom) → (as : RawArgs n xs)
        → RawTy n xs
  _⇒̇_ : (F₁ F₂ : RawTy n xs)
        → RawTy n xs
  ∀̇_  : RawTy (suc n) xs
        → RawTy n xs

infixr 15 _⇒̇_
infixr 10 ∀̇_

Arg : Atoms → Set
Arg = RawArg 0

Ty : Atoms → Set
Ty = RawTy 0

CArg : Set
CArg = Arg []

CTy : Set
CTy = Ty []

--
module T {xs : Atoms} where
  private
    {-# TERMINATING #-} 
    instArg : ∀ {n} x → RawArg (suc n) xs → RawArg n (x ∷ xs)
    instArg {n} x (bvar i) with n ≟ℕ (toℕ i)
    ... | yes p = fvar x
    ... | no ¬p = bvar lower₁ i ¬p 
    instArg x (fvar y)   = fvar y
    instArg x (Con K as) = Con K (map (instArg x) as)
  
  inst : ∀ {n} x → RawTy (suc n) xs → RawTy n (x ∷ xs)
  inst x (At P ts) = At P (map (instArg x) ts)
  inst x (F₁ ⇒̇ F₂) = inst x F₁ ⇒̇ inst x F₂
  inst x (∀̇ F) = ∀̇ inst x F

  private
    {-# TERMINATING #-}
    absArg : ∀ {n} x → RawArg n (x ∷ xs) → RawArg (suc n) xs
    absArg x (bvar i) = bvar inject₁ i
    absArg {n} x (fvar_ y ⦃ y∈x∷xs ⦄ ) with x ≟A y
    ... | yes p = bvar (fromℕ n)
    ... | no ¬p = fvar_ y ⦃ ∈-∷-≢ (λ {refl → ¬p refl}) y∈x∷xs ⦄
    absArg x (Con K as) = Con K (map (absArg x) as)

  abs : ∀ {n} x → RawTy n (x ∷ xs) → RawTy (suc n) xs
  abs {n} x (At P ts) = At P (map (absArg x) ts)
  abs x (F ⇒̇ F₁) = abs x F ⇒̇ abs x F₁
  abs x (∀̇ F)    = ∀̇ abs x F

  private
    {-# TERMINATING #-}
    _⁺arg : ∀ {n} → RawArg n xs → RawArg (suc n) xs
    (bvar i) ⁺arg = bvar inject₁ i
    (fvar x) ⁺arg = fvar x
    Con K as ⁺arg = Con K (map _⁺arg as)

  _⁺ :  ∀ {n} → RawTy n xs → RawTy (suc n) xs
  At P ts ⁺  = At P (map _⁺arg ts)
  (F ⇒̇ F₁) ⁺ = F ⁺ ⇒̇ F₁ ⁺
  (∀̇ F) ⁺    = ∀̇ F ⁺

  private
    {-# TERMINATING #-}
    _⁺CxtArg : ∀ {n x} → RawArg n xs → RawArg n (x ∷ xs)
    (bvar i) ⁺CxtArg = bvar i
    (fvar x) ⁺CxtArg = fvar x
    Con K as ⁺CxtArg = Con K (map _⁺CxtArg as)
    
  _⁺Cxt : ∀ {n x} → RawTy n xs → RawTy n (x ∷ xs)
  At P as ⁺Cxt  = At P (map _⁺CxtArg as)
  (t ⇒̇ t₁) ⁺Cxt = (t ⁺Cxt) ⇒̇ (t₁ ⁺Cxt)
  (∀̇ t) ⁺Cxt    = ∀̇ (t ⁺Cxt)

  {-# TERMINATING #-}
  [_/_]arg : ∀ {n} → RawArg n xs
           → ∀ x → RawArg n (x ∷ xs) → RawArg n xs
  [ u / x ]arg (bvar i) = bvar i
  [ u / x ]arg (fvar_ y ⦃ y∈x∷xs ⦄) with x ≟A y
  ... | yes _ = u
  ... | no ¬p = fvar_ y ⦃ ∈-∷-≢ ((λ {refl → ¬p refl})) y∈x∷xs ⦄ 
  [ u / x ]arg (Con K as) = Con K (map ([ u / x ]arg) as)
   
