open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

module Type (Atom : Set)(_≟A_ : Decidable {A = Atom} (_≡_)) where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product hiding (map)

open import Distinct

private
  Atoms : Set
  Atoms = List Atom

Const : Set
Const = Atom

-- the type of terms (inside formulae)
data RawArg (n : ℕ)(xs : Atoms) : Set where
  none  :                                       RawArg n xs 
  bvar_ : (i : Fin n)                         → RawArg n xs
  fvar_ : (x : Atom) ⦃ _ : x ∈ xs ⦄           → RawArg n xs
  κ     : (K : Const) → (a₁ a₂ : RawArg n xs) → RawArg n xs

RawArgs : ℕ → Atoms → Set
RawArgs n xs = List (RawArg n xs)

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

TyBody : Atoms → Set
TyBody = RawTy 1

CArg : Set
CArg = Arg []

CTy : Set
CTy = Ty []

--
module T {xs : Atoms} where
  private
    instArg : ∀ {n} x → RawArg (suc n) xs → RawArg n (x ∷ xs)
    instArg {n} x (bvar i) with n ≟ℕ (toℕ i)
    ... | yes p = fvar x
    ... | no ¬p = bvar lower₁ i ¬p
    instArg x (fvar y)  = fvar y
    instArg x none      = none
    instArg x (κ K a b) = κ K (instArg x a) (instArg x b)
  
  inst : ∀ {n} x → RawTy (suc n) xs → RawTy n (x ∷ xs)
  inst x (At P ts) = At P (map (instArg x) ts)
  inst x (F₁ ⇒̇ F₂) = inst x F₁ ⇒̇ inst x F₂
  inst x (∀̇ F)     = ∀̇ inst x F

  private
    absArg : ∀ {n} x → RawArg n (x ∷ xs) → RawArg (suc n) xs
    absArg x (bvar i) = bvar inject₁ i
    absArg {n} x (fvar_ y ⦃ y∈x∷xs ⦄ ) with x ≟A y
    ... | yes p = bvar (fromℕ n)
    ... | no ¬p = fvar_ y ⦃ ∈-∷-≢ (λ {refl → ¬p refl}) y∈x∷xs ⦄
    absArg x none      = none
    absArg x (κ K a b) = κ K (absArg x a) (absArg x b)

  abs : ∀ {n} x → RawTy n (x ∷ xs) → RawTy (suc n) xs
  abs x (At P ts) = At P (map (absArg x) ts)
  abs x (F ⇒̇ F₁) = abs x F ⇒̇ abs x F₁
  abs x (∀̇ F)    = ∀̇ abs x F

  private
    _⁺arg : ∀ {n} → RawArg n xs → RawArg (suc n) xs
    (bvar i) ⁺arg = bvar inject₁ i
    (fvar x) ⁺arg = fvar x
    none ⁺arg     = none
    κ K a b ⁺arg = κ K (a ⁺arg) (b ⁺arg)

  _⁺ :  ∀ {n} → RawTy n xs → RawTy (suc n) xs
  At P ts ⁺  = At P (map _⁺arg ts)
  (F ⇒̇ F₁) ⁺ = F ⁺ ⇒̇ F₁ ⁺
  (∀̇ F) ⁺    = ∀̇ F ⁺

  private
    _⁺CxtArg : ∀ {n x} → RawArg n xs → RawArg n (x ∷ xs)
    (bvar i) ⁺CxtArg = bvar i
    (fvar x) ⁺CxtArg = fvar x
    none ⁺CxtArg     = none
    κ K a b ⁺CxtArg = κ K (a ⁺CxtArg) (b ⁺CxtArg)
   
  _⁺Cxt : ∀ {n x} → RawTy n xs → RawTy n (x ∷ xs)
  At P as ⁺Cxt  = At P (map _⁺CxtArg as)
  (t ⇒̇ t₁) ⁺Cxt = (t ⁺Cxt) ⇒̇ (t₁ ⁺Cxt)
  (∀̇ t) ⁺Cxt    = ∀̇ (t ⁺Cxt)

  [_/_]arg : ∀ {n} → RawArg n xs
           → ∀ x → RawArg n (x ∷ xs) → RawArg n xs
  [ u / x ]arg (bvar i) = bvar i
  [ u / x ]arg (fvar_ y ⦃ y∈x∷xs ⦄) with x ≟A y
  ... | yes _ = u
  ... | no ¬p = fvar_ y ⦃ ∈-∷-≢ ((λ {refl → ¬p refl})) y∈x∷xs ⦄
  [ u / x ]arg none     = none
  [ u / x ]arg (κ K a b) = κ K ([ u / x ]arg a) ([ u / x ]arg b)

  [_/_] : ∀ {n} → RawArg n xs
          → ∀ x → RawTy n (x ∷ xs) → RawTy n xs
  [ u / x ] (At P as) = At P (map [ u / x ]arg as)
  [ u / x ] (t ⇒̇ t₁)  = [ u / x ] t ⇒̇ [ u / x ] t₁
  [ u / x ] (∀̇ t)     = ∀̇ [ u ⁺arg / x ] t

  [_/] : Arg xs → TyBody xs → Ty xs
  [_/] u t =  [ u / proj₁ z ] (inst (proj₁ z) t)
    where
      postulate fresh-gen : (xs : Atoms) → Σ[ x ∈ Atom ] (x ∉ xs)
      z = fresh-gen xs
