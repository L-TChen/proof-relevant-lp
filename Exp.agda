module Exp where

open import Data.Nat
open import Data.Fin
open import Data.Product using (_×_)
open import Data.String
open import Data.List

Name : Set
Name = String

Names : Set
Names = List Name

BName : ℕ → Set
BName = Fin

data Term : ℕ → Set where
  bv : ∀ {n} → (i : BName n) → Term n
  fv : ∀ {n} → (x : Name) → Term n
  op : ∀ {n} → (k : Name) → (args : List (Term n)) → Term n 

data Atom : ℕ → Set where
  _⦅_⦆ : ∀ {n} → (P : Name) → (args : List (Term n)) → Atom n
  
data Typ : ℕ → Set where
  At  : ∀ {n} → (at : Atom n) → Typ n
  _⇒_ : ∀ {n} → Typ n → Typ n → Typ n
  ∀̇   : ∀ {n} → Typ (suc n) → Typ n

infixr 20 _⇒_

data Proof : ℕ → Set where
  const : ∀ {n} → (k : Name) → Proof n
  bv  : ∀ {n} → (i : BName n) → Proof n
  fv  : ∀ {n} → (x : Name) → Proof n
  _·_ : ∀ {n} → (e₁ e₂ : Proof n) → Proof n
  ƛ   : ∀ {n} → (e : Proof (suc n)) → Proof n

∀̇ⁿ_ : ∀ {n} → Typ n → Typ 0
∀̇ⁿ_ {zero} t = t
∀̇ⁿ_ {suc n} t = ∀̇ⁿ (∀̇ t)

infix 10 ∀̇ⁿ_

[_]⇒_ : ∀ {n} → List (Typ n) → Typ n → Typ n
[ [] ]⇒ y = y
[ x ∷ xs ]⇒ y = x ⇒ [ xs ]⇒ y

infix 30 [_]⇒_

Horn : ∀ n → List (Atom n) → Atom n → Typ 0 
Horn n bd hd = ∀̇ⁿ [ map At bd ]⇒ (At hd)

-- Pred3(Y) :- Pred1(X), Pred2(Y)
sample : Typ 0
sample = Horn 2
  ("Pred1" ⦅ fv "x" ∷ [] ⦆ ∷ ("Pred2" ⦅ fv "y" ∷ [] ⦆) ∷ []) ("Pred3" ⦅ fv "y" ∷ [] ⦆ )
