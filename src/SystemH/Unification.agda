open import Data.Nat as N
open import Relation.Binary
  hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

module SystemH.Unification (Op At : ℕ → Set)
  (_≟op_ : ∀ {n} → Decidable {A = Op n} _≡_)
  (_≟at_ : ∀ {n} → Decidable {A = At n} _≡_) where

open import Relation.Nullary
open import Data.Maybe as M
open import Data.Fin   as F
  hiding (_+_)
open import Data.Vec
  hiding (_>>=_; _++_)
open import Data.Product
open import Function

open import SystemH.Type.Base Op At

thin : Fin (suc Ξ) → Fin Ξ → Fin (suc Ξ)
thin = punchIn

thick : (x y : Fin (suc Ξ)) → Maybe (Fin Ξ)
thick x y with x F.≟ y
... | no neq = just (punchOut neq)
... | yes _  = nothing

sequence : {A : Set} → (Fin Ξ → Maybe A) → Maybe (Fin Ξ → A)
sequence xs = M.map lookup (mayTabulate xs)
  where
    mayTabulate : {A : Set} → (Fin Ξ → Maybe A) → Maybe (Vec A Ξ)
    mayTabulate {Ξ = 0F}    σ = just []
    mayTabulate {Ξ = suc n} σ = σ 0F >>= λ a → M.map (a ∷_) (mayTabulate (σ ∘ suc))

check : Fin (suc Ξ) → Tm (suc Ξ) {d} → Maybe (Tm Ξ)
check i (var x)   = M.map var (thick i x)
check i (op K ts) = M.map (op K) (sequence $ (check i) ∘ ts)

[_↦_]_ : Fin (suc Ξ) → Tm Ξ → Fin (suc Ξ) → Tm Ξ
[ i ↦ u ] j = maybe var u (thick i j)

data AList (Ξ : ℕ) : ℕ → Set where
  []    : AList Ξ Ξ
  _∷_/_ : AList Ξ m → (t : Tm m) → (i : Fin (suc m)) → AList Ξ (suc m)

AList′ : ℕ → Set
AList′ m = ∃[ n ] AList n m

pattern []′    = _ , []

_∷′_/_ : AList′ Ξ → Tm Ξ → Fin (suc Ξ) → AList′ (suc Ξ)
(_ , σ) ∷′ t / i = -, σ ∷ t / i

sub : AList Ξ m → (Fin m → Tm Ξ)
sub []          = var
sub (σ ∷ t / i) = sub σ ◇ [ i ↦ t ]_

sub′ : AList′ Ξ → ∃[ m ] (Fin Ξ → Tm m)
sub′ (- , as) = -, sub as

flexFlex : (x y : Fin Ξ) → AList′ Ξ
flexFlex {suc _} x y with thick x y
... | just y′ = []′ ∷′ var y′ / x
... | nothing = []′

flexRigid : Fin Ξ → Tm Ξ {d} → Maybe (AList′ Ξ)
flexRigid {suc m} x t =
  check x t >>= just ∘ ([]′ ∷′_/ x)

amguTm  : (t  u  : Tm  Ξ {d})   → AList′ Ξ → Maybe (AList′ Ξ)
amguTms : (ts us : Tms Ξ {d} n) → AList′ Ξ → Maybe (AList′ Ξ)

amguTm (op {n₁} K₁ ts) (op {n₂} K₂ us) acc with n₁ N.≟ n₂
... | no  _ = nothing
... | yes refl with K₁ ≟op K₂
... | no  _ = nothing
... | yes _ = amguTms ts us acc
amguTm (var x) (var y)    []′ = just (flexFlex x y)
amguTm (var x) u          []′ = flexRigid x u
amguTm t       (var y)    []′ = flexRigid y t
amguTm t       u          (_ , σ ∷ r / z) =
  M.map (_∷′ r / z) (amguTm ([ [ z ↦ r ]_ ]tm t) ([ [ z ↦ r ]_ ]tm u) (-, σ))

amguTms {n = zero}  ts us acc = just acc
amguTms {n = suc n} ts us acc = amguTm (ts 0F) (us 0F) acc
  >>= amguTms (ts ∘ suc) (us ∘ suc)

mguTm  : (t u : Tm Ξ) → Maybe (AList′ Ξ)
mguTm t u = amguTm t u []′

mguAt : (φ : Atom Ξ n) (ψ : Atom Ξ m)
  → Maybe (∃[ Ξ′ ] (Fin Ξ → Tm Ξ′))
mguAt {n = n} {m = m} (φ , ts) (ψ , us) with n N.≟ m
... | no _     = nothing
... | yes refl with φ ≟at ψ
... | no _  = nothing
... | yes _ = M.map sub′ (amguTms ts us []′)
