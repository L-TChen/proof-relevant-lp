open import Data.List

module Context (Atom : Set)(Type : List Atom → Set) where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.List.Properties
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Empty

open import Distinct

open import Type Atom 

module _ (xs : List Atom) where

  Cxt : Set
  Cxt = List (Atom × Type xs)

  dom : Cxt → List Atom
  dom = map proj₁

  cod : Cxt → List (Type xs)
  cod = map proj₂

  map-∈-ins : ∀ (Γ : Cxt) {x τ Δ} → x ∈ dom (Γ ++ (x , τ) ∷ Δ)
  map-∈-ins Γ {x} {τ} {Δ}
      rewrite map-++-commute proj₁ Γ ((x , τ) ∷ Δ) = ∈-insert (dom Γ)
      
  ∈-Cxt : ∀ {Γ x τ} → (x , τ) ∈ Γ → x ∈ dom Γ
  ∈-Cxt = ∈-map⁺ proj₁

  DomDist : Cxt → Set
  DomDist xs = Dist (dom xs)

  DomDist-rm : ∀ (Γ : Cxt) x {Δ τ}
           → DomDist (Γ ++ (x , τ) ∷ Δ) → DomDist (Γ ++ Δ)
  DomDist-rm Γ x {Δ} {τ} p
    rewrite map-++-commute proj₁ Γ ((x , τ) ∷ Δ)
          | map-++-commute proj₁ Γ Δ = Dist-rm (dom Γ) p

  DomDist-ins : ∀ (Γ : Cxt) {x Δ τ}
                 → DomDist (Γ ++ Δ)
                 → x ∉ dom (Γ ++ Δ)
                 → DomDist (Γ ++ (x , τ) ∷ Δ)
  DomDist-ins Γ {x} {Δ} {τ} p x∉domΓ++Δ
    rewrite map-++-commute proj₁ Γ Δ
          | map-++-commute proj₁ Γ ((x , τ) ∷ Δ) = Dist-ins (dom Γ) p x∉domΓ++Δ

  Cxt-≡ : ∀ (Γ : Cxt) x {τ σ Δ} 
            → DomDist   (Γ ++ (x , τ) ∷ Δ)
            → (x , σ) ∈ (Γ ++ (x , τ) ∷ Δ) 
            → σ ≡ τ
  Cxt-≡ [] x p (here refl) = refl
  Cxt-≡ [] x (x∉xs ∷ p) (there x∈Γ++Δ) = ⊥-elim (x∉xs (∈-map⁺ proj₁ x∈Γ++Δ))
  Cxt-≡ (_ ∷ Γ) x {τ} {_} {Δ} (y∉xs ∷ p) (here refl)
    rewrite map-++-commute proj₁ Γ ((x , τ) ∷ Δ) = ⊥-elim (y∉xs (∈-insert (dom Γ))) 
  Cxt-≡ (_ ∷ Γ) x (y∉xs ∷ p) (there x∈Γ++Δ) = Cxt-≡ Γ x p x∈Γ++Δ

  Cxt-≢ : ∀ (Γ : Cxt) x {τ Δ y σ} 
            → DomDist (Γ ++ (x , τ) ∷ Δ) → x ≢ y
            → (y , σ) ∈ Γ ++ (x , τ) ∷ Δ
            → (y , σ) ∈ Γ ++ Δ
  Cxt-≢ Γ x {τ} {Δ} p x≢y y∈Γ++x∷Δ with ∈-++⁻ Γ y∈Γ++x∷Δ
  ... | inj₂ (here refl)   = ⊥-elim (x≢y refl)
  ... | inj₂ (there y∈x∷Δ) = ∈-++⁺ʳ Γ y∈x∷Δ
  ... | inj₁ y∈Γ           = ∈-++⁺ˡ y∈Γ 


Cxt-Ty : ∀ {y ys}(f : Type ys → Type (y ∷ ys))
       → Cxt ys → Cxt (y ∷ ys)
Cxt-Ty f [] = []
Cxt-Ty f ((x , τ) ∷ Γ) = (x , f τ) ∷ Cxt-Ty f Γ
