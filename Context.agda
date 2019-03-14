{-# OPTIONS --allow-unsolved-metas #-}

module Context where

open import Relation.Nullary
open import Relation.Binary

open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Empty
open import Data.Unit

open import Level hiding (suc)

open import Type
open import Name

Typ : Set
Typ = Σ[ ys ∈ Names ] Ty ys

order : StrictTotalOrder 0ℓ 0ℓ 0ℓ
order = record
  { Carrier = Name × Typ
  ; _≈_ = λ { (x , _) (y , _) → x ≈ y }
  ; _<_ = λ { (x , _) (y , _) → x < y }
  ; isStrictTotalOrder = record
    { isEquivalence    = record
      { refl  = IsEquivalence.refl isEquivalence
      ; sym   = IsEquivalence.sym isEquivalence
      ; trans = IsEquivalence.trans isEquivalence
      }
    ; trans = trans
    ; compare = λ { (x , _) (y , _) → compare x y }
    }
  }

open import Data.AVL.Sets            order public
open import Data.AVL                 order
open import Data.AVL.Sets.Properties order public

Cxt : Set
Cxt = ⟨Set⟩

dom : Cxt → Names
dom = {!!} -- map proj₁

-- cod : Cxt → List Typ
-- cod = map proj₂

-- -- map-∈-ins : ∀ (Γ : Cxt) {x τ Δ} → x ∈ dom (Γ ++ (x , τ) ∷ Δ)
-- -- map-∈-ins Γ {x} {τ} {Δ}
-- --   rewrite map-++-commute proj₁ Γ ((x , τ) ∷ Δ) = ∈-insert (dom Γ)

-- -- instance
-- --   ∈-Cxt : ∀ {x τ} {Γ : Cxt} → (x , τ) ∈ Γ → x ∈ dom Γ
-- --   ∈-Cxt x∈Γ = ∈-map⁺ proj₁ x∈Γ

-- -- -- 
-- -- DomDist : Cxt → Set
-- -- DomDist xs = Dist (dom xs)

-- -- DomDist-rm : ∀ (Γ : Cxt) x {Δ τ}
-- --           → DomDist (Γ ++ (x , τ) ∷ Δ) → DomDist (Γ ++ Δ)
-- -- DomDist-rm Γ x {Δ} {τ} p
-- --  rewrite map-++-commute proj₁ Γ ((x , τ) ∷ Δ)
-- --        | map-++-commute proj₁ Γ Δ = Dist-rm (dom Γ) p

-- -- DomDist-ins : ∀ (Γ : Cxt) {x Δ τ}
-- --               → DomDist (Γ ++ Δ)
-- --               → x ∉ dom (Γ ++ Δ)
-- --               → DomDist (Γ ++ (x , τ) ∷ Δ)
-- -- DomDist-ins Γ {x} {Δ} {τ} p x∉domΓ++Δ
-- --  rewrite map-++-commute proj₁ Γ Δ
-- --        | map-++-commute proj₁ Γ ((x , τ) ∷ Δ) = Dist-ins (dom Γ) p x∉domΓ++Δ

-- -- DomCxt-≡ : ∀ (Γ : Cxt) x {τ σ Δ} 
-- --          → DomDist   (Γ ++ (x , τ) ∷ Δ)
-- --          → (x , σ) ∈ (Γ ++ (x , τ) ∷ Δ) 
-- --          → σ ≡ τ
-- -- DomCxt-≡ [] x p (here refl) = refl
-- -- DomCxt-≡ [] x (x∉xs ∷ p) (there x∈Γ++Δ) = ⊥-elim (x∉xs (∈-map⁺ proj₁ x∈Γ++Δ))
-- -- DomCxt-≡ (_ ∷ Γ) x {τ} {_} {Δ} (y∉xs ∷ p) (here refl)
-- --  rewrite map-++-commute proj₁ Γ ((x , τ) ∷ Δ) = ⊥-elim (y∉xs (∈-insert (dom Γ))) 
-- -- DomCxt-≡ (_ ∷ Γ) x (y∉xs ∷ p) (there x∈Γ++Δ) = DomCxt-≡ Γ x p x∈Γ++Δ

-- -- DomCxt-≢ : ∀ (Γ : Cxt) x {τ Δ y σ} 
-- --          → DomDist (Γ ++ (x , τ) ∷ Δ) → x ≢ y
-- --          → (y , σ) ∈ Γ ++ (x , τ) ∷ Δ
-- --          → (y , σ) ∈ Γ ++ Δ
-- -- DomCxt-≢ Γ x {τ} {Δ} p x≢y y∈Γ++x∷Δ with ∈-++⁻ Γ y∈Γ++x∷Δ
-- -- ... | inj₂ (here refl)   = ⊥-elim (x≢y refl)
-- -- ... | inj₂ (there y∈x∷Δ) = ∈-++⁺ʳ Γ y∈x∷Δ
-- -- ... | inj₁ y∈Γ           = ∈-++⁺ˡ y∈Γ 
