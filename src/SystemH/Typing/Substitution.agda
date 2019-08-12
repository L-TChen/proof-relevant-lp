open import Data.Nat

module SystemH.Typing.Substitution (Op At : ℕ → Set) where

open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Data.Vec.Membership.Propositional.Properties
open import Data.Vec.Relation.Unary.Any as Any
  using (here; there)
open import Data.Vec.Relation.Unary.All as All
  using (All)
  
open import Relation.Binary.PropositionalEquality
  renaming (subst to ≡-subst)
open import Data.Product
  hiding (map)

open import SystemH.Type        Op At
  hiding (single)
open import SystemH.Typing.Base Op At

-- TODO: Move this to agda-stdlib 
∈-map⁻ : ∀ {a b}{A : Set a} {B : Set b} {xs : Vec A n} {y}
  → (f : A → B)
  → y ∈ map f xs → ∃ λ x → x ∈ xs × y ≡ f x
∈-map⁻ {xs = xs} f y∈map with xs
∈-map⁻ {xs = xs} f (here refl)   | x ∷ xs' = x , here refl , refl
∈-map⁻ {xs = xs} f (there y∈map) | x ∷ xs' = x' , there x∈xs , y≡fx
  where
    pf = ∈-map⁻ f y∈map
    x' = proj₁ pf
    x∈xs = proj₁ (proj₂ pf)
    y≡fx = proj₂ (proj₂ pf)

↑-∈-↑ : {τ : Type} → τ ∈ Γ → ↑₁-ty τ ∈ (↑₁ Γ)
↑-∈-↑ = ∈-map⁺ ↑₁-ty

lower₁-∈-↑ : {τ : Type} → ↑₁-ty τ ∈ (↑₁ Γ) → τ ∈ Γ
lower₁-∈-↑ {Γ = _ ∷ Γ} (here px)  = here {!!} -- (↑-ty-injective px)
lower₁-∈-↑ {Γ = _ ∷ Γ} (there px) = there (lower₁-∈-↑ px)

ext : (∀ {τ} → τ ∈ Γ → τ ∈ Δ)
  → (∀ {τ σ} → τ ∈ (σ ∷ Γ) → τ ∈ σ ∷ Δ)
ext ρ (here px) = here  px
ext ρ (there p) = there (ρ p)

ext-↑ : (∀ {τ} → τ ∈ Γ → τ ∈ Δ)
  → ∀ {τ} → τ ∈ ↑₁ Γ → τ ∈ ↑₁ Δ
ext-↑ ρ px = ≡-subst (λ τ → τ ∈ (↑₁ _)) (sym τ=σ) (↑-∈-↑ (ρ σ∈Γ))
  where
    pf = ∈-map⁻ ↑₁-ty px
    σ∈Γ = proj₁ (proj₂ pf)
    τ=σ = proj₂ (proj₂ pf)

rename :
    (∀ {τ} → τ ∈ Γ → τ ∈ Δ)
    ------------------------------------------------  
  → ∀ {τ : Type} → [ Ψ , d ] Γ ⊢ τ → [ Ψ , d ] Δ ⊢ τ
rename ρ (ax ψ)   = ax ψ
rename ρ (var x)  = var (ρ x)
rename ρ (ƛ M)    = ƛ rename {!!} M
rename ρ (M · N)  = rename ρ M · All.map (rename ρ) N
rename ρ (M ∙₀ σ) = rename ρ M ∙₀ σ
rename ρ (M ∙₁ σ) = rename ρ M ∙₁ σ

-- ↑-⊢ : {Γ Ψ : Cxt Ξ} 
--   → [ Ξ , Ψ ] Γ ⊢ τ
--     ----------------------------------
--   → [ suc Ξ , ↑ Ψ ] ↑ Γ ⊢ ↑-ty τ
-- ↑-⊢ (ax ψ)   = ax  (↑-∈-↑ ψ)
-- ↑-⊢ (var x)  = var (↑-∈-↑ x)
-- ↑-⊢ (ƛ M)    = ƛ ↑-⊢ M
-- ↑-⊢ (M · M₁) = ↑-⊢ M · ↑-⊢ M₁
-- --↑-⊢ (∀₀ M)   = ∀₀ (↑-⊢ M)
-- ↑-⊢ (M ∙ t)  = ≡-subst (λ τ → [ _ , _ ] _ ⊢ τ)
--   (subst-↑-ty t _) (↑-⊢ M ∙ ↑-tm t)

-- exts : (∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] Δ ⊢ τ)
--     -----------------------------------------
--   → ∀ {τ σ} → τ ∈ σ ∷ Γ → [ Ξ , Ψ ] σ ∷ Δ ⊢ τ 
-- exts ρ (here refl) = var (here refl)
-- exts ρ (there px)  = rename there (ρ px)

-- exts-↑ : (∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] Δ ⊢ τ)
--     -----------------------------------------
--   → ∀ {τ} → τ ∈ ↑ Γ → [ suc Ξ , ↑ Ψ ] ↑ Δ ⊢ τ
-- exts-↑ ρ τ∈Γ = ≡-subst ([ _ , _ ] _ ⊢_) (sym τ=τ′) (↑-⊢ (ρ τ′∈Γ))
--   where
--     pf   = ∈-map⁻ ↑-ty τ∈Γ    
--     τ′∈Γ = proj₁ (proj₂ pf)
--     τ=τ′ = proj₂ (proj₂ pf) 

-- subst : {Γ Δ : Cxt Ξ}
--       → (∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] Δ ⊢ τ)
--         -------------------------------------------
--       → (∀ {τ} → [ Ξ , Ψ ] Γ ⊢ τ → [ Ξ , Ψ ] Δ ⊢ τ)
-- subst ρ (ax x)   = ax x
-- subst ρ (var x)  = ρ x
-- subst ρ (ƛ M)    = ƛ subst (exts ρ) M
-- subst ρ (M · N)  = subst ρ M · subst ρ N
-- --subst ρ (∀₀ M)   = ∀₀ (subst (exts-↑ ρ) M)
-- subst ρ (M ∙ t)  = subst (exts-↑ ρ) M ∙ t -- subst ρ M ∙ t

-- exts-comp : {E : Cxt Ξ}
--   → (∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] Δ ⊢ τ)
--   → (∀ {σ} → σ ∈ Δ → [ Ξ , Ψ ] E ⊢ σ)
--   → ∀ {τ} → τ ∈ Γ → [ Ξ , Ψ ] E ⊢ τ
-- exts-comp ρ₁ ρ₂ x = subst ρ₂ (ρ₁ x)

-- single : [ Ξ , Ψ ] Γ ⊢ σ
--   → (τ ∈ σ ∷ Γ → [ Ξ , Ψ ] Γ ⊢ τ)
-- single M (here refl) = M
-- single M (there x)   = var x

-- [_]_ : {τ₁ τ₂ : Ty Ξ}
--      → [ Ξ , Ψ ] Γ ⊢ τ₁
--      → [ Ξ , Ψ ] (τ₁ ∷ Γ) ⊢ τ₂
--        --------------------
--      → [ Ξ , Ψ ] Γ ⊢ τ₂
-- [_]_ M = subst (single M)
