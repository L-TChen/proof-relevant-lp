module SystemH.Example where

{-
_ : (ψ : At 0) (φ : At 1) (k : Op 0)
  → [ 0 , 0F , ∀₁ (at φ (var zero ∷ [])) ∷ [] ] at ψ [] ∷ [] ⊢ at φ (op 0F k [] ∷ [])
_ = λ ψ φ k → ax (here refl) ∙ op _ k []
-}
