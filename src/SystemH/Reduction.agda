open import Data.Nat

module SystemH.Reduction (Op At : ℕ → Set) where
 
open import SystemH.Reduction.Base      Op At
open import SystemH.Reduction.Progress  Op At

