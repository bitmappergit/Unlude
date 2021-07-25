module Data.Empty where

open import Data.Type

data ⊥ : Type where

⊥-elim : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
⊥-elim ()
