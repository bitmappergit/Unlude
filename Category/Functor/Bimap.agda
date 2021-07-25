module Category.Functor.Bimap where

open import Data.Type

record Bimap {ℓ₁ ℓ₂} (P : Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)) : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field bimap : ∀ {A B C D} → (A → B) → (C → D) → P A C → P B D

open Bimap ⦃ ... ⦄ public
