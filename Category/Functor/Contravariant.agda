module Category.Functor.Contravariant where

open import Data.Type

record Contravariant {ℓ₁ ℓ₂} (F : Type ℓ₁ → Type ℓ₂) : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field contramap : ∀ {A B} → F A → F B

open Contravariant ⦃ ... ⦄ public 
