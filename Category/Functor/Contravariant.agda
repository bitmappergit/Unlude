module Category.Functor.Contravariant where

open import Data.Type

record Contravariant {ℓ} (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field contramap : ∀ {A B} → F B → F A

open Contravariant ⦃ ... ⦄ public 
