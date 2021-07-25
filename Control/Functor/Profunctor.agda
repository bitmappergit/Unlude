module Control.Functor.Profunctor where

open import Data.Type
open import Control.Functor

record Profunctor {ℓ₁ ℓ₂} (P : Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)) : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field dimap : ∀ {A B C D} → (A → B) → (C → D) → P B C → P A D

open Profunctor ⦃ ... ⦄ public
