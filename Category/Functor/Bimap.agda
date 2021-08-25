module Category.Functor.Bimap where

open import Data.Type

record Bimap {ℓ} (P : Type ℓ → Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field bimap : ∀ {A B C D} → (A → B) → (C → D) → P A C → P B D

open Bimap ⦃ ... ⦄ public
