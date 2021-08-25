module Category.Functor.Profunctor where

open import Data.Type
open import Category.Functor

record Profunctor {ℓ} (P : Type ℓ → Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field dimap : ∀ {A B C D} → (A → B) → (C → D) → P B C → P A D

open Profunctor ⦃ ... ⦄ public
