module Data.Sequence where

open import Data.Type

record Sequence {ℓ} (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field head : ∀ {A} → F A → A
  field tail : ∀ {A} → F A → F A

open Sequence ⦃ ... ⦄ public
