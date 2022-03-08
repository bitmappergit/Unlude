module Data.Show where

open import Data.Type
open import Data.Core
open import Data.String

record Show {ℓ} (A : Type ℓ) : Type ℓ where
  field show : A → String

open Show ⦃ ... ⦄ public
