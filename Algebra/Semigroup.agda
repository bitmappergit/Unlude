module Algebra.Semigroup where

open import Data.Type

record Semigroup {ℓ} (A : Type ℓ) : Type ℓ where
  infixr 6 _<>_
  field _<>_ : A → A → A

open Semigroup ⦃ ... ⦄ public
