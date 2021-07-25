module Algebra.Monoid where

open import Data.Type
open import Algebra.Semigroup

record Monoid {ℓ} (A : Type ℓ) : Type ℓ where
  field empty : A
  field ⦃ super ⦄ : Semigroup A

open Monoid ⦃ ... ⦄ public
