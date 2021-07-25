module Algebra.Ring where

open import Data.Type
open import Algebra.Semiring

record Ring {ℓ} (A : Type ℓ) : Type ℓ where
  infixl 6 _-_
  
  field _-_ : A → A → A
  field negate : A → A
  field ⦃ super ⦄ : Semiring A

open Ring ⦃ ... ⦄ public
