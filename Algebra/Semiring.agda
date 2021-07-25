module Algebra.Semiring where

open import Data.Type

record Semiring {ℓ} (A : Type ℓ) : Type ℓ where
  infixl 6 _+_
  infixl 7 _*_

  field zro one : A
  field _+_ _*_ : A → A → A

  {-# INLINE zro #-}
  {-# INLINE one #-}

open Semiring ⦃ ... ⦄ public
