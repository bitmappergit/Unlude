module Class.Divisible where

open import Data.Type

record Divisible {ℓ} (A : Type ℓ) : Type ℓ where
  field _/_ : A → A → A
  field _%_ : A → A → A

open Divisible ⦃ ... ⦄ public
