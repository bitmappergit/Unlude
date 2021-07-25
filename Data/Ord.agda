module Class.Ord where

open import Data.Type
open import Data.Bool
open import Class.Eq

record Ord {ℓ} (A : Type ℓ) : Type ℓ where
  field ⦃ super ⦄ : Eq A

  field _<_ : A → A → Bool
  field _>_ : A → A → Bool

  _<=_ : A → A → Bool
  x <= y = (x < y) ∨ (x == y)
  
  _>=_ : A → A → Bool
  x >= y = (x > y) ∨ (x == y)

open Ord ⦃ ... ⦄ public
