module Data.Eq where

open import Data.Type
open import Data.Bool

record Eq {ℓ} (A : Type ℓ) : Type ℓ where
  field _==_ : A → A → Bool
  
  _!=_ : A → A → Bool
  x != y = not (x == y)

open Eq ⦃ ... ⦄ public

instance EqBool : Eq Bool

_==_ ⦃ EqBool ⦄ #t #t = #t
_==_ ⦃ EqBool ⦄ #f #f = #t
_==_ ⦃ EqBool ⦄ #f #t = #f
_==_ ⦃ EqBool ⦄ #t #f = #f
