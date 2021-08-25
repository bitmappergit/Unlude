module Data.Eq where

open import Data.Type
open import Data.Bool

record Eq {ℓ} (A : Type ℓ) : Type ℓ where
  field _≡ᵇ_ : A → A → Bool
  
  _≢ᵇ_ : A → A → Bool
  x ≢ᵇ y = not (x ≡ᵇ y)

open Eq ⦃ ... ⦄ public

instance EqBool : Eq Bool

_≡ᵇ_ ⦃ EqBool ⦄ #t #t = #t
_≡ᵇ_ ⦃ EqBool ⦄ #f #f = #t
_≡ᵇ_ ⦃ EqBool ⦄ #f #t = #f
_≡ᵇ_ ⦃ EqBool ⦄ #t #f = #f
