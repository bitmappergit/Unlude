module Data.Ord where

open import Data.Type
open import Data.Core
open import Data.Bool
open import Data.Eq
open import Relation.Equality
open import Relation.Negation

record Ord {ℓ} (A : Type ℓ) : Type ℓ where
  field ⦃ super ⦄ : Eq A

  infix 4 _<ᵇ_ _>ᵇ_ _≤ᵇ_ _≥ᵇ_

  field _<ᵇ_ : A → A → Bool

  _>ᵇ_ : A → A → Bool
  x >ᵇ y = y <ᵇ x
  
  _≤ᵇ_ : A → A → Bool
  x ≤ᵇ y = (x <ᵇ y) ∨ (x ≡ᵇ y)
  
  _≥ᵇ_ : A → A → Bool
  x ≥ᵇ y = (x >ᵇ y) ∨ (x ≡ᵇ y)


open Ord ⦃ ... ⦄ public
