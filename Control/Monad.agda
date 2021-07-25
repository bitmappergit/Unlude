module Control.Monad where

open import Data.Type
open import Data.Function
open import Control.Functor
open import Control.Applicative

record Monad {ℓ₁ ℓ₂} (M : Type ℓ₁ → Type ℓ₂) : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  infixl 1 _>>=_ _>>_

  field ⦃ super ⦄ : Applicative M

  field _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  
  return : ∀ {A} → A → M A
  return = pure

  _>>_ : ∀ {A B} → M A → M B → M B
  _>>_ a b = a >>= const b

open Monad ⦃ ... ⦄ public

