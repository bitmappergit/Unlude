module Category.Monad where

open import Data.Type
open import Data.Function
open import Category.Functor
open import Category.Applicative

record Monad {ℓ} (M : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  infixl 1 _>>=_ _>>_

  field ⦃ super ⦄ : Applicative M

  field _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  
  return : ∀ {A} → A → M A
  return = pure

  _>>_ : ∀ {A B} → M A → M B → M B
  _>>_ a b = a >>= const b

open Monad ⦃ ... ⦄ public

