module Category.Monad where

open import Data.Type
open import Data.Function
open import Category.Functor
open import Category.Applicative

record Monad {a b} (M : Type a → Type b) : Type (lsuc a ⊔ b) where
  infixl 1 _>>=_ _>>_
  infixr 1 _=<<_

  field ⦃ super ⦄ : Applicative M

  field _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  
  return : ∀ {A} → A → M A
  return = pure

  _>>_ : ∀ {A B} → M A → M B → M B
  _>>_ a b = a >>= const b

  _=<<_ : ∀ {A B} → (A → M B) → M A → M B
  _=<<_ = flip _>>=_

open Monad ⦃ ... ⦄ public

