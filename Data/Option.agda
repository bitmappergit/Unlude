module Data.Option where

open import Data.Type
open import Category.Functor
open import Category.Applicative
open import Category.Monad

data Option {ℓ} (A : Type ℓ) : Type ℓ where
  some : A → Option A
  none : Option A

instance FunctorOption : ∀ {ℓ} → Functor {ℓ} Option

FunctorOption. map f (some x) = some (f x)
FunctorOption. map _ none = none

instance ApplicativeOption : ∀ {ℓ} → Applicative {ℓ} Option

ApplicativeOption. pure = some

ApplicativeOption. _<*>_ (some f) (some x) = some (f x)
ApplicativeOption. _<*>_ (some _) none = none
ApplicativeOption. _<*>_ none (some _) = none
ApplicativeOption. _<*>_ none none = none

instance MonadOption : ∀ {ℓ} → Monad {ℓ} Option

MonadOption. _>>=_ (some x) f = f x
MonadOption. _>>=_ none _ = none
