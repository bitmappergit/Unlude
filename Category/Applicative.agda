module Category.Applicative where

open import Data.Type
open import Category.Functor

record Applicative {ℓ} (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  infixl 4 _<*>_

  field ⦃ super ⦄ : Functor F

  field pure : ∀ {A : Type ℓ} → A → F A
  field _<*>_ : ∀ {A B : Type ℓ} → F (A → B) → F A → F B

  liftA2 : ∀ {A B C : Type ℓ} → (A → B → C) → F A → F B → F C
  liftA2 f x y = f <$> x <*> y
  
open Applicative ⦃ ... ⦄ public
