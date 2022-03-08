module Category.Applicative where

open import Data.Type
open import Category.Functor

record Applicative {a b} (F : Type a → Type b) : Type (lsuc a ⊔ b) where
  infixl 4 _<*>_

  field ⦃ super ⦄ : Functor F

  field pure : ∀ {A} → A → F A
  field _<*>_ : ∀ {A B} → F (A → B) → F A → F B

  liftA2 : ∀ {A B C} → (A → B → C) → F A → F B → F C
  liftA2 f x y = f <$> x <*> y
  
open Applicative ⦃ ... ⦄ public
