module Category.Applicative where

open import Data.Type
open import Category.Functor

record Applicative {ℓ} (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  infixl 4 _<*>_

  field ⦃ super ⦄ : Functor F

  field pure : ∀ {A} → A → F A
  field _<*>_ : ∀ {A B} → F (A → B) → F A → F B

  
open Applicative ⦃ ... ⦄ public
