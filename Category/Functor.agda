module Category.Functor where

open import Data.Type

record Functor {ℓ} (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field map : ∀ {A B} → (A → B) → F A → F B

  _<$>_ : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = map

  infixl 4 _<$>_

open Functor ⦃ ... ⦄ public
