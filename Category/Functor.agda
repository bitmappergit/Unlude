module Category.Functor where

open import Data.Type

record Functor {ℓ₁ ℓ₂} (F : Type ℓ₁ → Type ℓ₂) : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field map : ∀ {A B} → (A → B) → F A → F B

  _<$>_ : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = map

  infixl 4 _<$>_

open Functor ⦃ ... ⦄ public
