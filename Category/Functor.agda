module Category.Functor where

open import Data.Type
open import Data.Core
open import Data.Function

record Functor {a b} (F : Type a → Type b) : Type (lsuc a ⊔ b) where
  field map : ∀ {A B} → (A → B) → F A → F B

  _<$>_ : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = map

  void : ∀ {A} → F A → F ⊤
  void = map (const unit)
  
  infixl 4 _<$>_

open Functor ⦃ ... ⦄ public
