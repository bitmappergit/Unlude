module Data.Product where

open import Data.Type
open import Data.Function
open import Data.Core

infixr 4 _×_

_×_ : ∀ {a b} → Type a → Type b → Type (a ⊔ b)
_×_ A B = Σ A (λ _ → B)

∃ : ∀ {a b} {A : Type a} → (B : A → Type b) → Type (a ⊔ b)
∃ = Σ _
