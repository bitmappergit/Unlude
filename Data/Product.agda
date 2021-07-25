module Data.Product where

open import Data.Type
open import Data.Function

record Σ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : A → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field fst : A
  field snd : B fst

open Σ public

infixr 4 _,_

_×_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
_×_ A B = Σ A (λ _ → B)
