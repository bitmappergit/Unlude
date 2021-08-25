module Data.Product where

open import Data.Type
open import Data.Function
open import Data.Core using (Σ; _,_; fst; snd) public

infixr 4 _×_

_×_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
_×_ A B = Σ A (λ _ → B)

∃ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → (B : A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
∃ = Σ _
