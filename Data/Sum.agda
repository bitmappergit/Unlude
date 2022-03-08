module Data.Sum where

open import Data.Type
open import Data.Core
open import Data.Function

infixr 1 _⊎_

data _⊎_ {a b} (A : Type a) (B : Type b) : Type (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,_] : ∀ {a b c}
      → {A : Type a}
      → {B : Type b}
      → {C : A ⊎ B → Type c}
      → ((x : A) → C (inj₁ x))
      → ((x : B) → C (inj₂ x))
      → ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

