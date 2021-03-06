module Data.Foldable where

open import Data.Type
open import Algebra.Semigroup
open import Algebra.Monoid
open import Data.Function

record Foldable {ℓ} (T : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field foldr : {A B : Type ℓ} → (A → B → B) → B → T A → B
  field foldl : {A B : Type ℓ} → (B → A → B) → B → T A → B

  foldMap : {A M : Type ℓ} ⦃ _ : Monoid M ⦄ → (A → M) → T A → M
  foldMap f = foldr (_<>_ ∘ f) empty
  -- foldl f z t = foldr (flip (λ a b → a ∘ b) ∘ flip f) id t z

open Foldable ⦃ ... ⦄ public
