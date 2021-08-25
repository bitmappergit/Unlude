module Data.Traversable where

open import Data.Type
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Data.Foldable
open import Data.Function

record Traversable {ℓ} (T : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field ⦃ super-functor ⦄ : Functor T
  field ⦃ super-foldable ⦄ : Foldable T

  field traverse : {F : Type ℓ → Type ℓ} {A B : Type ℓ} ⦃ _ : Applicative F ⦄ → (A → F B) → T A → F (T B)

  sequence : {F : Type ℓ → Type ℓ} {A : Type ℓ} ⦃ _ : Applicative F ⦄ → T (F A) → F (T A)
  sequence = traverse id

open Traversable ⦃ ... ⦄ public

  {-
sequence : ∀ {ℓ} {A : Type ℓ} {M : Type ℓ → Type ℓ} ⦃ _ : Monad M ⦄ → List (M A) → M (List A)
sequence [] = return []
sequence (c0 ∷ cs0) = do
  c1 ← c0
  cs1 ← sequence cs0
  return (c1 ∷ cs1)

mapM : ∀ {ℓ} {A : Type ℓ} {M : Type ℓ → Type ℓ} ⦃ _ : Monad M ⦄ → (A → M A) → List (M A) → M (List A)
mapM {A = A} {M = M} f = sequence ∘ helper f
  where helper : (A → M A) → List (M A) → List (M A)
        helper f (x ∷ xs) = x >>= λ n → return (f n ∷ helper f xs)
        helper _ [] = []
-}
