module Data.Traversable where

open import Data.Type
open import Data.Core
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

  mapM : {A B : Type ℓ} {M : Type ℓ → Type ℓ} ⦃ _ : Monad M ⦄ → (A → M B) → T A → M (T B)
  mapM f = sequence ∘ map f

  forM : {A B : Type ℓ} {M : Type ℓ → Type ℓ} ⦃ _ : Monad M ⦄ → T A → (A → M B) → M (T B)
  forM = flip mapM

open Traversable ⦃ ... ⦄ public
