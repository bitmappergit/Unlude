module Data.Indexable where

open import Data.Type

record Indexable {ℓ} (S : Type ℓ → Type ℓ) (I : Type ℓ) : Type (lsuc ℓ) where
  field update : ∀ {A} → I → A → S A → S A
  field index : ∀ {A} → I → S A → A

open Indexable ⦃ ... ⦄ public
