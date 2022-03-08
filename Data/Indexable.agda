module Data.Indexable where

open import Data.Type
open import Control.Lens

record Indexable {ℓ} (S : Type ℓ → Type ℓ) (I : Type ℓ) : Type (lsuc ℓ) where
  field update : {A : Type ℓ} → I → A → S A → S A
  field index : {A : Type ℓ} → I → S A → A
  
  at : {A : Type ℓ} → I → MonoLens (S A) A
  at idx = lens (index idx) (λ o n → update idx n o)
  
open Indexable ⦃ ... ⦄ public

{-# INLINE index #-}
{-# INLINE update #-}
