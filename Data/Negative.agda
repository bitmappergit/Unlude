module Data.Negative where

open import Data.Type
open import Data.Core
open import Algebra.Semiring
open import Algebra.Ring
open import Data.Num

record Negative {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
  field ⦃ semiring-super ⦄ : Semiring A
  field ⦃ ring-super ⦄ : Ring A
  field ⦃ num-super ⦄ : Num A

  field fromNeg : Nat → A
  
open Negative ⦃ ... ⦄ public

{-# BUILTIN FROMNEG fromNeg #-}
