module Data.Negative where

open import Data.Type
open import Algebra.Semiring
open import Algebra.Ring
open import Data.Num
open import Data.Nat

record Negative {ℓ} (A : Type ℓ) : Type ℓ where
  field ⦃ semiring-super ⦄ : Semiring A
  field ⦃ ring-super ⦄ : Ring A
  field ⦃ num-super ⦄ : Num A

  field fromNeg : Nat → A

  
open Negative ⦃ ... ⦄ public

{-# BUILTIN FROMNEG fromNeg #-}
