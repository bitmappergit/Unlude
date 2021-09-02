module Data.Num where

open import Data.Type
open import Data.Core
open import Data.Function
open import Algebra.Semiring
open import Data.Unit

record Num {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
  field Constraint : Nat -> Type ℓ
  field fromNat : (n : Nat) → ⦃ _ : Constraint n ⦄ → A
  field toNat : A → Nat
  
  {-# INLINE fromNat #-}
  {-# INLINE toNat #-}
    
open Num ⦃ ... ⦄ public

{-# BUILTIN FROMNAT fromNat #-}

instance NumNat : Num Nat

NumNat. Constraint _ = ⊤
NumNat. fromNat n = n
NumNat. toNat n = n
