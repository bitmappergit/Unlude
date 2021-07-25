module Class.Num where

open import Data.Type
open import Data.Function
open import Data.Nat
open import Algebra.Semiring

record Num {ℓ} (A : Type ℓ) : Type ℓ where
  field fromNat : Nat → A
  field toNat : A → Nat
  
  {-# INLINE fromNat #-}
  {-# INLINE toNat #-}

open Num ⦃ ... ⦄ public

{-# BUILTIN FROMNAT fromNat #-}

instance NumNat : Num Nat

fromNat ⦃ NumNat ⦄ = id
toNat ⦃ NumNat ⦄ = id
