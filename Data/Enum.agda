module Data.Enum where

open import Data.Type
open import Algebra.Semigroup
open import Algebra.Monoid
open import Data.Eq
open import Data.Nat
open import Data.Function
open import Category.Functor
open import Relation.Equality
open import Relation.Negation
open import Data.Core
open import Data.Vec

record Enum {ℓ} (A : Type ℓ) : Type ℓ where
  field succ : A → A
  field pred : A → A
  field toEnum : Nat → A
  field fromEnum : A → Nat

{-
  <_,_> : (s : A) → (e : A) → Vec A ((fromEnum s) ∸ (fromEnum e))
  <_,_> f t = result tn
    where fn = fromEnum f
          tn = fromEnum t
          result : (x : Nat) → Vec A x
          result n with n ≟ fn
          ... | (yes _) = []
          ... | (no _) = toEnum n ∷ result (suc n)
-}

open Enum ⦃ ... ⦄ public

instance EnumNat : Enum Nat

EnumNat. succ = suc
EnumNat. pred (suc n) = n
EnumNat. pred zero = zero
EnumNat. toEnum = id
EnumNat. fromEnum = id
