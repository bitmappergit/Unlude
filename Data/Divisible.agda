module Data.Divisible where

open import Data.Type
open import Relation.Negation
open import Relation.Equality
open import Algebra.Semiring

record Divisible {ℓ} (A : Type ℓ) : Type ℓ where
  field ⦃ super-semiring ⦄ : Semiring A
  field ⦃ super-deceq ⦄ : DecEq A
  field _/_ : (m n : A) → {prf : #F (n ≟ zro)} → A
  field _%_ : (m n : A) → {prf : #F (n ≟ zro)} → A

open Divisible ⦃ ... ⦄ public
