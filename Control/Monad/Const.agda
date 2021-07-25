module Control.Monad.Const where

open import Data.Type
open import Control.Functor
open import Control.Applicative
open import Control.Monad

record Const {ℓ} (A B : Type ℓ) : Type ℓ where
  constructor mkConst
  field getConst : A

open Const public

instance FunctorConst : ∀ {ℓ} {A : Type ℓ} → Functor (Const A)

FunctorConst. map f v = mkConst (getConst v)
