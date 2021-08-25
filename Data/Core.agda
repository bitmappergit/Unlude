module Data.Core where

open import Data.Type

data Nat : Type where
  suc : Nat → Nat
  zero : Nat

{-# BUILTIN NATURAL Nat #-}

infixr 5 _∷_

data List {ℓ} (A : Type ℓ) : Type ℓ where
  _∷_ : A → List A → List A
  [] : List A

{-# BUILTIN LIST List #-}

data Bool : Type where
  #t : Bool
  #f : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE #t #-}
{-# BUILTIN FALSE #f #-}

data Option {ℓ} (A : Type ℓ) : Type ℓ where
  some : A → Option A
  none : Option A

{-# BUILTIN MAYBE Option #-}

infixr 4 _,_

record Σ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : A → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field fst : A
  field snd : B fst

open Σ public

{-# BUILTIN SIGMA Σ #-}
