module Data.Unit where

open import Data.Type

record ⊤ : Type where
  instance constructor unit

{-# BUILTIN UNIT ⊤ #-}
{-# COMPILE GHC ⊤ = data () (()) #-}
