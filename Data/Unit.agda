module Data.Unit where

open import Data.Type

record ⊤ {ℓ} : Type ℓ where
  instance constructor unit

{-# BUILTIN UNIT ⊤ #-}
{-# FOREIGN GHC type AgdaUnit a = () #-}
{-# COMPILE GHC ⊤ = data AgdaUnit (()) #-}
