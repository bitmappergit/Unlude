module Data.Type where

import Agda.Primitive renaming (Set to Type)
open Agda.Primitive using (Type; Prop; lsuc; lzero; _⊔_; Level) public

record Lift {a} b (A : Type a) : Type (a ⊔ b) where
  constructor lift
  field lower : A

open Lift public

Function : ∀ {a b} → Type a → Type b → Type (a ⊔ b)
Function a b = a → b
