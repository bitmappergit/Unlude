module Data.Type where

import Agda.Primitive renaming (Set to Type)
open Agda.Primitive using (Type; Prop; lsuc; lzero; _⊔_) public

record Lift {ℓ₁} ℓ₂ (A : Type ℓ₁) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor lift
  field lower : A

open Lift public
