module Examples.Comb where

open import Prelude
open import Relation.Nat

infixr 7 _[_]

data Term {i : Nat} : Fin i → Type where
  B : Term (suc (fromNatᶠ i))
  C : Term zero
  K : Term zero
  _[_] : {a b : Fin i} → Term a → Term b → Term (a + b)

step : Term (suc _) → Term _
step (B [ x ] [ y ] [ z ]) = x [ y [ z ] ]
step (C [ x ] [ y ] [ z ]) = x [ z ] [ y ]
step (K [ x ] [ _ ]) = x
step (f [ x ]) = f [ x ]
step other = other
