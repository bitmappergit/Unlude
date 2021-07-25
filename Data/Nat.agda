module Data.Nat where

open import Data.Type
open import Data.Function
open import Algebra.Semiring
open import Data.Divisible
open import Data.Bool
open import Data.Eq
open import Data.Ord

data Nat : Type where
  suc : Nat → Nat
  zero : Nat

{-# BUILTIN NATURAL Nat #-}

private natPlus : Nat → Nat → Nat
natPlus zero n = n
natPlus (suc m) n = suc (natPlus m n)

private natTimes : Nat → Nat → Nat
natTimes zero _ = zero
natTimes (suc m) n = natPlus n (natTimes m n)

instance SemiringNat : Semiring Nat

SemiringNat. zro = zero
SemiringNat. one = suc zero
SemiringNat. _+_ = natPlus
SemiringNat. _*_ = natTimes 

{-# BUILTIN NATPLUS natPlus #-}
{-# BUILTIN NATTIMES natTimes #-}

_minus_ : Nat → Nat → Nat
n     minus zero = n
zero  minus suc m = zero
suc n minus suc m = n minus m

infixl 6 _minus_

{-# BUILTIN NATMINUS _minus_ #-}

div-helper : (k m n j : Nat) → Nat
div-helper k m zero j = k
div-helper k m (suc n) zero = div-helper (suc k) m n m
div-helper k m (suc n) (suc j) = div-helper k m n j

{-# BUILTIN NATDIVSUCAUX div-helper #-}

mod-helper : (k m n j : Nat) → Nat
mod-helper k m zero j = k
mod-helper k m (suc n) zero = mod-helper zero m n m
mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j

{-# BUILTIN NATMODSUCAUX mod-helper #-}

instance DivisibleNat : Divisible Nat

DivisibleNat. _/_ n (suc m) = div-helper zero m n m
DivisibleNat. _/_ _ zero = zero

DivisibleNat. _%_ n (suc m) = mod-helper zero m n m
DivisibleNat. _%_ _ zero = zero

instance EqNat : Eq Nat

EqNat. _==_ zero zero = #t
EqNat. _==_ (suc x) (suc y) = x == y
EqNat. _==_ (suc _) zero = #f
EqNat. _==_ zero (suc _) = #f

instance OrdNat : Ord Nat

OrdNat. _<_ zero (suc _) = #t
OrdNat. _<_ (suc _) zero = #f
OrdNat. _<_ (suc x) (suc y) = x < y
OrdNat. _<_ zero zero = #f

OrdNat. _>_ zero (suc _) = #f
OrdNat. _>_ (suc _) zero = #t
OrdNat. _>_ (suc x) (suc y) = x > y
OrdNat. _>_ zero zero = #f
