module Data.Nat where

open import Data.Type
open import Data.Function
open import Algebra.Semiring
open import Data.Divisible
open import Data.Bool
open import Data.Eq
open import Data.Ord
open import Relation.Negation
open import Relation.Equality
open import Data.Empty
open import Data.Core

nat-plus : Nat → Nat → Nat
nat-plus zero n = n
nat-plus (suc m) n = suc (nat-plus m n)

nat-times : Nat → Nat → Nat
nat-times zero _ = zero
nat-times (suc m) n = nat-plus n (nat-times m n)

{-# DISPLAY nat-plus m n = m + n #-}
{-# DISPLAY nat-times m n = m * n #-}

instance SemiringNat : Semiring Nat

SemiringNat. zro = zero
SemiringNat. one = suc zero
SemiringNat. _+_ = nat-plus
SemiringNat. _*_ = nat-times 

{-# BUILTIN NATPLUS nat-plus #-}
{-# BUILTIN NATTIMES nat-times #-}

_∸_ : Nat → Nat → Nat
n     ∸ zero  = n
zero  ∸ suc m = zero
suc n ∸ suc m = n ∸ m

infixl 6 _∸_

{-# BUILTIN NATMINUS _∸_ #-}

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

z≢s : ∀ {n} → zero ≡ suc n → ⊥
z≢s ()

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

instance DecEqNat : DecEq Nat

DecEqNat. _≟_ zero zero = yes refl
DecEqNat. _≟_ zero (suc _) = no λ ()
DecEqNat. _≟_ (suc _) zero = no λ ()
DecEqNat. _≟_ (suc m) (suc n) with m ≟ n
... | yes m≡n = yes (cong suc m≡n)
... | no m≢n = no (m≢n ∘ suc-injective)

instance DivisibleNat : Divisible Nat

DivisibleNat. _/_ n (suc m) = div-helper zero m n m
DivisibleNat. _/_ _ zero = zero

DivisibleNat. _%_ n (suc m) = mod-helper zero m n m
DivisibleNat. _%_ _ zero = zero

private nat-eq : Nat → Nat → Bool
nat-eq zero zero = #t
nat-eq (suc x) (suc y) = nat-eq x y
nat-eq (suc _) zero = #f
nat-eq zero (suc _) = #f

{-# DISPLAY nat-eq m n = m ≡ᵇ n #-}

{-# BUILTIN NATEQUALS nat-eq #-}

private nat-less : Nat → Nat → Bool
nat-less _ zero = #f
nat-less zero (suc _) = #t
nat-less (suc x) (suc y) = nat-less x y

{-# DISPLAY nat-less m n = m <ᵇ n #-}

{-# BUILTIN NATLESS nat-less #-}

instance EqNat : Eq Nat

EqNat. _≡ᵇ_ = nat-eq

instance OrdNat : Ord Nat

OrdNat. _<ᵇ_ = nat-less

double : Nat → Nat
double (suc n) = suc (suc (double n))
double zero = zero
