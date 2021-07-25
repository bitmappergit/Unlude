module Data.Vec where

open import Data.Type

open import Data.Nat
open import Category.Functor
open import Algebra.Semiring
open import Data.Function
open import Algebra.Semigroup
open import Algebra.Monoid

infixr 5 _::_ _++_

data Vec {ℓ} (A : Type ℓ) : Nat → Type ℓ where
  _::_ : {s : Nat} → A → Vec A s → Vec A (suc s)
  [] : Vec A 0

replicate : ∀ {ℓ} {s} {A : Type ℓ} → A → Vec A s
replicate {s = suc x} val = val :: replicate {s = x} val
replicate {s = zero} val = []

instance FunctorVec : ∀ {ℓ} {s} → Functor {ℓ} (λ A → Vec A s)

FunctorVec. map f (x :: xs) = f x :: map f xs
FunctorVec. map _ [] = []

drop : ∀ {ℓ} {A : Type ℓ} {s} → (t : Nat) → Vec A (t + s) → Vec A s
drop (suc t) (_ :: xs) = drop t xs
drop zero result = result

take : ∀ {ℓ} {A : Type ℓ} {s} → (t : Nat) → Vec A (t + s) → Vec A t
take (suc t) (x :: xs) = x :: take t xs
take zero _ = []

_++_ : ∀ {ℓ} {A : Type ℓ} {m n} → Vec A m → Vec A n → Vec A (m + n)
_++_ [] ys = ys
_++_ (x :: xs) ys = x :: xs ++ ys
