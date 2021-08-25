module Data.Vec where

open import Data.Type

open import Data.Nat
open import Category.Functor
open import Algebra.Semiring
open import Data.Function
open import Algebra.Semigroup
open import Algebra.Monoid
open import Data.Fin
open import Data.Indexable

infixr 5 _∷_ _++_

data Vec {ℓ} (A : Type ℓ) : Nat → Type ℓ where
  _∷_ : {s : Nat} → A → Vec A s → Vec A (suc s)
  [] : Vec A 0

replicate : ∀ {ℓ} {s} {A : Type ℓ} → A → Vec A s
replicate {s = suc x} val = val ∷ replicate {s = x} val
replicate {s = zero} val = []

instance FunctorVec : ∀ {ℓ} {s} → Functor {ℓ} (λ A → Vec A s)

FunctorVec. map f (x ∷ xs) = f x ∷ map f xs
FunctorVec. map _ [] = []

drop : ∀ {ℓ} {A : Type ℓ} {s} → (t : Nat) → Vec A (t + s) → Vec A s
drop (suc t) (_ ∷ xs) = drop t xs
drop zero result = result

take : ∀ {ℓ} {A : Type ℓ} {s} → (t : Nat) → Vec A (t + s) → Vec A t
take (suc t) (x ∷ xs) = x ∷ take t xs
take zero _ = []

_++_ : ∀ {ℓ} {A : Type ℓ} {m n} → Vec A m → Vec A n → Vec A (m + n)
_++_ [] ys = ys
_++_ (x ∷ xs) ys = x ∷ xs ++ ys

snoc : ∀ {ℓ} {A : Type ℓ} {m} → A → Vec A m → Vec A (suc m)
snoc v (x ∷ xs) = x ∷ snoc v xs
snoc v [] = v ∷ []

but-last : ∀ {ℓ} {A : Type ℓ} {s} → Vec A (suc s) → Vec A s
but-last {s = suc s} (x ∷ xs) = x ∷ but-last {s = s} xs
but-last (x ∷ []) = []

last : ∀ {ℓ} {A : Type ℓ} {s} → Vec A (suc s) → A
last {s = suc s} (_ ∷ xs) = last {s = s} xs
last (x ∷ []) = x

zip-with : ∀ {ℓ} {A B C : Type ℓ} {s} → (A → B → C) → Vec A s → Vec B s → Vec C s
zip-with f (x ∷ xs) (y ∷ ys) = f x y ∷ zip-with f xs ys
zip-with _ [] [] = []

instance IndexableVec : ∀ {s} → Indexable (λ A → Vec A s) (Fin s)

-- index : ∀ {ℓ} {A : Type ℓ} {s} → Fin s → Vec A s → A
IndexableVec. index (suc c) (_ ∷ xs) = index c xs
IndexableVec. index zero (x ∷ xs) = x

-- update : ∀ {ℓ} {A : Type ℓ} {s} → Fin s → A → Vec A s → Vec A s
IndexableVec. update (suc c) n (x ∷ xs) = x ∷ update c n xs
IndexableVec. update zero n (_ ∷ xs) = n ∷ xs
