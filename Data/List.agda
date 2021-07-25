module Data.List where

open import Data.Type
open import Data.Option
open import Control.Functor
open import Algebra.Semigroup
open import Algebra.Monoid

infixr 5 _::_

data List {ℓ} (A : Type ℓ) : Type ℓ where
  _::_ : A → List A → List A
  [] : List A

{-# BUILTIN LIST List #-}

instance FunctorList : ∀ {ℓ} → Functor {ℓ} List

FunctorList. map f (x :: xs) = f x :: map f xs
FunctorList. map _ [] = []

instance SemigroupList : ∀ {ℓ} {A : Type ℓ} → Semigroup (List A)

SemigroupList. _<>_ [] ys = ys
SemigroupList. _<>_ (x :: xs) ys = x :: xs <> ys

instance MonoidList : ∀ {ℓ} {A : Type ℓ} → Monoid (List A)

MonoidList. empty = []

foldMap : ∀ {ℓ} {A M : Type ℓ} ⦃ _ : Monoid M ⦄ → (A → M) → List A → M
foldMap f (x :: xs) = f x <> foldMap f xs
foldMap f [] = empty
