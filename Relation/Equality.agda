module Relation.Equality where

open import Data.Type
open import Data.Product
open import Relation.Negation

infix 4 _≡_

data _≡_ {ℓ} {A : Type ℓ} (x : A) : A → Type ℓ where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≢_

_≢_ : ∀ {ℓ} {A : Type ℓ} → (x y : A) → Type ℓ
x ≢ y = ¬ (x ≡ y)

cong : ∀ {ℓ} {A B : Type ℓ} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl


