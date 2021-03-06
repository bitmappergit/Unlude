module Relation.Equality where

open import Data.Type
open import Data.Product
open import Data.Function
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

subst : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) {x y : A} → x ≡ y → P x → P y
subst _ refl a = a

cast : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
cast = subst id

record DecEq {ℓ} (A : Type ℓ) : Type ℓ where
  field _≟_ : (x : A) → (y : A) → Dec (x ≡ y)

open DecEq ⦃ ... ⦄ public


private
  primitive primEraseEquality : ∀ {a} {A : Type a} {x y : A} → x ≡ y → x ≡ y
  postulate unsafePrimTrustMe : ∀ {a} {A : Type a} {x y : A} → x ≡ y

  primTrustMe : ∀ {a} {A : Type a} {x y : A} → x ≡ y
  primTrustMe = primEraseEquality unsafePrimTrustMe
  
trustMe : ∀ {a} {A : Type a} {x y : A} → x ≡ y
trustMe = primTrustMe

erase : ∀ {a} {A : Type a} {x y : A} → x ≡ y → x ≡ y
erase _ = trustMe
