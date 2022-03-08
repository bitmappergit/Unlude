module Data.Function where

open import Data.Type
open import Data.Core

infixr 0 _$_
infixr 9 _∘_
infixl 1 _&_

id : ∀ {ℓ} {A : Type ℓ} → A → A
id x = x

{-# INLINE id #-}

const : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → A → B → A
const x _ = x

{-# INLINE const #-}

_$_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
    → ((x : A) → B x)
    → (x : A)
    → B x
_$_ f x = f x

{-# INLINE _$_ #-}

_&_ : ∀ {ℓ₁ ℓ₂}
    → {A : Type ℓ₁}
    → {B : A → Type ℓ₂}
    → (x : A)
    → ((x : A) → B x)
    → B x
_&_ x f = f x

{-# INLINE _&_ #-}

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃}
    → {A : Type ℓ₁}
    → {B : A → Type ℓ₂}
    → {C : (x : A) → B x → Type ℓ₃}
    → (f : {x : A} → (y : B x) → C x y)
    → (g : (x : A) → B x)
    → ((x : A) → C x (g x))
_∘_ f g = λ x → f (g x)

{-# INLINE _∘_ #-}

flip : ∀ {ℓ₁ ℓ₂ ℓ₃}
     → {A : Type ℓ₁}
     → {B : Type ℓ₂}
     → {C : A → B → Type ℓ₃}
     → ((x : A) (y : B) → C x y)
     → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

{-# INLINE flip #-}

_∘′_ : ∀ {ℓ} {A B C : Type ℓ} → (B → C) → (A → B) → (A → C)
_∘′_ f g = λ x → f (g x)

{-# INLINE _∘′_ #-}

flip′ : ∀ {ℓ} {A B C : Type ℓ} → (A → B → C) → (B → A → C)
flip′ f = λ y x → f x y

{-# INLINE flip′ #-}

case_of_ : ∀ {ℓ₁ ℓ₂}
         → {A : Type ℓ₁}
         → {B : A → Type ℓ₂}
         → (x : A)
         → ((x : A) → B x)
         → B x
case_of_ = _&_

infix 0 case_of_

{-# INLINE case_of_ #-}

repeat : ∀ {ℓ} {A : Type ℓ} → Nat → (A → A) → A → A
repeat (suc c) f = f ∘ repeat c f
repeat zero _ = id

{-# INLINE repeat #-}

the : ∀ {ℓ} → (A : Type ℓ) → A → A
the _ v = v

{-# INLINE the #-}
