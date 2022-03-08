module Control.Optics where

open import Data.Type
open import Data.Core
open import Data.Product
open import Data.Function
open import Category.Functor
open import Category.Monad
open import Category.Monad.Identity
open import Category.Monad.Const
open import Category.Functor.Profunctor

Simple : ∀ {a} → (F : (S T A B : Type a) → Type a) → (S A : Type a) → Type a
Simple F S A = F S S A A

Optic : ∀ {a} → (P : Type a → Type a → Type a) → (S T A B : Type a) → Type a
Optic P S T A B = P A B → P S T

Iso : ∀ {a} → (S T A B : Type a) → Type (lsuc a)
Iso {a} S T A B = {P : Type a → Type a → Type a} ⦃ _ : Profunctor P ⦄ → Optic P S T A B

Lens : ∀ {a} → (S T A B : Type a) → Type (lsuc a)
Lens {a} S T A B = {P : Type a → Type a → Type a} ⦃ _ : Strong P ⦄ → Optic P S T A B

Getter : ∀ {a} → (S A : Type a) → Type a
Getter S A = Optic (Star (Const A)) S S A A

Setter : ∀ {a} → (S T A B : Type a) → Type a
Setter S T A B = Optic (Star Identity) S T A B

iso : ∀ {a} {S T A B : Type a} → (S → A) → (B → T) → Iso S T A B
iso sa bt = dimap sa bt

lens : ∀ {a} {S T A B : Type a} → (S → A) → (S → B → T) → Lens S T A B
lens getter setter = dimap (λ s → (getter s , s)) (λ (b , s) → setter s b) ∘ first

view : ∀ {a} {S A : Type a} → Optic (Star (Const A)) S S A A → S → A
view l = getConst ∘ runStar (l (mkStar mkConst))
