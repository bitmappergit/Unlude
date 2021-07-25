module Control.Lens where

open import Data.Type
open import Data.Function
open import Category.Functor
open import Category.Monad.Identity
open import Category.Monad.Const
open import Category.Functor.Profunctor

record Exchange {ℓ} (A B S T : Type ℓ) : Type ℓ where
  constructor exchange
  field sa : (S → A)
  field bt : (B → T)

instance ProfunctorExchange : ∀ {ℓ} {A B : Type ℓ} → Profunctor (Exchange A B)

ProfunctorExchange. dimap f g (exchange sa bt) = exchange (sa ∘ f) (g ∘ bt)

instance FunctorExchange : ∀ {ℓ} {A S B : Type ℓ} → Functor (Exchange A B S)

FunctorExchange. map f (exchange sa bt) = exchange sa (f ∘ bt)

Iso : ∀ {ℓ} → (S T A B : Type ℓ) → Type (lsuc ℓ)
Iso {ℓ} S T A B = {P : Type ℓ → Type ℓ → Type ℓ}
                → {F : Type ℓ → Type ℓ}
                → ⦃ _ : Profunctor P ⦄
                → ⦃ _ : Functor F ⦄
                → P A (F B)
                → P S (F T)

MonoIso : ∀ {ℓ} → (S A : Type ℓ) → Type (lsuc ℓ)
MonoIso S A = Iso S S A A

AnIso : ∀ {ℓ} → (S T A B : Type ℓ) → Type ℓ
AnIso S T A B = Exchange A B A (Identity B) → Exchange A B S (Identity S)

MonoAnIso : ∀ {ℓ} → (S A : Type ℓ) → Type ℓ
MonoAnIso S A = AnIso S S A A

iso : ∀ {ℓ} {S T A B : Type ℓ} → (S → A) → (B → T) → Iso S T A B
iso sa bt = dimap sa (map bt)

Lens : ∀ {ℓ} → (S T A B : Type ℓ) → Type (lsuc ℓ)
Lens {ℓ} S T A B = {F : Type ℓ → Type ℓ}
                 → ⦃ _ : Functor F ⦄
                 → (A → F B)
                 → (S → F T)

MonoLens : ∀ {ℓ} → (S A : Type ℓ) → Type (lsuc ℓ)
MonoLens S A = Lens S S A A

Setter : ∀ {ℓ} → (S T A B : Type ℓ) → Type ℓ
Setter S T A B = (A → Identity B) → (S → Identity T)

MonoSetter : ∀ {ℓ} → (S A : Type ℓ) → Type ℓ
MonoSetter S A = Setter S S A A

Getter : ∀ {ℓ} → (R S A : Type ℓ) → Type ℓ
Getter R S A = (A → Const R A) → (S → Const R S)

MonoGetter : ∀ {ℓ} → (S A : Type ℓ) → Type ℓ
MonoGetter S A = Getter A S A

view : ∀ {ℓ} {S A : Type ℓ} → Getter A S A → S → A
view l = getConst ∘ l mkConst

over : ∀ {ℓ} {S T A B : Type ℓ} → Setter S T A B → (A → B) → S → T
over l f = runIdentity ∘ l (mkIdentity ∘ f)

set : ∀ {ℓ} {S T A B : Type ℓ} → Setter S T A B → B → S → T
set l a = runIdentity ∘ l (mkIdentity ∘ const a)
 
infixr 4 _%~_
infixr 4 _:~_
infixr 4 _at_

_%~_ : ∀ {ℓ} {S T A B : Type ℓ} → Setter S T A B → (A → B) → S → T
_%~_ = over

_:~_ : ∀ {ℓ} {S T A B : Type ℓ} → Setter S T A B → B → S → T
_:~_ = set

_at_ : ∀ {ℓ} {S A : Type ℓ} → S → Getter A S A → A
_at_ = flip view

lens : ∀ {ℓ} {S T A B : Type ℓ} → (S → A) → (S → B → T) → Lens S T A B
lens sa sbt afb s = sbt s <$> afb (sa s)
