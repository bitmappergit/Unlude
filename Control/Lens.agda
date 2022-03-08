module Control.Lens where

open import Data.Type
open import Data.Function
open import Category.Functor
open import Category.Monad
open import Category.Monad.Identity
open import Category.Monad.Const
open import Category.Functor.Profunctor

record Exchange {a} (A B S T : Type a) : Type a where
  constructor exchange
  field sa : (S → A)
  field bt : (B → T)

instance ProfunctorExchange : ∀ {a} {A B : Type a} → Profunctor (Exchange A B)

ProfunctorExchange. promap f g (exchange sa bt) = exchange (sa ∘ f) (g ∘ bt)

instance FunctorExchange : ∀ {a} {A S B : Type a} → Functor (Exchange A B S)

FunctorExchange. map f (exchange sa bt) = exchange sa (f ∘ bt)

Iso : ∀ {a} → (S T A B : Type a) → Type (lsuc a)
Iso {a} S T A B = {P : Type a → Type a → Type a}
                → {F : Type a → Type a}
                → ⦃ _ : Profunctor P ⦄
                → ⦃ _ : Functor F ⦄
                → P A (F B)
                → P S (F T)

MonoIso : ∀ {a} → (S A : Type a) → Type (lsuc a)
MonoIso S A = Iso S S A A

AnIso : ∀ {a} → (S T A B : Type a) → Type a
AnIso S T A B = Exchange A B A (Identity B) → Exchange A B S (Identity S)

MonoAnIso : ∀ {a} → (S A : Type a) → Type a
MonoAnIso S A = AnIso S S A A

iso : ∀ {a} {S T A B : Type a} → (S → A) → (B → T) → Iso S T A B
iso sa bt = promap sa (map bt)

Lens : ∀ {a} → (S T A B : Type a) → Type (lsuc a)
Lens {a} S T A B = {F : Type a → Type a}
                 → ⦃ _ : Functor F ⦄
                 → (A → F B)
                 → (S → F T)

MonoLens : ∀ {a} → (S A : Type a) → Type (lsuc a)
MonoLens S A = Lens S S A A

Setter : ∀ {a} → (S T A B : Type a) → Type a
Setter S T A B = (A → Identity B) → (S → Identity T)

MonoSetter : ∀ {a} → (S A : Type a) → Type a
MonoSetter S A = Setter S S A A

Getter : ∀ {a} → (R S A : Type a) → Type a
Getter R S A = (A → Const R A) → (S → Const R S)

MonoGetter : ∀ {a} → (S A : Type a) → Type a
MonoGetter S A = Getter A S A

view : ∀ {a} {S A : Type a} → Getter A S A → S → A
view l = getConst ∘ l mkConst

over : ∀ {a} {S T A B : Type a} → Setter S T A B → (A → B) → S → T
over l f = runIdentity ∘ l (mkIdentity ∘ f)

set : ∀ {a} {S T A B : Type a} → Setter S T A B → B → S → T
set l a = runIdentity ∘ l (mkIdentity ∘ const a)
 
infixr 4 _%~_
infixr 4 _:~_
infixr 4 _∙_

_%~_ : ∀ {a} {S T A B : Type a} → Setter S T A B → (A → B) → S → T
_%~_ = over

_:~_ : ∀ {a} {S T A B : Type a} → Setter S T A B → B → S → T
_:~_ = set

_∙_ : ∀ {a} {S A : Type a} → S → Getter A S A → A
_∙_ = flip view

lens : ∀ {a} {S T A B : Type a} → (S → A) → (S → B → T) → Lens S T A B
lens sa sbt afb s = sbt s <$> afb (sa s)
