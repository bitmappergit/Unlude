module Category.Monad.State where

open import Data.Type
open import Data.Core
open import Data.Function
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Data.Product
open import Category.Monad.Identity
open import Data.Unit
open import Control.Lens
open import Algebra.Semiring
open import Algebra.Ring
open import Data.Word

record StateT {ℓ} (S : Type ℓ) (M : Type ℓ → Type ℓ) (A : Type ℓ) : Type ℓ where
  constructor mkStateT
  field runStateT : S → M (A × S)

open StateT public

state : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ → (S → (A × S)) → StateT S M A
state f = mkStateT (return ∘ f)

State : ∀ {ℓ} → Type ℓ → Type ℓ → Type ℓ
State S A = StateT S Identity A

runState : ∀ {ℓ} {S A : Type ℓ} → State S A → S → (A × S)
runState m = runIdentity ∘ runStateT m

evalState : ∀ {ℓ} {S A : Type ℓ} → State S A → S → A
evalState m s = fst (runState m s)

execState : ∀ {ℓ} {S A : Type ℓ} → State S A → S → S
execState m s = snd (runState m s)

instance FunctorStateT : ∀ {ℓ} {S : Type ℓ} {M} ⦃ _ : Monad M ⦄ → Functor (StateT S M)

FunctorStateT. map f m = mkStateT λ s → map (λ (a , x) → (f a , x)) (runStateT m s)

instance ApplicativeStateT : ∀ {ℓ} {S : Type ℓ} {M : Type ℓ → Type ℓ} ⦃ _ : Monad M ⦄ → Applicative (StateT S M)

ApplicativeStateT. pure a = mkStateT λ s → return (a , s)
 
ApplicativeStateT. _<*>_ (mkStateT mf) (mkStateT mx) = mkStateT λ s →
  do (f , sf) ← mf s
     (x , sx) ← mx sf
     return (f x , sx)

instance MonadStateT : ∀ {ℓ} {S : Type ℓ} {M} ⦃ _ : Monad M ⦄ → Monad (StateT S M)

MonadStateT. _>>=_ m k = mkStateT λ s →
  do (a , ns) ← runStateT m s
     runStateT (k a) ns

gets : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ → (S → A) → StateT S M A
gets f = state λ s → (f s , s)

modify : ∀ {ℓ} {S : Type ℓ} {M} ⦃ _ : Monad M ⦄ → (S → S) → StateT S M ⊤
modify f = state λ s → (unit , f s)

get : ∀ {ℓ} {S : Type ℓ} {M} ⦃ _ : Monad M ⦄ → StateT S M S
get = state λ s → (s , s)

infix 4 _%=_ _:=_ _+=_ _*=_ _-=_

_%=_ : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ → MonoSetter S A → (A → A) → StateT S M ⊤
_%=_ l f = modify (l %~ f)

_:=_ : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ → MonoSetter S A → A → StateT S M ⊤
_:=_ l x = modify (l :~ x)

_+=_ : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ ⦃ _ : Semiring A ⦄ → MonoSetter S A → A → StateT S M ⊤
_+=_ l f = modify (l %~ _+ f)

_*=_ : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ ⦃ _ : Semiring A ⦄ → MonoSetter S A → A → StateT S M ⊤
_*=_ l f = modify (l %~ _* f)

_-=_ : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ ⦃ _ : Ring A ⦄ → MonoSetter S A → A → StateT S M ⊤
_-=_ l f = modify (l %~ _- f)

infixr 2 _<%=_ _<:=_ _<+=_ _<*=_ _<-=_ _<~_

_<%=_ : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ → MonoSetter S A → StateT S M (A → A) → StateT S M ⊤
_<%=_ l v = v >>= l %=_

_<:=_ : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ → MonoSetter S A → StateT S M A → StateT S M ⊤
_<:=_ l v = v >>= l :=_

_<+=_ : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ ⦃ _ : Semiring A ⦄ → MonoSetter S A → StateT S M A → StateT S M ⊤
_<+=_ l v = modify =<< over l <$> map _+_ v

_<*=_ : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ ⦃ _ : Semiring A ⦄ → MonoSetter S A → StateT S M A → StateT S M ⊤
_<*=_ l v = modify =<< over l <$> map _*_ v

_<-=_ : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ ⦃ _ : Ring A ⦄ → MonoSetter S A → StateT S M A → StateT S M ⊤
_<-=_ l v = modify =<< over l <$> map _-_ v

_<~_ = _<:=_

--_<^=_ : ∀ {ℓ} {s} {S : Type ℓ} {M} ⦃ _ : Monad M ⦄ → MonoSetter S (Lift ℓ (Word s)) → StateT S M (Lift ℓ (Word s)) → StateT S M ⊤
--_<^=_ l v = modify =<< over l <$> map _xor_ v

use : ∀ {ℓ} {S A : Type ℓ} {M} ⦃ _ : Monad M ⦄ → MonoGetter S A → StateT S M A
use = gets ∘ view
