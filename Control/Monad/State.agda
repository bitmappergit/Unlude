module Control.Monad.State where

open import Data.Type
open import Data.Function
open import Control.Functor
open import Control.Applicative
open import Control.Monad
open import Data.Product
open import Control.Monad.Identity
open import Data.Unit
open import Control.Lens
open import Algebra.Semiring
open import Algebra.Ring

record StateT (S : Type) (M : Type → Type) (A : Type) : Type where
  constructor mkStateT
  field runStateT : S → M (A × S)

open StateT public

state : ∀ {S A M} ⦃ _ : Monad M ⦄ → (S → (A × S)) → StateT S M A
state f = mkStateT (return ∘ f)

State : Type → Type → Type
State S A = StateT S Identity A

runState : {S A : Type} → State S A → S → (A × S)
runState m = runIdentity ∘ runStateT m

evalState : {S A : Type} → State S A → S → A
evalState m s = fst (runState m s)

instance FunctorStateT : ∀ {S M} ⦃ _ : Monad M ⦄ → Functor (StateT S M)

FunctorStateT. map f m = mkStateT λ s → map (λ (a , x) → (f a , x)) (runStateT m s)

instance ApplicativeStateT : ∀ {S M} ⦃ _ : Monad M ⦄ → Applicative (StateT S M)

ApplicativeStateT. pure a = mkStateT λ s → return (a , s)
 
ApplicativeStateT. _<*>_ (mkStateT mf) (mkStateT mx) = mkStateT λ s →
  do (f , sf) ← mf s
     (x , sx) ← mx sf
     return (f x , sx)

instance MonadStateT : ∀ {S M} ⦃ _ : Monad M ⦄ → Monad (StateT S M)

MonadStateT. _>>=_ m k = mkStateT λ s →
  do (a , ns) ← runStateT m s
     runStateT (k a) ns

gets : ∀ {S A M} ⦃ _ : Monad M ⦄ → (S → A) → StateT S M A
gets f = state λ s → (f s , s)

modify : ∀ {S M} ⦃ _ : Monad M ⦄ → (S → S) → StateT S M ⊤
modify f = state λ s → (unit , f s)

get : ∀ {S M} ⦃ _ : Monad M ⦄ → StateT S M S
get = state λ s → (s , s)

_%=_ : ∀ {S A M} ⦃ _ : Monad M ⦄ → MonoSetter S A → (A → A) → StateT S M ⊤
_%=_ l f = modify (l %~ f)

_:=_ : ∀ {S A M} ⦃ _ : Monad M ⦄ → MonoSetter S A → A → StateT S M ⊤
_:=_ l x = modify (l :~ x)

_+=_ : ∀ {S A M} ⦃ _ : Monad M ⦄ ⦃ _ : Semiring A ⦄ → MonoSetter S A → A → StateT S M ⊤
_+=_ l f = modify (l %~ _+ f)

_-=_ : ∀ {S A M} ⦃ _ : Monad M ⦄ ⦃ _ : Ring A ⦄ → MonoSetter S A → A → StateT S M ⊤
_-=_ l f = modify (l %~ _- f)

use : ∀ {S A M} ⦃ _ : Monad M ⦄ → MonoGetter S A → StateT S M A
use = gets ∘ view
