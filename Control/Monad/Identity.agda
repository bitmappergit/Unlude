module Control.Monad.Identity where

open import Data.Type
open import Control.Functor
open import Control.Applicative
open import Control.Monad

record Identity {ℓ} (A : Type ℓ) : Type ℓ where
  constructor mkIdentity
  field runIdentity : A

open Identity public

instance FunctorIdentity : ∀ {ℓ} → Functor {ℓ} Identity
instance ApplicativeIdentity : ∀ {ℓ} → Applicative {ℓ} Identity
instance MonadIdentity : ∀ {ℓ} → Monad {ℓ} Identity

FunctorIdentity. map f (mkIdentity x) = mkIdentity (f x)

ApplicativeIdentity. _<*>_ (mkIdentity f) (mkIdentity x) = mkIdentity (f x)
ApplicativeIdentity. pure = mkIdentity

MonadIdentity. _>>=_ (mkIdentity v) f = f v
