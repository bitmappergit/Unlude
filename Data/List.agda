module Data.List where

open import Data.Type
open import Data.Option
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Algebra.Semigroup
open import Algebra.Monoid
open import Data.Foldable
open import Data.Traversable
open import Data.Core using (List; _∷_; []) public

instance SemigroupList : ∀ {ℓ} {A : Type ℓ} → Semigroup (List A)

SemigroupList. _<>_ [] ys = ys
SemigroupList. _<>_ (x ∷ xs) ys = x ∷ xs <> ys

instance MonoidList : ∀ {ℓ} {A : Type ℓ} → Monoid (List A)

MonoidList. empty = []

instance FunctorList : ∀ {ℓ} → Functor {ℓ} List

FunctorList. map f (x ∷ xs) = f x ∷ map f xs
FunctorList. map _ [] = []

instance ApplicativeList : ∀ {ℓ} → Applicative {ℓ} List

ApplicativeList. pure x = x ∷ []
ApplicativeList. _<*>_ (f ∷ fs) (x ∷ xs) = f x ∷ (fs <*> xs)
ApplicativeList. _<*>_ [] (_ ∷ _) = []
ApplicativeList. _<*>_ (_ ∷ _) [] = []
ApplicativeList. _<*>_ [] [] = []

instance MonadList : ∀ {ℓ} → Monad {ℓ} List

MonadList. _>>=_ (x ∷ xs) f = f x <> (xs >>= f)
MonadList. _>>=_ [] _ = []
{-
foldMap : ∀ {ℓ}
        → {A : Type ℓ}
        → {F : Type ℓ → Type ℓ}
        → ⦃ _ : Foldable F ⦄
        → (A → B → B)
        → B
        → T A
        → B
foldMap f (x ∷ xs) = f x <> foldMap f xs
foldMap f [] = empty
-}
