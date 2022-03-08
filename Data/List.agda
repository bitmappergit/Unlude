module Data.List where

open import Data.Type
open import Data.Core
open import Data.Option
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Algebra.Semigroup
open import Algebra.Monoid
open import Data.Foldable
open import Data.Traversable
open import Data.Function

instance SemigroupList : ∀ {ℓ} {A : Type ℓ} → Semigroup (List A)

SemigroupList. _<>_ tx ty with tx
... | [] = ty
... | x ∷ xs = x ∷ xs <> ty

instance MonoidList : ∀ {ℓ} {A : Type ℓ} → Monoid (List A)

MonoidList. empty = []

instance FunctorList : ∀ {ℓ} → Functor {ℓ} List

FunctorList. map f t with t
... | x ∷ xs = f x ∷ map f xs
... | [] = []

instance ApplicativeList : ∀ {ℓ} → Applicative {ℓ} List

ApplicativeList. pure x = x ∷ []
ApplicativeList. _<*>_ fa fb with fa | fb
... | f ∷ fs | x ∷ xs = f x ∷ (fs <*> xs)
... | []     | _ ∷ _  = []
... | _ ∷ _  | []     = []
... | []     | []     = []

instance MonadList : ∀ {ℓ} → Monad {ℓ} List

MonadList. _>>=_ t f with t
... | x ∷ xs = f x <> (xs >>= f)
... | [] = []

instance FoldableList : ∀ {ℓ} → Foldable {ℓ} List

FoldableList. foldr f v t with t
... | [] = v
... | x ∷ xs = f x (foldr f v xs)

FoldableList. foldl f v t with t
... | [] = v
... | x ∷ xs = f (foldl f v xs) x

instance TraversableList : ∀ {ℓ} → Traversable {ℓ} List

TraversableList. traverse f = foldr (λ x ys → liftA2 _∷_ (f x) ys) (pure [])
