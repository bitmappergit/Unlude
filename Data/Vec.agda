module Data.Vec where

open import Data.Type
open import Data.Core
open import Data.Nat
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Algebra.Semiring
open import Data.Function
open import Algebra.Semigroup
open import Algebra.Monoid
open import Data.Fin
open import Data.Indexable
open import Data.Foldable
open import Data.Traversable

infixr 5 _∷_ _++_

data Vec {ℓ} (A : Type ℓ) : Nat → Type ℓ where
  _∷_ : {s : Nat} → A → Vec A s → Vec A (suc s)
  [] : Vec A 0

instance FunctorVec : ∀ {ℓ} {s} → Functor {ℓ} (λ A → Vec A s)

FunctorVec. map f (x ∷ xs) = f x ∷ map f xs
FunctorVec. map _ [] = []

replicate : ∀ {ℓ} {s} {A : Type ℓ} → A → Vec A s
replicate {s = suc x} val = val ∷ replicate {s = x} val
replicate {s = zero} val = []

tail : ∀ {ℓ} {A : Type ℓ} {s} → Vec A (suc s) → Vec A s
tail (_ ∷ xs) = xs

head : ∀ {ℓ} {A : Type ℓ} {s} → Vec A (suc s) → A
head (x ∷ _) = x

drop : ∀ {ℓ} {A : Type ℓ} {s} → (t : Nat) → Vec A (t + s) → Vec A s
drop (suc t) (_ ∷ xs) = drop t xs
drop zero result = result

take : ∀ {ℓ} {A : Type ℓ} {s} → (t : Nat) → Vec A (t + s) → Vec A t
take (suc t) (x ∷ xs) = x ∷ take t xs
take zero _ = []

_++_ : ∀ {ℓ} {A : Type ℓ} {m n} → Vec A m → Vec A n → Vec A (m + n)
_++_ [] ys = ys
_++_ (x ∷ xs) ys = x ∷ xs ++ ys

snoc : ∀ {ℓ} {A : Type ℓ} {m} → A → Vec A m → Vec A (suc m)
snoc v (x ∷ xs) = x ∷ snoc v xs
snoc v [] = v ∷ []

butLast : ∀ {ℓ} {A : Type ℓ} {s} → Vec A (suc s) → Vec A s
butLast {s = suc s} (x ∷ xs) = x ∷ butLast {s = s} xs
butLast (x ∷ []) = []

last : ∀ {ℓ} {A : Type ℓ} {s} → Vec A (suc s) → A
last {s = suc s} (_ ∷ xs) = last {s = s} xs
last (x ∷ []) = x

zipWith : ∀ {ℓ} {A B C : Type ℓ} {s} → (A → B → C) → Vec A s → Vec B s → Vec C s
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
zipWith _ [] [] = []

instance IndexableVec : ∀ {s} → Indexable (λ A → Vec A s) (Fin s)

-- index : ∀ {ℓ} {A : Type ℓ} {s} → Fin s → Vec A s → A
IndexableVec. index (suc c) (_ ∷ xs) = index c xs
IndexableVec. index zero (x ∷ xs) = x

-- update : ∀ {ℓ} {A : Type ℓ} {s} → Fin s → A → Vec A s → Vec A s
IndexableVec. update (suc c) n (x ∷ xs) = x ∷ update c n xs
IndexableVec. update zero n (_ ∷ xs) = n ∷ xs

instance ApplicativeVec : ∀ {ℓ} {s} → Applicative {ℓ} (λ A → Vec A s)

ApplicativeVec. pure x = replicate x
ApplicativeVec. _<*>_ (f ∷ fs) (x ∷ xs) = f x ∷ (fs <*> xs)
ApplicativeVec. _<*>_ [] [] = []

diag : ∀ {ℓ} {s} {A : Type ℓ} → Vec (Vec A s) s → Vec A s
diag [] = []
diag ((x ∷ xs) ∷ xss) = x ∷ diag (map tail xss)

instance MonadVec : ∀ {ℓ} {s} → Monad {ℓ} (λ A → Vec A s)

MonadVec. _>>=_ m f = diag (map f m)

instance FoldableVec : ∀ {ℓ} {s} → Foldable {ℓ} (λ A → Vec A s)

FoldableVec. foldr _ v [] = v
FoldableVec. foldr f v (x ∷ xs) = f x (foldr f v xs)

instance TraversableVec : ∀ {ℓ} {s} → Traversable {ℓ} (λ A → Vec A s)

TraversableVec. traverse f [] = pure []
TraversableVec. traverse f (x ∷ xs) = _∷_ <$> f x <*> traverse f xs

{-
diag : Vect len (Vect len elem) -> Vect len elem
diag []             = []
diag ((x::xs)::xss) = x :: diag (map tail xss)
-}
