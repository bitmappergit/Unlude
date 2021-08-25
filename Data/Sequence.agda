module Data.Sequence where

open import Data.Type
open import Data.Nat
open import Algebra.Semiring
open import Algebra.Ring
open import Data.Bool
open import Data.Ord
open import Data.Option
open import Category.Monad
open import Data.List
open import Data.Product
open import Relation.Nat
open import Relation.Equality
open import Relation.Negation
open import Data.Unit
open import Data.Empty
open import Data.Fin
open import Data.Indexable

data Tree {ℓ} (A : Type ℓ) : Nat → Type ℓ where
  leaf : A → Tree A 1
  node : ∀ {s} → A → Tree A s → Tree A s → Tree A (suc (s + s))

tree-index : ∀ {ℓ} {A : Type ℓ} {s} → Nat → Tree A s → Option A
tree-index zero (leaf x) = some x
tree-index (suc _) (leaf x) = none
tree-index zero (node x _ _) = some x
tree-index (suc i) (node {cs} x a b) with i <ᵇ cs
... | #t = tree-index i a
... | #f = tree-index (i ∸ cs) a

tree-update : ∀ {ℓ} {A : Type ℓ} {s} → Nat → A → Tree A s → Option (Tree A s)
tree-update zero n (leaf _) = some (leaf n)
tree-update (suc _) _ (leaf _) = none
tree-update zero n (node x a b) = some (node n a b)
tree-update i@(suc _) n (node {cs} x a b) with i <ᵇ cs
... | #t = tree-update i n a >>= λ c → some (node x c b)
... | #f = tree-update i n b >>= λ c → some (node x a c)

Seq : ∀ {ℓ} → Type ℓ → Type ℓ
Seq A = List (Σ Nat (Tree A))

indexˢ : ∀ {ℓ} {A : Type ℓ} → Nat → Seq A → Option A
indexˢ _ [] = none
indexˢ i ((s , t) ∷ rest) with i <ᵇ s
... | #t = tree-index i t
... | #f = indexˢ (i ∸ s) rest

updateˢ : ∀ {ℓ} {A : Type ℓ} → Nat → A → Seq A → Option (Seq A)
updateˢ _ _ [] = none
updateˢ i y ((s , t) ∷ rest) with i <ᵇ s
... | #t = tree-update i y t >>= λ n → some ((s , n) ∷ rest)
... | #f = updateˢ (i ∸ s) y rest >>= λ n → some ((s , t) ∷ n)

infixr 5 _∷ˢ_

_∷ˢ_ : ∀ {ℓ} {A : Type ℓ} → A → Seq A → Seq A
_∷ˢ_ {A = A} x xs@((sa , a) ∷ (sb , b) ∷ rest) with sb ≟ sa
... | yes sb≡sa = (suc (sa + sa) , node x a (subst (Tree A) sb≡sa b)) ∷ rest
... | no _ = (1 , leaf x) ∷ xs
_∷ˢ_ x xs@(_ ∷ []) = (1 , leaf x) ∷ xs
_∷ˢ_ x [] = (1 , leaf x) ∷ []

head : ∀ {ℓ} {A : Type ℓ} → Seq A → Option A
head [] = none
head ((_ , leaf x) ∷ rest) = some x
head ((_ , node x _ _) ∷ rest) = some x

tail : ∀ {ℓ} {A : Type ℓ} → Seq A → Option (Seq A)
tail [] = none
tail ((_ , leaf _) ∷ rest) = some rest
tail ((_ , node {s} x a b) ∷ rest) = some ((s , a) ∷ (s , b) ∷ rest)
