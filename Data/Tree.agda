module Data.Tree where

open import Data.Type
open import Data.Core
open import Relation.Equality
open import Data.Nat
open import Data.Num
open import Data.Fin
open import Data.Sum
open import Algebra.Semiring
open import Relation.Equality
open import Relation.Negation
open import Data.Function

data Tree {a} (A : Type a) : Nat → Type a where
  leaf : A → Tree A 1
  node : {s n : Nat}
       → A
       → Tree A s
       → Tree A s
       → ⦃ prf : n ≡ s + s ⦄
       → Tree A (suc n)

hm : Tree Nat 15
hm = node 0 (node 1 (node 2 (leaf 3)
                            (leaf 4))
                    (node 5 (leaf 6)
                            (leaf 7)))
            (node 8 (node 9 (leaf 10)
                            (leaf 11))
                    (node 12 (leaf 13)
                             (leaf 14)))

zip-with : ∀ {a} {A B C : Type a} {s : Nat}
         → (A → B → C)
         → Tree A s
         → Tree B s
         → Tree C s
zip-with f (leaf x) (leaf y) = leaf (f x y)
zip-with f (node x xl xr ⦃ xprf ⦄) (node y yl yr ⦃ yprf ⦄)
  = node (f x y) (zip-with f xl (subst (Tree _) yprf yl)) (zip-with f xr yr)

index : ∀ {a} {A : Type a} {s : Nat} → Fin s → Tree A s → A
index zero (leaf x) = x
index zero (node x _ _) = x
index (suc i) (node {s} _ l r ⦃ prf = prf ⦄) with splitAt s (subst Fin prf i)
... | inj₁ c = index c l
... | inj₂ c = index c r

update : ∀ {a} {A : Type a} {s : Nat} → Fin s → A → Tree A s → Tree A s
update zero n (leaf _) = leaf n
update zero n (node _ l r) = node n l r
update (suc i) n (node {s} x l r ⦃ prf = prf ⦄) with splitAt s (subst Fin prf i)
... | inj₁ c = node x (update c n l) r
... | inj₂ c = node x l (update c n r)
