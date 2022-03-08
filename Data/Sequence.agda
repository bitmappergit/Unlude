module Data.Sequence where

open import Data.Type
open import Data.Core
open import Data.Nat
open import Data.Num
open import Algebra.Semiring
open import Algebra.Ring
open import Data.Bool
open import Data.Ord
open import Category.Monad
open import Data.List
open import Relation.Nat
open import Relation.Equality
open import Relation.Negation
open import Data.Unit
open import Data.Empty
open import Data.Fin
open import Data.Indexable
open import Data.Sum
open import Category.Functor
open import Data.Foldable
open import Data.Vec

data Tree {a} (A : Type a) : Nat → Type a where
  leaf : A → Tree A 1
  node : ∀ {s} → A → Tree A s → Tree A s → Tree A (suc (s + s))

{-
treeZipWith : ∀ {a} {A B C : Type a} {s : Nat} → (A → B → C) → Tree A s → Tree B s → Tree C s
treeZipWith f (node x xl xr) (node y yl yr) = node (f x y) (treeZipWith f xl yl) (treeZipWith f xr yr)
treeZipWith f (leaf x) (leaf y) = leaf (f x y)
-}

instance IndexableTree : {s : Nat} → Indexable (λ A → Tree A s) (Fin s)

IndexableTree. index zero (leaf x) = x
IndexableTree. index zero (node x _ _) = x
IndexableTree. index (suc i) (node {cs} _ a b) with splitAt cs i
... | inj₁ c = index c a
... | inj₂ c = index c b

IndexableTree. update zero n (leaf _) = leaf n
IndexableTree. update zero n (node _ a b) = node n a b
IndexableTree. update (suc i) n (node {cs} x a b) with splitAt cs i
... | inj₁ c = node x (update c n a) b
... | inj₂ c = node x a (update c n b)

instance FunctorTree : ∀ {a} {s : Nat} → Functor {a} (λ A → Tree A s)

FunctorTree. map f (leaf x) = leaf (f x)
FunctorTree. map f (node x l r) = node (f x) (map f l) (map f r)

data Seq {a} (A : Type a) : Nat → Type a where
  _∷_ : {s o : Nat} → Tree A s → Seq A o → Seq A (s + o)
  [] : Seq A 0

instance IndexableSeq : {s : Nat} → Indexable (λ A → Seq A s) (Fin s)

IndexableSeq. index i (_∷_ {s = s} t rest) with splitAt s i
... | inj₁ c = index c t
... | inj₂ c = index c rest

IndexableSeq. update i y (_∷_ {s = s} t rest) with splitAt s i
... | inj₁ c = _∷_ {s = s} (update c y t) rest
... | inj₂ c = _∷_ {s = s} t (update c y rest)

instance FunctorSeq : ∀ {ℓ} {s : Nat} → Functor {ℓ} (λ A → Seq A s)

FunctorSeq. map f (x ∷ xs) = map f x ∷ map f xs
FunctorSeq. map _ [] = []
-- subst (λ a+b → a + a + c ≡ a+b + c) a+a≡a+b refl
infixr 5 _<:_
{-
_::_ : ∀ {a} {s : Nat} {A : Type a} → A → Seq A s → Seq A (suc s)
_::_ {A = A} x seq@(_∷_ {sa} a (_∷_ {sb} {ob} b rest)) with sb ≟ sa
... | no _ = leaf x ∷ seq
... | yes pa with suc (sa + sa + ob) ≟ suc (sa + (sb + ob))
...             | yes pb = subst (Seq A) pb (node x a (subst (Tree A) pa b) ∷ rest)
...             | no _ = leaf x ∷ seq
_::_ x seq@(_ ∷ []) = leaf x ∷ seq
_::_ x [] = leaf x ∷ []
-}
_<:_ : ∀ {a} {A : Type a} {s : Nat} → A → Seq A s → Seq A (1 + s)
_<:_ {_} {A} x seq@(_∷_ {headA} {tailA} a (_∷_ {headB} {tailB} b rest)) with headA ≟ headB
... | no _ = leaf x ∷ seq
... | yes headA≡headB rewrite sym (+-assoc headA headB tailB)
           = let headA+headA≡headA+headB = subst (λ headB → headA + headA ≡ headA + headB) headA≡headB refl
                 headA+headA+tailB≡headA+headB+tailB = subst (λ headA+headB → headA + headA + tailB ≡ headA+headB + tailB) headA+headA≡headA+headB refl
                 suc[headA+headA+tailB]≡suc[headA+headB+tailB] = cong suc headA+headA+tailB≡headA+headB+tailB
                 headB≡headA = sym headA≡headB
             in subst (Seq A) suc[headA+headA+tailB]≡suc[headA+headB+tailB] (node x a (subst (Tree A) headB≡headA b) ∷ rest)
_<:_ x seq@(_ ∷ []) = leaf x ∷ seq
_<:_ x [] = leaf x ∷ []

toSeq : ∀ {a} {A : Type a} {s : Nat} → Vec A s → Seq A s
toSeq (x ∷ xs) = x <: toSeq xs
toSeq [] = []

treeToVec : ∀ {a} {A : Type a} {s : Nat} → Tree A s → Vec A s
treeToVec (node x l r) = x ∷ treeToVec l ++ treeToVec r
treeToVec (leaf x) = x ∷ []

toVec : ∀ {a} {A : Type a} {s : Nat} → Seq A s → Vec A s
toVec (x ∷ xs) = treeToVec x ++ toVec xs
toVec [] = []
