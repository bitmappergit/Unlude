{-# OPTIONS --rewriting #-}

module Data.FingerTree where

open import Data.Type
open import Data.Core
open import Data.Nat
open import Algebra.Semiring
open import Data.Foldable
open import Data.Function
open import Data.List
open import Data.Vec
open import Algebra.Semigroup
open import Relation.Equality
open import Relation.Nat

{-# BUILTIN REWRITE _≡_ #-}

data Digit {ℓ : Level} (A : Type ℓ) : Nat → Type ℓ where
  digit-1 : A → Digit A 1
  digit-2 : A → A → Digit A 2
  digit-3 : A → A → A → Digit A 3
  digit-4 : A → A → A → A → Digit A 4

instance FoldableDigit : {ℓ : Level} → {s : Nat} → Foldable {ℓ} (flip Digit s)

FoldableDigit. foldr f acc digit with digit
... | digit-1 a = f a acc
... | digit-2 a b = f a (f b acc)
... | digit-3 a b c = f a (f b (f c acc))
... | digit-4 a b c d = f a (f b (f c (f d acc)))

FoldableDigit. foldl f acc digit with digit
... | digit-1 a = f acc a
... | digit-2 a b = f (f acc a) b
... | digit-3 a b c = f (f (f acc a) b) c
... | digit-4 a b c d = f (f (f (f acc a) b) c) d

data Node {ℓ : Level} (A : Type ℓ) : Nat → Type ℓ where
  node-2 : A → A → Node A 2
  node-3 : A → A → A → Node A 3

instance FoldableNode : {ℓ : Level} → {s : Nat} → Foldable {ℓ} (flip Node s)

FoldableNode. foldr f acc node with node
... | node-2 a b = f a (f b acc)
... | node-3 a b c = f a (f b (f c acc))

FoldableNode. foldl f acc node with node
... | node-2 a b = f (f acc a) b
... | node-3 a b c = f (f (f acc a) b) c

data FingerTree {ℓ : Level} (A : Type ℓ) : Nat → Type ℓ where
  [] : FingerTree A 0
  [_] : A → FingerTree A 1
  [_∥_∥_] : {ls ts rs ds fs : Nat}
          → (left : Digit A ls)
          → (trunk : FingerTree A ts)
          → (right : Digit A rs)
          → ⦃ digit : ds ≡ ls + rs ⦄
          → ⦃ proof : fs ≡ ts + ds ⦄
          → FingerTree A fs

instance FoldableFingerTree : {ℓ : Level} → {s : Nat} → Foldable {ℓ} (flip FingerTree s)

FoldableFingerTree. foldr f acc tree with tree
... | [] = acc
... | [ x ] = f x acc
... | [ l ∥ t ∥ r ] = foldr f (foldr f (foldr f acc r) t) l

FoldableFingerTree. foldl f acc tree with tree
... | [] = acc
... | [ x ] = f acc x
... | [ l ∥ t ∥ r ] = foldl f (foldl f (foldl f acc l) t) r

infixr 5 _<:_
infixl 4 _:>_

pattern [_∥_∥_][_,_] a b c d e
  = [_∥_∥_] a b c ⦃ digit = d ⦄ ⦃ proof = e ⦄

{-# REWRITE +-identity +-suc #-}

_<:_ : {ℓ : Level} → {A : Type ℓ} → {s : Nat} → A → FingerTree A s → FingerTree A (suc s)
a <: [] = [ a ]
a <: [ b ] = [ digit-1 a ∥ [] ∥ digit-1 b ]
a <: [ l ∥ t ∥ r ][ digit , proof ] rewrite digit rewrite proof with l
... | digit-4 b c d e = [ digit-4 a b c d ∥ e <: t ∥ r ] -- [ digit-4 a b c d ∥ e <: t ∥ r ]
... | digit-3 b c d = [ digit-4 a b c d ∥ t ∥ r ] -- ⦃ proof = sym (+-suc ts (ls + rs)) ⦄ -- [ digit-4 a b c d ∥ t ∥ r ]
... | digit-2 b c = [ digit-3 a b c ∥ t ∥ r ] --⦃ proof = sym (+-suc ts (ls + rs)) ⦄
... | digit-1 b = [ digit-2 a b ∥ t ∥ r ] -- ⦃ proof = sym (+-suc ts (ls + rs)) ⦄

_:>_ : {ℓ : Level} → {A : Type ℓ} → {s : Nat} → FingerTree A s → A → FingerTree A (suc s)
[] :> a = [ a ]
[ b ] :> a = [ digit-1 b ∥ [] ∥ digit-1 a ]
[ l ∥ t ∥ r ][ ls , ts , rs , ds , fs ][ digit , proof ] :> a rewrite digit rewrite proof with r
... | digit-4 e d c b = [ l ∥ t :> e ∥ digit-4 d c b a ]
... | digit-3 d c b = [ l ∥ t ∥ digit-4 d c b a ] -- ⦃ sym (+-suc ls rs) ⦄ ⦃ sym (+-suc ts (ls + rs)) ⦄
... | digit-2 c b = [ l ∥ t ∥ digit-3 c b a ] -- ⦃ sym (+-suc ls rs) ⦄ ⦃ sym (+-suc ts (ls + rs)) ⦄
... | digit-1 b = [ l ∥ t ∥ digit-2 b a ] -- ⦃ sym (+-suc ls rs) ⦄ ⦃ sym (+-suc ts (ls + rs)) ⦄

demo : FingerTree Nat 10
demo = 1 <: 2 <: 3 <: 4 <: 5 <: [] :> 6 :> 7 :> 8 :> 9 :> 10

toTree : ∀ {ℓ} {A : Type ℓ} {s : Nat} → Vec A s → FingerTree A s
toTree (x ∷ xs) = x <: toTree xs
toTree [] = []

toList : ∀ {ℓ} {A : Type ℓ} {F : Type ℓ → Type ℓ} ⦃ _ : Foldable F ⦄ → F A → List A
toList = foldr _∷_ []
{-
toDigit : ∀ {ℓ} {A : Type ℓ} → Node A → Digit A
toDigit (n-two a b) = d-two a b
toDigit (n-three a b c) = d-three a b c
-}
data Viewₗ {ℓ} (S : Type ℓ → Type ℓ) (A : Type ℓ) : Type ℓ where
  [] : Viewₗ S A
  _∷_ : A → S A → Viewₗ S A
{-
viewₗ : ∀ {ℓ} {A : Type ℓ} → FingerTree A → Viewₗ FingerTree A
viewₗ [] = []
viewₗ [ x ] = x ∷ []
viewₗ [ pr / m / sf ] with pr
... | d-four a b c d = a ∷ [ d-three b c d / m / sf ]
... | d-three a b c = a ∷ [ d-two b c / m / sf ]
... | d-two a b = a ∷ [ d-one b / m / sf ]
... | d-one a with viewₗ m
...              | [] = a ∷ toTree sf
...              | x ∷ xs = a ∷ [ toDigit x / xs / sf ]

isEmpty : ∀ {ℓ} {A : Type ℓ} → FingerTree A → Bool
isEmpty x with viewₗ x
... | [] = #t
... | _ ∷ _ = #f

headₗ : ∀ {ℓ} {A : Type ℓ} → FingerTree A → Option A
headₗ x with viewₗ x
... | [] = none
... | x ∷ _ = some x

tailₗ : ∀ {ℓ} {A : Type ℓ} → FingerTree A → Option (FingerTree A)
tailₗ x with viewₗ x
... | [] = none
... | _ ∷ xs = some xs

nodes : ∀ {ℓ} {A : Type ℓ} → List A → List (Node A)
nodes [] = []
nodes (x ∷ []) = []
nodes (a ∷ b ∷ []) = n-two a b ∷ []
nodes (a ∷ b ∷ c ∷ xs) with xs
... | [] = n-three a b c ∷ []
... | d ∷ [] = n-two a b ∷ n-two c d ∷ []
... | _ ∷ _ ∷ _ = n-three a b c ∷ nodes xs

app3 : ∀ {ℓ} {A : Type ℓ} → FingerTree A → List A → FingerTree A → FingerTree A
app3 [] ts [] = toTree ts
app3 [] ts xs = foldr (_<:_) xs ts
app3 xs ts [] = foldl (_:>_) xs ts
app3 [ x ] ts xs = x <: (foldr (_<:_) xs ts)
app3 xs ts [ x ] = (foldl (_:>_) xs ts) :> x
app3 [ pr₁ / m₁ / sf₁ ] ts [ pr₂ / m₂ / sf₂ ] = [ pr₁ / app3 m₁ n m₂ / sf₂ ]
  where n = nodes (toList sf₁ <> ts <> toList pr₂)

_><_ : ∀ {ℓ} {A : Type ℓ} → FingerTree A → FingerTree A → FingerTree A
_><_ xs ys = app3 xs [] ys

test : FingerTree Nat
test = 1 <: 2 <: 3 <: 4 <: 5 <: 6 <: 7 <: 8 <: []

test2 = test :> 10

demo = toTree (the (List Nat) (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []))
-}
