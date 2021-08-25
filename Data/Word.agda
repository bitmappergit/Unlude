module Data.Word where

open import Data.Type
open import Data.Vec
open import Data.Bool
open import Data.Function
open import Category.Functor
open import Data.Num
open import Data.Nat
open import Algebra.Semiring
open import Algebra.Ring
open import Data.Divisible
open import Data.Negative
open import Data.Eq
open import Data.Ord
open import Data.Unit
open import Relation.Negation
open import Relation.Nat
open import Relation.Equality

Word : Nat → Type
Word = Vec Bool

word-add : ∀ {s} → Bool → Word s → Word s → Word s
word-add c (#t ∷ m) (#t ∷ n) = c ∷ word-add #t m n
word-add c (#f ∷ m) (#f ∷ n) = c ∷ word-add #f m n
word-add c (#t ∷ m) (#f ∷ n) = not c ∷ word-add c m n
word-add c (#f ∷ m) (#t ∷ n) = not c ∷ word-add c m n
word-add _ [] [] = []

{-# INLINE word-add #-}

mutual
  instance SemiringWord : ∀ {s} → Semiring (Word s)

  SemiringWord. zro = replicate #f
  SemiringWord. one = one′
    where one′ : ∀ {s} → Word s
          one′ {s = zero} = []
          one′ {s = suc _} = #t ∷ zro
  SemiringWord. _+_ = word-add #f
  SemiringWord. _*_ a = mul a ∘ toNat
    where mul : ∀ {s} → Word s → Nat → Word s
          mul m (suc n) = word-add #f m (mul m n)
          mul m zero = zro

  instance RingWord : ∀ {s} → Ring (Word s)

  RingWord. negate x = word-add #t zro (map not x)
  RingWord. _-_ a b = word-add #t a (map not b)

  instance NumWord : ∀ {s} → Num (Word s)

  NumWord. Constraint _ = ⊤
  
  NumWord. fromNat m = fromNat′ m
    where fromNat′ : ∀ {s} → Nat → Word s
          fromNat′ {s = zero} _ = []
          fromNat′ {s = suc _} zero = zro
          fromNat′ {s = suc _} (suc x) with (suc x % suc one)
          ... | zero = #f ∷ fromNat (suc x / suc one)
          ... | suc _ = #t ∷ fromNat (suc x / suc one)

  NumWord. toNat = toNat′ one
    where toNat′ : ∀ {s} → Nat → Word s → Nat
          toNat′ c (#t ∷ xs) = c + toNat′ (c * suc one) xs
          toNat′ c (#f ∷ xs) = toNat′ (c * suc one) xs
          toNat′ c [] = zro

  instance NegativeWord : ∀ {s} → Negative (Word s)

  NegativeWord. fromNeg m = negate (fromNat m)
  
Word4 = Word 4
Word8 = Word 8
Word16 = Word 16
Word32 = Word 32
Word64 = Word 64

instance EqWord : ∀ {s} → Eq (Word s)

EqWord. _≡ᵇ_ (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ (xs ≡ᵇ ys)
EqWord. _≡ᵇ_ [] [] = #t

instance OrdWord : ∀ {s} → Ord (Word s)

OrdWord. _<ᵇ_ (#t ∷ xs) (#t ∷ ys) = xs <ᵇ ys
OrdWord. _<ᵇ_ (#f ∷ xs) (#f ∷ ys) = xs <ᵇ ys
OrdWord. _<ᵇ_ (#t ∷ xs) (#f ∷ ys) = #f
OrdWord. _<ᵇ_ (#f ∷ xs) (#t ∷ ys) = #t
OrdWord. _<ᵇ_ [] [] = #f

_<<<_ : ∀ {s} → Word (suc s) → Nat → Word (suc s)
_<<<_ res times with times
... | suc c = (last res ∷ but-last res) <<< c
... | zero = res

_xor_ : ∀ {s} → Word s → Word s → Word s
_xor_ (#t ∷ xs) (#t ∷ ys) = #f ∷ (xs xor ys)
_xor_ (#f ∷ xs) (#f ∷ ys) = #f ∷ (xs xor ys)
_xor_ (#t ∷ xs) (#f ∷ ys) = #t ∷ (xs xor ys)
_xor_ (#f ∷ xs) (#t ∷ ys) = #t ∷ (xs xor ys)
_xor_ [] [] = []
