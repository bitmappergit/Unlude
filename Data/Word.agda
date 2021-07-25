module Data.Word where

open import Data.Type
open import Data.Vec
open import Data.Bool
open import Data.Function
open import Control.Functor
open import Data.Num
open import Data.Nat
open import Algebra.Semiring
open import Algebra.Ring
open import Data.Divisible
open import Data.Negative
open import Data.Eq
open import Data.Ord

Word : Nat → Type
Word = Vec Bool

word-add : ∀ {s} → Bool → Word s → Word s → Word s
word-add c (#t :: m) (#t :: n) = c :: word-add #t m n
word-add c (#f :: m) (#f :: n) = c :: word-add #f m n
word-add c (#t :: m) (#f :: n) = not c :: word-add c m n
word-add c (#f :: m) (#t :: n) = not c :: word-add c m n
word-add _ [] [] = []

{-# INLINE word-add #-}

mutual
  instance SemiringWord : ∀ {s} → Semiring (Word s)

  SemiringWord. zro = replicate #f
  SemiringWord. one = one′
    where one′ : ∀ {s} → Word s
          one′ {s = zero} = []
          one′ {s = suc _} = #t :: zro
  SemiringWord. _+_ = word-add #f
  SemiringWord. _*_ a = mul a ∘ toNat
    where mul : ∀ {s} → Word s → Nat → Word s
          mul m (suc n) = word-add #f m (mul m n)
          mul m zero = zro

  instance RingWord : ∀ {s} → Ring (Word s)

  RingWord. negate x = word-add #t zro (map not x)
  RingWord. _-_ a b = word-add #t a (map not b)

  instance NumWord : ∀ {s} → Num (Word s)

  NumWord. fromNat = fromNat′
    where fromNat′ : ∀ {s} → Nat → Word s
          fromNat′ {s = zero} _ = []
          fromNat′ {s = suc _} zero = zro
          fromNat′ {s = suc _} (suc x) with (suc x % suc one)
          ... | zero = #f :: fromNat (suc x / suc one)
          ... | suc _ = #t :: fromNat (suc x / suc one)

  NumWord. toNat = toNat′ one
    where toNat′ : ∀ {s} → Nat → Word s → Nat
          toNat′ c (#t :: xs) = c + toNat′ (c * suc one) xs
          toNat′ c (#f :: xs) = toNat′ (c * suc one) xs
          toNat′ c [] = zro

  instance NegativeWord : ∀ {s} → Negative (Word s)

  NegativeWord. fromNeg = negate ∘ fromNat

Word4 = Word 4
Word8 = Word 8
Word16 = Word 16
Word32 = Word 32
Word64 = Word 64

instance EqWord : ∀ {s} → Eq (Word s)

EqWord. _==_ (x :: xs) (y :: ys) = (x == y) ∧ (xs == ys)
EqWord. _==_ [] [] = #t

instance OrdWord : ∀ {s} → Ord (Word s)

OrdWord. _<_ (#t :: xs) (#t :: ys) = xs < ys
OrdWord. _<_ (#f :: xs) (#f :: ys) = xs < ys
OrdWord. _<_ (#t :: xs) (#f :: ys) = #f
OrdWord. _<_ (#f :: xs) (#t :: ys) = #t
OrdWord. _<_ [] [] = #f

OrdWord. _>_ (#t :: xs) (#t :: ys) = xs > ys
OrdWord. _>_ (#f :: xs) (#f :: ys) = xs > ys
OrdWord. _>_ (#t :: xs) (#f :: ys) = #t
OrdWord. _>_ (#f :: xs) (#t :: ys) = #f
OrdWord. _>_ [] [] = #f
