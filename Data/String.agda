module Data.String where

open import Data.Type
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Char
open import Algebra.Semigroup
open import Algebra.Monoid
open import Class.Eq

postulate String : Type

{-# BUILTIN STRING String #-}

primitive primStringToList : String → List Char
primitive primStringFromList : List Char → String
primitive primStringAppend : String → String → String
primitive primStringEquality : String → String → Bool
primitive primShowChar : Char → String
primitive primShowString : String → String
primitive primShowNat : Nat → String

instance SemigroupString : Semigroup String

SemigroupString. _<>_ = primStringAppend

instance MonoidString : Monoid String

MonoidString. empty = ""

instance EqString : Eq String

EqString. _==_ = primStringEquality
