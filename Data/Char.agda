module Data.Char where

open import Data.Type
open import Data.Nat
open import Data.Bool
open import Data.Eq

postulate Char : Type

{-# BUILTIN CHAR Char #-}

primitive primIsLower : Char → Bool
primitive primIsDigit : Char → Bool
primitive primIsAlpha : Char → Bool
primitive primIsSpace : Char → Bool
primitive primIsAscii : Char → Bool
primitive primIsLatin1 : Char → Bool
primitive primIsPrint : Char → Bool
primitive primIsHexDigit : Char → Bool
primitive primToUpper : Char → Char
primitive primToLower : Char → Char
primitive primCharToNat : Char → Nat
primitive primNatToChar : Nat → Char
primitive primCharEquality : Char → Char → Bool

instance EqChar : Eq Char

EqChar. _≡ᵇ_ = primCharEquality
