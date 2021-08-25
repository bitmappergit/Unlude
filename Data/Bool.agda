module Data.Bool where

open import Data.Type
open import Data.Unit
open import Data.Empty
open import Data.Core using (Bool; #t; #f) public

not : Bool → Bool
not #t = #f
not #f = #t

_∧_ : Bool → Bool → Bool
#t ∧ #t = #t
#f ∧ #f = #f
#t ∧ #f = #f
#f ∧ #t = #f

_∨_ : Bool → Bool → Bool
#t ∨ #t = #t
#f ∨ #f = #f
#t ∨ #f = #t
#f ∨ #t = #t

infix 0 if_then_else_

if_then_else_ : ∀ {ℓ} {A : Type ℓ} → Bool → A → A → A
if #t then x else _ = x
if #f then _ else y = y

So : Bool → Type
So #t = ⊤
So #f = ⊥
