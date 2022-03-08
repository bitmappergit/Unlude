module Examples.Salsa20 where

open import Prelude

step : (x y z : Fin 16) → Nat → State (Vec Word32 16) Word32
step x y z n = do
  x ← use (at x)
  y ← use (at y)
  z ← use (at z)
  return (x xor ((y + z) <<< n))

{-# INLINE step #-}

quarterPass : (a b c d : Fin 16) → State (Vec Word32 16) Unit
quarterPass a b c d = do
  at b <:= step b a d 7
  at c <:= step c b a 9
  at d <:= step d c b 13
  at a <:= step a d c 18
   
{-# INLINE quarterPass #-}

doublePass : State (Vec Word32 16) Unit
doublePass = do
  quarterPass  0  4  8 12
  quarterPass  5  9 13  1
  quarterPass 10 14  2  6
  quarterPass 15  3  7 11
  quarterPass  0  1  2  3
  quarterPass  5  6  7  4
  quarterPass 10 11  8  9
  quarterPass 15 12 13 14

{-# INLINE doublePass #-}

fullPass : State (Vec Word32 16) Unit
fullPass = for _ ∈ 0 to 11 := doublePass

{-# INLINE fullPass #-}

salsa20 : Vec Word32 16 → Vec Word32 16
salsa20 s = zipWith _+_ s (execState fullPass s)

{-# INLINE salsa20 #-}

testInput : Word32 → Vec Word32 16
testInput x = x +  0 ∷ x +  1 ∷ x +  2 ∷ x +  3
            ∷ x +  4 ∷ x +  5 ∷ x +  6 ∷ x +  7
            ∷ x +  8 ∷ x +  9 ∷ x + 10 ∷ x + 11
            ∷ x + 12 ∷ x + 13 ∷ x + 14 ∷ x + 15
            ∷ []

main : IO Unit
main = do
  for c ∈ 1 to 1000 := do
    let result = salsa20 (testInput (fromNat c))
    for i ∈ result := do
      print i
  
