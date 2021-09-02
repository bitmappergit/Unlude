module Examples.Salsa20 where

open import Prelude

¼-pass : (a b c d : Fin 16) → Vec Word32 16 → Vec Word32 16
¼-pass a b c d s0 = s4
  where a0 = index a s0
        b0 = index b s0
        c0 = index c s0
        d0 = index d s0
        b1 = b0 xor ((a0 + d0) <<< 7)
        c1 = c0 xor ((b1 + a0) <<< 9)
        d1 = d0 xor ((c1 + b1) <<< 13)
        a1 = a0 xor ((d1 + c1) <<< 18)
        s1 = update a a1 s0
        s2 = update b b1 s1
        s3 = update c c1 s2
        s4 = update d d1 s3

salsa20 : Vec Word32 16 → Vec Word32 16
salsa20 s = zipWith _+_ s $ repeat 10 pass s
  where pass : Vec Word32 16 → Vec Word32 16
        pass = ¼-pass 15 12 13 14
             ∘ ¼-pass 10 11  8  9
             ∘ ¼-pass  5  6  7  4
             ∘ ¼-pass  0  1  2  3
             ∘ ¼-pass 15  3  7 11
             ∘ ¼-pass 10 14  2  6
             ∘ ¼-pass  5  9 13  1
             ∘ ¼-pass  0  4  8 12
    
