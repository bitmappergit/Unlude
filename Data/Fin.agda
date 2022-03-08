module Data.Fin where

open import Data.Type
open import Data.Core
open import Data.Nat
open import Algebra.Semiring
open import Relation.Negation
open import Relation.Equality
open import Data.Function
open import Data.Eq
open import Data.Bool
open import Data.Ord
open import Relation.Nat
open import Data.Empty
open import Data.Num
open import Data.Product
open import Algebra.Semiring
open import Data.Unit
open import Data.Sum

data Fin : Nat → Type where
  suc : {n : Nat} → Fin n → Fin (suc n)
  zero : {n : Nat} → Fin (suc n)

Fin-Σ : Type
Fin-Σ = Σ Nat (λ s → Fin (suc s))

instance NumFin-Σ : Num Fin-Σ

fromNatᶠ : (n : Nat) → Fin (suc n)
fromNatᶠ zero = zero
fromNatᶠ (suc n) = suc (fromNatᶠ n)

toNatᶠ : ∀ {n} → Fin n → Nat
toNatᶠ zero = zero
toNatᶠ {suc s} (suc i) = suc (toNatᶠ {s} i)

_≤-simple_ : Nat → Nat → Type
zero  ≤-simple n = ⊤
suc m ≤-simple zero = ⊥
suc m ≤-simple suc n = m ≤-simple n

fromNat≤ : ∀ m n → m ≤-simple n → Fin (suc n)
fromNat≤ zero _ _ = zero
fromNat≤ (suc _) zero ()
fromNat≤ (suc m) (suc n) p = suc (fromNat≤ m n p)

NumFin-Σ. Constraint _ = ⊤
NumFin-Σ. fromNat n = (n , fromNatᶠ n)
NumFin-Σ. toNat (_ , n) = toNatᶠ n

_+ᶠ_ : ∀ {m n} → Fin m → Fin n → Fin (m + n)
_+ᶠ_ zero n = zero
_+ᶠ_ (suc m) n = suc (m +ᶠ n)

instance NumFin : ∀ {n} → Num (Fin (suc n))

NumFin {n} .Constraint m = m ≤-simple n
NumFin {n} .fromNat m ⦃ m<n ⦄ = fromNat≤ m n m<n
NumFin {n} .toNat m = toNatᶠ m

instance SemiringFin-Σ : Semiring Fin-Σ

SemiringFin-Σ. one = (1 , suc zero)
SemiringFin-Σ. zro = (0 , zero)
SemiringFin-Σ. _+_ (_ , zero) n = n
SemiringFin-Σ. _+_ (suc s , suc m) n = let (o , p) = (s , m) + n in (suc o , suc p)
SemiringFin-Σ. _*_ m@(_ , zero) _ = m
SemiringFin-Σ. _*_ (suc s , suc m) n = n + ((s , m) * n)

suc-injectiveᶠ : ∀ {s} {m n : Fin s} → (Fin.suc m) ≡ (Fin.suc n) → m ≡ n
suc-injectiveᶠ refl = refl

instance DecEqFin : ∀ {s} → DecEq (Fin s)

DecEqFin. _≟_ zero zero = yes refl
DecEqFin. _≟_ zero (suc _) = no λ ()
DecEqFin. _≟_ (suc _) zero = no λ ()
DecEqFin. _≟_ (suc m) (suc n) with m ≟ n
... | yes m≡n = yes (cong suc m≡n)
... | no m≢n = no (m≢n ∘ suc-injectiveᶠ)

instance EqFin : ∀ {s} → Eq (Fin s)

EqFin. _≡ᵇ_ zero zero = #t
EqFin. _≡ᵇ_ zero (suc _) = #f
EqFin. _≡ᵇ_ (suc _) zero = #f
EqFin. _≡ᵇ_ (suc m) (suc n) = m ≡ᵇ n

instance OrdFin : ∀ {s} → Ord (Fin s)

OrdFin. _<ᵇ_ zero zero = #f
OrdFin. _<ᵇ_ zero (suc _) = #t
OrdFin. _<ᵇ_ (suc _) zero = #f
OrdFin. _<ᵇ_ (suc m) (suc n) = m <ᵇ n

_∸ᶠ_ : ∀ {m} (i : Fin m) (j : Fin (toNat (suc i))) → Fin (m ∸ toNatᶠ j)
i     ∸ᶠ zero   = i
suc i ∸ᶠ suc j  = i ∸ᶠ j

splitAt : {n : Nat} → (m : Nat) → Fin (m + n) → Fin m ⊎ Fin n
splitAt zero i = inj₂ i
splitAt (suc m) zero = inj₁ zero
splitAt (suc m) (suc i) with splitAt m i
... | inj₁ c = inj₁ (suc c)
... | inj₂ c = inj₂ c
