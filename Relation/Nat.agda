module Relation.Nat where

open import Data.Type
open import Data.Core using (Nat; suc; zero)
open import Data.Nat
open import Relation.Equality
open import Relation.Negation
open import Data.Eq
open import Data.Bool
open import Data.Function
open import Algebra.Semiring
open import Data.Ord
open import Data.Empty

_⊔ⁿ_ : Nat → Nat → Nat
zero  ⊔ⁿ n     = n
suc m ⊔ⁿ zero  = suc m
suc m ⊔ⁿ suc n = suc (m ⊔ⁿ n)

_⊓ⁿ_ : Nat → Nat → Nat
zero  ⊓ⁿ n     = zero
suc m ⊓ⁿ zero  = zero
suc m ⊓ⁿ suc n = suc (m ⊓ⁿ n)

infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≮_ _≱_ _≯_ _≤?_ _<?_ _≥?_ _>?_ 

data _≤_ : Nat → Nat → Type where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

m+1⇒suc : ∀ {m} → m + one ≡ suc m
m+1⇒suc {suc _} = cong suc m+1⇒suc
m+1⇒suc {zero} = refl

+-identity : (m : Nat) → m + zero ≡ m
+-identity zero = refl
+-identity (suc m) = cong suc (+-identity m)

+-suc : (m n : Nat) → m + suc n ≡ suc (m + n)
+-suc zero _ = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : (m n : Nat) → m + n ≡ n + m
+-comm m zero = +-identity m
+-comm m (suc n) rewrite +-suc m n = cong suc (+-comm m n)

+-comm-suc : (m n : Nat) → m + suc n ≡ suc (n + m)
+-comm-suc m n rewrite +-suc m n = cong suc (+-comm m n)

+-rotate : (m n o : Nat) → m + n + o ≡ o + n + m
+-rotate m zero o
  rewrite +-identity m
  rewrite +-identity o = +-comm m o
+-rotate m (suc n) o
  rewrite +-suc m n
  rewrite +-suc o n = cong suc (+-rotate m n o)

+-assoc : (m n p : Nat) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s m≤n) = m≤n

_<_ : Nat → Nat → Type
m < n = suc m ≤ n

_≥_ : Nat → Nat → Type
m ≥ n = n ≤ m

_>_ : Nat → Nat → Type
m > n = n < m

_≰_ : Nat → Nat → Type
a ≰ b = ¬ a ≤ b

_≮_ : Nat → Nat → Type
a ≮ b = ¬ a < b

_≱_ : Nat → Nat → Type
a ≱ b = ¬ a ≥ b

_≯_ : Nat → Nat → Type
a ≯ b = ¬ a > b

_≤?_ : (m n : Nat) → Dec (m ≤ n)
_≤?_ (suc _) zero = no λ ()
_≤?_ zero _ = yes z≤n
_≤?_ (suc m) (suc n) with m ≤? n
... | yes prf = yes (s≤s prf)
... | no prf = no λ { (s≤s o) → prf o }

_<?_ : (m n : Nat) → Dec (m < n)
_<?_ m n = suc m ≤? n

_≥?_ : (m n : Nat) → Dec (m ≥ n)
_≥?_ m n = n ≤? m

_>?_ : (m n : Nat) → Dec (m > n)
_>?_ m n = n <? m

<ᵇ⇒< : ∀ m n → So (m <ᵇ n) → m < n
<ᵇ⇒< zero (suc n) m<n = s≤s z≤n
<ᵇ⇒< (suc m) (suc n) m<n = s≤s (<ᵇ⇒< m n m<n)

≡ᵇ⇒≡ : (m n : Nat) → So (m ≡ᵇ n) → m ≡ n
≡ᵇ⇒≡ zero zero _ = refl
≡ᵇ⇒≡ (suc m) (suc n) m≡ᵇn = cong suc (≡ᵇ⇒≡ m n m≡ᵇn)

mutual
  data Even : Nat → Type where
    zero : Even zero
    suc : ∀ {n} → Odd n → Even (suc n)

  data Odd : Nat → Type where
    suc : ∀ {n} → Even n → Odd (suc n)

  odd[one] : Odd (suc zero)
  odd[one] = suc zero

  even[zero] : Even zero
  even[zero] = zero

  ¬odd[zero] : ¬ Odd zero
  ¬odd[zero] ()

  ¬even[one] : ¬ Even (suc zero)
  ¬even[one] (suc n) = ¬odd[zero] n

mutual
  odd⇒nat : ∀ {n} → Odd n → Nat
  odd⇒nat (suc n) = suc (even⇒nat n)

  even⇒nat : ∀ {n} → Even n → Nat
  even⇒nat (suc n) = suc (odd⇒nat n)
  even⇒nat zero = zero
  
  odd? : (n : Nat) → Dec (Odd n)    
  odd? (suc n) with even? n
  ... | yes prf = yes (suc prf)
  ... | no prf = no λ { (suc x) → prf x }
  odd? zero = no ¬odd[zero]

  even? : (n : Nat) → Dec (Even n)
  even? (suc n) with odd? n
  ... | yes prf = yes (suc prf)
  ... | no prf = no λ { (suc x) → prf x }
  even? zero = yes even[zero]

mutual
  even+even≡even : ∀ {n m} → Even n → Even m → Even (n + m)
  even+even≡even zero em = em
  even+even≡even (suc on) em = suc (odd+even≡odd on em)

  odd+even≡odd : ∀ {n m} → Odd n → Even m → Odd (n + m)
  odd+even≡odd (suc en) em = suc (even+even≡even en em)
  
  odd+odd≡even : ∀ {n m} → Odd n → Odd m → Even (n + m)
  odd+odd≡even (suc zero) m = suc m
  odd+odd≡even (suc (suc n)) m = suc (suc (odd+odd≡even n m))

  suc[even]≡odd : ∀ {n} → Even n → Odd (suc n)
  suc[even]≡odd (suc n) = suc (suc n)
  suc[even]≡odd zero = suc zero

  suc[odd]≡even : ∀ {n} → Odd n → Even (suc n)
  suc[odd]≡even (suc (suc n)) = suc (suc (suc n))
  suc[odd]≡even (suc zero) = suc (suc zero)
