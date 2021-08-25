module Relation.Negation where

open import Data.Type
open import Data.Empty
open import Data.Bool
open import Data.Function

infix 3 ¬_

¬_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬ p = p → ⊥

data Dec {ℓ} (A : Type ℓ) : Type ℓ where
  yes : A → Dec A
  no : ¬ A → Dec A

yes? : ∀ {ℓ} {A : Type ℓ} → Dec A → Bool
yes? (yes _) = #t
yes? (no _) = #f

no? : ∀ {ℓ} {A : Type ℓ} → Dec A → Bool
no? (yes _) = #f
no? (no _) = #t

#T : ∀ {ℓ} {A : Type ℓ} → Dec A → Type
#T Q = So (yes? Q)

#F : ∀ {ℓ} {A : Type ℓ} → Dec A → Type
#F Q = So (no? Q)

¬-elim : ∀ {ℓ} {A : Type ℓ} → ¬ A → A → ⊥
¬-elim n a = n a

contradiction : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {W : Type ℓ₂} → A → ¬ A → W
contradiction a n = ⊥-elim (n a)
