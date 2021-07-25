module Relation.Negation where

open import Data.Type
open import Data.Empty

infix 3 ¬_

¬_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬ p = p → ⊥

