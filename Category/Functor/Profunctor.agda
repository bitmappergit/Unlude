module Category.Functor.Profunctor where

open import Data.Type
open import Data.Core
open import Data.Function
open import Data.Product
open import Data.Sum
open import Category.Functor
open import Category.Applicative

record Profunctor {a b} (P : Type a → Type a → Type b) : Type (lsuc a ⊔ b) where
  field promap : {A B C D : Type a} → (A → B) → (C → D) → P B C → P A D

  lmap : {A B C : Type a} → (A → B) → P B C → P A C
  lmap f = promap f id
  
  rmap : {A B C : Type a} → (B → C) → P A B → P A C
  rmap f = promap id f
  
open Profunctor ⦃ ... ⦄ public

record Strong {a b} (P : Type a → Type a → Type b) : Type (lsuc a ⊔ b) where
  field ⦃ super ⦄ : Profunctor P
  
  field first : {A B C : Type a} → P A B → P (A × C) (B × C)
  field second : {A B C : Type a} → P A B → P (C × A) (C × B)

open Strong ⦃ ... ⦄ public

record Choice {a b} (P : Type a → Type a → Type b) : Type (lsuc a ⊔ b) where
  field ⦃ super ⦄ : Profunctor P

  field left : {A B C : Type a} → P A B → P (A ⊎ C) (B ⊎ C)
  field right : {A B C : Type a} → P A B → P (C ⊎ A) (C ⊎ B)

open Choice ⦃ ... ⦄ public

record Star {a b} (F : Type a → Type b) (A B : Type a) : Type (a ⊔ b) where
  constructor mkStar
  field runStar : A → F B

open Star ⦃ ... ⦄ public

instance ProfunctorFunction : ∀ {a} → Profunctor {a} Function

ProfunctorFunction. promap f g p = g ∘ (p ∘ f)

instance StrongFunction : ∀ {a} → Strong {a} Function

StrongFunction. first f (a , c) = (f a , c)
StrongFunction. second f (a , c) = (a , f c)

instance ChoiceFunction : ∀ {a} → Choice {a} Function

ChoiceFunction. left f = [ inj₁ ∘ f , inj₂ ]
ChoiceFunction. right f = [ inj₁ , inj₂ ∘ f ]

instance ProfunctorStar : ∀ {a b} {F : Type a → Type b} ⦃ _ : Functor F ⦄ → Profunctor {a} (Star F)

ProfunctorStar. promap f g (mkStar h) = mkStar (map g ∘ h ∘ f)

instance StrongStar : ∀ {a b} {F : Type a → Type b} ⦃ _ : Functor F ⦄ → Strong {a} (Star F)

StrongStar. first (mkStar f) = mkStar λ (a , c) → map (_, c) (f a)
StrongStar. second (mkStar f) = mkStar λ (c , b) → map (c ,_) (f b)

instance ChoiceStar : ∀ {a b} {F : Type a → Type b} ⦃ _ : Applicative F ⦄ → Choice {a} (Star F)

ChoiceStar. left (mkStar f) = mkStar [ map inj₁ ∘ f , map inj₂ ∘ pure ]
ChoiceStar. right (mkStar f) = mkStar [ map inj₁ ∘ pure , map inj₂ ∘ f ]
