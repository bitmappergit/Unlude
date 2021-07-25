module Control.Monad.IO where

open import Data.Type
open import Control.Functor
open import Control.Applicative
open import Control.Monad
open import Data.String
open import Data.Unit
open import Data.List
open import Algebra.Semigroup
open import Algebra.Monoid

postulate IO : ∀ {ℓ} → Type ℓ → Type ℓ

{-# POLARITY IO ++ ++ #-}
{-# BUILTIN IO IO #-}

{-# FOREIGN GHC type AgdaIO a b = IO b #-}
{-# COMPILE GHC IO = type AgdaIO #-}

postulate mapIO : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → IO A → IO B
postulate pureIO : ∀ {ℓ} {A : Type ℓ} → A → IO A
postulate appIO : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → IO (A → B) → IO A → IO B
postulate bindIO : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → IO A → (A → IO B) → IO B

{-# COMPILE GHC mapIO = \_ _ _ _ -> fmap #-}
{-# COMPILE GHC pureIO = \_ _ -> pure #-}
{-# COMPILE GHC appIO = \_ _ _ _ -> (<*>) #-}
{-# COMPILE GHC bindIO = \_ _ _ _ -> (>>=) #-}

instance FunctorIO : ∀ {ℓ} → Functor {ℓ} IO

FunctorIO. map = mapIO

instance ApplicativeIO : ∀ {ℓ} → Applicative {ℓ} IO

ApplicativeIO. pure = pureIO
ApplicativeIO. _<*>_ = appIO

instance MonadIO : ∀ {ℓ} → Monad {ℓ} IO

MonadIO. _>>=_ = bindIO

postulate putStrLn : String → IO ⊤
postulate putStr : String → IO ⊤
postulate getStr : IO String
postulate readFile : String → IO String
postulate writeFile : String → String → IO ⊤
postulate getArgs : IO (List String)

{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# FOREIGN GHC import qualified System.Environment #-}

{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}
{-# COMPILE GHC putStr = Data.Text.IO.putStr #-}
{-# COMPILE GHC getStr = Data.Text.IO.getLine #-}
{-# COMPILE GHC readFile = \x -> Data.Text.IO.readFile (Data.Text.unpack x) #-}
{-# COMPILE GHC writeFile = \x -> Data.Text.IO.writeFile (Data.Text.unpack x) #-}
{-# COMPILE GHC getArgs = fmap (map Data.Text.pack) System.Environment.getArgs #-}

instance SemigroupIO : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Semigroup A ⦄ → Semigroup (IO A)

SemigroupIO. _<>_ a b = _<>_ <$> a <*> b

instance MonoidIO : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Monoid A ⦄ → Monoid (IO A)

MonoidIO. empty = return empty
