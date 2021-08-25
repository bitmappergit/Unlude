module Category.Monad.IO where

open import Data.Type
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Data.String
open import Data.Unit
open import Data.List
open import Algebra.Semigroup
open import Algebra.Monoid
open import Data.Core using (Nat)

postulate IO : ∀ {ℓ} → Type ℓ → Type ℓ

{-# POLARITY IO ++ ++ #-}
{-# BUILTIN IO IO #-}

{-# FOREIGN GHC type AgdaIO a b = IO b #-}
{-# COMPILE GHC IO = type AgdaIO #-}

private postulate mapIO : ∀ {ℓ} {A B : Type ℓ} → (A → B) → IO A → IO B
private postulate pureIO : ∀ {ℓ} {A : Type ℓ} → A → IO A
private postulate appIO : ∀ {ℓ} {A B : Type ℓ} → IO (A → B) → IO A → IO B
private postulate bindIO : ∀ {ℓ} {A B : Type ℓ} → IO A → (A → IO B) → IO B

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

postulate putStrLn : ∀ {ℓ} → String → IO {ℓ} ⊤
postulate putStr : ∀ {ℓ} → String → IO {ℓ} ⊤
postulate getStr : IO String
postulate readFile : String → IO String
postulate writeFile : ∀ {ℓ} → String → String → IO {ℓ} ⊤
postulate getArgs : IO (List String)
postulate printNat : ∀ {ℓ} → Nat → IO {ℓ} ⊤

{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# FOREIGN GHC import qualified System.Environment #-}

{-# COMPILE GHC putStrLn = \_ -> Data.Text.IO.putStrLn #-}
{-# COMPILE GHC putStr = \_ -> Data.Text.IO.putStr #-}
{-# COMPILE GHC getStr = Data.Text.IO.getLine #-}
{-# COMPILE GHC readFile = Data.Text.IO.readFile . Data.Text.unpack #-}
{-# COMPILE GHC writeFile = \_ -> Data.Text.IO.writeFile . Data.Text.unpack #-}
{-# COMPILE GHC getArgs = fmap (map Data.Text.pack) System.Environment.getArgs #-}
{-# COMPILE GHC printNat = \_ -> Data.Text.IO.putStrLn . Data.Text.pack . show #-}

instance SemigroupIO : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Semigroup A ⦄ → Semigroup (IO A)

SemigroupIO. _<>_ a b = _<>_ <$> a <*> b

instance MonoidIO : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Monoid A ⦄ → Monoid (IO A)

MonoidIO. empty = return empty
