module Main where

open import IO
open import Data.Nat
open import Data.Nat.Show
open import Data.Maybe
open import Data.Empty
open import Data.Unit
open import Coinduction
open import SortedExhaustiveStream
open import Sieve

print : ℕ → IO ⊤
print n = putStrLn (show n)

printAll : ∀ {P : ℕ → Set} {b : Maybe ℕ} → SortedExhaustiveStream' _<_ P b → IO ⊥
printAll (minimum x _ _ ∷ taill) = ♯ print x >> ♯ printAll (♭ taill)

main = run (printAll all-primes)