module Sieve where

open import Coinduction
open import Data.Maybe
open import Data.Product
open import Data.Unit using (⊤)
open import Data.Empty

open import Factorisation

open import Relation.Nullary
open import Relation.Binary hiding(Minimum)
open import Relation.Unary using(Pred)
import Level

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)

import MRel

open import SortedExhaustiveStream

open import Function.Equivalence

open import Data.Nat hiding(_<_; compare; _≟_)
open import Data.Nat.Divisibility
open import Data.Nat.Coprimality

open import Data.Nat.Properties

import NatBoundedGtWF
open StrictTotalOrder Data.Nat.Properties.strictTotalOrder
open WithTotalOrder ℕ _<_ ( StrictTotalOrder.isStrictTotalOrder (Data.Nat.Properties.strictTotalOrder)) NatBoundedGtWF.wf

private
 module ≤O = DecTotalOrder Data.Nat.Properties.≤-decTotalOrder
 module <O = StrictTotalOrder Data.Nat.Properties.strictTotalOrder

open import Sieve0

open import Function
open import Multiples

open import Algebra

abstract
 small-not-retained : ∀ {n} {x} → IsRetainedAfterSieve≤ n x → x > n
 small-not-retained {n} {x} (x>1 , ret) with factor x
 small-not-retained (() , ret) | zero
 small-not-retained (s≤s () , ret) | one
 small-not-retained (x>1 , ret) | fact (p , p-prime) m = ≰⇒> (λ x≤n → ret p (≤O.trans (≤O.trans (≤O.reflexive (+-comm 0 p)) ((≤O.reflexive (PropEq.refl {x = 1}) +-mono (z≤n {m})) *-mono  ≤O.reflexive {p} PropEq.refl)) x≤n) p-prime (divides (suc m) PropEq.refl))

hoho : ∀ {n} → Minimum (λ x → IsRetainedAfterSieve≤ n x × ⊤) _<_ → Minimum (IsPrime'> n) _<_
hoho {n} (minimum p ((p>1 , isRet) , _) isMin) = minimum p (isPrime , p>n) isMin' where

  p≢1 : ¬ p ≡ 1
  p≢1 p≡1 = irrefl (PropEq.sym p≡1) p>1

  open import Data.Sum

  isMin' : IsMinimal (IsPrime'> n) _<_ p
  isMin' {q} ((q>1 , q-prime) , n<q) = isMin {q} ((q>1 , gg) , record {}) where
   gg : ∀ x → x ≤ n → IsPrime x → ¬ x ∣ q
   gg p' p'≤n = q-prime p' (≤O.trans (s≤s p'≤n) n<q)

  isPrime : IsPrime' p
  isPrime = p>1 , (λ m m<p mp → isRet m (≮⇒≥ (λ n<m → isMin' {m} (prime⇒prime' mp , n<m) m<p)) mp)

  p>n : p > n
  p>n = small-not-retained (p>1 , isRet)


sieve-step : ∀ {n} → Sifted≤ n → Σ (Minimum (IsPrime'> n) _<_) (λ pmin → Sifted≤ (Minimum.value pmin))
sieve-step {n} (headd ∷ taill) = p , substExhaustiveStream to from (subtract {b = nothing} (headd ∷ taill) (multiples pv pv>0) infinite) where
  pv : ℕ
  pv = Minimum.value headd

  p : Minimum (IsPrime'> n) _<_
  p = hoho headd

  pv>0 : pv > 0
  pv>0 with pv | proj₁ (proj₁ (Minimum.holds p))
  pv>0 | .(suc n') | s≤s {.1} {n'} m≤n = s≤s z≤n

  to : ∀ {x} → IsRetainedAfterSieve≤ n x × ¬ pv ∣ x → IsRetainedAfterSieve≤ pv x
  to {x} (ret , ord) = isRetainedAfterSieve-step p ret ord

  from : ∀ {x} → IsRetainedAfterSieve≤ pv x → IsRetainedAfterSieve≤ n x × ¬ pv ∣ x
  from x = isRetainedAfterSieve-step-rev p x

  open MRel _<_

  import PrimesInfinite

  infinite' : ∀ n' → ∃ (λ m → n' < m × IsRetainedAfterSieve≤ n m × ¬ pv ∣ m)
  infinite' n = case PrimesInfinite.infinite (1 + pv + n) of λ where
    (m , 1+pv+n<m , good) → m , (≤O.trans (s≤s (n≤m+n (1 + pv) n)) 1+pv+n<m , from (≤O.trans (m≤m+n 2 (pv + n)) 1+pv+n<m , λ {x x≤pv → good x (≤O.trans x≤pv (≤O.trans (m≤m+n pv n) (n≤m+n 1 (pv + n)))) } ))

  infinite : ∀ n' → ∃ (λ m → n' m< just m × IsRetainedAfterSieve≤ n m × ¬ pv ∣ m)
  infinite nothing = case infinite' 0 of λ where
   (m , _ , res) → m , record {} , res
  infinite (just n) = infinite' n

AllPrimes = SortedExhaustiveStream _<_ IsPrime' (just 0)

abstract
 sieve-step-abs : ∀ {n} → Sifted≤ n → Σ (Minimum (IsPrime'> n) _<_) (λ pmin → Sifted≤ (Minimum.value pmin))
 sieve-step-abs = sieve-step


go-primes : ∀ {n} → Sifted≤ n → SortedExhaustiveStream _<_ IsPrime' (just n)
go-primes sifted with sieve-step-abs sifted
go-primes sifted | prime , sifted' = prime ∷ (♯ go-primes sifted')

seed : Sifted≤ 0
seed = gono where

  stupid : ∀ {n} x → x ≤ 0 → IsPrime x → ¬ x ∣ n
  stupid .0 z≤n qq x1 = zero-nonprime qq
  
  go : ∀ n-1 → SortedExhaustiveStream _<_ (IsRetainedAfterSieve≤ 0) (just (suc n-1))
  go n-1 = (minimum (suc (suc n-1)) good minimal) ∷ ♯ go (suc n-1) where

    n = suc n-1
    Good' = λ y → IsRetainedAfterSieve≤ 0 y × y > n

    good : Good' (suc n)
    good = (s≤s (s≤s z≤n) , stupid) , (≤O.reflexive PropEq.refl)
 
    minimal : ∀ {y} → Good' y → ¬ y < suc n
    minimal (proj₁ , n<y) (s≤s y<1+n) = <O.irrefl PropEq.refl (≤O.trans n<y  y<1+n)

  gono : SortedExhaustiveStream _<_ (IsRetainedAfterSieve≤ 0) nothing
  gono = (minimum 2 (((s≤s (s≤s z≤n)) , stupid) , Data.Unit.tt) minimal) ∷ ♯ go 1 where
   Good' = λ y → IsRetainedAfterSieve≤ 0 y × ⊤

   minimal : ∀ {y} → Good' y → ¬ y < 2
   minimal ((s≤s (s≤s m≤n) , proj₂) , proj₂') (s≤s (s≤s ()))

all-primes : SortedExhaustiveStream _<_ IsPrime' (just 0)
all-primes = go-primes seed
