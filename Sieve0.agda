module Sieve0 where

open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Product
open import Factorisation
open import Relation.Nullary

IsRetainedAfterSieve≤ : ℕ → ℕ → Set
IsRetainedAfterSieve≤ m n = n ≥ 2 × (∀ x → x ≤ m → IsPrime x → ¬ x ∣ n)

IsPrime'> : ℕ → ℕ → Set
IsPrime'> n p = IsPrime' p × p > n

open import SortedExhaustiveStream
open import Data.Maybe

Sifted≤ : ℕ → Set
Sifted≤ n = SortedExhaustiveStream _<_ (IsRetainedAfterSieve≤  n) nothing

open import Relation.Binary
open import Data.Nat.Properties
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)
open import Data.Empty

private
 module ≤O = DecTotalOrder Data.Nat.Properties.≤-decTotalOrder
 module <O = StrictTotalOrder Data.Nat.Properties.strictTotalOrder


abstract 
 zzzz : ∀ {a b} → a ≤ b → ¬ a ≡ b → a < b
 zzzz .{0} {zero} z≤n neqqq = ⊥-elim (neqqq PropEq.refl) 
 zzzz .{0} {suc n} z≤n neqqq = s≤s z≤n
 zzzz .{suc m} .{suc n} (s≤s {m} {n} m≤n) neqqq = s≤s (zzzz m≤n (λ x → neqqq (PropEq.cong suc x)))

 isRetainedAfterSieve-step : ∀ { n } → (p : Minimum (IsPrime'> n) _<_) 
   → ∀ { m }
   → IsRetainedAfterSieve≤ n m
   → let pv = Minimum.value p in
     ¬ pv ∣ m
   → IsRetainedAfterSieve≤ pv m
 isRetainedAfterSieve-step {n} (minimum pv _ isMin) {m} (m>1 , no-divs) ¬div = m>1 , nonono where
   nonono : (∀ x → x ≤ pv → IsPrime x → ¬ x ∣ m)
   nonono x x≤p isP x∣m with x ≟ pv
   nonono .pv x≤p isP x∣m | yes PropEq.refl = ¬div x∣m
   ... | no neq = no-divs x x≤n isP x∣m where
    x≤n : x ≤ n
    x≤n with x ≤? n
    x≤n | yes x≤n = x≤n
    x≤n | no ¬x≤n = ⊥-elim (isMin {x} (prime⇒prime' isP , ≰⇒> ¬x≤n) (zzzz x≤p neq))

 isRetainedAfterSieve-step-rev : ∀ { n } → (p : Minimum (IsPrime'> n) _<_) 
   → ∀ { m }
   → let pv = Minimum.value p in
   IsRetainedAfterSieve≤ pv m
   → IsRetainedAfterSieve≤ n m × ¬ pv ∣ m
 isRetainedAfterSieve-step-rev {n} (minimum p (p-prime , n<p) isMin) {m} (m>1 , ret) = (m>1 , prevRet) , ¬div where

   prevRet : ∀ x → x ≤ n → IsPrime x → ¬ x ∣ m
   prevRet x x≤n = ret x (≤O.trans x≤n (≤O.trans (n≤m+n 1 n) n<p))

   ¬div : ¬ p ∣ m
   ¬div p∣m = ret p (≤O.reflexive PropEq.refl) (prime'⇒prime p-prime) p∣m
