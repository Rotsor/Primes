module Multiples where

open import Data.Nat
open import Data.Product
open import Data.Maybe

getBound : ℕ → ℕ → Maybe ℕ
getBound _ zero = nothing
getBound n (suc k) = just (k * n)

open import Data.Nat.Properties
open import Data.Nat.Divisibility

open import Algebra
open CommutativeSemiring Data.Nat.Properties.commutativeSemiring using (+-comm; *-comm; *-identity)

open import SortedExhaustiveStream
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary
open import Coinduction

private
 module ≤O = DecTotalOrder Data.Nat.decTotalOrder
 module <O = StrictTotalOrder Data.Nat.Properties.strictTotalOrder

abstract
 multiples' : ∀ n (k : ℕ) → n > 0 → SortedExhaustiveStream _<_ (λ x → n ∣ x) (getBound n k)
 multiples' n k n>0 = (minimum (k * n) (divides k PropEq.refl , good) minimal) ∷ ♯ multiples' n (suc k) n>0 where

  +-lem-inv : ∀ {n a b} → a ≤ b → n + a ≤ n + b
  +-lem-inv {zero} le = le
  +-lem-inv {suc n} le = s≤s (+-lem-inv {n} le)

  +-lem : ∀ {n a b} → n + a ≤ n + b → a ≤ b
  +-lem {zero} le = le
  +-lem {suc n'} (s≤s m≤n) = +-lem {n'} m≤n

  *-lem-inv : ∀ {n a b} → n > 0 → a ≥ b → a * n ≥ b * n
  *-lem-inv n>1 z≤n = z≤n
  *-lem-inv {n} n>1 (s≤s m≤n) = +-lem-inv {n} (*-lem-inv n>1 m≤n)

  ≥⇒≯ : ∀ {a b} → a ≥ b → ¬ b > a
  ≥⇒≯ z≤n ()
  ≥⇒≯ (s≤s m≤n) (s≤s m≤n') = ≥⇒≯ m≤n m≤n'

  *-lem : ∀ {a b n} → n > 0 → a * n < b * n → a < b
  *-lem n>0 lss = ≰⇒> (λ le → ≥⇒≯ (*-lem-inv n>0 le) lss)

  import MRel
  open MRel _<_
  good : getBound n k m< (just (k * n))
  good with k
  good | zero = record {}
  good | suc k-1 with n | n>0
  good | suc k-1 | .(suc n') | s≤s {.0} {n'} m≤n = s≤s (n≤m+n n' (k-1 * suc n'))

  minimal : ∀ {y} → n ∣ y ×  getBound n k m< just y → ¬ y < k * n
  minimal (n∣y , nk<y) y<kn with k
  minimal (n∣y , nk<y) () | zero
  minimal (divides q PropEq.refl , nk<y) y<kn | suc k with *-lem {k} {q} {n}  n>0 nk<y
  ... | zzz = ≥⇒≯ (zzz *-mono ≤O.reflexive (PropEq.refl {x = n})) y<kn

abstract
 multiples : ∀ n → n > 0 → SortedExhaustiveStream _<_ (λ x → n ∣ x) nothing
 multiples n n>0 = multiples' n 0 n>0

