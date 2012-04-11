module DividesProduct where

open import Data.List
open import Data.List.Any
open import Data.Nat
import Data.Nat.Divisibility as Div
open Div
import Relation.Binary.PropositionalEquality as PropEq
open PropEq
open Membership (setoid ℕ)
open import Data.Nat.Properties
open SemiringSolver
open import Relation.Binary

theorem : ∀ {x l} → x ∈ l → x ∣ product l
theorem {l = x ∷ t} (here refl) = divides (product t) (solve 2 (λ a b → a :* b := b :* a) refl x (product t))
theorem {l = x ∷ t} (there pxs) with theorem pxs
theorem {l = x ∷ t} (there pxs) | th = Poset.trans Div.poset th (divides x refl)
theorem {l = []} ()
