module NatBoundedGtWF where

open import Induction.WellFounded
open import Data.Nat hiding (compare; _<_; _≟_)
import Data.Nat.Properties 
open import Data.Product
open import Relation.Binary
open Relation.Binary.StrictTotalOrder Data.Nat.Properties.strictTotalOrder

wf : ∀ max → Well-founded (λ a b → a > b × a < max)
wf = qqq where
 
 import Relation.Binary.PropositionalEquality as PropEq
 open PropEq using (_≡_; _≢_)

 data _≤''_ : ℕ → ℕ → Set where
  ≤''-refl : ∀ {m} →                         m ≤'' m
  ≤''-step : ∀ {m n} (m≤′n : m ≤'' n) → pred m ≤'' n

 <'⇒≤′ : ∀ a b → a <′ b → a ≤′ b
 <'⇒≤′ a .(suc a) ≤′-refl = ≤′-step ≤′-refl
 <'⇒≤′ a .(suc n) (≤′-step {n} m≤′n) = ≤′-step (<'⇒≤′ a n m≤′n)

 sssss : ∀ a b → a ≤'' b → a ≤'' suc b
 sssss .b b ≤''-refl = ≤''-step ≤''-refl
 sssss .0 b (≤''-step {zero} m≤′n) = sssss zero b m≤′n
 sssss .n b (≤''-step {suc n} m≤′n) = ≤''-step (sssss (suc n) b m≤′n)

 ≤''→≤′ : ∀ a b → a ≤'' b → a ≤′ b
 ≤''→≤′ .b b ≤''-refl = ≤′-refl
 ≤''→≤′ .0 b (≤''-step {zero} m≤′n) = ≤''→≤′ zero b m≤′n
 ≤''→≤′ .n b (≤''-step {suc n} m≤′n) with ≤''→≤′ (suc n) b m≤′n
 ... | rec = <'⇒≤′ n b rec

 ≤′→≤'' : ∀ a b → a ≤′ b → a ≤'' b
 ≤′→≤'' .b b ≤′-refl = ≤''-refl
 ≤′→≤'' a .(suc n) (≤′-step {n} m≤′n) with ≤′→≤'' a n m≤′n
 ... | rec = sssss a n rec

 open import Relation.Nullary

 open import Data.Empty

 lemm : ∀ a b → a > pred b → a ≢ b → a > b
 lemm a zero gt neq = gt
 lemm a (suc n) gt neq with compare a (suc n)
 lemm a (suc n) gt neq | tri< a' ¬b ¬c = ⊥-elim (irrefl PropEq.refl (Relation.Binary.DecTotalOrder.trans Data.Nat.decTotalOrder a' gt))
 lemm a (suc n) gt neq | tri≈ ¬a b ¬c = ⊥-elim (neq b)
 lemm a (suc n) gt neq | tri> ¬a ¬b c = c

 zzz : ∀ max x → x ≤'' max → Acc (λ a b → a > b × a < max) x
 zzz max .max ≤''-refl = acc (λ { y (max<y , y<max) → ⊥-elim (irrefl PropEq.refl (trans max<y y<max)) })
 zzz max .(pred m) (≤''-step {m} m≤′n) with zzz max m m≤′n
 ... | acc rec = acc go where
  go : ∀ y → (y > pred m × y < max) → Acc (λ a b → a > b × a < max) y
  go y (y>m , y<max) with y ≟ m
  go .m (y>m , y<max) | yes PropEq.refl = acc rec
  ... | no neq = rec y (lemm y m y>m neq , y<max)

 qqq : ∀ max x → Acc (λ a b → a > b × a < max) x
 qqq max x with x ≤? max
 ... | yes x≤max = zzz max x ( ≤′→≤'' _ _ (Data.Nat.Properties.≤⇒≤′ x≤max))
 ... | no x>max = acc  (λ { y (x<y , y<max) →  ⊥-elim (x>max (Data.Nat.Properties.≤′⇒≤ (<'⇒≤′ _ _ (Data.Nat.Properties.≤⇒≤′ (trans x<y y<max))))) })
