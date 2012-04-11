
module SortedExhaustiveStream where

import MRel
open import Data.Maybe
open import Data.Empty
open import Data.Product
open import Coinduction
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)
open import Relation.Unary
open import Relation.Nullary
import Level

IsMinimal : ∀ {A : Set} → (P : Pred A Level.zero) (_<_ : A → A → Set) → Pred A Level.zero
IsMinimal P _<_ x = ∀ {y} → P y → ¬ y < x

record Minimum {A : Set} (P : Pred A Level.zero) (_<_ : A → A → Set) : Set where
 constructor minimum
 field
  value : A
  holds : P value
  isMin : IsMinimal P _<_ value

record SortedExhaustiveStream' {A : Set} (_<_ : A → A → Set) (P : A → Set) (b : Maybe A) : Set where
 constructor _∷_
 open MRel _<_
 Good : Pred A Level.zero
 Good x = P x × b m< just x
 field
  headd : Minimum Good _<_
  taill : ∞ (SortedExhaustiveStream' _<_ P (just (Minimum.value headd)))

open import Function

Bounded-> : ∀ {A : Set} → (_<_ : A → A → Set) → A → (A → A → Set)
Bounded-> _<_ max = λ a b → b < a × a < max

open import Induction.WellFounded

module WithTotalOrder (A : Set) (_<_ : A → A → Set) (order : IsStrictTotalOrder _≡_ _<_)
  (>-wf : ∀ max → Well-founded (Bounded-> _<_ max))
    where
  open IsStrictTotalOrder order

{-   data _∈_ {P : A → Set} {b : Maybe A} : A → SortedExhaustiveStream' _<_ P b → Set where
    here : ∀ {stream} → SortedExhaustiveStream'.headd stream ∈ stream
    there : ∀ {x stream} → x ∈ (♭ (SortedExhaustiveStream'.taill stream)) → x ∈ stream -}

  module MR = MRel _<_
  open MR using (_m<_)
  mtrans : ∀ {a b c} → a m< b → b m< c → a m< c
  mtrans {a} {b} {c} = MR.trans trans {a} {b} {c}

  m>-wf : ∀ max → Well-founded (Bounded-> _m<_ max)
  m>-wf nothing = λ _ → acc λ { x (_ , ()) }
  m>-wf (just max) = gogogo where
    ACC = Acc (Bounded-> _m<_ (just max))
    ACc = Acc (Bounded-> _<_ max)
    go : ∀ x → ACc x → ACC (just x)
    go x (acc accc) = acc (λ { nothing (() , _) ; (just y) lsss → go y (accc y lsss) })

    gogo : ∀ x → ACC (just x)
    gogo x = go x (>-wf max x)

    gogogo : ∀ x → ACC x
    gogogo nothing = acc λ { nothing (() , _) ; (just y) lsss → gogo y }
    gogogo (just x) = gogo x

  SSTEP : (P₁ P₂ : A → Set) → (mx : A) → (n : Maybe A) → Set
  SSTEP P₁ P₂ mx n = 
    n m< just mx
    → (as : SortedExhaustiveStream' _<_ P₁ n)
    → (bs : SortedExhaustiveStream' _<_ P₂ n)
    → Σ (Minimum (λ y → (P₁ y × ¬ P₂ y) × n m< just y) _<_) (λ mn → let x = Minimum.value mn in SortedExhaustiveStream' {A} _<_ P₁ (just x) × SortedExhaustiveStream' {A} _<_ P₂ (just x))

  subtract'-step : 
    ∀ {P₁ : A → Set} {P₂ : A → Set} {n : Maybe A}
    → (mx : A)
    → (P₁ mx × ¬ P₂ mx)
    → SSTEP P₁ P₂ mx n
  subtract'-step {P₁} {P₂} {n} mx (p₁x , ¬p₂x) = All.wfRec (m>-wf (just mx)) (SSTEP P₁ P₂ mx) go n where 

    _>_ = Bounded-> _m<_ (just mx)

    go : ∀ n → (rec : ∀ n' → n' > n → SSTEP P₁ P₂ mx n') →  SSTEP P₁ P₂ mx n
    go n rec n<mx (minimum a good minimal ∷ as) (minimum b good' minimal' ∷ bs) with compare a b
    go n rec n<mx (minimum a (pa , n<a) a-minimal ∷ as) (minimum b (p₂b , n<b) b-minimal ∷ bs) | tri< a<b ¬b ¬c = minimum a ((pa , (λ p₂a → b-minimal (p₂a , n<a) a<b)) , n<a) (λ { {y} ((p₁y , ¬p₂y) , n<y) y<a → a-minimal {y} (p₁y , n<y) y<a }) , ♭ as , (minimum b (p₂b , a<b) (λ { {y} (p₂y , a<y) → b-minimal (p₂y , mtrans {n} {just a} {just y} n<a a<y )} ) ∷ bs)
    go n rec n<mx (minimum .b (p₁a , n<a) a-minimal ∷ as) (minimum b (p₂b , n<b) b-minimal ∷ bs) | tri≈ ¬a<b PropEq.refl ¬b<a with rec (just b) (n<b , b<mx) b<mx (♭ as) (♭ bs)  where
      b<mx : b < mx
      b<mx with compare b mx
      b<mx | tri< b<mx _ _ = b<mx
      b<mx | tri≈ _ b≡mx _ = ⊥-elim (¬p₂x (PropEq.subst P₂ b≡mx p₂b))
      b<mx | tri> _ _ b>mx = ⊥-elim (a-minimal {mx} (p₁x , n<mx) b>mx)
    ... | (minimum r (p₁¬p₂r , b<r) r-minimal) , str₁ , str₂ = minimum r (p₁¬p₂r , mtrans {n} {just b} {just r} n<b b<r) r-minimal' , str₁ , str₂ where
      r-minimal' : IsMinimal (λ y → (P₁ y × ¬ P₂ y) × n m< just y) _<_ r
      r-minimal' {y} gg y<r with compare b y
      r-minimal' {y} (good-y , n<y) y<r | tri< b<y _ _ = r-minimal {y} (good-y , b<y) y<r
      r-minimal' ((proj₁ , ¬p₂y) , n<y) y<r | tri≈ ¬a PropEq.refl ¬c = ¬p₂y p₂b
      r-minimal' {y} ((p₁y , _) , n<y) y<r | tri> _ _ y<b = a-minimal {y} (p₁y , n<y) (y<b)
    go n rec n<mx (minimum a (p₁a , n<a) a-minimal ∷ as) (minimum b (p₂b , n<b) b-minimal ∷ bs) | tri> ¬a<b ¬a≈b b<a with rec (just b) (n<b , b<mx) b<mx (minimum a (p₁a , b<a) (λ { {y} (p₁y , b<y) y<a → a-minimal {y} (p₁y , mtrans {n} {just b} {just y} n<b b<y) y<a }) ∷ as) (♭ bs) where
      b<mx : b < mx
      b<mx with compare b mx
      b<mx | tri< b<mx _ _ = b<mx
      b<mx | tri≈ _ b≡mx _ = ⊥-elim (a-minimal {mx} (p₁x , n<mx) (PropEq.subst (λ q → q < a) b≡mx b<a))
      b<mx | tri> _ _ b>mx = ⊥-elim (a-minimal {mx} (p₁x , n<mx) (trans b>mx b<a))
    ... | minimum r (p₁¬p₂r , b<r) r-minimal , str₁ , str₂ = minimum r (p₁¬p₂r , mtrans {n} {just b} {just r} n<b b<r) r-minimal' , str₁ , str₂ where
      r-minimal' : IsMinimal (λ y → (P₁ y × ¬ P₂ y) × n m< just y) _<_ r
      r-minimal' {y} gg y<r with compare b y
      r-minimal' {y} (good-y , n<y) y<r | tri< b<y _ _ = r-minimal {y} (good-y , b<y) y<r
      r-minimal' ((proj₁ , ¬p₂y) , n<y) y<r | tri≈ ¬a PropEq.refl ¬c = ¬p₂y p₂b
      r-minimal' {y} ((p₁y , _) , n<y) y<r | tri> _ _ y<b = a-minimal {y} (p₁y , n<y) (trans y<b b<a)

  subtract' : 
    {P₁ : A → Set} {P₂ : A → Set} {b : Maybe A}
    → SortedExhaustiveStream' _<_ P₁ b
    → SortedExhaustiveStream' _<_ P₂ b
    → (∀ n → ∃ (λ m → n m< just m × P₁ m × ¬ P₂ m))
    → SortedExhaustiveStream' {A} _<_ (λ x → P₁ x × ¬ P₂ x) b
  subtract' {b = b} str₁ str₂ good with good b
  ... | (m , b<m , gm) with subtract'-step m gm b<m str₁ str₂
  ... | x , r-str₁ , r-str₂ = x ∷ ♯ subtract' r-str₁ r-str₂ good



substMinimum : ∀ {A : Set} → {P Q : A → Set} → {_<_ : A → A → Set}
  → (∀ {p} → P p → Q p) 
  → (∀ {q} → Q q → P q)
  → Minimum P _<_
  → Minimum Q _<_
substMinimum to from (minimum value holds isMin) = minimum value (to holds) (λ qy → isMin (from qy))

substExhaustiveStream' : 
  ∀ {A : Set}  {_<_ : A → A → Set} → {P Q : A → Set}
  → (∀ {p} → P p → Q p) 
  → (∀ {q} → Q q → P q)
  → ∀ {b}
  → SortedExhaustiveStream' _<_ P b
  → SortedExhaustiveStream' _<_ Q b
substExhaustiveStream' {P = P} {Q = Q} to from {b} (headd ∷ taill) = substMinimum (λ { (p , o) → (to p , o) }) (λ { (p , o) → (from p , o) }) headd ∷ ♯ substExhaustiveStream' to from (♭ taill)
