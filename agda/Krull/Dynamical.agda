{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch --safe #-}

open import Level
open import Algebra.Bundles
open import Data.Sum
open import Data.Product hiding (map₂)
open import Data.List
open import Data.List.Membership.Propositional renaming (_∈_ to _⋿_)
open import Algebra.Bundles
import Data.Nat as Nat
import Data.Nat.Properties
open import Relation.Unary hiding (∅)
import Relation.Binary.PropositionalEquality as PE
import Data.Fin as Fin

module Krull.Dynamical (R… : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R… renaming (Carrier to R)

open import Krull.Base R…
open import Krull.WildRing
import Krull.LinearAlgebra as LA
import Krull.WildLinearAlgebra as WLA
import Krull.QuotientRing as QR
open import Forcing.Levy R
open import Forcing.Base
open ForcingNotion L…
open import Forcing.Monad L…

G : {{σ : L}} → Nat.ℕ → Pred R 0ℓ
G {{σ}} Nat.zero    = ∅
G {{σ}} (Nat.suc n) = G n ∪ ｛ x ∶ Enum n ∣ (∀ {{τ : L}} {{_ : τ ≼ σ}} → ¬ 1# ∈ ⟨ G {{τ}} n ∪ ｛ x ｝ ⟩) ｝

G-monotone : {n : Nat.ℕ} {σ τ : L} → τ ≼ σ → G {{σ}} n ⊆ G {{τ}} n
G-monotone {Nat.zero}  τ≼σ p = p
G-monotone {Nat.suc n} τ≼σ (inj₁ p) = inj₁ (G-monotone {n} τ≼σ p)
G-monotone {Nat.suc n} τ≼σ (inj₂ (In p q)) = inj₂ (In (Enum-monotonic n _ τ≼σ p) λ {{ν}} {{ν≼τ}} → q {{ν}} {{≼-trans ν≼τ τ≼σ}})

G-increasing-step : {{σ : L}} {n : Nat.ℕ} → G n ⊆ G (Nat.suc n)
G-increasing-step p = inj₁ p

G-increasing : {{σ : L}} {n m : Nat.ℕ} → n Nat.≤ m → G n ⊆ G m
G-increasing p = go (Data.Nat.Properties.≤⇒≤′ p)
  where
  go : {n m : Nat.ℕ} → n Nat.≤′ m → G n ⊆ G m
  go Nat.≤′-refl = λ z → z
  go (Nat.≤′-step p) = λ z → G-increasing-step (go p z)

all-stages-proper : {{σ : L}} (n : Nat.ℕ) → ¬ 1# ∈ ⟨ G n ⟩
all-stages-proper ⦃ σ ⦄ Nat.zero    p = ⟨∅⟩-trivial p
all-stages-proper ⦃ σ ⦄ (Nat.suc n) p with ⟨⟩-union₀ p
... | inj₁ q = all-stages-proper n q
... | inj₂ (x , In q f) = f {{σ}} {{≼-refl}} (⟨⟩-monotone (λ { (inj₁ r) → inj₁ r ; (inj₂ (In r s)) → inj₂ (Enum-singlevalued n x _ q r)} ) p)

-- (no ∇ here, to simplify the development, so this is just the presheaf)
𝔪 : {{σ : L}} → Pred R 0ℓ
𝔪 {{σ}} = ⋃[ n ∶ Nat.ℕ ] G n

𝔪-monotone : {σ τ : L} → τ ≼ σ → 𝔪 {{σ}} ⊆ 𝔪 {{τ}}
𝔪-monotone τ≼σ (n , p) = (n , G-monotone {n} τ≼σ p)

𝔪-proper : {{σ : L}} → ¬ 1# ∈ 𝔪
𝔪-proper (n , q) = all-stages-proper n (Base q)

⟨𝔪⟩-proper : {{σ : L}} → ¬ 1# ∈ ⟨ 𝔪 ⟩
⟨𝔪⟩-proper p with ⟨⟩-compact G G-increasing p
... | n , q = all-stages-proper n q

3⇒4 : {{σ : L}} → {n : Nat.ℕ} → ¬ 1# ∈ ⟨ 𝔪 ∪ Enum n ⟩ → ¬ 1# ∈ ⟨ G n ∪ Enum n ⟩
3⇒4 {n} = contraposition λ p → ⟨⟩-monotone (λ { (inj₁ q) → inj₁ (n , q) ; (inj₂ q) → inj₂ q }) {1#} p

4⇒1 : {{σ : L}} → {n : Nat.ℕ} → (∀ {{τ : L}} {{_ : τ ≼ σ}} → ¬ 1# ∈ ⟨ G {{τ}} n ∪ Enum {{τ}} n ⟩) → Enum n ⊆ G (Nat.suc n)
4⇒1 {{σ}} p q = inj₂ (In q (λ {{τ}} {{τ≼σ}} → contraposition (⟨⟩-monotone (λ { (inj₁ r) → inj₁ r ; (inj₂ PE.refl) → inj₂ (Enum-monotonic _ _ τ≼σ q) }) {1#}) (p {{τ}} {{τ≼σ}})))

1⇒2 : {{σ : L}} {n : Nat.ℕ} → Enum n ⊆ G (Nat.suc n) → Enum n ⊆ 𝔪
1⇒2 {n} p q = Nat.suc n , p q

2⇒3 : {{σ : L}} {n : Nat.ℕ} → Enum n ⊆ 𝔪 → ¬ 1# ∈ ⟨ 𝔪 ∪ Enum n ⟩
2⇒3 {{σ}} p q = ⟨𝔪⟩-proper (⟨⟩-monotone (λ { (inj₁ r) → r ; (inj₂ r) → p r }) {1#} q)

3⇒2 : {{σ : L}} {n : Nat.ℕ} → (∀ {{τ : L}} {{_ : τ ≼ σ}} → ¬ 1# ∈ ⟨ 𝔪 {{τ}} ∪ Enum {{τ}} n ⟩) → Enum n ⊆ 𝔪
3⇒2 p = 1⇒2 (4⇒1 λ {{τ}} {{τ≼σ}} → 3⇒4 {{τ}} (p {{τ}}))

𝔪-is-ideal : {{σ : L}} → (x : R) → x ∈ ⟨ 𝔪 ⟩ → ∇ (λ {{τ}} → x ∈ 𝔪 {{τ}})
𝔪-is-ideal {{σ}} x p =
  Enum-surjective x ⟫=
  λ {{τ}} {{τ≼σ}} (n , r) →
  now (3⇒2 {{τ}} (λ {{ν}} {{ν≼τ}} q → ⟨𝔪⟩-proper {{ν}} (⟨⟩-idempotent (⟨⟩-monotone (λ { (inj₁ s) → Base s ; (inj₂ s) → Eq (≡⇒≈ (Enum-singlevalued {{ν}} n x _ (Enum-monotonic n x ν≼τ r) s)) (⟨⟩-monotone (𝔪-monotone (≼-trans ν≼τ τ≼σ)) p) }) q))) r)

𝔪-is-maximal
  : {{σ : L}}
  → (x : R)
  → (∀ {{τ : L}} {{_ : τ ≼ σ}} → ¬ 1# ∈ ⟨ 𝔪 {{τ}} ∪ ｛ x ｝ ⟩)
  → ∇ {{σ}} (λ {{τ}} → x ∈ 𝔪 {{τ}})
𝔪-is-maximal {{σ}} x p =
  Enum-surjective x ⟫=
  λ {{τ}} {{τ≼σ}} (n , r) →
  now (3⇒2 {{τ}} (λ {{ν}} {{ν≼τ}} → contraposition (⟨⟩-monotone (λ { (inj₁ s) → inj₁ s ; (inj₂ s) → inj₂ (Enum-singlevalued {{ν}} n x _ (Enum-monotonic n x ν≼τ r) s) }) {1#}) (p {{ν}} {{≼-trans ν≼τ τ≼σ}})) r)

-- The following example is the (2×1)-case of the general statement that
-- matrices with more rows that columns can only be surjective if 1 ≈ 0.
example : (a b u v : R) → u * a ≈ 1# → u * b ≈ 0# → v * a ≈ 0# → v * b ≈ 1# → ⊥
example a b u v ua1 ub0 va0 vb1 = escape {[]} (_⟫=_ {{[]}} (𝔪-is-maximal {{[]}} a case-a-inv) λ p → now (case-a-zero p))
  where
  -- If 1 ∈ ⟨ 𝔪, a ⟩, then 1 = vb ∈ ⟨ vb 𝔪, vb a ⟩ = ⟨ vb 𝔪 ⟩ ⊆ 𝔪, hence ⊥.
  case-a-inv : {{σ : L}} → 1# ∈ ⟨ 𝔪 ∪ ｛ a ｝ ⟩ → ⊥
  case-a-inv p = ⟨𝔪⟩-proper (⟨⟩-idempotent (⟨⟩-monotone (λ { (w , eq , inj₁ p) → Eq (≡⇒≈ (PE.sym eq)) (Magnet (Base p)) ; (w , eq , inj₂ PE.refl) → Eq (trans (trans (sym (zeroˡ b)) (trans (*-congʳ (sym va0)) (trans (*-assoc v w b) (trans (*-congˡ (*-comm w b)) (sym (*-assoc v b w)))))) (≡⇒≈ (PE.sym eq))) Zero }) (Eq (trans (*-identityʳ (v * b)) vb1) (⟨⟩-mult (v * b) p))))

  -- If a ∈ 𝔪, then 1 = ua ∈ 𝔪.
  case-a-zero : {{σ : L}} → a ∈ 𝔪 → ⊥
  case-a-zero p = ⟨𝔪⟩-proper (Eq ua1 (Magnet (Base p)))

-- Open linear algebra for R
open WLA (forget R…) public using (Matrix; matprod; δ; finSum; reduce-matrix; reduce-inverse)
open LA R… public using (reduce-surjective; zero-columns; surj-zero-first-row)

-- Quotient equality and ring, parametric in σ
_≈/𝔪_ : {{σ : L}} → R → R → Set
_≈/𝔪_ {{σ}} x y = (x - y) ∈ ⟨ 𝔪 {{σ}} ⟩

R/𝔪… : {{σ : L}} → CommutativeRing 0ℓ 0ℓ
R/𝔪… {{σ}} = QR.R/M… R… (𝔪 {{σ}})

embed/𝔪 : {{σ : L}} → {x y : R} → x ≈ y → x ≈/𝔪 y
embed/𝔪 {{σ}} = QR.embed R… (𝔪 {{σ}})

⟨𝔪⟩-neg : {{σ : L}} → {x : R} → x ∈ ⟨ 𝔪 ⟩ → (- x) ∈ ⟨ 𝔪 ⟩
⟨𝔪⟩-neg = QR.⟨M⟩-neg R… 𝔪

-- Monotonicity: quotient equality propagates to stronger conditions
≈/𝔪-monotone : {σ τ : L} {x y : R} → τ ≼ σ → _≈/𝔪_ {{σ}} x y → _≈/𝔪_ {{τ}} x y
≈/𝔪-monotone τ≼σ p = ⟨⟩-monotone (𝔪-monotone τ≼σ) p

-- Quotient-⊥ → Ring-⊥
⊥/𝔪→⊥ : {{σ : L}} → 1# ≈/𝔪 0# → ⊥
⊥/𝔪→⊥ p = ⟨𝔪⟩-proper (Eq (trans (+-congˡ (sym (inverse-unique 0# 0# (+-identityˡ 0#)))) (+-identityʳ 1#)) p)

-- Sequencing ∇ over Fin n
fin-∇ : {{σ : L}} {m : Nat.ℕ} {P : Fin.Fin m → L → Set}
  → (mono : ∀ j → Monotonic (P j))
  → (f : (j : Fin.Fin m) → ∇ {{σ}} (λ {{τ}} → P j τ))
  → ∇ {{σ}} (λ {{τ}} → ∀ j → P j τ)
fin-∇ {m = Nat.zero} mono f = now λ ()
fin-∇ {m = Nat.suc m} mono f =
  f Fin.zero ⟫= λ {{τ}} {{τ≼σ}} p →
  _⟫=_ {{τ}} (fin-∇ {{τ}} (λ j → mono (Fin.suc j)) (λ j → weaken-ev (mono (Fin.suc j)) τ≼σ (f (Fin.suc j))))
  λ {{ν}} {{ν≼τ}} h → now λ { Fin.zero → mono Fin.zero ν≼τ p ; (Fin.suc j) → h j }

-- matprod and δ are definitionally equal across quotient rings,
-- but we need propositional witnesses to embed R-equalities into R/𝔪-equalities.
module _ {{σ : L}} where
  private
    module LA/𝔪 = LA R/𝔪…

-- Dynamical field condition: if x*s is not ≈/𝔪 1 at any future stage for all s,
-- then eventually x ≈/𝔪 0.
field-condition-∇ : {{σ : L}} → (x : R)
  → ((s : R) → ∀ {{τ : L}} {{_ : τ ≼ σ}} → ¬ _≈/𝔪_ {{τ}} (x * s) 1#)
  → ∇ {{σ}} (λ {{τ}} → _≈/𝔪_ {{τ}} x 0#)
field-condition-∇ {{σ}} x not-inv = fmap (λ {{τ}} p → Sum (Base p) (⟨𝔪⟩-neg {{τ}} Zero)) (𝔪-is-maximal x λ {{τ}} → derive-⊥ {{τ}})
  where
  derive-⊥ : {{τ : L}} {{_ : τ ≼ σ}} → ¬ 1# ∈ ⟨ 𝔪 {{τ}} ∪ ｛ x ｝ ⟩
  derive-⊥ {{τ}} p with ideal-decompose (𝔪 {{τ}}) x p
  ... | u , s , eq , q = not-inv s {{τ}} (Eq (sym (inverse-unique u (x * s - 1#) sum≈0)) (⟨𝔪⟩-neg {{τ}} q))
    where
    sum≈0 : u + (x * s - 1#) ≈ 0#
    sum≈0 =
      trans (+-congˡ (+-congʳ (*-comm x s)))
      (trans (sym (+-assoc u (s * x) (- 1#)))
      (trans (+-congʳ (sym eq))
              (-‿inverseʳ 1#)))

-- The main inductive argument, lifted into ∇.
-- We use matprod/δ from R (not R/𝔪) to avoid definitional equality issues across σ.
surj-matrix-∇ : {{σ : L}} → {n m : Nat.ℕ} → m Nat.< n
  → (M' : Matrix R n m) → (N' : Matrix R m n)
  → (∀ p q → matprod M' N' p q ≈/𝔪 δ p q)
  → ∇ {{σ}} (λ {{_}} → ⊥)
surj-matrix-∇ {{σ}} {Nat.suc _} {Nat.zero} _ M' N' MN≡I =
  now (⊥/𝔪→⊥ (LA.zero-columns (R/𝔪… {{σ}}) M' N' MN≡I))
surj-matrix-∇ {{σ}} {Nat.suc _} {Nat.suc m} m<n M' N' MN≡I =
  fin-∇ {{σ}}
    (λ j τ≼σ p → ≈/𝔪-monotone τ≼σ p)
    (λ j → field-condition-∇ {{σ}} (M' Fin.zero j) λ s {{τ}} {{τ≼σ}} h →
      let (N'' , N''-inv) = LA.reduce-surjective (R/𝔪… {{τ}}) M' Fin.zero j s h N' (λ p q → ≈/𝔪-monotone τ≼σ (MN≡I p q))
      in  escape (surj-matrix-∇ {{τ}} (Data.Nat.Properties.≤-pred m<n)
                   (reduce-matrix M' Fin.zero j s) N'' N''-inv))
  ⟫= λ {{τ}} {{τ≼σ}} all-zero →
  now (⊥/𝔪→⊥ {{τ}} (LA.surj-zero-first-row (R/𝔪… {{τ}}) M' all-zero N'
    (λ p q → ≈/𝔪-monotone τ≼σ (MN≡I p q))))

example' : {n m : Nat.ℕ} → m Nat.< n
  → (M' : Matrix R n m) → (N' : Matrix R m n)
  → (∀ p q → matprod M' N' p q ≈ δ p q)
  → ⊥
example' m<n M' N' MN≡I = escape {[]}
  (surj-matrix-∇ {{[]}} m<n M' N'
    (λ p q → embed/𝔪 {{[]}} (MN≡I p q)))
