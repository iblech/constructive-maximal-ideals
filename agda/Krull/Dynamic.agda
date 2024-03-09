{-# OPTIONS --cubical-compatible --safe #-}

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

module Krull.Dynamic (R… : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R… renaming (Carrier to R)

open import Krull.Base R…
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
