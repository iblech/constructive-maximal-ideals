{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch --safe #-}

open import Level
open import Algebra.Bundles
open import Data.Sum
open import Data.Product hiding (map₂)
open import Data.List
open import Data.List.Membership.Propositional renaming (_∈_ to _⋿_)
import Data.Fin as Fin
import Data.Nat as Nat
import Data.Nat.Properties
open import Relation.Unary hiding (∅)
import Relation.Binary.PropositionalEquality as PE

module Krull.Static
  (R… : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R… renaming (Carrier to R))
  (Enum : Nat.ℕ → Pred R 0ℓ)
  (Enum-singlevalued : {n : Nat.ℕ} {x y : R} → Enum n x → Enum n y → x PE.≡ y) where

open import Krull.Base (R…)
open import Relation.Binary.Reasoning.Setoid setoid
import Krull.LinearAlgebra
import Krull.QuotientRing

G : Nat.ℕ → Pred R 0ℓ
G Nat.zero    = ∅
G (Nat.suc n) = G n ∪ ｛ x ∶ Enum n ∣ ¬ 1# ∈ ⟨ G n ∪ ｛ x ｝ ⟩ ｝

G-increasing : {n m : Nat.ℕ} → n Nat.≤ m → G n ⊆ G m
G-increasing p = go (Data.Nat.Properties.≤⇒≤′ p)
  where
  go : {n m : Nat.ℕ} → n Nat.≤′ m → G n ⊆ G m
  go Nat.≤′-refl     z = z
  go (Nat.≤′-step p) z = inj₁ (go p z)

all-stages-proper : (n : Nat.ℕ) → ¬ 1# ∈ ⟨ G n ⟩
all-stages-proper Nat.zero    p = ⟨∅⟩-trivial p
all-stages-proper (Nat.suc n) p with ⟨⟩-union₀ p
... | inj₁ q = all-stages-proper n q
... | inj₂ (x , In q f) = f (⟨⟩-monotone (map₂ λ { (In r s) → Enum-singlevalued q r} ) p)

𝔪 : Pred R 0ℓ
𝔪 = ⋃[ n ∶ Nat.ℕ ] G n

𝔪-proper : ¬ 1# ∈ 𝔪
𝔪-proper (n , q) = all-stages-proper n (Base q)

⟨𝔪⟩-proper : ¬ 1# ∈ ⟨ 𝔪 ⟩
⟨𝔪⟩-proper p with ⟨⟩-compact G G-increasing p
... | n , q = all-stages-proper n q

3⇒4 : {n : Nat.ℕ} → ¬ 1# ∈ ⟨ 𝔪 ∪ Enum n ⟩ → ¬ 1# ∈ ⟨ G n ∪ Enum n ⟩
3⇒4 {n} = contraposition λ p → ⟨⟩-monotone (λ { (inj₁ q) → inj₁ (n , q) ; (inj₂ q) → inj₂ q }) {1#} p

4⇒1 : {n : Nat.ℕ} → ¬ 1# ∈ ⟨ G n ∪ Enum n ⟩ → Enum n ⊆ G (Nat.suc n)
4⇒1 p q = inj₂ (In q (contraposition (⟨⟩-monotone (map₂ λ { PE.refl → q }) {1#}) p))

1⇒2 : {n : Nat.ℕ} → Enum n ⊆ G (Nat.suc n) → Enum n ⊆ 𝔪
1⇒2 {n} p q = Nat.suc n , p q

2⇒3 : {n : Nat.ℕ} → Enum n ⊆ 𝔪 → ¬ 1# ∈ ⟨ 𝔪 ∪ Enum n ⟩
2⇒3 p q = ⟨𝔪⟩-proper (⟨⟩-monotone (λ { (inj₁ r) → r ; (inj₂ r) → p r }) {1#} q)

3⇒2 : {n : Nat.ℕ} → ¬ 1# ∈ ⟨ 𝔪 ∪ Enum n ⟩ → Enum n ⊆ 𝔪
3⇒2 p = 1⇒2 (4⇒1 (3⇒4 p))

module _ (Enum-surjective : (x : R) → Σ[ n ∈ Nat.ℕ ] Enum n x) where
  𝔪-is-ideal : ⟨ 𝔪 ⟩ ⊆ 𝔪
  𝔪-is-ideal {x} p with Enum-surjective x
  ... | n , r = 3⇒2 (λ q → ⟨𝔪⟩-proper (⟨⟩-idempotent (⟨⟩-monotone (λ { (inj₁ s) → Base s ; (inj₂ s) → Eq (≡⇒≈ (Enum-singlevalued r s)) p }) q))) r

  𝔪-is-maximal
    : (x : R)
    → ¬ 1# ∈ ⟨ 𝔪 ∪ ｛ x ｝ ⟩
    → x ∈ 𝔪
  𝔪-is-maximal x p with Enum-surjective x
  ... | n , r = 3⇒2 (contraposition (⟨⟩-monotone (map₂ λ s → Enum-singlevalued r s) {1#}) p) r

  -- The following example is the (2×1)-case of the general statement that
  -- matrices with more rows that columns can only be surjective if 1 ≈ 0.
  example : (a b u v : R) → u * a ≈ 1# → u * b ≈ 0# → v * a ≈ 0# → v * b ≈ 1# → ⊥
  example a b u v ua1 ub0 va0 vb1 = case-a-zero (𝔪-is-maximal a case-a-inv)
    where
    -- If 1 ∈ ⟨ 𝔪, a ⟩, then 1 = vb ∈ ⟨ vb 𝔪, vb a ⟩ = ⟨ vb 𝔪 ⟩ ⊆ 𝔪, hence ⊥.
    case-a-inv : 1# ∈ ⟨ 𝔪 ∪ ｛ a ｝ ⟩ → ⊥
    case-a-inv p = ⟨𝔪⟩-proper (⟨⟩-idempotent (⟨⟩-monotone handle (Eq vb·1≈1 vb1*p)))
      where
      vb1*p : (v * b) * 1# ∈ ⟨ image ((v * b) *_) (𝔪 ∪ ｛ a ｝) ⟩
      vb1*p = ⟨⟩-mult (v * b) p

      vb·1≈1 : (v * b) * 1# ≈ 1#
      vb·1≈1 = begin
        (v * b) * 1# ≈⟨ *-identityʳ (v * b) ⟩
        v * b        ≈⟨ vb1 ⟩
        1#           ∎

      handle : image ((v * b) *_) (𝔪 ∪ ｛ a ｝) ⊆ ⟨ 𝔪 ⟩
      handle (w , eq , inj₁ q) = Eq (≡⇒≈ (PE.sym eq)) (Magnet (Base q))
      handle (w , eq , inj₂ PE.refl) = Eq 0≈y Zero
        where
        0≈vb·w : 0# ≈ (v * b) * w
        0≈vb·w = begin
          0#          ≈˘⟨ zeroˡ b ⟩
          0# * b      ≈˘⟨ *-congʳ va0 ⟩
          (v * w) * b ≈⟨ *-assoc v w b ⟩
          v * (w * b) ≈⟨ *-congˡ (*-comm w b) ⟩
          v * (b * w) ≈˘⟨ *-assoc v b w ⟩
          (v * b) * w ∎

        0≈y : 0# ≈ _
        0≈y = trans 0≈vb·w (≡⇒≈ (PE.sym eq))

    -- If a ∈ 𝔪, then 1 = ua ∈ 𝔪.
    case-a-zero : a ∈ 𝔪 → ⊥
    case-a-zero p = ⟨𝔪⟩-proper (Eq ua1 (Magnet (Base p)))

  open import Krull.WildRing
  open import Krull.WildLinearAlgebra (forget R…)
  open Krull.LinearAlgebra R…
  open Krull.QuotientRing R… 𝔪
    renaming (R/M… to R/𝔪… ; _≈/M_ to _≈/𝔪_)

  -- The quotient R/𝔪 is a field (non-invertible elements are zero).
  R/𝔪-is-field : (x : R) → ((s : R) → ¬ (x * s) ≈/𝔪 1#) → x ≈/𝔪 0#
  R/𝔪-is-field = R/M-is-field
    where
    open WithMaximalIdeal 𝔪 𝔪-is-maximal

  ⊥/𝔪→⊥ : 1# ≈/𝔪 0# → ⊥
  ⊥/𝔪→⊥ p = ⟨𝔪⟩-proper (Eq (trans (+-congˡ (sym (inverse-unique 0# 0# (+-identityˡ 0#)))) (+-identityʳ 1#)) p)

  R/𝔪-is-field' : (x : R) → ((s : R) → (x * s) ≈/𝔪 1# → 1# ≈/𝔪 0#) → x ≈/𝔪 0#
  R/𝔪-is-field' x h = R/𝔪-is-field x λ s p → ⊥/𝔪→⊥ (h s p)

  example'
    : {n m : Nat.ℕ} → m Nat.< n → (M : Matrix R n m)
    → (N : Matrix R m n)
    → (∀ p q → matprod M N p q ≈ δ p q)
    → ⊥
  -- example' m<n M N MN≡I = ⊥/𝔪→⊥ (surj-matrix m<n M N λ i j → embed (trans (sym (matprod-homo M N i j)) (trans (MN≡I i j) (δ-homo i j))))
  example' m<n M N MN≡I = ⊥/𝔪→⊥ (surj-matrix m<n M N λ i j → embed (MN≡I i j))
    where
    import Krull.LinearAlgebra R/𝔪… as Q
    open Q.WithFieldCondition R/𝔪-is-field'
