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
open import Relation.Binary.PropositionalEquality

module Krull.Static
  (R… : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R… renaming (Carrier to R))
  (Enum : Nat.ℕ → Pred R 0ℓ)
  (Enum-singlevalued : {n : Nat.ℕ} {x y : R} → Enum n x → Enum n y → x ≡ y) where

open import Krull.Base (R…)

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
all-stages-proper (Nat.suc n) p with ⟨⟩-union p
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
4⇒1 p q = inj₂ (In q (contraposition (⟨⟩-monotone (map₂ λ { Relation.Binary.PropositionalEquality.refl → q }) {1#}) p))

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
