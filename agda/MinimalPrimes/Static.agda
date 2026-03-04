{-# OPTIONS --cubical-compatible #-}

open import Level
open import Algebra.Bundles
open import Data.Sum
open import Data.Product hiding (map₂)
open import Data.List
open import Data.List.Membership.Propositional renaming (_∈_ to _⋿_)
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Algebra.Bundles
import Data.Nat as Nat
import Data.Nat.Properties
open import Relation.Unary hiding (∅)
import Relation.Binary.PropositionalEquality as PE

module MinimalPrimes.Static
  (R… : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R… renaming (Carrier to R))
  (Enum : Nat.ℕ → Pred R 0ℓ)
  (Enum-singlevalued : {n : Nat.ℕ} {x y : R} → Enum n x → Enum n y → x PE.≡ y) where

open import MinimalPrimes.Base (R…)

G : Nat.ℕ → Pred R 0ℓ
G Nat.zero    = ∅
G (Nat.suc n) = G n ∪ ｛ x ∶ Enum n ∣ ¬ 0# ∈ ⟨ G n ∪ ｛ x ｝ ⟩ ｝

G-increasing : {n m : Nat.ℕ} → n Nat.≤ m → G n ⊆ G m
G-increasing p = go (Data.Nat.Properties.≤⇒≤′ p)
  where
  go : {n m : Nat.ℕ} → n Nat.≤′ m → G n ⊆ G m
  go Nat.≤′-refl     z = z
  go (Nat.≤′-step p) z = inj₁ (go p z)

all-stages-proper : (n : Nat.ℕ) → ¬ 0# ∈ ⟨ G n ⟩
all-stages-proper Nat.zero    p = ⟨∅⟩-trivial p
all-stages-proper (Nat.suc n) p with ⟨⟩-union₀ p
... | inj₁ q = all-stages-proper n q
... | inj₂ (x , In q f) = f (⟨⟩-monotone (map₂ λ { (In r s) → Enum-singlevalued q r }) p)

S : Pred R 0ℓ
S = ⋃[ n ∶ Nat.ℕ ] G n

S-proper : ¬ 0# ∈ S
S-proper (n , q) = all-stages-proper n (0# ∷ [] , sym (*-identityʳ 0#) , ms)
  where ms : All (G n) (0# ∷ []) ; ms = q ∷ []

⟨S⟩-proper : ¬ 0# ∈ ⟨ S ⟩
⟨S⟩-proper p with ⟨⟩-compact G G-increasing p
... | n , q = all-stages-proper n q

3⇒4 : {n : Nat.ℕ} → ¬ 0# ∈ ⟨ S ∪ Enum n ⟩ → ¬ 0# ∈ ⟨ G n ∪ Enum n ⟩
3⇒4 {n} = contraposition λ p → ⟨⟩-monotone (λ { (inj₁ q) → inj₁ (n , q) ; (inj₂ q) → inj₂ q }) p

4⇒1 : {n : Nat.ℕ} → ¬ 0# ∈ ⟨ G n ∪ Enum n ⟩ → Enum n ⊆ G (Nat.suc n)
4⇒1 p q = inj₂ (In q (contraposition (⟨⟩-monotone (map₂ λ { PE.refl → q })) p))

1⇒2 : {n : Nat.ℕ} → Enum n ⊆ G (Nat.suc n) → Enum n ⊆ S
1⇒2 {n} p q = Nat.suc n , p q

2⇒3 : {n : Nat.ℕ} → Enum n ⊆ S → ¬ 0# ∈ ⟨ S ∪ Enum n ⟩
2⇒3 p q = ⟨S⟩-proper (⟨⟩-monotone (λ { (inj₁ r) → r ; (inj₂ r) → p r }) q)

3⇒2 : {n : Nat.ℕ} → ¬ 0# ∈ ⟨ S ∪ Enum n ⟩ → Enum n ⊆ S
3⇒2 p = 1⇒2 (4⇒1 (3⇒4 p))

module _ (Enum-surjective : (x : R) → Σ[ n ∈ Nat.ℕ ] Enum n x) where

  S-is-multiplicative-system : ⟨ S ⟩ ⊆ S
  S-is-multiplicative-system {x} p with Enum-surjective x
  ... | n , r = 3⇒2 (λ q → ⟨S⟩-proper (⟨⟩-idempotent (⟨⟩-monotone go q))) r
    where
    go : S ∪ Enum n ⊆ ⟨ S ⟩
    go {y} (inj₁ s) = y ∷ [] , sym (*-identityʳ y) , ms
      where ms : All S (y ∷ []) ; ms = s ∷ []
    go     (inj₂ s) = PE.subst (⟨ S ⟩) (Enum-singlevalued r s) p

  S-is-maximal
    : (x : R)
    → ¬ 0# ∈ ⟨ S ∪ ｛ x ｝ ⟩
    → x ∈ S
  S-is-maximal x p with Enum-surjective x
  ... | n , r = 3⇒2 (contraposition (⟨⟩-monotone (map₂ λ s → Enum-singlevalued r s)) p) r

  S-dni : {x : R} → ¬ ¬ S x → S x
  S-dni {x} nns = S-is-maximal x
    λ q → nns (λ sx → ⟨S⟩-proper (⟨⟩-monotone (λ { (inj₁ s) → s ; (inj₂ PE.refl) → sx }) q))
