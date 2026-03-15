{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch --safe #-}

open import Level
open import Algebra.Bundles
open import Data.Product
open import Data.Sum
import Data.Nat as Nat
import Data.Nat.Properties
import Data.Fin as Fin
open import Relation.Unary hiding (∅)
import Relation.Binary.PropositionalEquality as PE

open import Krull.WildRing

module Krull.LinearAlgebra (R… : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R… renaming (Carrier to R)
open import Relation.Binary.Reasoning.Setoid setoid
open import Krull.Base (R…)
import Krull.QuotientRing as QR
open import Krull.WildLinearAlgebra (forget R…)


-- Auxiliary lemmas for reduce-surjective

finSum-congr : {n : Nat.ℕ} {f g : Fin.Fin n → R}
  → (∀ j → f j ≈ g j) → finSum f ≈ finSum g
finSum-congr {Nat.zero}  h = refl
finSum-congr {Nat.suc n} h = +-cong (h Fin.zero) (finSum-congr (λ j → h (Fin.suc j)))

finSum-add : {n : Nat.ℕ} (f g : Fin.Fin n → R)
  → finSum (λ j → f j + g j) ≈ finSum f + finSum g
finSum-add {Nat.zero}  f g = sym (+-identityˡ 0#)
finSum-add {Nat.suc n} f g = begin
  (a + b) + finSum (λ j → f (Fin.suc j) + g (Fin.suc j))
    ≈⟨ +-congˡ (finSum-add (λ j → f (Fin.suc j)) (λ j → g (Fin.suc j))) ⟩
  (a + b) + (sf + sg)
    ≈⟨ +-assoc _ _ _ ⟩
  a + (b + (sf + sg))
    ≈˘⟨ +-congˡ (+-assoc b sf sg) ⟩
  a + ((b + sf) + sg)
    ≈⟨ +-congˡ (+-congʳ (+-comm b sf)) ⟩
  a + ((sf + b) + sg)
    ≈⟨ +-congˡ (+-assoc sf b sg) ⟩
  a + (sf + (b + sg))
    ≈˘⟨ +-assoc a sf _ ⟩
  (a + sf) + (b + sg)
    ∎
  where
  a  = f Fin.zero
  b  = g Fin.zero
  sf = finSum (λ j → f (Fin.suc j))
  sg = finSum (λ j → g (Fin.suc j))

finSum-scale : {n : Nat.ℕ} (c : R) (f : Fin.Fin n → R)
  → finSum (λ j → c * f j) ≈ c * finSum f
finSum-scale {Nat.zero}  c f = sym (zeroʳ c)
finSum-scale {Nat.suc n} c f = begin
  c * f Fin.zero + finSum (λ j → c * f (Fin.suc j))
    ≈⟨ +-congˡ (finSum-scale c (λ j → f (Fin.suc j))) ⟩
  c * f Fin.zero + c * finSum (λ j → f (Fin.suc j))
    ≈˘⟨ distribˡ c _ _ ⟩
  c * (f Fin.zero + finSum (λ j → f (Fin.suc j)))
    ∎

-- finSum over Fin (suc m) equals f(j) plus the sum over the complement of j
finSum-punchIn : {m : Nat.ℕ} (j : Fin.Fin (Nat.suc m)) (f : Fin.Fin (Nat.suc m) → R)
  → finSum f ≈ f j + finSum (λ j' → f (Fin.punchIn j j'))
finSum-punchIn           Fin.zero    f = refl
finSum-punchIn {Nat.suc _} (Fin.suc j) f = begin
  f Fin.zero + finSum (λ j' → f (Fin.suc j'))
    ≈⟨ +-congˡ (finSum-punchIn j (λ j' → f (Fin.suc j'))) ⟩
  f Fin.zero + (f (Fin.suc j) + s')
    ≈˘⟨ +-assoc (f Fin.zero) _ _ ⟩
  (f Fin.zero + f (Fin.suc j)) + s'
    ≈⟨ +-congʳ (+-comm (f Fin.zero) _) ⟩
  (f (Fin.suc j) + f Fin.zero) + s'
    ≈⟨ +-assoc _ _ _ ⟩
  f (Fin.suc j) + (f Fin.zero + s')
    ∎
  where s' = finSum (λ j' → f (Fin.suc (Fin.punchIn j j')))

finSum-neg : {n : Nat.ℕ} (f : Fin.Fin n → R)
  → finSum (λ j → - f j) ≈ - finSum f
finSum-neg f = begin
  finSum (λ j → - f j)
    ≈⟨ finSum-congr (λ j → sym (neg-one-times (f j))) ⟩
  finSum (λ j → - 1# * f j)
    ≈⟨ finSum-scale (- 1#) f ⟩
  - 1# * finSum f
    ≈⟨ neg-one-times (finSum f) ⟩
  - finSum f
    ∎

finSum-sub : {n : Nat.ℕ} (f g : Fin.Fin n → R)
  → finSum (λ j → f j - g j) ≈ finSum f - finSum g
finSum-sub f g = begin
  finSum (λ j → f j - g j)
    ≈⟨ finSum-add f (λ j → - g j) ⟩
  finSum f + finSum (λ j → - g j)
    ≈⟨ +-congˡ (finSum-neg g) ⟩
  finSum f - finSum g
    ∎

-- δ(i, punchIn i q) = 0 because punchIn i always avoids i
δ-punchIn-avoid : {n : Nat.ℕ} (i : Fin.Fin (Nat.suc n)) (q : Fin.Fin n)
  → δ i (Fin.punchIn i q) ≈ 0#
δ-punchIn-avoid Fin.zero      q           = refl
δ-punchIn-avoid (Fin.suc i)   Fin.zero    = refl
δ-punchIn-avoid (Fin.suc i)   (Fin.suc q) = δ-punchIn-avoid i q

-- δ(punchIn i p, punchIn i q) = δ(p, q) because punchIn i is injective
δ-punchIn-inj : {n : Nat.ℕ} (i : Fin.Fin (Nat.suc n)) (p q : Fin.Fin n)
  → δ (Fin.punchIn i p) (Fin.punchIn i q) ≈ δ p q
δ-punchIn-inj Fin.zero      p           q           = refl
δ-punchIn-inj (Fin.suc i)   Fin.zero    Fin.zero    = refl
δ-punchIn-inj (Fin.suc i)   Fin.zero    (Fin.suc q) = refl
δ-punchIn-inj (Fin.suc i)   (Fin.suc p) Fin.zero    = refl
δ-punchIn-inj (Fin.suc i)   (Fin.suc p) (Fin.suc q) = δ-punchIn-inj i p q

-- reduce-inverse N i j is a right inverse of reduce-matrix M i j s,
-- provided N is a right inverse of M and M i j * s ≈ 1#.
reduce-inverse-correct : {n m : Nat.ℕ}
  → (M : Matrix R (Nat.suc n) (Nat.suc m))
  → (i : Fin.Fin (Nat.suc n)) (j : Fin.Fin (Nat.suc m))
  → (s : R) → M i j * s ≈ 1#
  → (N : Matrix R (Nat.suc m) (Nat.suc n))
  → (∀ p q → matprod M N p q ≈ δ p q)
  → ∀ p q → matprod (reduce-matrix M i j s) (reduce-inverse N i j) p q ≈ δ p q
reduce-inverse-correct M i j s Mij-inv N MN≡I p' q' = begin
  matprod (reduce-matrix M i j s) (reduce-inverse N i j) p' q'
    ≈⟨ finSum-congr (λ k' → sub-distribʳ
         (M p (Fin.punchIn j k')) (M p j * s * M i (Fin.punchIn j k')) (N (Fin.punchIn j k') q)) ⟩
  finSum (λ k' → f₁ k' - f₂ k')
    ≈⟨ finSum-sub f₁ f₂ ⟩
  finSum f₁ - finSum f₂
    ≈⟨ +-cong sum1-eq (-‿cong sum2-eq) ⟩
  (δ p' q' - M p j * N j q) + - (- (M p j * N j q))
    ≈⟨ combine ⟩
  δ p' q'
    ∎
  where
  p = Fin.punchIn i p'
  q = Fin.punchIn i q'
  f₁ = λ k' → M p (Fin.punchIn j k') * N (Fin.punchIn j k') q
  f₂ = λ k' → M p j * s * M i (Fin.punchIn j k') * N (Fin.punchIn j k') q

  -- (a * s) * (M i j * d) ≈ a * d, using Mij-inv and commutativity
  cancel-inv : (a d : R) → (a * s) * (M i j * d) ≈ a * d
  cancel-inv a d = begin
    (a * s) * (M i j * d)
      ≈⟨ *-assoc a s _ ⟩
    a * (s * (M i j * d))
      ≈˘⟨ *-congˡ (*-assoc s (M i j) d) ⟩
    a * ((s * M i j) * d)
      ≈⟨ *-congˡ (*-congʳ (*-comm s (M i j))) ⟩
    a * ((M i j * s) * d)
      ≈⟨ *-congˡ (*-congʳ Mij-inv) ⟩
    a * (1# * d)
      ≈⟨ *-congˡ (*-identityˡ d) ⟩
    a * d
      ∎

  -- First sum ≈ δ p' q' - M p j * N j q  (via finSum-punchIn + MN≡I + δ-punchIn-inj)
  sum1-eq = begin
    finSum (λ k' → M p (Fin.punchIn j k') * N (Fin.punchIn j k') q)
      ≈⟨ +-cancelˡ-to-sub _ _ _ (finSum-punchIn j (λ k → M p k * N k q)) ⟩
    matprod M N p q - M p j * N j q
      ≈⟨ +-congʳ (trans (MN≡I p q) (δ-punchIn-inj i p' q')) ⟩
    δ p' q' - M p j * N j q
      ∎

  -- Inner sum in second term ≈ - (M i j * N j q)  (via finSum-punchIn + δ-punchIn-avoid)
  inner-sum-eq = begin
    finSum (λ k' → M i (Fin.punchIn j k') * N (Fin.punchIn j k') q)
      ≈⟨ +-cancelˡ-to-sub _ _ _ (finSum-punchIn j (λ k → M i k * N k q)) ⟩
    matprod M N i q - M i j * N j q
      ≈⟨ +-congʳ (trans (MN≡I i q) (δ-punchIn-avoid i q')) ⟩
    0# + - (M i j * N j q)
      ≈⟨ +-identityˡ _ ⟩
    - (M i j * N j q)
      ∎

  -- Second sum ≈ - (M p j * N j q)  (via *-assoc, finSum-scale, inner-sum-eq, cancel-inv)
  sum2-eq = begin
    finSum (λ k' → M p j * s * M i (Fin.punchIn j k') * N (Fin.punchIn j k') q)
      ≈⟨ finSum-congr (λ k' → *-assoc α (M i (Fin.punchIn j k')) (N (Fin.punchIn j k') q)) ⟩
    finSum (λ k' → α * (M i (Fin.punchIn j k') * N (Fin.punchIn j k') q))
      ≈⟨ finSum-scale α β ⟩
    α * finSum β
      ≈⟨ *-congˡ inner-sum-eq ⟩
    α * - (M i j * N j q)
      ≈⟨ neg-distribʳ-* α (M i j * N j q) ⟩
    - (α * (M i j * N j q))
      ≈⟨ -‿cong (cancel-inv (M p j) (N j q)) ⟩
    - (M p j * N j q)
      ∎
    where
    α = M p j * s
    β = λ k' → M i (Fin.punchIn j k') * N (Fin.punchIn j k') q

  -- (δ p' q' - a) + (- (- a)) ≈ δ p' q'  via -‿inverseʳ
  combine = begin
    (δ p' q' - M p j * N j q) + - (- (M p j * N j q))
      ≈⟨ +-assoc (δ p' q') _ _ ⟩
    δ p' q' + (- (M p j * N j q) + - (- (M p j * N j q)))
      ≈⟨ +-congˡ (-‿inverseʳ _) ⟩
    δ p' q' + 0#
      ≈⟨ +-identityʳ _ ⟩
    δ p' q'
      ∎

-- Combining the two: a right inverse of M yields a right inverse of reduce-matrix M i j s.
reduce-surjective : {n m : Nat.ℕ}
  → (M : Matrix R (Nat.suc n) (Nat.suc m))
  → (i : Fin.Fin (Nat.suc n)) (j : Fin.Fin (Nat.suc m))
  → (s : R) → M i j * s ≈ 1#
  → (N : Matrix R (Nat.suc m) (Nat.suc n))
  → (∀ p q → matprod M N p q ≈ δ p q)
  → Σ[ N' ∈ Matrix R m n ] ∀ p q → matprod (reduce-matrix M i j s) N' p q ≈ δ p q
reduce-surjective M i j s h N inv =
  reduce-inverse N i j , reduce-inverse-correct M i j s h N inv

-- A surjective matrix with zero columns and at least one row is absurd.
zero-columns : {n : Nat.ℕ}
  → (M : Matrix R (Nat.suc n) Nat.zero)
  → (N : Matrix R Nat.zero (Nat.suc n))
  → (∀ p q → matprod M N p q ≈ δ p q)
  → ⊥
zero-columns M N MN≡I = sym (MN≡I Fin.zero Fin.zero)

-- A surjective matrix with at least one row consisting only of zeros is absurd.
surj-zero-matrix : {n m : Nat.ℕ}
  → (M : Matrix R (Nat.suc n) m)
  → (∀ i j → M i j ≈ 0#)
  → (N : Matrix R m (Nat.suc n))
  → (∀ p q → matprod M N p q ≈ δ p q)
  → ⊥
surj-zero-matrix M M-zero N MN≡I = begin
  1#
    ≈˘⟨ MN≡I Fin.zero Fin.zero ⟩
  matprod M N Fin.zero Fin.zero
    ≈⟨ finSum-congr (λ j' → *-congʳ (M-zero Fin.zero j')) ⟩
  finSum (λ j' → 0# * N j' Fin.zero)
    ≈⟨ finSum-scale 0# (λ j' → N j' Fin.zero) ⟩
  0# * finSum (λ j' → N j' Fin.zero)
    ≈⟨ zeroˡ _ ⟩
  0#
    ∎

-- A surjective matrix with at least one row whose first row is all zeros is absurd.
surj-zero-first-row : {n m : Nat.ℕ}
  → (M : Matrix R (Nat.suc n) m)
  → (∀ j → M Fin.zero j ≈ 0#)
  → (N : Matrix R m (Nat.suc n))
  → (∀ p q → matprod M N p q ≈ δ p q)
  → ⊥
surj-zero-first-row M M-zero-row N MN≡I = begin
  1#
    ≈˘⟨ MN≡I Fin.zero Fin.zero ⟩
  matprod M N Fin.zero Fin.zero
    ≈⟨ finSum-congr (λ j' → *-congʳ (M-zero-row j')) ⟩
  finSum (λ j' → 0# * N j' Fin.zero)
    ≈⟨ finSum-scale 0# (λ j' → N j' Fin.zero) ⟩
  0# * finSum (λ j' → N j' Fin.zero)
    ≈⟨ zeroˡ _ ⟩
  0#
    ∎

-- Helper lemmas for the 2×1 example: given a proper ideal I and
-- elements a, b, u, v with ua≈1, ub≈0, va≈0, vb≈1,
-- we can show a is neither invertible mod I nor in I.

-- If ⟨I⟩ is proper and v*a ≈ 0, v*b ≈ 1, then a is not invertible modulo I.
example-case-a-inv-lemma : (I : Pred R 0ℓ) → ¬ 1# ∈ ⟨ I ⟩
  → (a b v : R) → v * a ≈ 0# → v * b ≈ 1#
  → ¬ 1# ∈ ⟨ I ∪ ｛ a ｝ ⟩
example-case-a-inv-lemma I ⟨I⟩-proper a b v va0 vb1 p =
  ⟨I⟩-proper (⟨⟩-idempotent (⟨⟩-monotone handle (Eq vb·1≈1 vb1*p)))
  where
  vb1*p : (v * b) * 1# ∈ ⟨ image ((v * b) *_) (I ∪ ｛ a ｝) ⟩
  vb1*p = ⟨⟩-mult (v * b) p

  vb·1≈1 : (v * b) * 1# ≈ 1#
  vb·1≈1 = begin
    (v * b) * 1# ≈⟨ *-identityʳ (v * b) ⟩
    v * b        ≈⟨ vb1 ⟩
    1#           ∎

  handle : image ((v * b) *_) (I ∪ ｛ a ｝) ⊆ ⟨ I ⟩
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

-- If ⟨I⟩ is proper and u*a ≈ 1, then a ∉ I.
example-case-a-zero-lemma : (I : Pred R 0ℓ) → ¬ 1# ∈ ⟨ I ⟩
  → (a u : R) → u * a ≈ 1#
  → a ∈ I → ⊥
example-case-a-zero-lemma I ⟨I⟩-proper a u ua1 p =
  ⟨I⟩-proper (Eq ua1 (Magnet (Base p)))

module WithFieldCondition
  (field-condition : (x : R) → (∀ s → ¬ x * s ≈ 1#) → x ≈ 0#) where

  -- A surjective matrix with more rows than columns is absurd.
  surj-matrix
    : {n m : Nat.ℕ} → m Nat.< n
    → (M : Matrix R n m)
    → (N : Matrix R m n)
    → (∀ p q → matprod M N p q ≈ δ p q)
    → ⊥
  surj-matrix {Nat.suc _} {Nat.zero}  _   M N MN≡I = zero-columns M N MN≡I
  surj-matrix {Nat.suc _} {Nat.suc _} m<n M N MN≡I =
    surj-zero-first-row M
      (λ j → field-condition (M Fin.zero j)
        (λ s h → let (N' , N'-inv) = reduce-surjective M Fin.zero j s h N MN≡I in
          surj-matrix (Data.Nat.Properties.≤-pred m<n) (reduce-matrix M Fin.zero j s) N' N'-inv))
      N MN≡I

module WithMaximalIdeal
  (I : Pred R 0ℓ)
  (I-maximal : (x : R) → ¬ 1# ∈ ⟨ I ∪ ｛ x ｝ ⟩ → x ∈ I)
  where

  open QR R… I public

  -- A maximal ideal gives a field: non-invertible elements are zero.
  R/M-is-field : (x : R) → ((s : R) → ¬ (x * s) ≈/M 1#) → x ≈/M 0#
  R/M-is-field x not-inv = Sum (Base (I-maximal x derive-⊥)) (⟨M⟩-neg Zero)
    where
    derive-⊥ : 1# ∈ ⟨ I ∪ ｛ x ｝ ⟩ → ⊥
    derive-⊥ one∈I∪x with ideal-decompose I x one∈I∪x
    ... | u , s , one≈u+sx , u∈⟨I⟩ = not-inv s (Eq (sym (inverse-unique u (x * s - 1#) sum≈0)) (⟨M⟩-neg u∈⟨I⟩))
      where
      sum≈0 : u + (x * s - 1#) ≈ 0#
      sum≈0 = begin
        u + (x * s - 1#)
          ≈⟨ +-congˡ (+-congʳ (*-comm x s)) ⟩
        u + (s * x - 1#)
          ≈˘⟨ +-assoc u (s * x) (- 1#) ⟩
        (u + s * x) - 1#
          ≈˘⟨ +-congʳ one≈u+sx ⟩
        1# - 1#
          ≈⟨ -‿inverseʳ 1# ⟩
        0#
          ∎
