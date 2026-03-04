{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch #-}

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

module Krull.Static
  (R… : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R… renaming (Carrier to R))
  (Enum : Nat.ℕ → Pred R 0ℓ)
  (Enum-singlevalued : {n : Nat.ℕ} {x y : R} → Enum n x → Enum n y → x PE.≡ y) where

open import Krull.Base (R…)

Matrix : Set → Nat.ℕ → Nat.ℕ → Set
Matrix A n m = Fin.Fin n → Fin.Fin m → A

-- Sum of a function over Fin n
finSum : {n : Nat.ℕ} → (Fin.Fin n → R) → R
finSum {Nat.zero}  _ = 0#
finSum {Nat.suc n} f = f Fin.zero + finSum (λ x → f (Fin.suc x))

-- Matrix product: (matprod M N) i k = Σ_j M i j * N j k
matprod : {p q r : Nat.ℕ} → Matrix R p q → Matrix R q r → Matrix R p r
matprod M N i k = finSum (λ j → M i j * N j k)

-- Kronecker delta
δ : {n : Nat.ℕ} → Fin.Fin n → Fin.Fin n → R
δ Fin.zero    Fin.zero    = 1#
δ Fin.zero    (Fin.suc _) = 0#
δ (Fin.suc _) Fin.zero    = 0#
δ (Fin.suc i) (Fin.suc j) = δ i j

-- Auxiliary lemmas for reduce-surjective

finSum-congr : {n : Nat.ℕ} {f g : Fin.Fin n → R}
  → (∀ j → f j ≈ g j) → finSum f ≈ finSum g
finSum-congr {Nat.zero}  h = refl
finSum-congr {Nat.suc n} h = +-cong (h Fin.zero) (finSum-congr (λ j → h (Fin.suc j)))

finSum-add : {n : Nat.ℕ} (f g : Fin.Fin n → R)
  → finSum (λ j → f j + g j) ≈ finSum f + finSum g
finSum-add {Nat.zero}  f g = sym (+-identityˡ 0#)
finSum-add {Nat.suc n} f g =
  trans (+-congˡ (finSum-add (λ j → f (Fin.suc j)) (λ j → g (Fin.suc j))))
  (trans (+-assoc _ _ _)
  (trans (+-congˡ (trans (sym (+-assoc _ _ _)) (trans (+-congʳ (+-comm _ _)) (+-assoc _ _ _))))
         (sym (+-assoc _ _ _))))

finSum-scale : {n : Nat.ℕ} (c : R) (f : Fin.Fin n → R)
  → finSum (λ j → c * f j) ≈ c * finSum f
finSum-scale {Nat.zero}  c f = sym (zeroʳ c)
finSum-scale {Nat.suc n} c f =
  trans (+-congˡ (finSum-scale c (λ j → f (Fin.suc j))))
        (sym (distribˡ c (f Fin.zero) (finSum (λ j → f (Fin.suc j)))))

neg-one-times : (x : R) → (- 1#) * x ≈ - x
neg-one-times x =
  let step1 : (- 1#) * x + x ≈ 0#
      step1 = trans (+-congˡ (sym (*-identityˡ x)))
              (trans (sym (distribʳ x (- 1#) 1#))
              (trans (*-congʳ (-‿inverseˡ 1#))
                     (zeroˡ x)))
  in trans (sym (+-identityʳ ((- 1#) * x)))
     (trans (+-congˡ (sym (-‿inverseʳ x)))
     (trans (sym (+-assoc ((- 1#) * x) x (- x)))
     (trans (+-congʳ step1)
            (+-identityˡ (- x)))))

-- finSum over Fin (suc m) equals f(j) plus the sum over the complement of j
finSum-punchIn : {m : Nat.ℕ} (j : Fin.Fin (Nat.suc m)) (f : Fin.Fin (Nat.suc m) → R)
  → finSum f ≈ f j + finSum (λ j' → f (Fin.punchIn j j'))
finSum-punchIn           Fin.zero    f = refl
finSum-punchIn {Nat.suc _} (Fin.suc j) f =
  trans (+-congˡ (finSum-punchIn j (λ j' → f (Fin.suc j'))))
  (trans (sym (+-assoc (f Fin.zero) _ _))
  (trans (+-congʳ (+-comm (f Fin.zero) _))
         (+-assoc _ _ _)))

finSum-neg : {n : Nat.ℕ} (f : Fin.Fin n → R)
  → finSum (λ j → - f j) ≈ - finSum f
finSum-neg f =
  trans (finSum-congr (λ j → sym (neg-one-times (f j))))
  (trans (finSum-scale (- 1#) f)
         (neg-one-times (finSum f)))

finSum-sub : {n : Nat.ℕ} (f g : Fin.Fin n → R)
  → finSum (λ j → f j - g j) ≈ finSum f - finSum g
finSum-sub f g = trans (finSum-add f (λ j → - g j)) (+-congˡ (finSum-neg g))

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

-- (1) The matrix obtained by eliminating column j using the invertible entry M i j
-- (with inverse s) via row operations, then deleting row i and column j.
reduce-matrix : {n m : Nat.ℕ}
  → Matrix R (Nat.suc n) (Nat.suc m)
  → (i : Fin.Fin (Nat.suc n)) (j : Fin.Fin (Nat.suc m))
  → (s : R)
  → Matrix R n m
reduce-matrix M i j s i' j' =
  M (Fin.punchIn i i') (Fin.punchIn j j') - M (Fin.punchIn i i') j * s * M i (Fin.punchIn j j')

-- (2) Submatrix of N obtained by deleting row j and column i.
-- This is the candidate right inverse for reduce-matrix M i j s.
reduce-inverse : {n m : Nat.ℕ}
  → Matrix R (Nat.suc m) (Nat.suc n)
  → (i : Fin.Fin (Nat.suc n)) (j : Fin.Fin (Nat.suc m))
  → Matrix R m n
reduce-inverse N i j p' q' = N (Fin.punchIn j p') (Fin.punchIn i q')

sub-distribʳ : (a b c : R) → (a - b) * c ≈ a * c - b * c
sub-distribʳ a b c =
  trans (distribʳ c a (- b))
        (+-congˡ (trans (*-congʳ (sym (neg-one-times b)))
                 (trans (*-assoc (- 1#) b c)
                        (neg-one-times (b * c)))))

+-cancelˡ-to-sub : (a b c : R) → a ≈ b + c → c ≈ a - b
+-cancelˡ-to-sub a b c h =
  trans (sym (+-identityˡ c))
  (trans (+-congʳ (sym (-‿inverseˡ b)))
  (trans (+-assoc (- b) b c)
  (trans (+-congˡ (sym h))
         (+-comm (- b) a))))

neg-distribʳ-* : (a b : R) → a * (- b) ≈ - (a * b)
neg-distribʳ-* a b =
  trans (*-congˡ (sym (neg-one-times b)))
  (trans (sym (*-assoc a (- 1#) b))
  (trans (*-congʳ (*-comm a (- 1#)))
  (trans (*-assoc (- 1#) a b)
         (neg-one-times (a * b)))))

-- (2') reduce-inverse N i j is a right inverse of reduce-matrix M i j s,
-- provided N is a right inverse of M and M i j * s ≈ 1#.
reduce-inverse-correct : {n m : Nat.ℕ}
  → (M : Matrix R (Nat.suc n) (Nat.suc m))
  → (i : Fin.Fin (Nat.suc n)) (j : Fin.Fin (Nat.suc m))
  → (s : R) → M i j * s ≈ 1#
  → (N : Matrix R (Nat.suc m) (Nat.suc n))
  → (∀ p q → matprod M N p q ≈ δ p q)
  → ∀ p q → matprod (reduce-matrix M i j s) (reduce-inverse N i j) p q ≈ δ p q
reduce-inverse-correct M i j s Mij-inv N MN≡I p' q' =
  trans (finSum-congr (λ k' → sub-distribʳ
    (M p (Fin.punchIn j k')) (M p j * s * M i (Fin.punchIn j k')) (N (Fin.punchIn j k') q)))
  (trans (finSum-sub
    (λ k' → M p (Fin.punchIn j k') * N (Fin.punchIn j k') q)
    (λ k' → M p j * s * M i (Fin.punchIn j k') * N (Fin.punchIn j k') q))
  (trans (+-cong sum1-eq (-‿cong sum2-eq))
         combine))
  where
  p = Fin.punchIn i p'
  q = Fin.punchIn i q'

  -- (a * s) * (M i j * d) ≈ a * d, using Mij-inv and commutativity
  cancel-inv : (a d : R) → (a * s) * (M i j * d) ≈ a * d
  cancel-inv a d =
    trans (*-assoc a s (M i j * d))
    (*-congˡ (trans (sym (*-assoc s (M i j) d))
             (trans (*-congʳ (*-comm s (M i j)))
             (trans (*-congʳ Mij-inv)
                    (*-identityˡ d)))))

  -- First sum ≈ δ p' q' - M p j * N j q  (via finSum-punchIn + MN≡I + δ-punchIn-inj)
  sum1-eq =
    trans (+-cancelˡ-to-sub (matprod M N p q) (M p j * N j q) _
             (finSum-punchIn j (λ k → M p k * N k q)))
          (+-congʳ (trans (MN≡I p q) (δ-punchIn-inj i p' q')))

  -- Inner sum in second term ≈ - (M i j * N j q)  (via finSum-punchIn + δ-punchIn-avoid)
  inner-sum-eq =
    trans (+-cancelˡ-to-sub (matprod M N i q) (M i j * N j q) _
             (finSum-punchIn j (λ k → M i k * N k q)))
    (trans (+-congʳ (trans (MN≡I i q) (δ-punchIn-avoid i q')))
           (+-identityˡ _))

  -- Second sum ≈ - (M p j * N j q)  (via *-assoc, finSum-scale, inner-sum-eq, cancel-inv)
  sum2-eq =
    trans (finSum-congr (λ k' → *-assoc (M p j * s) (M i (Fin.punchIn j k')) (N (Fin.punchIn j k') q)))
    (trans (finSum-scale (M p j * s) (λ k' → M i (Fin.punchIn j k') * N (Fin.punchIn j k') q))
    (trans (*-congˡ inner-sum-eq)
    (trans (neg-distribʳ-* (M p j * s) (M i j * N j q))
           (-‿cong (cancel-inv (M p j) (N j q))))))

  -- (δ p' q' - a) + (- (- a)) ≈ δ p' q'  via -‿inverseʳ
  combine =
    trans (+-assoc (δ p' q') _ _)
    (trans (+-congˡ (-‿inverseʳ _))
           (+-identityʳ _))

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

-- (3) A surjective matrix with zero columns and at least one row is absurd.
zero-columns : {n : Nat.ℕ}
  → (M : Matrix R (Nat.suc n) Nat.zero)
  → (N : Matrix R Nat.zero (Nat.suc n))
  → (∀ p q → matprod M N p q ≈ δ p q)
  → ⊥
zero-columns M N MN≡I = sym (MN≡I Fin.zero Fin.zero)

-- (3') A surjective matrix with at least one row consisting only of zeros is absurd.
surj-zero-matrix : {n m : Nat.ℕ}
  → (M : Matrix R (Nat.suc n) m)
  → (∀ i j → M i j ≈ 0#)
  → (N : Matrix R m (Nat.suc n))
  → (∀ p q → matprod M N p q ≈ δ p q)
  → ⊥
surj-zero-matrix M M-zero N MN≡I =
  trans (sym (MN≡I Fin.zero Fin.zero))
    (trans (finSum-congr (λ j' → *-congʳ (M-zero Fin.zero j')))
           (trans (finSum-scale 0# (λ j' → N j' Fin.zero))
                  (zeroˡ _)))

-- A surjective matrix with at least one row whose first row is all zeros is absurd.
surj-zero-first-row : {n m : Nat.ℕ}
  → (M : Matrix R (Nat.suc n) m)
  → (∀ j → M Fin.zero j ≈ 0#)
  → (N : Matrix R m (Nat.suc n))
  → (∀ p q → matprod M N p q ≈ δ p q)
  → ⊥
surj-zero-first-row M M-zero-row N MN≡I =
  trans (sym (MN≡I Fin.zero Fin.zero))
    (trans (finSum-congr (λ j' → *-congʳ (M-zero-row j')))
           (trans (finSum-scale 0# (λ j' → N j' Fin.zero))
                  (zeroˡ _)))

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
    case-a-inv p = ⟨𝔪⟩-proper (⟨⟩-idempotent (⟨⟩-monotone (λ { (w , eq , inj₁ p) → Eq (≡⇒≈ (PE.sym eq)) (Magnet (Base p)) ; (w , eq , inj₂ PE.refl) → Eq (trans (trans (sym (zeroˡ b)) (trans (*-congʳ (sym va0)) (trans (*-assoc v w b) (trans (*-congˡ (*-comm w b)) (sym (*-assoc v b w)))))) (≡⇒≈ (PE.sym eq))) Zero }) (Eq (trans (*-identityʳ (v * b)) vb1) (⟨⟩-mult (v * b) p))))

    -- If a ∈ 𝔪, then 1 = ua ∈ 𝔪.
    case-a-zero : a ∈ 𝔪 → ⊥
    case-a-zero p = ⟨𝔪⟩-proper (Eq ua1 (Magnet (Base p)))

  postulate
    -- Non-invertible elements are zero (field condition).
    field-condition : (x : R) → (∀ s → ¬ x * s ≈ 1#) → x ≈ 0#

  {-# TERMINATING #-}
  mutual
    -- (5) Any surjective matrix with more rows than columns is absurd.
    surj-matrix
      : {n m : Nat.ℕ} → m Nat.< n
      → (M : Matrix R n m)
      → (N : Matrix R m n)
      → (∀ p q → matprod M N p q ≈ δ p q)
      → ⊥
    surj-matrix {Nat.suc _} {Nat.zero}  _    M N MN≡I = zero-columns M N MN≡I
    surj-matrix {Nat.suc _} {Nat.suc _} m<n M N MN≡I =
      surj-zero-first-row M
        (λ j → field-condition (M Fin.zero j)
          (λ s h → surj-with-invertible-entry
            (Data.Nat.Properties.≤-pred m<n) M Fin.zero j s h N MN≡I))
        N MN≡I

    -- (4) A surjective matrix with more rows than columns and an invertible entry is absurd.
    surj-with-invertible-entry
      : {n m : Nat.ℕ} → m Nat.< n
      → (M : Matrix R (Nat.suc n) (Nat.suc m))
      → (i : Fin.Fin (Nat.suc n)) (j : Fin.Fin (Nat.suc m))
      → (s : R) → M i j * s ≈ 1#
      → (N : Matrix R (Nat.suc m) (Nat.suc n))
      → (∀ p q → matprod M N p q ≈ δ p q)
      → ⊥
    surj-with-invertible-entry m<n M i j s Mij-inv N MN≡I
      with reduce-surjective M i j s Mij-inv N MN≡I
    ... | N' , N'-inv = surj-matrix m<n (reduce-matrix M i j s) N' N'-inv
