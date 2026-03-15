{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch --safe #-}

open import Level
open import Algebra.Bundles
open import Data.Product
import Data.Nat as Nat
import Data.Nat.Properties
import Data.Fin as Fin
open import Relation.Unary hiding (∅)

module Krull.LinearAlgebra (R… : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R… renaming (Carrier to R)
open import Krull.Base (R…)
import Krull.QuotientRing as QR

Matrix : Set → Nat.ℕ → Nat.ℕ → Set
Matrix A n m = Fin.Fin n → Fin.Fin m → A

-- Sum of a function over Fin n
finSum : {n : Nat.ℕ} → (Fin.Fin n → R) → R
finSum {Nat.zero}  _ = 0#
finSum {Nat.suc n} f = f Fin.zero + finSum (λ x → f (Fin.suc x))

finSum-extensional : {n : Nat.ℕ} → (f g : Fin.Fin n → R) → ((i : Fin.Fin n) → f i ≈ g i) → finSum f ≈ finSum g
finSum-extensional {Nat.zero} f g p = refl
finSum-extensional {Nat.suc n} f g p = +-cong (p Fin.zero) (finSum-extensional (λ x → f (Fin.suc x)) (λ x → g (Fin.suc x))
                                                             (λ i → p (Fin.suc i)))

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

-- The matrix obtained by eliminating column j using the invertible entry M i j
-- (with inverse s) via row operations, then deleting row i and column j.
reduce-matrix : {n m : Nat.ℕ}
  → Matrix R (Nat.suc n) (Nat.suc m)
  → (i : Fin.Fin (Nat.suc n)) (j : Fin.Fin (Nat.suc m))
  → (s : R)
  → Matrix R n m
reduce-matrix M i j s i' j' =
  M (Fin.punchIn i i') (Fin.punchIn j j') - M (Fin.punchIn i i') j * s * M i (Fin.punchIn j j')

-- Submatrix of N obtained by deleting row j and column i.
-- This is the candidate right inverse for reduce-matrix M i j s.
reduce-inverse : {n m : Nat.ℕ}
  → Matrix R (Nat.suc m) (Nat.suc n)
  → (i : Fin.Fin (Nat.suc n)) (j : Fin.Fin (Nat.suc m))
  → Matrix R m n
reduce-inverse N i j p' q' = N (Fin.punchIn j p') (Fin.punchIn i q')

-- reduce-inverse N i j is a right inverse of reduce-matrix M i j s,
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

module WithFieldCondition
  (field-condition : (x : R) → (∀ s → ¬ x * s ≈ 1#) → x ≈ 0#) where

  -- Any surjective matrix with more rows than columns is absurd.
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
  R/M-is-field x not-inv = Sum (Base x∈I) (⟨M⟩-neg Zero)
    where
    derive-⊥ : 1# ∈ ⟨ I ∪ ｛ x ｝ ⟩ → ⊥
    derive-⊥ one∈I∪x with ideal-decompose I x one∈I∪x
    ... | u , s , one≈u+sx , u∈⟨I⟩ = not-inv s (Eq (sym xs-1≈-u) (⟨M⟩-neg u∈⟨I⟩))
      where
      -- u + (x * s - 1) ≈ (u + s * x) - 1 ≈ 1 - 1 ≈ 0
      sum≈0 : u + (x * s - 1#) ≈ 0#
      sum≈0 =
        trans (+-congˡ (+-congʳ (*-comm x s)))
        (trans (sym (+-assoc u (s * x) (- 1#)))
        (trans (+-congʳ (sym one≈u+sx))
               (-‿inverseʳ 1#)))

      xs-1≈-u : x * s - 1# ≈ - u
      xs-1≈-u = inverse-unique u (x * s - 1#) sum≈0

    x∈I : x ∈ I
    x∈I = I-maximal x derive-⊥
