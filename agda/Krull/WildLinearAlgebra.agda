{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch --safe #-}

open import Level
open import Algebra.Bundles
open import Data.Product
import Data.Nat as Nat
import Data.Nat.Properties
import Data.Fin as Fin
open import Relation.Unary hiding (∅)
open import Krull.WildRing

module Krull.WildLinearAlgebra (R… : WildRing) where

open WildRing R… renaming (Carrier to R)

Matrix : Set → Nat.ℕ → Nat.ℕ → Set
Matrix A n m = Fin.Fin n → Fin.Fin m → A

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

