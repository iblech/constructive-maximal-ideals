{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch #-}

open import Level
open import Algebra.Bundles
open import Data.Product using (_,_)
open import Relation.Unary hiding (∅)

module Krull.QuotientRing
  (R… : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R… renaming (Carrier to R))
  (M : Pred R 0ℓ)
  where

open import Krull.Base (R…)
open import Relation.Binary using (Rel)
import Relation.Binary.Reasoning.Setoid as SetoidR
open SetoidR setoid

-- Quotient equality: x ≈/M y iff x - y ∈ ⟨ M ⟩
_≈/M_ : Rel R 0ℓ
x ≈/M y = (x - y) ∈ ⟨ M ⟩

-- Ring lemmas (private)
private
  neg-one-times : (x : R) → (- 1#) * x ≈ - x
  neg-one-times x = begin
    (- 1#) * x             ≈⟨ sym (+-identityʳ _) ⟩
    (- 1#) * x + 0#        ≈⟨ +-congˡ (sym (-‿inverseʳ x)) ⟩
    (- 1#) * x + (x - x)   ≈⟨ sym (+-assoc _ x (- x)) ⟩
    ((- 1#) * x + x) - x   ≈⟨ +-congʳ (+-congˡ (sym (*-identityˡ x))) ⟩
    ((- 1#) * x + 1# * x) - x ≈⟨ +-congʳ (sym (distribʳ x (- 1#) 1#)) ⟩
    ((- 1#) + 1#) * x - x  ≈⟨ +-congʳ (*-congʳ (-‿inverseˡ 1#)) ⟩
    0# * x - x             ≈⟨ +-congʳ (zeroˡ x) ⟩
    0# - x                 ≈⟨ +-identityˡ (- x) ⟩
    - x                    ∎

  inverse-unique : (x y : R) → x + y ≈ 0# → y ≈ - x
  inverse-unique x y h = begin
    y              ≈⟨ sym (+-identityˡ y) ⟩
    0# + y         ≈⟨ +-congʳ (sym (-‿inverseˡ x)) ⟩
    (- x + x) + y  ≈⟨ +-assoc (- x) x y ⟩
    - x + (x + y)  ≈⟨ +-congˡ h ⟩
    - x + 0#       ≈⟨ +-identityʳ (- x) ⟩
    - x            ∎

  double-neg : (x : R) → - (- x) ≈ x
  double-neg x = sym (inverse-unique (- x) x (-‿inverseˡ x))

  neg-distrib-+ : (a b : R) → - (a + b) ≈ (- a) + (- b)
  neg-distrib-+ a b = sym (inverse-unique (a + b) ((- a) + (- b)) lemma)
    where
    lemma : (a + b) + ((- a) + (- b)) ≈ 0#
    lemma = begin
      (a + b) + ((- a) + (- b))  ≈⟨ +-assoc a b ((- a) + (- b)) ⟩
      a + (b + ((- a) + (- b)))  ≈⟨ +-congˡ (sym (+-assoc b (- a) (- b))) ⟩
      a + ((b + (- a)) + (- b))  ≈⟨ +-congˡ (+-congʳ (+-comm b (- a))) ⟩
      a + (((- a) + b) + (- b))  ≈⟨ +-congˡ (+-assoc (- a) b (- b)) ⟩
      a + ((- a) + (b + (- b)))  ≈⟨ +-congˡ (+-congˡ (-‿inverseʳ b)) ⟩
      a + ((- a) + 0#)          ≈⟨ +-congˡ (+-identityʳ (- a)) ⟩
      a + (- a)                 ≈⟨ -‿inverseʳ a ⟩
      0#                        ∎

  neg-distribʳ-* : (a b : R) → a * (- b) ≈ - (a * b)
  neg-distribʳ-* a b = begin
    a * (- b)         ≈⟨ *-congˡ (sym (neg-one-times b)) ⟩
    a * ((- 1#) * b)  ≈⟨ sym (*-assoc a (- 1#) b) ⟩
    (a * (- 1#)) * b  ≈⟨ *-congʳ (*-comm a (- 1#)) ⟩
    ((- 1#) * a) * b  ≈⟨ *-assoc (- 1#) a b ⟩
    (- 1#) * (a * b)  ≈⟨ neg-one-times (a * b) ⟩
    - (a * b)         ∎

-- Ideal closure under negation
⟨M⟩-neg : {x : R} → x ∈ ⟨ M ⟩ → (- x) ∈ ⟨ M ⟩
⟨M⟩-neg p = Eq (neg-one-times _) (Magnet {r = - 1#} p)

-- Lift original equality into quotient equality
embed : {x y : R} → x ≈ y → x ≈/M y
embed {x} {y} h = Eq (sym (trans (+-congʳ h) (-‿inverseʳ y))) Zero

-- Equivalence
≈/M-refl : {x : R} → x ≈/M x
≈/M-refl {x} = Eq (sym (-‿inverseʳ x)) Zero

≈/M-sym : {x y : R} → x ≈/M y → y ≈/M x
≈/M-sym {x} {y} p = Eq (sym lemma) (⟨M⟩-neg p)
  where
  lemma : y - x ≈ - (x - y)
  lemma = begin
    y - x                ≈⟨ +-congʳ (sym (double-neg y)) ⟩
    - (- y) - x          ≈⟨ +-comm (- (- y)) (- x) ⟩
    - x + (- (- y))      ≈⟨ sym (neg-distrib-+ x (- y)) ⟩
    - (x + (- y))        ∎

≈/M-trans : {x y z : R} → x ≈/M y → y ≈/M z → x ≈/M z
≈/M-trans {x} {y} {z} p q = Eq (sym lemma) (Sum p q)
  where
  lemma : x - z ≈ (x - y) + (y - z)
  lemma = sym (begin
    (x - y) + (y - z)          ≈⟨ +-assoc x (- y) (y - z) ⟩
    x + ((- y) + (y - z))      ≈⟨ +-congˡ (sym (+-assoc (- y) y (- z))) ⟩
    x + (((- y) + y) + (- z))  ≈⟨ +-congˡ (+-congʳ (-‿inverseˡ y)) ⟩
    x + (0# + (- z))           ≈⟨ +-congˡ (+-identityˡ (- z)) ⟩
    x - z                      ∎)

-- Congruence
+-cong/M : {a b c d : R} → a ≈/M b → c ≈/M d → (a + c) ≈/M (b + d)
+-cong/M {a} {b} {c} {d} p q = Eq (sym lemma) (Sum p q)
  where
  lemma : (a + c) - (b + d) ≈ (a - b) + (c - d)
  lemma = sym (begin
    (a - b) + (c - d)                ≈⟨ +-assoc a (- b) (c - d) ⟩
    a + ((- b) + (c - d))            ≈⟨ +-congˡ (sym (+-assoc (- b) c (- d))) ⟩
    a + (((- b) + c) + (- d))        ≈⟨ +-congˡ (+-congʳ (+-comm (- b) c)) ⟩
    a + ((c + (- b)) + (- d))        ≈⟨ +-congˡ (+-assoc c (- b) (- d)) ⟩
    a + (c + ((- b) + (- d)))        ≈⟨ sym (+-assoc a c ((- b) + (- d))) ⟩
    (a + c) + ((- b) + (- d))        ≈⟨ +-congˡ (sym (neg-distrib-+ b d)) ⟩
    (a + c) + (- (b + d))            ∎)

-‿cong/M : {x y : R} → x ≈/M y → (- x) ≈/M (- y)
-‿cong/M {x} {y} p = Eq (sym lemma) (≈/M-sym p)
  where
  lemma : (- x) - (- y) ≈ y - x
  lemma = begin
    (- x) + (- (- y))  ≈⟨ +-congˡ (double-neg y) ⟩
    (- x) + y          ≈⟨ +-comm (- x) y ⟩
    y + (- x)          ∎

*-cong/M : {a b c d : R} → a ≈/M b → c ≈/M d → (a * c) ≈/M (b * d)
*-cong/M {a} {b} {c} {d} p q = ≈/M-trans step₁ step₂
  where
  -- a * c ≈/M a * d  (left factor fixed, use q : c - d ∈ ⟨M⟩)
  step₁ : (a * c) ≈/M (a * d)
  step₁ = Eq (sym lemma₁) (Magnet q)
    where
    lemma₁ : a * c - a * d ≈ a * (c - d)
    lemma₁ = sym (begin
      a * (c - d)        ≈⟨ distribˡ a c (- d) ⟩
      a * c + a * (- d)  ≈⟨ +-congˡ (neg-distribʳ-* a d) ⟩
      a * c + (- (a * d)) ∎)

  -- a * d ≈/M b * d  (right factor fixed, use p : a - b ∈ ⟨M⟩)
  step₂ : (a * d) ≈/M (b * d)
  step₂ = Eq (sym lemma₂) (Magnet {r = d} p)
    where
    lemma₂ : a * d - b * d ≈ d * (a - b)
    lemma₂ = sym (begin
      d * (a - b)        ≈⟨ distribˡ d a (- b) ⟩
      d * a + d * (- b)  ≈⟨ +-cong (*-comm d a) (trans (neg-distribʳ-* d b) (-‿cong (*-comm d b))) ⟩
      a * d + (- (b * d)) ∎)

-- The quotient ring
R/M : CommutativeRing 0ℓ 0ℓ
R/M = record
  { Carrier = R
  ; _≈_ = _≈/M_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = 0#
  ; 1# = 1#
  ; isCommutativeRing = record
    { isRing = record
      { +-isAbelianGroup = record
        { isGroup = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = record
                  { refl  = ≈/M-refl
                  ; sym   = ≈/M-sym
                  ; trans = ≈/M-trans
                  }
                ; ∙-cong = +-cong/M
                }
              ; assoc = λ x y z → embed (+-assoc x y z)
              }
            ; identity = (λ x → embed (+-identityˡ x)) , (λ x → embed (+-identityʳ x))
            }
          ; inverse = (λ x → embed (-‿inverseˡ x)) , (λ x → embed (-‿inverseʳ x))
          ; ⁻¹-cong = -‿cong/M
          }
        ; comm = λ x y → embed (+-comm x y)
        }
      ; *-cong = *-cong/M
      ; *-assoc = λ x y z → embed (*-assoc x y z)
      ; *-identity = (λ x → embed (*-identityˡ x)) , (λ x → embed (*-identityʳ x))
      ; distrib = (λ x y z → embed (distribˡ x y z)) , (λ x y z → embed (distribʳ x y z))
      }
    ; *-comm = λ x y → embed (*-comm x y)
    }
  }

-- If x ≈ y in the quotient ring, then x - y ∈ ⟨ M ⟩
reflects : {x y : R} → x ≈/M y → (x - y) ∈ ⟨ M ⟩
reflects p = p
