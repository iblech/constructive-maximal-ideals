{-# OPTIONS --cubical-compatible --safe #-}

open import Level
open import Algebra.Bundles
open import Relation.Binary
open import Data.Product

module Krull.FreeRing where

infixl 6 _+_
infixl 7 _*_

data Term (X : Set) : Set where
  0#  : Term X
  1#  : Term X
  _+_ : Term X → Term X → Term X
  _*_ : Term X → Term X → Term X
  -_  : Term X → Term X
  var : X → Term X

private
  module _ {X : Set} {Eq : Rel (Term X) 0ℓ} where
    infix 4 _≈_
    data _≈_ : Term X → Term X → Set where
      base  : {x y : Term X} → Eq x y → x ≈ y
      refl  : {x : Term X}     → x ≈ x
      sym   : {x y : Term X}   → x ≈ y → y ≈ x
      trans : {x y z : Term X} → x ≈ y → y ≈ z → x ≈ z
      +-cong  : {a b x y : Term X} → a ≈ b → x ≈ y → a + x ≈ b + y
      +-assoc : (x y z : Term X) → (x + y) + z ≈ x + (y + z)
      +-identityˡ : (x : Term X) → 0# + x ≈ x
      +-identityʳ : (x : Term X) → x + 0# ≈ x
      -‿inverseˡ : (x : Term X) → (- x) + x ≈ 0#
      -‿inverseʳ : (x : Term X) → x + (- x) ≈ 0#
      -‿-cong : {x y : Term X} → x ≈ y → - x ≈ - y
      +-comm : (x y : Term X) → x + y ≈ y + x
      *-cong : {a b x y : Term X} → a ≈ b → x ≈ y → a * x ≈ b * y
      *-assoc : (x y z : Term X) → (x * y) * z ≈ x * (y * z)
      *-identityˡ : (x : Term X) → 1# * x ≈ x
      *-identityʳ : (x : Term X) → x * 1# ≈ x
      distribˡ : (x y z : Term X) → x * (y + z) ≈ (x * y) + (x * z)
      distribʳ : (x y z : Term X) → (y + z) * x ≈ (y * x) + (z * x)
      *-comm : (x y : Term X) → x * y ≈ y * x

ℤ[_]/_ : (X : Set) → Rel (Term X) 0ℓ → CommutativeRing 0ℓ 0ℓ
ℤ[ X ]/ I = record
  { Carrier = Term X
  ; _≈_ = _≈_ {X} {I}
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
                  { refl  = refl
                  ; sym   = sym
                  ; trans = trans
                  }
                ; ∙-cong = +-cong
                }
              ; assoc = +-assoc
              }
            ; identity = +-identityˡ , +-identityʳ
            }
          ; inverse = -‿inverseˡ , -‿inverseʳ
          ; ⁻¹-cong = -‿-cong
          }
        ; comm = +-comm
        }
      ; *-cong = *-cong
      ; *-assoc = *-assoc
      ; *-identity = *-identityˡ , *-identityʳ
      ; distrib = distribˡ , distribʳ
      }
    ; *-comm = *-comm
    }
  }

module _ {X : Set} {I : Rel (Term X) 0ℓ} where
  module R… = CommutativeRing (ℤ[ X ]/ I)

  eq : {s t : Term X} → I s t → s R….≈ t
  eq = base
