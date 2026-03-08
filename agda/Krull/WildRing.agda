{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch --safe #-}

{-
  A "wild ring" is a ring but without a specified equality (and hence without laws).

  It is used in Krull.WildLinearAlgebra to define certain computations such as
  matrix products which formally make sense even without equality.

  This enables Agda to recognize that certain computations, when carried out in
  a ring or one of its quotient rings, yield definitionally equal results.
-}

open import Level
open import Algebra.Bundles

module Krull.WildRing where

record WildRing : Set₁ where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infixl 6 _-_

  field
    Carrier : Set
    0#      : Carrier
    1#      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _*_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier

  _-_ : Carrier → Carrier → Carrier
  x - y = x + (- y)

forget : CommutativeRing 0ℓ 0ℓ → WildRing
forget R… = let open CommutativeRing R… in record
  { Carrier = Carrier
  ; 0#      = 0#
  ; 1#      = 1#
  ; _+_     = _+_
  ; _*_     = _*_
  ; -_      = -_
  }
