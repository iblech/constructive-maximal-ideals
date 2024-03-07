{-# OPTIONS --cubical-compatible --safe #-}
module Forcing.Base where

open import Level
open import Data.Sum
open import Data.Product
open import Relation.Unary

record ForcingNotion : Set₁ where
  field
    L       : Set
    _≼_     : L → L → Set
    ≼-refl  : {x : L} → x ≼ x
    ≼-trans : {x y z : L} → x ≼ y → y ≼ z → x ≼ z
    Cov     : L → Set
    _◁_     : {x : L} → (a : L) → (R : Cov x) → Set
    ◁⇒≼     : {x y : L} {R : Cov x} → y ◁ R → y ≼ x
    stable  : {x y : L} → y ≼ x → (R : Cov x) → Σ[ S ∈ Cov y ] ({a : L} → a ◁ S → Σ[ b ∈ L ] (a ≼ b × b ◁ R))

record Filter (L… : ForcingNotion) : Set₁ where
  open ForcingNotion L…

  field
    F : Pred L 0ℓ
    upward-closed      : {x y : L} → y ≼ x → F y → F x
    downward-directed₁ : Σ[ x ∈ L ] F x
    downward-directed₂ : {a b : L} → F a → F b → Σ[ x ∈ L ] x ≼ a × x ≼ b × F x
    split              : {x : L} {R : Cov x} → F x → Σ[ y ∈ L ] F y × y ◁ R
