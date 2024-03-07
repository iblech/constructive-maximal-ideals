{-# OPTIONS --cubical-compatible --safe #-}
open import Forcing.Base
open import Relation.Unary
open import Data.Product

module Forcing.Monad.Conservative
  (L… : ForcingNotion)
  (open ForcingNotion L…)
  (all-coverings-inhabited : {x : L} (R : Cov x) → Satisfiable (_◁ R)) where

open import Forcing.Monad L…

escape : {x : L} {P : Set} → ∇ {{x}} P → P
escape (now p)     = p
escape (later R f) = escape (f (proj₂ (all-coverings-inhabited R)))
