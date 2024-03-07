{-# OPTIONS --cubical-compatible --safe #-}
open import Forcing.Base

module Forcing.Monad (L… : ForcingNotion) where

open import Data.Product
open import Relation.Unary

open ForcingNotion L…

data Ev (P : L → Set) : L → Set where
  now   : {x : L} → P x → Ev P x
  later : {x : L} (R : Cov x) → ({y : L} → y ◁ R → Ev P y) → Ev P x

Monotonic : (L → Set) → Set
Monotonic P = {x y : L} → y ≼ x → P x → P y

module _ {P : L → Set} (k : Monotonic P) where
  weaken-ev : Monotonic (Ev P)
  weaken-ev y≼x (now p)     = now (k y≼x p)
  weaken-ev y≼x (later R f) = later S λ y◁S →
    weaken-ev (proj₁ (proj₂ (g y◁S))) (f (proj₂ (proj₂ (g y◁S))))
    where
    S = proj₁ (stable y≼x R)
    g = proj₂ (stable y≼x R)

module _ {P : L → Set} {F… : Filter L…} where
  open Filter F…

  Ev⇒Filter : {x : L} → Ev P x → F x → Σ[ y ∈ L ] y ≼ x × F y × P y
  Ev⇒Filter (now p)     u = _ , ≼-refl , u , p
  Ev⇒Filter (later R f) u with Ev⇒Filter (f (proj₂ (proj₂ (split u)))) (proj₁ (proj₂ (split u)))
  ... | z , z≼y , Fz , Pz = z , ≼-trans z≼y (◁⇒≼ (proj₂ (proj₂ (split u)))) , Fz , Pz

∇ : {{x : L}} → (P : {{y : L}} → Set) → Set
∇ {{x}} P = Ev (λ y → P {{y}}) x

_⟫=_ : {{x : L}} {P Q : L → Set} → Ev P x → ({{y : L}} {{_ : y ≼ x}} → P y → Ev Q y) → Ev Q x
now   p   ⟫= g = g {{_}} {{≼-refl}} p
later R f ⟫= g = later R (λ {y} u → _⟫=_ {{y}} (f u) λ {{z}} {{z≼y}} → g {{z}} {{≼-trans z≼y (◁⇒≼ u)}})

fmap : {{x : L}} {P Q : {{y : L}} → Set} → ({{y : L}} → P {{y}} → Q {{y}}) → ∇ {{x}} (λ {{y}} → P {{y}}) → ∇ {{x}} (λ {{y}} → Q {{y}})
fmap f p = p ⟫= λ {{y}} u → now (f {{y}} u)

