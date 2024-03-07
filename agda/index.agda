{-# OPTIONS --cubical-compatible #-}

module index where

open import Level
open import Algebra.Bundles
open import Relation.Unary hiding (∅)
open import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List

{- Overview of all modules -}
import Forcing.Base
import Forcing.Monad
import Forcing.Monad.Conservative
import Forcing.Levy
import Forcing.Semantics
import Krull.Base
import Krull.Static
import Krull.Dynamic

{- §1. An iterative construction of maximal ideals -}
module §1 where
  postulate
    R… : CommutativeRing 0ℓ 0ℓ
  
  open CommutativeRing R… renaming (Carrier to R)

  postulate
    Enum : Nat.ℕ → Pred R 0ℓ
    Enum-singlevalued : {n : Nat.ℕ} {x y : R} → Enum n x → Enum n y → x ≡ y
    Enum-surjective : (x : R) → Σ[ n ∈ Nat.ℕ ] Enum n x

  open Krull.Base R…
  open Krull.Static R… Enum Enum-singlevalued

  Construction-1 : Pred R 0ℓ
  Construction-1 = 𝔪

  module Lemma-1-1 where
    a : ⟨ 𝔪 ⟩ ⊆ 𝔪
    a = 𝔪-is-ideal Enum-surjective

    b : ¬ 1# ∈ 𝔪
    b = 𝔪-proper

    c : {n : Nat.ℕ} →
      let [1] = Enum n ⊆ G (Nat.suc n)
          [2] = Enum n ⊆ 𝔪
          [3] = ¬ 1# ∈ ⟨ 𝔪 ∪ Enum n ⟩
          [4] = ¬ 1# ∈ ⟨ G n ∪ Enum n ⟩
      in ([1] → [2]) × ([2] → [3]) × ([3] → [4]) × ([4] → [1])
    c = 1⇒2 , 2⇒3 , 3⇒4 , 4⇒1

  Corollary-1-2 : (x : R) → ¬ 1# ∈ ⟨ 𝔪 ∪ ｛ x ｝ ⟩ → x ∈ 𝔪
  Corollary-1-2 = 𝔪-is-maximal Enum-surjective


{- §4. Expanding the scope to general rings -}
module §4 where
  open Forcing.Base

  module §4-1 where
    Definition-4-1 : Set₁
    Definition-4-1 = ForcingNotion

    Definition-4-2 : ForcingNotion → Set₁
    Definition-4-2 = Filter

    Example-4-3 : Set → ForcingNotion
    Example-4-3 = Forcing.Levy.L…

  module §4-2 (L… : ForcingNotion) where
    open ForcingNotion L…
    open Forcing.Monad L…

    Definition-Ev : (L → Set) → (L → Set)
    Definition-Ev = Ev

    Lemma-4-10 : {P : L → Set} → Monotonic P → Monotonic (Ev P)
    Lemma-4-10 = weaken-ev

    Proposition-4-11
      : {P : L → Set} {F… : Filter L…} {x : L} (open Filter F…)
      → Ev P x → F x → Σ[ y ∈ L ] y ≼ x × F y × P y
    Proposition-4-11 {P} {F…} {x} = Ev⇒Filter {P} {F…} {x}

    Proposition-4-12
      : (all-coverings-inhabited : {x : L} (R : Cov x) → Satisfiable (_◁ R))
      → {{x : L}} {P : Set} → ∇ P → P
    Proposition-4-12 all-coverings-inhabited = escape
      where open Forcing.Monad.Conservative L… all-coverings-inhabited

  Example-4-13 = Forcing.Levy.escape

  module §4-3 (L… : ForcingNotion) where
    open Forcing.Semantics L…

    Definition-Language  = Formula
    Definition-Semantics = exec∇

    Lemma-4-17 = weaken

    module Theorem-4-22 = 1ˢᵗ-Order-Equivalence

  module §4-4 = Krull.Dynamic
