{-

  This module provides a forcing notion for obtaining the "generic prime ideal"
  of a given ring.

-}

{-# OPTIONS --cubical-compatible --safe -WnoUnsupportedIndexedMatch #-}

open import Level
open import Algebra.Bundles
open import Data.Product hiding (zip)
open import Data.Sum
open import Data.List hiding (product)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋿_)
open import Relation.Binary.PropositionalEquality
import Data.Nat as Nat
open import Data.Empty
open import Relation.Unary
open import Relation.Unary.Properties
open import Data.List.Relation.Binary.Prefix.Heterogeneous hiding (_++_)
import Data.List.Relation.Binary.Prefix.Homogeneous.Properties as P
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.All
open import Forcing.Base
import Forcing.Monad

module Forcing.Prime (A… : CommutativeRing 0ℓ 0ℓ) where

open import Krull.Base (A…) renaming (⟨_⟩ to ⟨_⟩') hiding (⊥)
open CommutativeRing A… renaming (Carrier to A)
open import Algebra.Definitions.RawSemiring (Algebra.Bundles.Semiring.rawSemiring semiring) using (_^_)

private
  ⟨_⟩ : List A → Pred A 0ℓ
  ⟨ xs ⟩ = ⟨ (_⋿ xs) ⟩'

  _≼_ : List A → List A → Set
  ys ≼ xs = ⟨ xs ⟩ ⊆ ⟨ ys ⟩

  ≼-bind : {xs ys : List A} → All (λ x → x ∈ ⟨ ys ⟩) xs → ys ≼ xs
  ≼-bind f p = ⟨⟩-idempotent (⟨⟩-monotone (λ x⋿xs → Data.List.Relation.Unary.All.lookup f x⋿xs) p)

  ≼-bind' : {xs ys : List A} → ({x : A} → x ⋿ xs → x ∈ ⟨ ys ⟩) → ys ≼ xs
  ≼-bind' f p = ⟨⟩-idempotent (⟨⟩-monotone f p)

  data Cov : List A → Set where
    proper  : {xs : List A} → 1# ∈ ⟨ xs ⟩ → Cov xs
    product : {xs : List A} (a b : A) → (a * b) ∈ ⟨ xs ⟩ → Cov xs

  _◁_ : {xs : List A} → List A → Cov xs → Set
  _◁_ {xs} ys (proper _)      = ⊥
  _◁_ {xs} ys (product a b _) = (ys ≡ a ∷ xs) ⊎ (ys ≡ b ∷ xs)

  ◁⇒≼ : {xs ys : List A} {R : Cov xs} → ys ◁ R → ys ≼ xs
  ◁⇒≼ {xs} {ys} {proper p}      ()
  ◁⇒≼ {xs} {ys} {product a b p} (inj₁ refl) = ⟨⟩-monotone λ {x} x⋿xs → there x⋿xs
  ◁⇒≼ {xs} {ys} {product a b p} (inj₂ refl) = ⟨⟩-monotone λ {x} x⋿xs → there x⋿xs

  monotone : {xs ys : List A} {x : A} → ys ≼ xs → x ∈ ⟨ xs ⟩ → x ∈ ⟨ ys ⟩
  monotone ys≼xs = ≼-bind' λ a⋿xs → ys≼xs (Base a⋿xs)

  cons-monotone : {xs ys : List A} (a : A) → ys ≼ xs → (a ∷ ys) ≼ (a ∷ xs)
  cons-monotone a ys≼xs = ≼-bind' λ
    { (here  p) → Base (here p)
    ; (there p) → ⟨⟩-monotone there (ys≼xs (Base p))
    }

  stable : {xs ys : List A} → ys ≼ xs → (R : Cov xs) → Σ[ S ∈ Cov ys ] ({a : List A} → a ◁ S → Σ[ b ∈ List A ] (a ≼ b × b ◁ R))
  stable ys≼xs (proper p)      = proper (monotone ys≼xs p) , λ ()
  stable ys≼xs (product a b p) = product a b (monotone ys≼xs p) , λ
    { (inj₁ refl) → a ∷ _ , cons-monotone a ys≼xs , inj₁ _≡_.refl
    ; (inj₂ refl) → b ∷ _ , cons-monotone b ys≼xs , inj₂ _≡_.refl
    }

L… : ForcingNotion
L… = record { L = List A ; _≼_ = _≼_ ; ≼-refl = λ p → p ; ≼-trans = λ f g p → f (g p) ; Cov = Cov; _◁_ = _◁_; ◁⇒≼ = ◁⇒≼ ; stable = stable }

-- The generic prime ideal of A
𝔭 : {{xs : List A}} → Pred A 0ℓ
𝔭 {{xs}} x = x ∈ ⟨ xs ⟩

𝔭-monotone : {xs ys : List A} → ys ≼ xs → 𝔭 {{xs}} ⊆ 𝔭 {{ys}}
𝔭-monotone p = p

open Forcing.Monad L…

𝔭-proper : {{xs : List A}} → 1# ∈ 𝔭 → ∇ ⊥
𝔭-proper p = later (proper p) now

𝔭-product : {xs : List A} {a b : A} → (a * b) ∈ 𝔭 {{xs}} → ∇ {{xs}} (a ∈ 𝔭 ⊎ b ∈ 𝔭)
𝔭-product {a = a} {b = b} p = later (product a b p) λ
  { (inj₁ refl) → now (inj₁ (Base (here _≡_.refl)))
  ; (inj₂ refl) → now (inj₂ (Base (here _≡_.refl)))
  }

private
  lemma : {xs : List A} {a b : A} {x y : A} → x ∈ ⟨ a ∷ xs ⟩ → y ∈ ⟨ b ∷ xs ⟩ → x * y ∈ ⟨ a * b ∷ xs ⟩
  lemma {xs} {a} {b} {x} {y} p q = ⟨⟩-idempotent (⟨⟩-monotone (λ { (z , refl , r) → go r }) (⟨⟩-mult x q))
    where
    go' : {z : A} → z ⋿ (a ∷ xs) → b * z ∈ ⟨ a * b ∷ xs ⟩
    go' (here refl) = Eq (*-comm a b) (Base (here _≡_.refl))
    go' (there r)   = Magnet (Base (there r))
    go : {z : A} → z ⋿ (b ∷ xs) → x * z ∈ ⟨ a * b ∷ xs ⟩
    go (here  refl) = Eq (*-comm b x) (⟨⟩-idempotent (⟨⟩-monotone (λ { (z , refl , r) → go' r }) (⟨⟩-mult b p)))
    go (there r)    = Magnet (Base (there r))

  lemma' : {xs : List A} {a b : A} {x : A} → a * b ∈ ⟨ xs ⟩ → x ∈ √ ⟨ a ∷ xs ⟩ → x ∈ √ ⟨ b ∷ xs ⟩ → x ∈ √ ⟨ xs ⟩
  lemma' {x = x} p (n , u) (m , v)
    = n Nat.+ m
    , Eq (^-* x n m) (≼-bind' (λ { (here refl) → p ; (there r) → Base r }) (lemma u v))

theorem : {xs : List A} {x : A} → ∇ {{xs}} (x ∈ 𝔭) → x ∈ √ ⟨ xs ⟩
theorem (now p)                   = 1 , Eq (*-comm 1# _) (Magnet p)
theorem (later (proper  p)     f) = 1 , Magnet p
theorem (later (product a b p) f) = lemma' p (theorem (f (inj₁ _≡_.refl))) (theorem (f (inj₂ _≡_.refl)))

-- If an element is contained in the generic prime ideal, then it is nilpotent.
-- A constructivization of the classical claim that an element is nilpotent
-- if it is contained in all prime ideals.
corollary : {x : A} → ∇ {{[]}} (x ∈ 𝔭) → Σ[ n ∈ Nat.ℕ ] x ^ n ≈ 0#
corollary p with theorem p
... | n , q = n , ⟨∅⟩-trivial (⟨⟩-monotone (λ ()) q) 
