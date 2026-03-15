{-

  This module provides a forcing notion for obtaining the "generic maximal ideal"
  of a given ring.

  Note that this does not coincide with the iterative maximal ideal
  construction applied to the generic enumeration (for this, see
  Krull.Dynamical).

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

module Forcing.Maximal (A… : CommutativeRing 0ℓ 0ℓ) where

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
    maximal : {xs : List A} (a : A) → Cov xs

  _◁_ : {xs : List A} → List A → Cov xs → Set
  _◁_ {xs} ys (proper _)  = ⊥
  _◁_ {xs} ys (maximal x) = (ys ≡ x ∷ xs) ⊎ ∃[ u ] ∃[ v ] (1# ≈ u + v * x × ys ≡ u ∷ xs)

  ◁⇒≼ : {xs ys : List A} {R : Cov xs} → ys ◁ R → ys ≼ xs
  ◁⇒≼ {xs} {ys} {proper p}  ()
  ◁⇒≼ {xs} {ys} {maximal x} (inj₁ refl)               = ⟨⟩-monotone λ x⋿xs → there x⋿xs
  ◁⇒≼ {xs} {ys} {maximal x} (inj₂ (_ , _ , _ , refl)) = ⟨⟩-monotone λ x⋿xs → there x⋿xs

  monotone : {xs ys : List A} {x : A} → ys ≼ xs → x ∈ ⟨ xs ⟩ → x ∈ ⟨ ys ⟩
  monotone ys≼xs = ≼-bind' λ a⋿xs → ys≼xs (Base a⋿xs)

  cons-monotone : {xs ys : List A} (a : A) → ys ≼ xs → (a ∷ ys) ≼ (a ∷ xs)
  cons-monotone a ys≼xs = ≼-bind' λ
    { (here  p) → Base (here p)
    ; (there p) → ⟨⟩-monotone there (ys≼xs (Base p))
    }

  stable : {xs ys : List A} → ys ≼ xs → (R : Cov xs) → Σ[ S ∈ Cov ys ] ({a : List A} → a ◁ S → Σ[ b ∈ List A ] (a ≼ b × b ◁ R))
  stable ys≼xs (proper p)  = proper (monotone ys≼xs p) , λ ()
  stable ys≼xs (maximal x) = maximal x , λ
    { (inj₁ refl)                → x ∷ _ , cons-monotone x ys≼xs , inj₁ _≡_.refl
    ; (inj₂ (u , v , eq , refl)) → u ∷ _ , cons-monotone u ys≼xs , inj₂ (u , v , eq , _≡_.refl)
    }

L… : ForcingNotion
L… = record { L = List A ; _≼_ = _≼_ ; ≼-refl = λ p → p ; ≼-trans = λ f g p → f (g p) ; Cov = Cov; _◁_ = _◁_; ◁⇒≼ = ◁⇒≼ ; stable = stable }

-- The generic prime ideal of A
𝔫 : {{xs : List A}} → Pred A 0ℓ
𝔫 {{xs}} x = x ∈ ⟨ xs ⟩

𝔫-monotone : {xs ys : List A} → ys ≼ xs → 𝔫 {{xs}} ⊆ 𝔫 {{ys}}
𝔫-monotone p = p

open Forcing.Monad L…

𝔫-proper : {{xs : List A}} → 1# ∈ 𝔫 → ∇ ⊥
𝔫-proper p = later (proper p) now

𝔫-product : {xs : List A} (x : A) → ∇ {{xs}} (x ∈ 𝔫 ⊎ ∃[ u ] ∃[ v ] (1# ≈ u + v * x × u ∈ 𝔫))
𝔫-product x = later (maximal x) λ
  { (inj₁ refl)                → now (inj₁ (Base (here _≡_.refl)))
  ; (inj₂ (u , v , eq , refl)) → now (inj₂ (u , v , eq , Base (here _≡_.refl)))
  }

{-
private
  lemma : {xs : List A} {a x : A} → x ∈ Jac ⟨ a ∷ xs ⟩ → ((v : A) → x ∈ Jac ⟨ (1# - v * a) ∷ xs ⟩) → x ∈ Jac ⟨ xs ⟩
  lemma = {!!}

theorem : {xs : List A} {x : A} → ∇ {{xs}} (x ∈ 𝔫) → x ∈ Jac ⟨ xs ⟩
theorem {xs} {x} (now p) = Jac-inflationary _ p
theorem {xs} {x} (later (proper p) _)  = Jac-inflationary _ (Eq (*-identityʳ _) (Magnet p))
theorem {xs} {x} (later (maximal a) f) = lemma (theorem (f (inj₁ _≡_.refl))) λ v → theorem (f (inj₂ (1# - v * a , v , {!!} , _≡_.refl)))

-- If an element is contained in the generic maximal ideal, then it is contained in the the Jacobson radical of the ring.
-- A constructivization of the classical claim that an element is contained in the Jacobson radical
-- if it is contained in all maximal ideals.
Jac' : Pred A 0ℓ
Jac' x = (u : A) → ∃[ v ] ((1# - u * x) * v ≈ 1#)

corollary : {x : A} → ∇ {{[]}} (x ∈ 𝔫) → x ∈ Jac'
corollary p u with theorem p u
... | v , w = v , {!!}
-}
