{-

  This module provides the Lévy forcing notion for collapsing any given set X to
  be countable.

  More precisely, the forcing notion presented here gives rise to a generic
  *partial* surjection ℕ ⇀ X. True Lévy forcing wouldn't be much more difficult
  to implement, but we don't need it for the application in Krull.Dynamical
  and hence it seems prudent to use the more economical forcing notion.

-}

{-# OPTIONS --cubical-compatible --safe #-}

module Forcing.Levy (X : Set) where

import Data.Nat as Nat
open import Data.List.Membership.Propositional renaming (_∈_ to _⋿_)
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Product
open import Data.List.Relation.Unary.Any
open import Data.Fin
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.List.Relation.Binary.Prefix.Heterogeneous hiding (_++_)
import Data.List.Relation.Binary.Prefix.Homogeneous.Properties as P
open import Relation.Binary.Structures using (IsPreorder)
open import Level
open import Data.List.Relation.Unary.Any.Properties

open import Forcing.Base
import Forcing.Monad
import Forcing.Monad.Conservative

private
  lookupMaybe : List X → Nat.ℕ → Maybe X
  lookupMaybe []       _           = nothing
  lookupMaybe (x ∷ xs) Nat.zero    = just x
  lookupMaybe (x ∷ xs) (Nat.suc n) = lookupMaybe xs n

  _[_]≡_ : List X → Nat.ℕ → X → Set
  xs [ n ]≡ x = lookupMaybe xs n ≡ just x

  lookup-singlevalued : (xs : List X) (n : Nat.ℕ) (a b : X) → xs [ n ]≡ a → xs [ n ]≡ b → a ≡ b
  lookup-singlevalued xs n a b p q = just-injective (trans (sym p) q)

  lookup-succeeds : (xs : List X) (a : X) (p : a ⋿ xs) → xs [ toℕ (index p) ]≡ a
  lookup-succeeds .(_ ∷ _) a (here px) = cong just (sym px)
  lookup-succeeds .(_ ∷ _) a (there p) = lookup-succeeds _ a p

  lookup-monotone : (n : Nat.ℕ) (a : X) (xs ys : List X) → xs [ n ]≡ a → (xs ++ ys) [ n ]≡ a
  lookup-monotone Nat.zero    a (x ∷ xs) ys p = p
  lookup-monotone (Nat.suc n) a (x ∷ xs) ys p = lookup-monotone n a xs ys p

  ⋿-last : (xs : List X) (a : X) → a ⋿ (xs ∷ʳ a)
  ⋿-last []       a = here refl
  ⋿-last (x ∷ xs) a = there (⋿-last xs a)

  _≼_ : List X → List X → Set
  ys ≼ xs = Prefix _≡_ xs ys

  ≼-splitting : {xs ys : List X} → ys ≼ xs → Σ[ zs ∈ List X ] ys ≡ xs ++ zs
  ≼-splitting [] = _ , refl
  ≼-splitting (refl ∷ ys≼xs) with ≼-splitting ys≼xs
  ... | zs , p = zs , cong (_ ∷_) p

  module _ where
    module Q = IsPreorder (P.isPreorder (isPreorder {0ℓ} {X}))

    ≼-refl : {xs : List X} → xs ≼ xs
    ≼-refl = Q.refl

    ≼-trans : {xs ys zs : List X} → xs ≼ ys → ys ≼ zs → xs ≼ zs
    ≼-trans p q = Q.trans q p

  data Cov : List X → Set where
    hit : {xs : List X} → (x : X) → Cov xs

  _◁_ : {xs : List X} → List X → Cov xs → Set
  _◁_ {xs} as (hit x) = as ≼ xs × x ⋿ as

  ◁⇒≼ : {xs ys : List X} {R : Cov xs} → ys ◁ R → ys ≼ xs
  ◁⇒≼ {xs} {ys} {hit x} = proj₁

  stable : {xs ys : List X} → ys ≼ xs → (R : Cov xs) → Σ[ S ∈ Cov ys ] ({a : List X} → a ◁ S → Σ[ b ∈ List X ] (a ≼ b × b ◁ R))
  stable ys≼xs (hit x) = hit x , λ {as} (as≼ys , x∈as) → as , ≼-refl , ≼-trans as≼ys ys≼xs , x∈as

L… : ForcingNotion
L… = record { L = List X ; _≼_ = _≼_ ; ≼-refl = ≼-refl ; ≼-trans = ≼-trans ; Cov = Cov; _◁_ = _◁_; ◁⇒≼ = ◁⇒≼ ; stable = stable }

-- The generic partial surjection ℕ ⇀ X
Enum : {{xs : List X}} → Nat.ℕ → X → Set
Enum {{xs}} n x = xs [ n ]≡ x

Enum-monotonic : {xs ys : List X} (n : Nat.ℕ) (x : X) → ys ≼ xs → Enum {{xs}} n x → Enum {{ys}} n x
Enum-monotonic {xs} {ys} n x ys≼xs p with ≼-splitting ys≼xs
... | zs , q = subst (λ ws → lookupMaybe ws n ≡ just x) (sym q) (lookup-monotone n x xs zs p)

Enum-singlevalued : {{xs : List X}} (n : Nat.ℕ) (a b : X) → Enum n a → Enum n b → a ≡ b
Enum-singlevalued {{xs}} n a b p q = lookup-singlevalued xs n a b p q

open Forcing.Monad L…

Enum-surjective : {{xs : List X}} (a : X) → ∇ {{xs}} (λ {{xs}} → Σ[ n ∈ Nat.ℕ ] Enum {{xs}} n a)
Enum-surjective a = later (hit a) λ (ys≼xs , a∈ys) → now (toℕ (index a∈ys) , lookup-succeeds _ a a∈ys)

open Forcing.Monad.Conservative L… (λ { {xs} (hit a) → xs ∷ʳ a , _++ᵖ_ ≼-refl (a ∷ []) , ⋿-last xs a }) public
