{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch #-}

open import Level
open import Algebra.Bundles
open import Relation.Unary hiding (∅)
open import Data.Sum
import Data.Nat as Nat
import Data.Nat.Properties
open import Data.Product
open import Function.Base
import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.Reasoning.Setoid
open import Data.List hiding (product)
open import Data.List.Properties hiding (sum-++)
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties
import Data.List.Relation.Binary.Pointwise as PW

module MinimalPrimes.Base (R… : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R… renaming (Carrier to R)
open Relation.Binary.Reasoning.Setoid setoid

⊥ : Set
⊥ = 1# ≈ 0#

infix 3 ¬_
¬_ : Set → Set
¬_ P = P → ⊥

∅ : Pred R 0ℓ
∅ = λ _ → ⊥

contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f k x = k (f x)

data comprehension-syntax {X : Set} (F : Pred X 0ℓ) (P : X → Set) : Pred X 0ℓ where
  In : {x : X} → F x → P x → comprehension-syntax F P x

syntax comprehension-syntax A (λ x → B) = ｛ x ∶ A ∣ B ｝

product : List R → R
product []       = 1#
product (x ∷ xs) = x * product xs

product-++ : (xs ys : List R) → product xs * product ys ≈ product (xs ++ ys)
product-++ []       ys = *-identityˡ (product ys)
product-++ (x ∷ xs) ys = trans (*-assoc x (product xs) (product ys)) (*-congˡ (product-++ xs ys))

⟨_⟩ : Pred R 0ℓ → Pred R 0ℓ
⟨ M ⟩ a = Σ[ xs ∈ List R ] a ≈ product xs × All M xs

⟨⟩-monotone : {M N : Pred R 0ℓ} → M ⊆ N → ⟨ M ⟩ ⊆ ⟨ N ⟩
⟨⟩-monotone i (xs , eq , ms) = xs , (eq , Data.List.Relation.Unary.All.map i ms)

⟨⟩-closed : {M : Pred R 0ℓ} {a b : R} → a ∈ ⟨ M ⟩ → b ∈ ⟨ M ⟩ → (a * b) ∈ ⟨ M ⟩
⟨⟩-closed (xs , eq , ms) (xs' , eq' , ms') = xs ++ xs' , trans (*-cong eq eq') (product-++ xs xs') , ++⁺ ms ms' 

⟨⟩-cong : {M : Pred R 0ℓ} {a b : R} → a ≈ b → a ∈ ⟨ M ⟩ → b ∈ ⟨ M ⟩
⟨⟩-cong e (xs , eq , ms) = xs , trans (sym e) eq , ms

⟨⟩-union₀ : {M N : Pred R 0ℓ} {a : R} → a ∈ ⟨ M ∪ N ⟩ → a ∈ ⟨ M ⟩ ⊎ Satisfiable N
⟨⟩-union₀ {M} {N} (xs , eq , ms) = Data.Sum.map₁ (⟨⟩-cong (sym eq)) (go xs ms)
  where
  go : (xs : List R) → All (M ∪ N) xs → product xs ∈ ⟨ M ⟩ ⊎ Satisfiable N
  go []       []            = inj₁ ([] , refl , [])
  go (x ∷ xs) (inj₂ p ∷ ms) = inj₂ (x , p)
  go (x ∷ xs) (inj₁ m ∷ ms) with go xs ms
  ... | inj₁ (ys , eq , ns) = inj₁ (x ∷ ys , *-congˡ eq , m ∷ ns)
  ... | inj₂ p = inj₂ p

⟨∅⟩-trivial : 0# ∈ ⟨ ∅ ⟩ → ⊥
⟨∅⟩-trivial ([]     , eq , [])     = sym eq
⟨∅⟩-trivial (x ∷ xs , eq , m ∷ ms) = m

module _ (G : Nat.ℕ → Pred R 0ℓ) (increasing : {n m : Nat.ℕ} → n Nat.≤ m → G n ⊆ G m) where
  ⟨⟩-compact : {a : R} → (a ∈ ⟨ ⋃[ n ∶ Nat.ℕ ] G n ⟩) → Σ[ n ∈ Nat.ℕ ] a ∈ ⟨ G n ⟩
  ⟨⟩-compact (xs , eq , ms) = let (n , ms') = go xs ms in n , xs , eq , ms'
    where
    liftAll : {k m : Nat.ℕ} → k Nat.≤ m → {ys : List R} → All (G k) ys → All (G m) ys
    liftAll p []       = []
    liftAll p (q ∷ qs) = increasing p q ∷ liftAll p qs
    go : (ys : List R) → All (⋃[ n ∶ Nat.ℕ ] G n) ys → Σ[ n ∈ Nat.ℕ ] All (G n) ys
    go []            []            = Nat.zero , []
    go (y ∷ ys) ((k , p) ∷ ms) with go ys ms
    ... | m , ms' = k Nat.⊔ m , increasing (Data.Nat.Properties.m≤m⊔n k m) p ∷ liftAll (Data.Nat.Properties.m≤n⊔m k m) ms'

⟨⟩-idempotent : {M : Pred R 0ℓ} → ⟨ ⟨ M ⟩ ⟩ ⊆ ⟨ M ⟩
⟨⟩-idempotent {M} (xs , eq , ms) = let (ys , eq' , ms') = flatten xs ms in ys , trans eq eq' , ms'
  where
  flatten : (xs : List R) → All (⟨ M ⟩) xs → Σ[ ys ∈ List R ] product xs ≈ product ys × All M ys
  flatten []       []                                   = [] , refl , []
  flatten (x ∷ xs) ((ys , eq-x , ms-x) ∷ ms-rest) with flatten xs ms-rest
  ... | zs , eq-xs , ms-zs = ys ++ zs , trans (*-cong eq-x eq-xs) (product-++ ys zs) , ++⁺ ms-x ms-zs
