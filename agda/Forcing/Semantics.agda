{-# OPTIONS --cubical-compatible --safe -WnoUnsupportedIndexedMatch #-}
open import Forcing.Base

module Forcing.Semantics (L… : ForcingNotion) where

open import Data.List
open import Data.List.Membership.Propositional renaming (_∈_ to _⋿_)
open import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
import Relation.Unary

open import Forcing.Monad (L…)
open ForcingNotion L…

Ty : Set₁
Ty = Set

Cxt : Set₁
Cxt = List Set

Env : Cxt → Set₁
Env Γ = All (λ ty → ty) Γ

data Term (Γ : Cxt) (ty : Ty) : Set₁ where
  var : ty ⋿ Γ → Term Γ ty
  lit : ty → Term Γ ty
  app : {ty' : Ty} → Term Γ (ty' → ty) → Term Γ ty' → Term Γ ty

data Fragment : Set where
  coherent first-order : Fragment

data Language : Set₁ where
  base : Language
  with-generic-filter : Language

infixr 1 _∨_
infixr 2 _∧_

data Formula (Γ : Cxt) : Fragment → Language → Set₁ where
  Rel₂ : {frag : Fragment} {lang : Language} {ty ty' : Ty} → (ty → ty' → Set) → Term Γ ty → Term Γ ty' → Formula Γ frag lang
  top  : {frag : Fragment} {lang : Language} → Formula Γ frag lang
  bot  : {frag : Fragment} {lang : Language} → Formula Γ frag lang
  _∨_  : {frag : Fragment} {lang : Language} → Formula Γ frag lang → Formula Γ frag lang → Formula Γ frag lang
  _∧_  : {frag : Fragment} {lang : Language} → Formula Γ frag lang → Formula Γ frag lang → Formula Γ frag lang
  _⇒_  : {frag : Fragment} {lang : Language} → Formula Γ frag lang → Formula Γ frag lang → Formula Γ first-order lang
  EX   : {frag : Fragment} {lang : Language} {ty : Ty} → Formula (ty ∷ Γ) frag lang → Formula Γ frag lang
  FA   : {frag : Fragment} {lang : Language} {ty : Ty} → Formula (ty ∷ Γ) frag lang → Formula Γ first-order lang
  G    : {frag : Fragment} → Term Γ L → Formula Γ frag with-generic-filter

1ˢᵗ : {Γ : Cxt} {frag : Fragment} {lang : Language} → Formula Γ frag lang → Formula Γ first-order lang
1ˢᵗ (Rel₂ R s t) = Rel₂ R s t
1ˢᵗ top          = top
1ˢᵗ bot          = top
1ˢᵗ (φ ∨ ψ)      = 1ˢᵗ φ ∨ 1ˢᵗ ψ
1ˢᵗ (φ ∧ ψ)      = 1ˢᵗ φ ∧ 1ˢᵗ ψ
1ˢᵗ (φ ⇒ ψ)      = 1ˢᵗ φ ⇒ 1ˢᵗ ψ
1ˢᵗ (EX φ)       = EX (1ˢᵗ φ)
1ˢᵗ (FA φ)       = FA (1ˢᵗ φ)
1ˢᵗ (G t)        = G t

eval : {Γ : Cxt} {ty : Ty} → Env Γ → Term Γ ty → ty
eval env (var v) = Data.List.Relation.Unary.All.lookup env v
eval env (lit u) = u
eval env (app f u) = eval env f (eval env u)

exec : {frag : Fragment} {Γ : Cxt} → Env Γ → Formula Γ frag base → Set
exec env (Rel₂ R s t) = R (eval env s) (eval env t)
exec env top     = ⊤
exec env bot     = ⊥
exec env (φ ∨ ψ) = exec env φ ⊎ exec env ψ
exec env (φ ∧ ψ) = exec env φ × exec env ψ
exec env (φ ⇒ ψ) = exec env φ → exec env ψ
exec env (EX φ)  = Σ[ x ∈ _ ] exec (x ∷ env) φ
exec env (FA φ)  = (x : _) → exec (x ∷ env) φ

-- Presheaf semantics
execP : {{x : L}} {frag : Fragment} {lang : Language} {Γ : Cxt} → Env Γ → Formula Γ frag lang → Set
execP {{x}} env (Rel₂ R s t) = R (eval env s) (eval env t)
execP {{x}} env top     = ⊤
execP {{x}} env bot     = ⊥
execP {{x}} env (φ ∨ ψ) = execP {{x}} env φ ⊎ execP {{x}} env ψ
execP {{x}} env (φ ∧ ψ) = execP env φ × execP env ψ
execP {{x}} env (φ ⇒ ψ) = {{y : L}} {{y≼x : y ≼ x}} → execP {{y}} env φ → execP {{y}} env ψ
execP {{x}} env (EX φ)  = Σ[ u ∈ _ ] execP {{x}} (u ∷ env) φ
execP {{x}} env (FA φ)  = {{y : L}} {{y≼x : y ≼ x}} (u : _) → execP {{y}} (u ∷ env) φ
execP {{x}} env (G t)   = x ≼ eval env t

-- Sheaf semantics
exec∇ : {{x : L}} {frag : Fragment} {lang : Language} {Γ : Cxt} → Env Γ → Formula Γ frag lang → Set
exec∇ {{x}} env (Rel₂ R s t) = ∇ (R (eval env s) (eval env t))
exec∇ {{x}} env top     = ⊤
exec∇ {{x}} env bot     = ∇ ⊥
exec∇ {{x}} env (φ ∨ ψ) = ∇ (λ {{x}} → exec∇ {{x}} env φ ⊎ exec∇ {{x}} env ψ)
exec∇ {{x}} env (φ ∧ ψ) = exec∇ env φ × exec∇ env ψ
exec∇ {{x}} env (φ ⇒ ψ) = {{y : L}} {{y≼x : y ≼ x}} → exec∇ {{y}} env φ → exec∇ {{y}} env ψ
exec∇ {{x}} env (EX φ)  = ∇ (λ {{x}} → Σ[ u ∈ _ ] exec∇ {{x}} (u ∷ env) φ)
exec∇ {{x}} env (FA φ)  = {{y : L}} {{y≼x : y ≼ x}} (u : _) → exec∇ {{y}} (u ∷ env) φ
exec∇ {{x}} env (G t)   = ∇ (λ {{y}} → y ≼ eval env t)

weakenP
  : {frag : Fragment} {lang : Language} {Γ : Cxt} {env : Env Γ}
  → (φ : Formula Γ frag lang)
  → {x y : L} → y ≼ x → execP {{x}} env φ → execP {{y}} env φ
weakenP (Rel₂ R s t) y≼x p = p
weakenP top          y≼x p = p
weakenP (φ ∨ ψ)      y≼x (inj₁ p) = inj₁ (weakenP φ y≼x p)
weakenP (φ ∨ ψ)      y≼x (inj₂ p) = inj₂ (weakenP ψ y≼x p)
weakenP (φ ∧ ψ)      y≼x (p , q)  = weakenP φ y≼x p , weakenP ψ y≼x q
weakenP (φ ⇒ ψ)      y≼x p {{z}} {{z≼y}} = λ q → p {{z}} {{≼-trans z≼y y≼x}} q
weakenP (EX φ)       y≼x (u , p) = u , weakenP φ y≼x p
weakenP (FA φ)       y≼x p {{z}} {{z≼y}} = λ u → p {{z}} {{≼-trans z≼y y≼x}} u
weakenP (G x)        y≼x p = ≼-trans y≼x p

weaken
  : {frag : Fragment} {lang : Language} {Γ : Cxt} {φ : Formula Γ frag lang} {env : Env Γ}
  → {x y : L} → y ≼ x → exec∇ {{x}} env φ → exec∇ {{y}} env φ
weaken {φ = Rel₂ R s t} y≼x p = weaken-ev (λ _ q → q) y≼x p
weaken {φ = top}        y≼x p = tt
weaken {φ = bot}        y≼x p = weaken-ev (λ _ q → q) y≼x p
weaken {φ = φ ∨ ψ}      y≼x p = weaken-ev (λ z≼w → [ (λ q → inj₁ (weaken z≼w q)) , (λ q → inj₂ (weaken z≼w q)) ]′) y≼x p
weaken {φ = φ ∧ ψ}      y≼x p = weaken y≼x (proj₁ p) , weaken y≼x (proj₂ p)
weaken {φ = φ ⇒ ψ}      y≼x p {{z}} {{z≼y}} q = p {{z}} {{≼-trans z≼y y≼x}} q
weaken {φ = EX φ}       y≼x p = weaken-ev (λ z≼w (u , q) → u , weaken z≼w q) y≼x p
weaken {φ = FA φ}       y≼x p {{z}} {{z≼y}} u = p {{z}} {{≼-trans z≼y y≼x}} u
weaken {φ = G t}        y≼x p = weaken-ev ≼-trans y≼x p

{-
local
  : {{x : L}} {frag : Fragment} {lang : Language} {Γ : Cxt} (φ : Formula Γ frag lang) (env : Env Γ)
  → ∇ (λ {{y}} → exec∇ {{y}} env φ) → exec∇ env φ
local (Rel₂ R s t) env p = {!!}
local top          env p = tt
local bot          env p = p ⟫= λ q → q
local (φ ∨ ψ)      env p = {!!}
local (φ ∧ ψ)      env p = local φ env (fmap proj₁ p) , local ψ env (fmap proj₂ p)
local (φ ⇒ ψ)      env p {{y}} {{y≼x}} q = {!!} -- local {{y}} ψ env (fmap {{y}} (λ f → f (weaken _ q)) (weaken y≼x p))
local (EX φ)       env p = {!!}
local (FA φ)       env p = {!!}
local (G x)        env p = {!!}
-}

open import Data.List.Relation.Unary.Any

var₀ : {Γ : Cxt} {ty : Ty} → Term (ty ∷ Γ) ty
var₀ = var (here refl)

var₁ : {Γ : Cxt} {ty ty' : Ty} → Term (ty ∷ ty' ∷ Γ) ty'
var₁ = var (there (here refl))

var₂ : {Γ : Cxt} {ty ty' ty'' : Ty} → Term (ty ∷ ty' ∷ ty'' ∷ Γ) ty''
var₂ = var (there (there (here refl)))

{-
filter-condition : Formula [] first-order with-generic-filter
filter-condition
  = FA (FA (Rel₂ _≼_ var₀ var₁ ⇒ (1ˢᵗ (G var₀) ⇒ G var₁)))
  ∧ EX (G var₀)
  ∧ FA (FA (G var₀ ⇒ (1ˢᵗ (G var₁) ⇒ (EX (Rel₂ _≼_ var₀ var₁ ∧ Rel₂ _≼_ var₀ var₂ ∧ G var₀)))))
  ∧ FA (1ˢᵗ (G (app (lit proj₁) var₀)) ⇒ EX (G var₀ ∧ Rel₂ (λ (x , R) a → _◁_ {x} a R) var₁ var₀))
-}

{-
lemma-gen-filter₂ₐ : {{x : L}} → exec∇ [] filter-condition
lemma-gen-filter₂ₐ
  = (λ x y y≼x z≼y → _⟫=_ {{_}} z≼y λ z≼y' → weaken-ev (λ _ p → p) (≼-trans {!!} {!!}) y≼x ⟫= {!!})
  , now (_ , now ≼-refl)
  , {!!}
  , (λ xR Gx → {!!})
-}

lemma-exec-coherent₁
  : {{x : L}} {lang : Language} {Γ : Cxt}
  → (env : Env Γ) (φ : Formula Γ coherent lang)
  → exec∇ env φ → ∇ (λ {{y}} → execP {{y}} env φ)
lemma-exec-coherent₁ env (Rel₂ R s t) p = p
lemma-exec-coherent₁ env top          p = now tt
lemma-exec-coherent₁ env bot          p = p ⟫= ⊥-elim
lemma-exec-coherent₁ env (φ ∨ ψ)      p = p ⟫= λ {{y}} {{y≼x}} → [ (λ q → fmap {{y}} inj₁ (lemma-exec-coherent₁ {{y}} env φ q)), (λ q → fmap {{y}} inj₂ (lemma-exec-coherent₁ {{y}} env ψ q)) ]′
lemma-exec-coherent₁ env (φ ∧ ψ)      p = lemma-exec-coherent₁ {{_}} env φ (proj₁ p) ⟫= λ {{y}} {{y≼x}} q → _⟫=_ {{y}} (lemma-exec-coherent₁ {{y}} env ψ (weaken y≼x (proj₂ p))) λ {{z}} {{z≼y}} r → now (weakenP φ z≼y q , r)
lemma-exec-coherent₁ env (EX φ)       p = p ⟫= λ {{y}} {{y≼x}} (u , q) → _⟫=_ {{y}} (lemma-exec-coherent₁ {{y}} (u ∷ env) φ q) λ {{z}} {{z≼y}} r → now (u , r)
lemma-exec-coherent₁ env (G x)        p = p

lemma-exec-coherent₂
  : {{x : L}} {lang : Language} {Γ : Cxt}
  → (env : Env Γ) (φ : Formula Γ coherent lang)
  → ∇ (λ {{y}} → execP {{y}} env φ) → exec∇ env φ
lemma-exec-coherent₂ env (Rel₂ R s t) p = p
lemma-exec-coherent₂ env top          p = tt
lemma-exec-coherent₂ env bot          p = p
lemma-exec-coherent₂ env (φ ∨ ψ)      p = fmap (λ {{y}} → [ (λ q → inj₁ (lemma-exec-coherent₂ {{y}} env φ (now q))) , (λ q → inj₂ (lemma-exec-coherent₂ {{y}} env ψ (now q))) ]′) p
lemma-exec-coherent₂ env (φ ∧ ψ)      p = lemma-exec-coherent₂ env φ (fmap proj₁ p) , lemma-exec-coherent₂ env ψ (fmap proj₂ p)
lemma-exec-coherent₂ env (EX φ)       p = p ⟫= λ {{y}} (u , q) → fmap {{y}} (u ,_) (now (lemma-exec-coherent₂ {{y}} (u ∷ env) φ (now q)))
lemma-exec-coherent₂ env (G x)        p = p

lemma-exec-coherent₁'
  : {{x : L}} {Γ : Cxt}
  → (env : Env Γ) (φ : Formula Γ coherent base)
  → execP env φ → exec env φ
lemma-exec-coherent₁' env (Rel₂ R s t) p = p
lemma-exec-coherent₁' env top          p = p
lemma-exec-coherent₁' env (φ ∨ ψ)      p = Data.Sum.map (lemma-exec-coherent₁' env φ) (lemma-exec-coherent₁' env ψ) p
lemma-exec-coherent₁' env (φ ∧ ψ)      p = Data.Product.map (lemma-exec-coherent₁' env φ) (lemma-exec-coherent₁' env ψ) p
lemma-exec-coherent₁' env (EX φ)       p = proj₁ p , lemma-exec-coherent₁' (proj₁ p ∷ env) φ (proj₂ p)

lemma-exec-coherent₂'
  : {{x : L}} {Γ : Cxt}
  → (env : Env Γ) (φ : Formula Γ coherent base)
  → exec env φ → execP env φ
lemma-exec-coherent₂' env (Rel₂ R s t) p = p
lemma-exec-coherent₂' env top          p = p
lemma-exec-coherent₂' env (φ ∨ ψ)      p = Data.Sum.map (lemma-exec-coherent₂' env φ) (lemma-exec-coherent₂' env ψ) p
lemma-exec-coherent₂' env (φ ∧ ψ)      p = Data.Product.map (lemma-exec-coherent₂' env φ) (lemma-exec-coherent₂' env ψ) p
lemma-exec-coherent₂' env (EX φ)       p = proj₁ p , lemma-exec-coherent₂' (proj₁ p ∷ env) φ (proj₂ p)

module 1ˢᵗOrderEquivalence
  (all-coverings-inhabited : {x : L} (R : Cov x) → Relation.Unary.Satisfiable (_◁ R)) where

  open import Forcing.Monad.Conservative L… all-coverings-inhabited

  thm₁
    : {{x : L}}
    → {frag : Fragment} {Γ : Cxt}
    → (env : Env Γ) (φ : Formula Γ frag base)
    → exec env φ → exec∇ env φ

  thm₂
    : {{x : L}}
    → {frag : Fragment} {Γ : Cxt}
    → (env : Env Γ) (φ : Formula Γ frag base)
    → exec∇ {{x}} env φ → exec env φ

  thm₁ env (Rel₂ R s t) p            = now p
  thm₁ env top     p                 = p
  thm₁ env (φ ∨ ψ) (inj₁ p)          = now (inj₁ (thm₁ env φ p))
  thm₁ env (φ ∨ ψ) (inj₂ p)          = now (inj₂ (thm₁ env ψ p))
  thm₁ env (φ ∧ ψ) (p , q)           = thm₁ env φ p , thm₁ env ψ q
  thm₁ env (φ ⇒ ψ) p {{y}} {{y≼x}} q = thm₁ {{y}} env ψ (p (thm₂ {{y}} env φ q))
  thm₁ env (EX φ)  (u , p)           = now (u , thm₁ (u ∷ env) φ p)
  thm₁ env (FA φ)  p {{y}} {{y≼x}}   = λ u → thm₁ {{y}} (u ∷ env) φ (p u)

  thm₂ {{x}} env (Rel₂ R s t) p = escape p
  thm₂ {{x}} env top          p = tt
  thm₂ {{x}} env bot          p = escape p
  thm₂ {{x}} env (φ ∨ ψ)      p = escape (fmap {{x}} (λ {{y}} → [ (λ q → inj₁ (thm₂ {{y}} env φ q)) , (λ q → inj₂ (thm₂ {{y}} env ψ q)) ]′) p)
  thm₂ {{x}} env (φ ∧ ψ)      p = thm₂ env φ (proj₁ p) , thm₂ env ψ (proj₂ p)
  thm₂ {{x}} env (φ ⇒ ψ)      p = λ q → thm₂ {{x}} env ψ (p {{x}} {{≼-refl}} (thm₁ {{x}} env φ q))
  thm₂ {{x}} env (EX φ)       p = escape (fmap (λ {{y}} (u , q) → u , thm₂ {{y}} (u ∷ env) φ q) p)
  thm₂ {{x}} env (FA φ)       p = λ u → thm₂ (u ∷ env) φ (p {{x}} {{≼-refl}} u)

module CoherentEquivalence
  (top : L)
  (escape : {P : Set} → ∇ {{top}} P → P) where

  thm₁
    : {{x : L}}
    → {Γ : Cxt}
    → (env : Env Γ)
    → (φ ψ : Formula Γ coherent base)
    → exec env (φ ⇒ ψ) → exec∇ {{x}} env (φ ⇒ ψ)
  thm₁ env φ ψ p {{y}} {{y≼x}} q = lemma-exec-coherent₂ {{y}} env ψ (fmap {{y}} (λ {{z}} → lemma-exec-coherent₂' {{z}} env ψ) (fmap {{y}} p (fmap {{y}} (λ {{z}} → lemma-exec-coherent₁' {{z}} env φ) (lemma-exec-coherent₁ {{y}} env φ q))))

  thm₁⁺
    : {ty : Ty}
    → (φ ψ : Formula (ty ∷ []) coherent base)
    → exec [] (FA (φ ⇒ ψ)) → exec∇ {{top}} [] (FA (φ ⇒ ψ))
  thm₁⁺ φ ψ p {{y}} {{y≼top}} = λ u {{z}} {{z≼y}} → thm₁ {{y}} (u ∷ []) φ ψ (p u) {{z}} {{z≼y}}

  thm₂
    : {Γ : Cxt}
    → (env : Env Γ)
    → (φ ψ : Formula Γ coherent base)
    → exec∇ {{top}} env (φ ⇒ ψ) → exec env (φ ⇒ ψ)
  thm₂ env φ ψ p q =
    escape (fmap {{top}} (lemma-exec-coherent₁' env ψ) (lemma-exec-coherent₁ {{top}} env ψ (p {{top}} {{≼-refl}} (lemma-exec-coherent₂ {{top}} env φ (now (lemma-exec-coherent₂' {{top}} env φ q))))))

  thm₂⁺
    : {ty : Ty}
    → (φ ψ : Formula (ty ∷ []) coherent base)
    → exec∇ {{top}} [] (FA (φ ⇒ ψ)) → exec [] (FA (φ ⇒ ψ))
  thm₂⁺ φ ψ p = λ u q → thm₂ (u ∷ []) φ ψ (p {{top}} {{≼-refl}} u) q
