```agda
{-# OPTIONS --without-K --safe #-}

module ProofTree where

open import Data.List using (List ; _∷_ ; [])
open import Data.List.Relation.Unary.All using (All ; _∷_ ; [])
open import Data.String using (String)
open import Data.Unit using (tt)
open import Function using (_∘_)

open import Exp public
open import ExpShorthand public

pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []

infixl 2 _,̣_꞉_
infix 1 _⊢_type
infix 1 _⊢_꞉_
infix 1 _⊢_≐_꞉_
infix 1 _⊢Judgment_
infixl -2 Rule_─────_
infixl -2 _─────_via_
infixl -2 _^────_via_

data Context : Env → Set where
  Γ₀ : Context []
  _,̣_꞉_
    : {e : Env}
    → Context e
    → (v : String)
    → Exp e
    → Context (v ∷ e)

module ContextExamples where
  example-Γ₁ = Γ₀ ,̣ "x" ꞉ 𝟘
  example-Γ₂ = Γ₀ ,̣ "x" ꞉ 𝟘 ,̣ "y" ꞉ "x" #0

data Judgment (e : Env) : Set where
  IsType : Exp e → Judgment e
  InstOf : Exp e → Exp e → Judgment e
  JudgmentallyEqual : Exp e → Exp e → Exp e → Judgment e
data Γ⊢Judgment : Set where
  _⊢Judgment_ : {e : Env} → Context e → Judgment e → Γ⊢Judgment

_⊢_type : {e : Env} → Context e → Exp e → Γ⊢Judgment
Γ ⊢ t type = Γ ⊢Judgment IsType t
_⊢_꞉_ : {e : Env} → Context e → Exp e → Exp e → Γ⊢Judgment
Γ ⊢ a ꞉ A = Γ ⊢Judgment InstOf a A
_⊢_≐_꞉_ : {e : Env} → Context e → Exp e → Exp e → Exp e → Γ⊢Judgment
Γ ⊢ x ≐ y ꞉ A = Γ ⊢Judgment JudgmentallyEqual x y A

map-env-Judgment
  : {old new : Env}
  → (VarIn old → Exp new)
  → Judgment old
  → Judgment new
map-env-Judgment f = λ where
  (IsType x) → IsType (map-env f x)
  (InstOf a A) → InstOf (map-env f a) (map-env f A)
  (JudgmentallyEqual x y A) →
    JudgmentallyEqual (map-env f x) (map-env f y) (map-env f A)

module JudgmentExamples where
  example₁ =
    Γ₀ ,̣ "A" ꞉ 𝟘 ,̣ "a" ꞉ "A" #0 ⊢ "a" #0 ꞉ "A" #1

data Rule_─────_ : List Γ⊢Judgment → Γ⊢Judgment → Set where
  projection₀
    : {e : Env} {Γ : Context e} {a : String} {A : Exp e}
    → Rule
        []
        ─────
        Γ ,̣ a ꞉ A ⊢ a #0 ꞉ drop-env₀ A
  projectionᵣ
    : {e : Env} {Γ : Context e} {a : String} {A : Exp e} {j : Judgment e}
      {js : List Γ⊢Judgment}
    → Rule
        js
        ─────
        Γ ⊢Judgment j
    → Rule
        js
        ─────
        Γ ,̣ a ꞉ A ⊢Judgment map-env-Judgment (Var ∘ NextVar) j
  rename₀
    : {e : Env} {Γ : Context e} {a b : String} {A : Exp e}
      {j : Judgment (a ∷ e)}
    → Rule
        [ Γ ,̣ a ꞉ A ⊢Judgment j ]
        ─────
        Γ ,̣ b ꞉ A ⊢Judgment map-env-Judgment (Var ∘ rename-var) j

  Π-form
    : {e : Env} {Γ : Context e} {a : String} {A : Exp e} {B : Exp (a ∷ e)}
    → Rule
        [ Γ ,̣ a ꞉ A ⊢ B type ]
        ─────
        Γ ⊢ Π a ꞉ A , B type
  Π-intro
    : {e : Env} {Γ : Context e} {a : String} {A : Exp e} {b B : Exp (a ∷ e)}
    → Rule
        [ Γ ,̣ a ꞉ A ⊢ b ꞉ B ]
        ─────
        Γ ⊢ π a , b ꞉ Π a ꞉ A , B
  Π-elim
    : {e : Env} {Γ : Context e} {x : String} {f a A : Exp e} {B : Exp (x ∷ e)}
    → Rule
        [ Γ ⊢ f ꞉ Π x ꞉ A , B ]
        ─────
        Γ ⊢ f ◃ a ꞉ (B [ a / x ])
  Π-comp-β
    : {e : Env} {Γ : Context e} {x : String} {a A : Exp e} {b B : Exp (x ∷ e)}
    → Rule
        [ Γ ,̣ x ꞉ A ⊢ b ꞉ B , Γ ⊢ a ꞉ A ]
        ─────
        Γ ⊢ (π x , b) ◃ a ≐ (b [ a / x ]) ꞉ B [ a / x ]
  Π-comp-η
    : {e : Env} {Γ : Context e} {x : String} {f A : Exp e} {B : Exp (x ∷ e)}
    → Rule
        [ Γ ⊢ f ꞉ Π x ꞉ A , B ]
        ─────
        Γ ⊢ (π x , drop-env₀ f ◃ x #0) ≐ f ꞉ Π x ꞉ A , B

  Σ-form
    : {e : Env} {Γ : Context e} {a : String} {A : Exp e} {B : Exp (a ∷ e)}
    → Rule
        [ Γ ,̣ a ꞉ A ⊢ B type ]
        ─────
        Γ ⊢ Σ a ꞉ A , B type
  Σ-intro
    : {e : Env} {Γ : Context e} {x : String} {a A b : Exp e} {B : Exp (x ∷ e)}
    → Rule
        [ Γ ⊢ a ꞉ A , Γ ⊢ b ꞉ B [ a / x ] ]
        ─────
        Γ ⊢ σ a , b ꞉ Σ x ꞉ A , B

  ℕ-form
    : Rule
        []
        ─────
        Γ₀ ⊢ ℕ type
  ℕ-intro-𝟎
    : Rule
        []
        ─────
        Γ₀ ⊢ 𝟎 ꞉ ℕ
  ℕ-intro-s
    : {e : Env} {Γ : Context e} {n : Exp e}
    → Rule
        [ Γ ⊢ n ꞉ ℕ ]
        ─────
        Γ ⊢ S n ꞉ ℕ
  ℕ-elim
    : {e : Env} {Γ : Context e}
      {xD xb yb x : String}
      {a : Exp e}
      {D : Exp (xD ∷ e)}
      {b : Exp (yb ∷ xb ∷ e)}
    → Rule
        [ Γ ,̣ xD ꞉ ℕ ⊢ D type
        , Γ ⊢ a ꞉ D [ 𝟎 / xD ]
        , Γ ,̣ xb ꞉ ℕ ,̣ yb ꞉ rename-env₀ D
            ⊢ b ꞉ drop-env₀ (map-env₀ (S (xb #0)) D)
        ]
        ─────
        Γ ,̣ x ꞉ ℕ
        ⊢ ind-ℕ
            (drop-env₀ a)
            (w/var-inserted-at x 2 b {tt})
            (x #0)
            ꞉ rename-env₀ D
  ℕ-comp-𝟎
    : {e : Env} {Γ : Context e}
      {xD xb yb : String}
      {a : Exp e}
      {D : Exp (xD ∷ e)}
      {b : Exp (yb ∷ xb ∷ e)}
    → Rule
        [ Γ ,̣ xD ꞉ ℕ ⊢ D type
        , Γ ⊢ a ꞉ D [ 𝟎 / xD ]
        , Γ ,̣ xb ꞉ ℕ ,̣ yb ꞉ rename-env₀ D
            ⊢ b ꞉ drop-env₀ (map-env₀ (S (xb #0)) D)
        ]
        ─────
        Γ ⊢ ind-ℕ a b 𝟎 ≐ a ꞉ D [ 𝟎 / xD ]
  ℕ-comp-s
    : {e : Env} {Γ : Context e}
      {xD xb yb x : String}
      {a : Exp e}
      {D : Exp (xD ∷ e)}
      {b : Exp (yb ∷ xb ∷ e)}
    → Rule
        [ Γ ,̣ xD ꞉ ℕ ⊢ D type
        , Γ ⊢ a ꞉ D [ 𝟎 / xD ]
        , Γ ,̣ xb ꞉ ℕ ,̣ yb ꞉ rename-env₀ D
            ⊢ b ꞉ drop-env₀ (map-env₀ (S (xb #0)) D)
        ]
        ─────
        Γ ,̣ x ꞉ ℕ
        ⊢ ind-ℕ
            (drop-env₀ a)
            (w/var-inserted-at x 2 b {tt})
            (S (x #0))
            ≐ map-env (Var ∘ within-var rename-var) b
            [ ind-ℕ
                (drop-env₀ a)
                (w/var-inserted-at x 2 b {tt})
                (x #0)
            / yb
            ]
            ꞉ map-env₀ (S (x #0)) D


data ProofTree : Γ⊢Judgment → Set where
  ApplyRule
    : {ins : List Γ⊢Judgment}
    → (inProofs : All ProofTree ins)
    → (out : Γ⊢Judgment)
    → Rule
        ins
        ─────
        out
    → ProofTree out

_─────_via_
  : {ins : List Γ⊢Judgment}
  → All ProofTree ins
  → (out : Γ⊢Judgment)
  → Rule
      ins
      ─────
      out
  → ProofTree out
inProofs ───── out via rule = ApplyRule inProofs out rule

_^────_via_
  : {a : Γ⊢Judgment}
  → ProofTree a
  → (out : Γ⊢Judgment)
  → Rule
      [ a ]
      ─────
      out
  → ProofTree out
_^────_via_ x y z = _─────_via_ [ x ] y z

empty : All ProofTree []
empty = []


```
