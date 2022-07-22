Trying to setup a type checked proof trees, to verify HoTT exercises.

Want a proof tree to look like:

  Γ ,̣ "x" ꞉ A ⊢ b ꞉ B
  ---[ Π-elim ]
  Γ ⊢ (π "x" ꞉ A , b) ꞉ Π "x" ꞉ A , B

```agda
{-# OPTIONS --without-K --safe #-}

module ProofTrees where

open import Agda.Builtin.Equality renaming (_≡_ to Id ; refl to ⋯)
open import Agda.Primitive using (Level)
open import Data.Empty using (⊥)
open import Data.List using (List ; _∷_ ; [] ; map ; _++_ ; length)
open import Data.List.Relation.Unary.All using (All ; _∷_ ; [])
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (zero ; suc) renaming (ℕ to Nat)
open import Data.String using (String)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_)

pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []

Env = List String

data VarIn : Env → Set where
  CurrVar : {rst : Env} → (v : String) → VarIn (v ∷ rst)
  NextVar
    : {v : String} {rst : Env} → VarIn rst → VarIn (v ∷ rst)

data Exp : Env → Set where
  Var : {e : Env} → VarIn e → Exp e
  𝟘 : {e : Env} → Exp e
  𝟙 : {e : Env} → Exp e
  ⋆ : {e : Env} → Exp e
  ℕ : {e : Env} → Exp e
  𝟎 : {e : Env} → Exp e
  S : {e : Env} → Exp e → Exp e
  ind-ℕ
    : {e : Env} 
    → (pz : Exp e)
    → {n prev : String}
    → (ps : Exp (prev ∷ n ∷ e))
    → (n : Exp e)
    → Exp e
  Π_꞉_,_ : {e : Env} → (v : String) → Exp e → Exp (v ∷ e) → Exp e
  π_,_ : {e : Env} → (v : String) → Exp (v ∷ e) → Exp e
  _◃_ : {e : Env} (func : Exp e) → (arg : Exp e) → Exp e
  Σ_꞉_,_ : {e : Env} → (v : String) → Exp e → Exp (v ∷ e) → Exp e
  σ_,_ : {e : Env} → Exp e → Exp e → Exp e
  ind-Σ
    : {e : Env} {prj₂ prj₁ : String}
    → (a : Exp (prj₂ ∷ prj₁ ∷ e))
    → (z : Exp e)
    → Exp e
  _≡_ : {e : Env} → Exp e → Exp e → Exp e

infix 9 _◃_
infix 5 Π_꞉_,_
infix 5 π_,_
infix 5 Σ_꞉_,_
infix 5 σ_,_
infix 3 _≡_
infixl 2 _,̣_꞉_
infix 1 _⊢_type
infix 1 _⊢_꞉_
infix 1 _⊢_≐_꞉_
infix 1 _⊢Judgment_
infixl -2 Rule_─────_
infixl -2 _─────_via_
infixl -2 _^────_via_

module ExpShorthand where
  infix 10 _#_#_
  infix 10 _#0
  infix 10 _#1
  infix 10 _#2
  infixr 4 _⟶_

  varNameAt : Nat → Env → Maybe String
  varNameAt = λ where
    _ [] → nothing
    zero (v ∷ rst) → just v
    (suc i) (v ∷ rst) → varNameAt i rst

  findVar
    : (v : String) → (i : Nat) → {e : Env}
    → {p : Id (varNameAt i e) (just v)}
    → VarIn e
  findVar v = λ where
    zero {x ∷ e} {p} → CurrVar x
    (suc i) {x ∷ e} {p} → NextVar (findVar v i {e} {p})
  _#_#_
    : {e : Env} → (v : String) → (i : Nat)
    → (p : Id (varNameAt i e) (just v))
    → Exp e
  _#_#_ {e} v i p = Var (findVar v i {e} {p})

  _#0 : {e : Env} → (v : String) → Exp (v ∷ e)
  _#1 : {e : Env} {a : String} → (v : String) → Exp (a ∷ v ∷ e)
  _#2 : {e : Env} {a b : String} → (v : String) → Exp (a ∷ b ∷ v ∷ e)
  _#0 v = v # 0 # ⋯
  _#1 v = v # 1 # ⋯
  _#2 v = v # 2 # ⋯

  within-var
    : {a : String} {e e' : Env}
    → (VarIn e → VarIn e')
    → VarIn (a ∷ e) → VarIn (a ∷ e')
  within-var f = λ where
    (CurrVar v) → CurrVar v
    (NextVar x) → NextVar (f x)

  map-var-to-var
    : {oldEnv newEnv : Env}
    → (VarIn oldEnv → VarIn newEnv)
    → Exp oldEnv
    → Exp newEnv
  map-var-to-var f = λ where
    (Var x) → Var (f x)
    𝟘 → 𝟘
    𝟙 → 𝟙
    ⋆ → ⋆
    ℕ → ℕ
    𝟎 → 𝟎
    (S e) → S (map-var-to-var f e)
    (ind-ℕ e e₁ e₂) →
      ind-ℕ
        (map-var-to-var f e)
        (map-var-to-var (within-var (within-var f)) e₁)
        (map-var-to-var f e₂)
    (Π v ꞉ e , e₁) →
      Π v ꞉ map-var-to-var f e , map-var-to-var (within-var f) e₁
    (π v , e) →
      π v , map-var-to-var (within-var f) e
    (e ◃ e₁) → map-var-to-var f e ◃ map-var-to-var f e₁
    (Σ v ꞉ e , e₁) →
      Σ v ꞉ map-var-to-var f e , map-var-to-var (within-var f) e₁
    (σ e , e₁) → σ map-var-to-var f e , map-var-to-var f e₁
    (ind-Σ e₁ e₂) →
      ind-Σ
        (map-var-to-var (within-var (within-var f)) e₁)
        (map-var-to-var f e₂)
    (e ≡ e₁) → map-var-to-var f e ≡ map-var-to-var f e₁

  within-var-mapping
    : {x : String} {oldEnv newEnv : Env}
    → (VarIn oldEnv → Exp newEnv)
    → VarIn (x ∷ oldEnv) → Exp (x ∷ newEnv)
  within-var-mapping f = λ where
    (CurrVar v) → Var (CurrVar v)
    (NextVar rst) → map-var-to-var NextVar (f rst)

  map-env
    : {oldEnv newEnv : Env}
    → (f : VarIn oldEnv → Exp newEnv)
    → Exp oldEnv
    → Exp newEnv
  map-env f = 
    λ where
      (Var x) → f x
      𝟘 → 𝟘
      𝟙 → 𝟙
      ⋆ → ⋆
      ℕ → ℕ
      𝟎 → 𝟎
      (S e) → S (map-env f e)
      (ind-ℕ e e₁ e₂) →
        ind-ℕ
          (map-env f e)
          (map-env (within-var-mapping (within-var-mapping f)) e₁)
          (map-env f e₂)
      (Π v ꞉ e , e₁) → Π v ꞉ map-env f e , map-env (within-var-mapping f) e₁
      (π v , e) → π v , map-env (within-var-mapping f) e
      (e ◃ e₁) → map-env f e ◃ map-env f e₁
      (Σ v ꞉ e , e₁) → Σ v ꞉ map-env f e , map-env (within-var-mapping f) e₁
      (σ e , e₁) → σ map-env f e , map-env f e₁
      (ind-Σ e₁ e₂) →
        ind-Σ
          (map-env (within-var-mapping (within-var-mapping f)) e₁)
          (map-env f e₂)
      (e ≡ e₁) → map-env f e ≡ map-env f e₁

  insert-index-in : Nat → Env → Set
  insert-index-in = λ where
    0 _ → ⊤
    (suc i) [] → ⊥
    (suc i) (v ∷ rst) → insert-index-in i rst

  insert-var-at
    : (v : String) → (i : Nat) → (e : Env) → {p : insert-index-in i e} → Env
  insert-var-at v = λ where
    zero e → v ∷ e
    (suc i) (x ∷ e) {p} → x ∷ insert-var-at v i e {p}

  w/var-inserted-at
    : (v : String)
    → (i : Nat)
    → {env : Env}
    → (exp : Exp env)
    → {p : insert-index-in i env}
    → Exp (insert-var-at v i env {p})
  w/var-inserted-at v i {env} exp {p} =
    map-env (λ varIn → Var (w/var-inserted-at-var v i {env} varIn {p})) exp
    where
      w/var-inserted-at-var
        : (v : String)
        → (i : Nat)
        → {env : Env}
        → VarIn env
        → {p : insert-index-in i env}
        → VarIn (insert-var-at v i env {p})
      w/var-inserted-at-var v = λ where
        zero w {p} → NextVar w
        (suc i) (CurrVar v₁) {p} → CurrVar v₁
        (suc i) (NextVar exp) {p} →
          NextVar (w/var-inserted-at-var v i exp {p})

  module Specific where
    drop-env₀ : {v : String} → {e : Env} → Exp e → Exp (v ∷ e)
    drop-env₀ = map-env (Var ∘ NextVar)

    rename-var : {a b : String} {e : Env} → VarIn (a ∷ e) → VarIn (b ∷ e)
    rename-var {b = b} = λ where
        (CurrVar _) → CurrVar b
        (NextVar x) → NextVar x
    rename-env₀ : {a b : String} {e : Env} → Exp (a ∷ e) → Exp (b ∷ e)
    rename-env₀ = map-env (Var ∘ rename-var)

    map-var₀
        : {x : String} {e pushed : Env}
        → Exp (pushed ++ e)
        → VarIn (x ∷ e)
        → Exp (pushed ++ e)
    map-var₀ newBot (CurrVar _) = newBot
    map-var₀ {pushed = p} newBot (NextVar v) = Var (drop-pushed v p)
        where
        drop-pushed : {e : Env} → VarIn e → (p : Env) → VarIn (p ++ e)
        drop-pushed v = λ where
            [] → v
            (_ ∷ p) → NextVar (drop-pushed v p)
    map-env₀
        : {x : String} {e pushed : Env}
        → (Exp (pushed ++ e))
        → Exp (x ∷ e)
        → Exp (pushed ++ e)
    map-env₀ = map-env ∘ map-var₀
  open Specific

  subvar-0
    : (oldVar : String)
    → {env : Env}
    → (newExp : Exp env)
    → (exp : Exp (oldVar ∷ env))
    → Exp env
  subvar-0 v {env} newExp e =
    map-env
      (λ where
        (CurrVar _) → newExp
        (NextVar exp) → Var exp)
      e
  syntax subvar-0 v newExp exp = exp [ newExp / v ]

  _⟶_ : {e : Env} → Exp e → Exp e → {v : String} → Exp e
  (A ⟶ B) {v} = Π v ꞉ A , drop-env₀ B

open ExpShorthand
open ExpShorthand.Specific

module ExpExamples where
  e₁ : Exp ("x" ∷ "y" ∷ [])
  e₁ = Π "a" ꞉ "x" #0 , "y" #2

  e2 : Exp ("y" ∷ [])
  e2 = e₁ [ 𝟘 / "x" ]

  pe2 : Id (e₁ [ 𝟘 / "x" ]) (Π "a" ꞉ 𝟘 , "y" #1)
  pe2 = ⋯

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

  ≡-form
    : {e : Env} {Γ : Context e} {x : String} {a A : Exp e}
    → Rule
        [ Γ ⊢ a ꞉ A ]
        ─────
        Γ ,̣ x ꞉ A ⊢ drop-env₀ a ≡ x #0 type

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
  -- Σ-elim
  --   : {e : Env} {Γ : Context e} {x z xa ya : String}
  --     {P : Exp e} {D : Exp (z ∷ e)}
  --     {Q : Exp (x ∷ e)} {a : Exp (ya ∷ xa ∷ e)}
  --   → Rule
  --     []
  --     (Γ ,̣ z ꞉ (Σ x ꞉ P , Q) ⊢ ind-Σ (drop-env₀ a) (z #0)) ꞉ D)

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


data Proof : Γ⊢Judgment → Set where
  ApplyRule
    : {ins : List Γ⊢Judgment}
    → (inProofs : All Proof ins)
    → (out : Γ⊢Judgment)
    → Rule
        ins
        ─────
        out
    → Proof out

_─────_via_
  : {ins : List Γ⊢Judgment}
  → All Proof ins
  → (out : Γ⊢Judgment)
  → Rule
      ins
      ─────
      out
  → Proof out
inProofs ───── out via rule = ApplyRule inProofs out rule

_^────_via_
  : {a : Γ⊢Judgment}
  → Proof a
  → (out : Γ⊢Judgment)
  → Rule
      [ a ]
      ─────
      out
  → Proof out
_^────_via_ x y z = _─────_via_ [ x ] y z

empty : All Proof []
empty = []

module ProofExamples where
  p₁ : Proof (Γ₀ ,̣ "a" ꞉ 𝟘 ⊢ "a" #0 ꞉ 𝟘)
  p₁ =
    empty
    ─────
    Γ₀ ,̣ "a" ꞉ 𝟘 ⊢ "a" #0 ꞉ 𝟘
    via projection₀


  add
    : Proof (
      Γ₀
      ⊢ π "x"
      , π "y"
      , ind-ℕ 
          𝟎
          {n = "a"} {prev = "z"} (S ("z" #0))
          ("y" #0)
      ꞉ ℕ ⟶ ℕ ⟶ ℕ
    )
  add =
    [ empty
      ─────
      Γ₀ ,̣ "x" ꞉ ℕ ,̣ "y" ꞉ ℕ ⊢ ℕ type
      via projectionᵣ (projectionᵣ ℕ-form)
    , empty
      ─────
      Γ₀ ,̣ "x" ꞉ ℕ ⊢ 𝟎 ꞉ ℕ
      via projectionᵣ ℕ-intro-𝟎
    , empty
      ─────
      Γ₀ ,̣ "x" ꞉ ℕ ,̣ "a" ꞉ ℕ ,̣ "z" ꞉ ℕ ⊢ "z" #0 ꞉ ℕ
      via projection₀
      ^────
      Γ₀ ,̣ "x" ꞉ ℕ ,̣ "a" ꞉ ℕ ,̣ "z" ꞉ ℕ ⊢ S ("z" #0) ꞉ ℕ
      via ℕ-intro-s
    ]
    ─────
    Γ₀ ,̣ "x" ꞉ ℕ ,̣ "y" ꞉ ℕ ⊢ ind-ℕ 𝟎 (S ("z" #0)) ("y" #0) ꞉ ℕ
    via ℕ-elim
    ^────
    Γ₀ ,̣ "x" ꞉ ℕ ⊢ π "y" , ind-ℕ 𝟎 (S ("z" #0)) ("y" #0) ꞉ ℕ ⟶ ℕ
    via Π-intro
    ^────
    Γ₀ ⊢ π "x" , π "y" , ind-ℕ 𝟎 (S ("z" #0)) ("y" #0) ꞉ ℕ ⟶ ℕ ⟶ ℕ
    via Π-intro

```
