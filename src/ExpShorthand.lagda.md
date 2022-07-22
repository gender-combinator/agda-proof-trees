Several utility functions that make writing terms shorter and more readable.

Useful ones to start with:
- Variable references: _#0 , _#1 , _#2

  The number refers to the variables index into the environment.

  Used like: "x" #0

- Variable substitution: <exp> [ <new-exp> / <var-to-substitute> ]

  For example, to substitue the variable "x" for the term ℕ in D:

  D [ ℕ / "x" ]

- Function types: A ⟶ B

```agda
{-# OPTIONS --without-K --safe #-}

module ExpShorthand where

open import Agda.Builtin.Equality renaming (_≡_ to Id ; refl to ⋯)
open import Data.Empty using (⊥)
open import Data.List using (_∷_ ; [] ; _++_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (zero ; suc) renaming (ℕ to Nat)
open import Data.String using (String)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_)

open import Exp

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

_⟶_ : {e : Env} → Exp e → Exp e → {v : String} → Exp e
(A ⟶ B) {v} = Π v ꞉ A , drop-env₀ B

module ExpExamples where
  e₁ : Exp ("x" ∷ "y" ∷ [])
  e₁ = Π "a" ꞉ "x" #0 , "y" #2

  p₁ : Id (e₁ [ 𝟘 / "x" ]) (Π "a" ꞉ 𝟘 , "y" #1)
  p₁ = ⋯

```
