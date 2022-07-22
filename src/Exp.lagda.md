Defines the *terms* for the Proof Trees to act on.

### To add a new term
- First add to the Exp type below
- Then modify the corresponding cases in map-var-to-var and map-env
See their definitions for more details.

```agda
{-# OPTIONS --without-K --safe #-}

module Exp where

open import Data.String using (String)
open import Data.List using (List ; _∷_ ; [])

infix 9 _◃_
infix 5 Π_꞉_,_
infix 5 λ̣_,_
infix 5 Σ_꞉_,_
infix 5 σ_,_

```
Env tracks all variables that a term may reference. (They may come from the surronding Context (Γ) or expressions like Π / Σ / λ̣)

This does allow multiple unique variables to have the same name. But, they will be distinguished when refering to them. Each references (VarIn) refers to a specific variable by index (De Bruijn style) into their environment. (See [ExpShorthand](ExpShorthand.lagda.md) for easy ways to refer to a variable.)
```agda
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
  λ̣_,_ : {e : Env} → (v : String) → Exp (v ∷ e) → Exp e
  _◃_ : {e : Env} (func : Exp e) → (arg : Exp e) → Exp e
  Σ_꞉_,_ : {e : Env} → (v : String) → Exp e → Exp (v ∷ e) → Exp e
  σ_,_ : {e : Env} → Exp e → Exp e → Exp e

within-var
  : {a : String} {e e' : Env}
  → (VarIn e → VarIn e')
  → VarIn (a ∷ e) → VarIn (a ∷ e')
within-var f = λ where
  (CurrVar v) → CurrVar v
  (NextVar x) → NextVar (f x)

```
map-var-to-var and map-env provide generic manipulation of variables in any term. Like common variable substitution or renaming.

They are nearly identical, but map-var-to-var exists to provide a clear terminating definition for Agda.

Most new terms can be added with a similar style case to the ones that already exist, by mapping their nested elements (if any) with the same function. Notice when their elements assume additional variables in their environment, then use the utilities within-var/within-var-to-env to *skip over* those vars. See Π as an example.
```agda
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
  (λ̣ v , e) →
    λ̣ v , map-var-to-var (within-var f) e
  (e ◃ e₁) → map-var-to-var f e ◃ map-var-to-var f e₁
  (Σ v ꞉ e , e₁) →
    Σ v ꞉ map-var-to-var f e , map-var-to-var (within-var f) e₁
  (σ e , e₁) → σ map-var-to-var f e , map-var-to-var f e₁

within-var-to-env
  : {x : String} {oldEnv newEnv : Env}
  → (VarIn oldEnv → Exp newEnv)
  → VarIn (x ∷ oldEnv) → Exp (x ∷ newEnv)
within-var-to-env f = λ where
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
        (map-env (within-var-to-env (within-var-to-env f)) e₁)
        (map-env f e₂)
    (Π v ꞉ e , e₁) → Π v ꞉ map-env f e , map-env (within-var-to-env f) e₁
    (λ̣ v , e) → λ̣ v , map-env (within-var-to-env f) e
    (e ◃ e₁) → map-env f e ◃ map-env f e₁
    (Σ v ꞉ e , e₁) → Σ v ꞉ map-env f e , map-env (within-var-to-env f) e₁
    (σ e , e₁) → σ map-env f e , map-env f e₁
```
