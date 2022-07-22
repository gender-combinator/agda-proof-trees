```agda
{-# OPTIONS --without-K --safe #-}

module Exp where

open import Data.String using (String)
open import Data.List using (List ; _∷_ ; [])

infix 9 _◃_
infix 5 Π_꞉_,_
infix 5 π_,_
infix 5 Σ_꞉_,_
infix 5 σ_,_
infix 3 _≡_

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
    (π v , e) → π v , map-env (within-var-to-env f) e
    (e ◃ e₁) → map-env f e ◃ map-env f e₁
    (Σ v ꞉ e , e₁) → Σ v ꞉ map-env f e , map-env (within-var-to-env f) e₁
    (σ e , e₁) → σ map-env f e , map-env f e₁
    (ind-Σ e₁ e₂) →
      ind-Σ
        (map-env (within-var-to-env (within-var-to-env f)) e₁)
        (map-env f e₂)
    (e ≡ e₁) → map-env f e ≡ map-env f e₁
```
