```agda

open import ProofTree

module Examples where

p₁ : ProofTree (Γ₀ ,̣ "a" ꞉ 𝟘 ⊢ "a" #0 ꞉ 𝟘)
p₁ =
  empty
  ─────
  Γ₀ ,̣ "a" ꞉ 𝟘 ⊢ "a" #0 ꞉ 𝟘
  via projection₀


add
  : ProofTree (
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
