```agda
{-# OPTIONS --safe #-}
open import ProofTree

module Examples where
```

Most syntax is close but may vary to work well in Agda. The biggest difference is the lack of horizontal layout of proof trees (that *would* be cool to write in Agda, but sadly not this version). 

Here's some quick examples to get an idea of the syntax:

```agda
p₁ : ProofTree (Γ₀ ,̣ "a" ꞉ 𝟘 ⊢ "a" #0 ꞉ 𝟘)
p₁ =
  empty
  ─────
  Γ₀ ,̣ "a" ꞉ 𝟘 ⊢ "a" #0 ꞉ 𝟘
  via projection₀
```

and a larger example that defines the proof tree for an add function for natural numbers:

```agda
add
  : ProofTree (
    Γ₀
    ⊢ λ̣ "x"
    , λ̣ "y"
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
  Γ₀ ,̣ "x" ꞉ ℕ ⊢ λ̣ "y" , ind-ℕ 𝟎 (S ("z" #0)) ("y" #0) ꞉ ℕ ⟶ ℕ
  via Π-intro
  ^────
  Γ₀ ⊢ λ̣ "x" , λ̣ "y" , ind-ℕ 𝟎 (S ("z" #0)) ("y" #0) ꞉ ℕ ⟶ ℕ ⟶ ℕ
  via Π-intro
```
