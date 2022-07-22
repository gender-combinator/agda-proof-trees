# agda-proof-trees

Proof trees are nice to look at some times. 🙃
This lets you write proof trees and their rules nearly word for word in Agda. 

## Some gotchas: 
### Syntax

- Colons are unicode colons ```꞉``` written as ```\:4```
- Commas in Contexts have a dot under them ```,̣``` written as ```,\_.```
- Lambdas also use dots underneath ```λ̣``` written similarly as ```\Gl\_.```
- Sigma pairs are written with lowercase sigma ```σ a , b```
- Bars ```^────``` and ```─────``` are using the char ```─``` written as ```\---```
- The bar you choose in a proof tree affects syntax for their dependencies.
  - Use ```─────``` when wanting to write its dependencies as a list expression.
  - Use ```^────``` to avoid lists of one element and just write its singular dependency as is.
  
### Variables
Variables are referred to by name and their De Bruijn index in their context / local lambdas (Pi, Sigma, etc). 
  
E.g.
```agda
Γ₀ ,̣ "x" ꞉ ℕ ,̣ "y" ꞉ ℕ ⊢ "y" #0 ꞉ ℕ
Γ₀ ,̣ "x" ꞉ ℕ ,̣ "y" ꞉ ℕ ⊢ "x" #1 ꞉ ℕ
```
  
Agda will alert when the variable name does not match the index. For example this code:
```agda
Γ₀ ,̣ "x" ꞉ ℕ ,̣ "y" ꞉ ℕ ⊢ "x" #0 ꞉ ℕ
```
will have the following error message:
```agda
"x" != "y" of type Agda.Builtin.String.String
when checking that the expression "x" #0 has type Exp [ "y" , "x" ]
```
