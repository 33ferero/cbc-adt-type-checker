module Program.Term  where

open import Prelude

open import Util.Scope
open import Program.Type
open import Util.Relations

private variable
  α : Scope

mutual
  data Pattern α : Set where
    `_#_∶_⟶_ : (x : String) → (p : x ∈ α) → (ns : List String) → Term (reverse ns ++ α) → Pattern α

  data Term α : Set where
    `_#_ : (x : String) → x ∈ α → Term α
    ƛ_∶_⇒_ : (x : String) (t : Type) (v : Term (x ∷ α)) → Term α
    Λ_ : Term α → Term α
    _◦_ : Term α → Type → Term α
    _·_   : (u v : Term α) → Term α
    `true : Term α
    `false : Term α
    `if_then_else_ : (b t e : Term α) → Term α
    `zero : Term α
    `suc : Term α → Term α
    `case_of⟦_⟧ : Term α → List (Pattern α) → Term α
 

infix  5  ƛ_∶_⇒_
infix  5  Λ_
infixl 7  _·_
infixl  7  _◦_
infix  9  `_#_
infix  6  `if_then_else_
infix  6  `case_of⟦_⟧
infix  5  `_#_∶_⟶_ 