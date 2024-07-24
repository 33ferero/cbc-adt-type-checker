module Program.Program where

open import Prelude

open import Program.Term
open import Program.TypeDeclaration

record Program : Set where
  constructor prog
  field
    declarations : List TypeDeclaration
    term : Term (constructorIds declarations)

open Program public