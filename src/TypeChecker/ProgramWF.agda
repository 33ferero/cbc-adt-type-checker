module TypeChecker.ProgramWF where

open import Prelude

open import Program.Program
open import Program.TypeDeclaration 
open import Program.Type
open import Util.Context
open import Program.Term
open import TypeChecker.TypingRules
open import Util.Scope
open import Util.Convert
open import Util.Relations

private variable
  n : ℕ

  -- Well-formedness check for 

-- checks that all arguments of a constructor are well-kinded
data DataConstructorWF (types : TyContext n) : DataConstructor → Set where
  wf : {name : String} {args : List Type}
    → types ⊢ᵏˢ args
    → DataConstructorWF types (⟨ name ∣ args ⟩)

-- checks that all constructors are valid
data TypeDeclarationWF (types : TyContext n) : TypeDeclaration → Set where
  wf : {type : String} {arity : ℕ} {constructors : List DataConstructor}
    → All (DataConstructorWF (addTVars arity types)) constructors
    → TypeDeclarationWF types (`data ⟨ type ^ arity ⟩ `where constructors)

data ProgramWF : Set where
 wf : {declarations : List TypeDeclaration} {term : Term (constructorIds declarations)} {type : Type}
    → All (TypeDeclarationWF (makeTyCtx (types declarations))) declarations
    → (declsToCtx declarations) ⨾ (makeTyCtx (types declarations)) ⊢ term ∶ type
    → ProgramWF
   