module Program.TypeDeclaration where

open import Prelude


open import Program.Type hiding (args)

record DataConstructor : Set where
  constructor ⟨_∣_⟩
  field
    name : String
    args : List Type

record TypeConstructor : Set where
  constructor ⟨_^_⟩
  field
    name : String
    arity : ℕ
 
record TypeDeclaration : Set where
  constructor `data_`where_
  field
    type : TypeConstructor
    constructors : List DataConstructor 
    
open TypeDeclaration public

types : List TypeDeclaration → List Type
types = map (uncurry T ∘ < TypeConstructor.name , map TVar ∘ downFrom ∘ TypeConstructor.arity > ∘ type)

typeIds : List TypeDeclaration → List String
typeIds = map (TypeConstructor.name ∘ type)

constructorIds : List TypeDeclaration → List String
constructorIds = concat ∘ map (map DataConstructor.name ∘ constructors)

infix 5 `data_`where_
infix 9 ⟨_∣_⟩
infix 9 ⟨_^_⟩