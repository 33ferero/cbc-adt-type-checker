module Util.Convert where

open import Prelude

open import Program.TypeDeclaration
open import Program.Type
open import Program.Term
open import Util.Context
open import Util.Relations
open import Util.Scope

private variable
  α : Scope

-- | Converts a list of type declarations to a context
declsToCtx : (tds : List TypeDeclaration) → Context (constructorIds tds)
declsToCtx [] = ∅
declsToCtx (td ∷ tds) = mergeCtx (go (constructors td)) (declsToCtx tds)
  where
    tc = type td
    arity = TypeConstructor.arity tc
    go : (cs : List DataConstructor) → Context (map DataConstructor.name cs)
    go [] = ∅
    go (dc ∷ dcs) = go dcs , DataConstructor.name dc ∶
      let targetType = T (TypeConstructor.name tc) (map TVar (downFrom arity))
          functionType = foldr _⇒_ targetType (DataConstructor.args dc)
          in foldr (λ _ → `∀) functionType (downFrom arity)

-- | Converts a context to a list of constructors of the given type
ctxToCons : Context α → String → List String
ctxToCons ctx s = filter isCapitalized (go ctx s)
  where
  go : Context α → String → List String
  go ∅ s = []
  go (ctx , x ∶ T n _) s with s s≟ n 
  ... | yes refl = x ∷ go ctx s
  ... | no _ = go ctx s
  go (ctx , x ∶ (_ ⇒ to)) s with (target to)
  ... | (T s₁ _) with s s≟ s₁
  ...             | yes refl = x ∷ (go ctx s)
  ...             | no _ = go ctx s
  go (ctx , x ∶ (_ ⇒ to)) s | _ = go ctx s  
  go (ctx , x ∶ (`∀ to)) s = go (ctx , x ∶ to) s
  go (ctx , _ ∶ _) s = go ctx s

-- | Converts a list of patterns to the constructors they match
patsToCons : List (Pattern α) → List String
patsToCons = foldr (λ where
  (` c # _ ∶ _ ⟶ _ ) → (c ∷_)) []