module Util.PropertyEvaluator where

open import Prelude

open import Util.Evaluator
open import Util.Relations
open import Util.Scope
open import Util.Context

private variable
  α : Scope
  A : Set

-- | Evaluator for whether a boolean is true
evalIsTrue : (b : Bool) → String → Evaluator (IsTrue b)
evalIsTrue true _ = return isTrue
evalIsTrue false s = evalError s

-- | Evaluator for whether a variable is in a list
evalElem : (x : String) -> (xs : List String) -> Evaluator (x ∈ xs)
evalElem x [] = evalError ("not found: " s++ x)
evalElem x (y ∷ xs) with x s≟ y
... | yes refl = return here
... | no _ = there <$> evalElem x xs

-- | Evaluator for whether set is a subset of another set
evalSubset : (xs ys : List String) -> Evaluator (xs ⊆ ys)
evalSubset [] ys = return ⊆empty
evalSubset (x ∷ xs) ys = do
  p ← evalElem x ys
  ps ← evalSubset xs ys
  return (⊆there p ps)

-- | Evaluator for whether two sets are equivalent (ignoring duplicates)
evalSetEquiv : (xs ys : List String) -> Evaluator (xs ↭ ys)
evalSetEquiv xs ys = do
  p₁ ← evalSubset xs ys
  p₂ ← evalSubset ys xs
  return (pequiv p₁ p₂)

evalEquiv : (a b : A) → ((x y : A) → Dec (x ≡ y)) → String → Evaluator (a ≡ b)
evalEquiv a b f err with f a b
... | yes refl = return refl
... | no _ = evalError err

-- | Evaluator for whether a variable is not in a list
evalNotElem : (x : String) -> (xs : List String) → String -> Evaluator (x ∉ xs)
evalNotElem x [] err = return ∉empty
evalNotElem x (y ∷ xs) err with x s≟ y
... | yes refl = evalError err
... | no p = ∉there p <$> evalNotElem x xs err

-- | Evaluator for whether a list is unique
evalUniqueList : (xs : List String) → String -> Evaluator (UniqueList xs)
evalUniqueList [] err = return uniqueEmpty
evalUniqueList (x ∷ xs) err = do
  p ← evalNotElem x xs err
  ps ← evalUniqueList xs err
  return (uniqueCons p ps)


-- | Evaluator for finding the index of a variable in a context
findIndex : (Γ : Context α) → (x : String) → Evaluator (x ∈ α)
findIndex ∅ x = evalError ("Variable \"" s++ x s++ "\" not found in scope.")
findIndex {a} _ x = evalElem x a

-- | Evaluator for the All relation
evalAll : {p : A → Set} → (xs : List A) → ((x : A) → Evaluator (p x)) → Evaluator (All p xs)
evalAll [] _ = return []
evalAll (x ∷ xs) f = do
  p ← f x
  ps ← evalAll xs f
  return (p ∷ₐ ps)  

-- | Evaluator for whether a number is smaller than another number
evalSmaller : (a b : ℕ) → String → Evaluator (a < b)
evalSmaller zero (suc b) err = return <z
evalSmaller (suc a) (suc b) err = <s <$> evalSmaller a b err
evalSmaller _ _ err = evalError err