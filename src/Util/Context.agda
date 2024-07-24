module Util.Context where

open import Prelude

open import Program.Type
open import Util.Evaluator
open import Util.Relations
open import Util.Scope

private variable
  α β : Scope
  n m : ℕ

data Context : Scope → Set where
  ∅ : Context Φ
  _,_∶_ : Context α → (x : String) → Type → Context (x ∷ α)

data TyContext : ℕ → Set where
  ∅ : TyContext 0
  _,_ : TyContext n → Type → TyContext n
  _,∙ : TyContext n → TyContext (suc n)

-- | Lookup a variable in the context given the index
lookupVar : (Γ : Context α) (x : String) (p : x ∈ α) → Type
lookupVar (_ , _ ∶ v   ) x here = v
lookupVar (ctx , _ ∶ _) x (there p) = lookupVar ctx x p

-- | Converting a list of types to a TyContext (used for declarations)
countTVars  : List Type → ℕ
countTVars  = foldr (λ where
  (TVar _) → suc
  _ → id) 0

-- | Extendending the TyContext with a specific number of type variables
addTVars : {n : ℕ} (m : ℕ) → TyContext n → TyContext (m + n)
addTVars 0 ctx = ctx
addTVars (suc m) ctx = addTVars m ctx ,∙


-- | Converts a list of types to a TyContext
makeTyCtx : (xs : List Type) → TyContext (countTVars xs)
makeTyCtx [] = ∅
makeTyCtx (TVar x ∷ xs) = makeTyCtx xs ,∙
makeTyCtx (`ℕ ∷ xs) = makeTyCtx xs , `ℕ
makeTyCtx (`Bool ∷ xs) = makeTyCtx xs , `Bool
makeTyCtx (t@(_ ⇒ _) ∷ xs) = makeTyCtx xs , t
makeTyCtx (t@(T _ _) ∷ xs) = makeTyCtx xs , t
makeTyCtx (t@(`∀ _) ∷ xs) = makeTyCtx xs , t

-- | Merge two contexts
mergeCtx : Context α → Context β → Context (α ++ β)
mergeCtx ∅ ctx = ctx
mergeCtx  (ctx , x ∶ t) ctx₁ = mergeCtx ctx ctx₁ , x ∶ t    

-- | Shift every binding in a context
shiftCtx : ℕ → Context α → Context α
shiftCtx n ∅ = ∅
shiftCtx n (ctx , x ∶ t) = shiftCtx n ctx , x ∶ shift n t

↑Γ : Context α → Context α
↑Γ = shiftCtx 0

-- | Function for extending the context with a list of bindings
extendCtx : Context α → (ns : List String) → (ts : List Type) → (length ns) ≡ (length ts) → Context (ns ++ α)
extendCtx ctx [] [] _ = ctx
extendCtx ctx (n ∷ ns) (t ∷ ts) p  = (extendCtx ctx ns ts (cong pred p)) , n ∶ t

