module TypeChecker.TypeChecker where

open import Prelude

open import Program.Term
open import Program.Program
open import Program.TypeDeclaration
open import Program.Type
open import TypeChecker.TypingRules 
open import TypeChecker.ProgramWF
open import Util.Context
open import Util.Evaluator
open import Util.Scope
open import Util.PropertyEvaluator
open import Util.Convert
open import Util.Relations

private variable
  α : Scope
  n n' : ℕ

--------------------------------------------------------------------------
-- | Functions for showing that a type is equal to another type
convert : (a b : Type) → Evaluator (a ≡ b)
convert x y = evalEquiv x y _t≟_ ("unequal types: " s++ show x s++ ", " s++ show y)

--------------------------------------------------------------------------
-- | Functions for checking types are well-kinded
checkKind : (Δ : TyContext n) (t : Type) → Evaluator (Δ ⊢ᵏ t)
checkKind' : (Δ : TyContext n) (Δ' : TyContext n') (t : Type) → Evaluator (Δ ⨾ Δ' ⊢ᵏ t)
checkKinds : (Δ : TyContext n) (ts : List Type) → Evaluator (Δ ⊢ᵏˢ ts)

-- | Check a type is well-kinded
checkKind ctx `ℕ = return ⊢ᵏℕ
checkKind ctx `Bool = return ⊢ᵏBool
checkKind ctx (t₁ ⇒ t₂) = do
  k₁ ← checkKind ctx t₁
  k₂ ← checkKind ctx t₂
  return (⊢ᵏ⇒ k₁ k₂)
checkKind ctx (`∀ t) = do
  k ← checkKind (ctx ,∙) t
  return (⊢ᵏ∀ k)
checkKind ctx t@(T _ _) = do
  k ← checkKind' ctx ctx t
  return (⊢ᵏT k)
checkKind {n} _ (TVar x) = do
  k ← evalSmaller x n "Free type variable"
  return (⊢ᵏTVar k)

-- | Check types that require traversing the context
checkKind' ctx ∅ (T x _) = evalError ("Type " s++ x s++ " not in scope")
checkKind' ctx (rest , T t₁ tvs₁) ty@(T t₂ tvs₂) with checkKind' ctx rest ty | t₁ s≟ t₂
...   | inj₁ _ | yes refl = do
  name ← evalEquiv t₁ t₂ _s≟_ ("Type " s++ t₂ s++ " not in scope")
  length ← evalEquiv (length tvs₁) (length tvs₂) _ℕ≟_ ("Type " s++ t₂ s++ " not well formed")
  k ← checkKinds ctx tvs₂
  return (⊢ᵏT' name length k)
... | inj₁ err | no _ = evalError err
... | inj₂ k | _ = return (⊢ᵏthere k)
checkKind' ctx (rest , _) t@(T _ _)= do
  k ← checkKind' ctx rest t
  return (⊢ᵏthere k)
checkKind' ctx (rest ,∙) t@(T _ _)= do
  k ← checkKind' ctx rest t
  return (⊢ᵏthere∙ k)
checkKind' _ _ _ = evalError "Type not in scope"

-- | Check a list of types
checkKinds _ [] = return ⊢ᵏˢempty
checkKinds ctx (t ∷ ts) = do
  k <- checkKind ctx t
  ks <- checkKinds ctx ts
  return (⊢ᵏˢcons k ks)

--------------------------------------------------------------------------
-- | Function signatures for inferring and checking terms and patterns
inferTerm : ∀ (Γ : Context α) (Δ : TyContext n) (u : Term α)             → Evaluator (Σ[ t ∈ Type ] Γ ⨾ Δ ⊢ u ∶ t)
checkTerm : ∀ (Γ : Context α) (Δ : TyContext n) (u : Term α) (ty : Type) → Evaluator (Γ ⨾ Δ ⊢ u ∶ ty)

inferPattern : ∀ (Γ : Context α) (Δ : TyContext n) (p : Pattern α) (n : Type)        → Evaluator (Σ[ t ∈ Type ] Γ ⨾ Δ ⊢ᵖ p ∶ n ⟶ t)
inferPatterns : ∀ (Γ : Context α) (Δ : TyContext n) (ps : List (Pattern α)) (n : Type) → Evaluator (Σ[ t ∈ Type ] Γ ⨾ Δ ⊢ᵖˢ ps ∶ n ⟶ t)

-- | Type inference for terms
inferTerm ctx tyCtx (` x # index ) = do
  return (lookupVar ctx x index , ⊢` index )
inferTerm ctx tyCtx (ƛ x ∶ aTy ⇒ body) = do
  bTy , btd ← inferTerm (ctx , x ∶ aTy) tyCtx body
  kind ← checkKind tyCtx aTy
  return (aTy ⇒ bTy , ⊢ƛ btd kind)
inferTerm ctx tyCtx (lam · arg) = do
  (a ⇒ b) , ltd ← inferTerm ctx tyCtx lam
    where (t , _) → evalError ("application head should have a function type: " s++ show t )
  atd ← checkTerm ctx tyCtx arg a
  return (b , ⊢· ltd atd)
inferTerm ctx tyCtx (Λ u) = do
  t , td ← inferTerm (shiftCtx 0 ctx) (tyCtx ,∙) u
  return (`∀ t , ⊢Λ td)
inferTerm ctx tyCtx (tabs ◦ t) = do
  (`∀ ty) , atd ← inferTerm ctx tyCtx tabs
    where (t , _) → evalError ("type application head should have a function type: " s++ show t )
  kind ← checkKind tyCtx t
  return (substitute 0 t ty , ⊢◦ atd kind)
inferTerm ctx tyCtx (`case tc of⟦ ps ⟧) = do 
  n@(T adt _) , tcttu ← inferTerm ctx tyCtx tc
    where _ → evalError "can not pattern match on non-adt"
  t , pstd ← inferPatterns ctx tyCtx ps n
  eq ← evalSetEquiv (ctxToCons ctx adt) (patsToCons ps)
  return (t , (⊢case tcttu pstd eq)  )

-- additional language constructs, not necessarily tied to ADTs
inferTerm ctx tyCtx (`true) = return (`Bool , ⊢true)
inferTerm ctx tyCtx (`false) = return (`Bool , ⊢false)
inferTerm ctx tyCtx (`if c then t else f) = do
  ctd ← checkTerm ctx tyCtx c `Bool
  tTy , ttd ← inferTerm ctx tyCtx t
  fTy , ftd ← inferTerm ctx tyCtx f
  refl ← convert tTy fTy
  return (tTy , ⊢if ctd ttd ftd)
inferTerm ctx tyCtx (`zero) = return (`ℕ , ⊢zero)
inferTerm ctx tyCtx (`suc n) = do
  ntd ← checkTerm ctx tyCtx n `ℕ
  return (`ℕ , ⊢suc ntd)

-- | Type checking for terms
checkTerm ctx tyCtx term ty = do
  (t , tr) ← inferTerm ctx tyCtx term
  refl ← convert t ty
  return tr

-- | Inference for a pattern
inferPattern ctx tyCtx (` x # p ∶ xs ⟶ body) f@(T n ts) = do
  let type = lookupVar ctx x p
  let instantiated = instantiateWith type ts
  let patternVars = reverse xs
  let constructorArgs = reverse (args instantiated)
  ty ← convert (target instantiated) f
  eq ← evalEquiv (length patternVars) (length constructorArgs) _ℕ≟_ "Incorrect number of arguments in pattern"
  t , bu ← inferTerm (extendCtx ctx patternVars constructorArgs eq) tyCtx body
  return (t , `⊢ᵖ p ty eq bu)
inferPattern _ _ _ _ = evalError "pattern does not match type"

-- | Inference for a list of patterns
inferPatterns ctx tyCtx (x ∷ []) n = do
  t , bu ← inferPattern ctx tyCtx x n
  return (t , ⊢ᵖˢcons bu ⊢ᵖˢempty)
inferPatterns ctx tyCtx (x ∷ xs) n = do
  t , bu ← inferPattern ctx tyCtx x n
  t' , bu' ← inferPatterns ctx tyCtx xs n
  refl ← convert t t'
  return (t , ⊢ᵖˢcons bu bu')
inferPatterns _ _ [] _ = evalError "empty pattern" 

--------------------------------------------------------------------------
-- | Constraint checks for type declarations

-- | Check a data constructor
checkDataConstructor : (types : TyContext n) → (dc : DataConstructor) → Evaluator (DataConstructorWF types dc)
checkDataConstructor types ⟨ dc ∣ args ⟩ = do
  kinds ← checkKinds types args
  return (wf kinds)

-- | Check a type declaration
checkTypeDeclaration : (tcs : TyContext n) (td : TypeDeclaration) → Evaluator (TypeDeclarationWF tcs td)
checkTypeDeclaration tcs (`data ⟨ tc ^ tvs ⟩ `where dcs)  = do
  constructors ← evalAll dcs (checkDataConstructor (addTVars tvs tcs))
  return (wf constructors)

--------------------------------------------------------------------------
-- | Inference and checking for programs

-- | Perform constraint checks on declarations and infer type of program
inferProgram : Program → Evaluator (Σ[ t ∈ Type ] ProgramWF )
inferProgram (prog tds term) = do
  wellFormed ← evalAll tds (checkTypeDeclaration (makeTyCtx (types tds)))
  t , td ← inferTerm (declsToCtx tds) (makeTyCtx (types tds)) term
  return (t , wf wellFormed td)

-- | Type check a program
checkProgram : Program → Type → Evaluator ProgramWF
checkProgram p ty = do
  t , check ← inferProgram p
  refl ← convert t ty
  return check
 