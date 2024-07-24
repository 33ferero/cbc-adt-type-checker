module TypeChecker.TypingRules  where

open import Prelude

open import Program.Term 
open import Program.Type
open import Util.Context
open import Util.Scope
open import Util.Relations
open import Util.Convert

private variable
  α : Scope
  n₁ n₂ n₃ : ℕ
  Δ' : TyContext n₂
  t t₁ t₂ : Type
  ts ts₁ ts₂ : List Type
  x x₁ x₂ n : String
  xs : List String
  e e₁ e₂ e₃ : Term α
  p : Pattern α
  ps : List (Pattern α)
  
mutual
  _⨾_⊢ᵖˢ_∶_⟶_ : Context α → TyContext n₁  → List (Pattern α) → Type → Type → Set
  Γ ⨾ Δ ⊢ᵖˢ ps ∶ fr ⟶ to = PatternListRule Γ Δ fr to ps

  _⨾_⊢ᵖ_∶_⟶_ : Context α → TyContext n₁ → Pattern α → Type → Type → Set
  Γ ⨾ Δ ⊢ᵖ p ∶ fr ⟶ to = PatternRule Γ Δ to fr p
  
  data _⨾_⊢_∶_ (Γ : Context α) (Δ : TyContext n₁) : Term α → Type → Set where
    ⊢`
      : (p : x ∈ α)
      ----------------------------------
      → Γ ⨾ Δ ⊢ ` x # p ∶ lookupVar Γ x p

    ⊢ƛ
      : Γ , x ∶ t₁ ⨾ Δ ⊢ e ∶ t₂
      → Δ ⊢ᵏ t₁
      -------------------------------
      → Γ ⨾ Δ ⊢ (ƛ x ∶ t₁ ⇒ e) ∶ t₁ ⇒ t₂

    ⊢·
      : Γ ⨾ Δ ⊢ e₁ ∶ (t₁ ⇒ t₂)
      → Γ ⨾ Δ ⊢ e₂ ∶ t₁
      ------------------------------------
      → Γ ⨾ Δ ⊢ e₁ · e₂ ∶ t₂

    ⊢Λ
      : ↑Γ Γ ⨾ Δ ,∙ ⊢ e ∶ t
      -------------------------------
      → Γ ⨾ Δ ⊢ (Λ e) ∶ `∀ t

    ⊢◦
      : Γ ⨾ Δ ⊢ e ∶ `∀ t₁
      → Δ ⊢ᵏ t₂
      ------------------------------------
      → Γ ⨾ Δ ⊢ e ◦ t₂ ∶ t₁ ⟦ t₂ ⟧ 

    ⊢true : 
      ----------------------------------
      Γ ⨾ Δ ⊢ `true ∶ `Bool

    ⊢false :
      ----------------------------------
      Γ ⨾ Δ ⊢ `false ∶ `Bool

    ⊢if
      : Γ ⨾ Δ ⊢ e₁ ∶ `Bool
      → Γ ⨾ Δ ⊢ e₂ ∶ t
      → Γ ⨾ Δ ⊢ e₃ ∶ t
      ------------------------------------
      → Γ ⨾ Δ ⊢ `if e₁ then e₂ else e₃ ∶ t

    ⊢zero :
      ----------------------------------
      Γ ⨾ Δ ⊢ `zero ∶ `ℕ

    ⊢suc
      : Γ ⨾ Δ ⊢ e ∶ `ℕ
      ----------------------------------
      → Γ ⨾ Δ ⊢ `suc e ∶ `ℕ

    ⊢case
      : Γ ⨾ Δ ⊢ e ∶ T n ts 
      → Γ ⨾ Δ ⊢ᵖˢ ps ∶ T n ts ⟶ t
      → (ctxToCons Γ n) ↭ (patsToCons ps)
      ------------------------------------
      → Γ ⨾ Δ ⊢ `case e of⟦ ps ⟧ ∶ t

  data PatternRule (Γ : Context α) (Δ : TyContext n₁) (t : Type) : Type → Pattern α → Set where
    `⊢ᵖ
      : {body : Term (reverse xs ++ α) }
      → (p : x ∈ α)
      → let type = lookupVar Γ x p
            instantiated = instantiateWith type ts
            patternVars = reverse xs
            constructorArgs = reverse (args instantiated)
        in target instantiated ≡ T n ts -- constructor matches scrutinee type
      → (eq : length patternVars ≡ length constructorArgs) -- pattern variables match constructor arity
      → (extendCtx Γ patternVars constructorArgs eq) ⨾ Δ ⊢ body ∶ t -- body is well-typed in extended context
      ----------------------------------
      → Γ ⨾ Δ ⊢ᵖ (` x # p ∶ xs ⟶ body) ∶ T n ts  ⟶ t

  data PatternListRule (Γ : Context α) (Δ : TyContext n₁) (t₁ : Type) (t₂ : Type)  : List (Pattern α) → Set where
    ⊢ᵖˢempty
      : Γ ⨾ Δ ⊢ᵖˢ [] ∶ t₁ ⟶ t₂

    ⊢ᵖˢcons
      : Γ ⨾ Δ ⊢ᵖ p ∶ t₁ ⟶ t₂
      → Γ ⨾ Δ ⊢ᵖˢ ps ∶ t₁ ⟶ t₂
      ------------------------------------
      → Γ ⨾ Δ ⊢ᵖˢ p ∷ ps ∶ t₁ ⟶ t₂

  data _⊢ᵏ_ (Δ : TyContext n₁) : Type → Set where
    ⊢ᵏℕ : 
      -------------------
      Δ ⊢ᵏ `ℕ

    ⊢ᵏBool : 
      ---------------------
      Δ ⊢ᵏ `Bool

    ⊢ᵏ⇒ 
      : Δ ⊢ᵏ t₁
      → Δ ⊢ᵏ t₂
      ----------------------
      → Δ ⊢ᵏ t₁ ⇒ t₂
    
    ⊢ᵏ∀ 
      : Δ ,∙ ⊢ᵏ t
      ----------------------
      → Δ ⊢ᵏ `∀ t

    ⊢ᵏT 
      : Δ ⨾ Δ ⊢ᵏ T x ts
      ----------------------
      → Δ ⊢ᵏ T x ts

    ⊢ᵏTVar
      : n₂ < n₁ -- if index is smaller than number of type variables in scope, then valid
      ----------------------
      → Δ ⊢ᵏ TVar n₂

  data _⨾_⊢ᵏ_ (Δ : TyContext n₁) : TyContext n₂ → Type → Set where

    ⊢ᵏT' 
      : x₁ ≡ x₂
      → length ts₁ ≡ length ts₂
      → Δ ⊢ᵏˢ ts₂
      ----------------------
      → Δ ⨾ Δ' , T x₁ ts₁  ⊢ᵏ T x₂ ts₂

    ⊢ᵏthere 
      : Δ ⨾ Δ' ⊢ᵏ t₁
      ----------------------
      → Δ ⨾ (Δ' , t₂) ⊢ᵏ t₁

    ⊢ᵏthere∙
      : Δ ⨾ Δ' ⊢ᵏ t₁
      ----------------------
      → Δ ⨾ (Δ' ,∙) ⊢ᵏ t₁

  data _⊢ᵏˢ_ (Δ : TyContext n₁) : List Type → Set where
    ⊢ᵏˢempty : Δ ⊢ᵏˢ []

    ⊢ᵏˢcons 
      : Δ ⊢ᵏ t 
      → Δ ⊢ᵏˢ ts 
      ---------------
      → Δ ⊢ᵏˢ (t ∷ ts)

  
infix 3 _⨾_⊢_∶_
infix 3 _⨾_⊢ᵖ_∶_⟶_
infix 3 _⨾_⊢ᵖˢ_∶_⟶_
infix 3 _⊢ᵏ_
infix 3 _⨾_⊢ᵏ_
infix 3 _⊢ᵏˢ_ 