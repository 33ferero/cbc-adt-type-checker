module Program.Type where

open import Prelude
  
data Type : Set where
  `ℕ : Type
  `Bool : Type
  _⇒_ : (a b : Type) → Type
  T : String → List Type → Type
  `∀ : Type → Type
  TVar : ℕ → Type

------------------------------------------------------------
-- | Functions for DeBruijn substitution

-- | Shifting of types
shift : ℕ → Type → Type
shift' : ℕ → List Type → List Type

-- ↓ if n < m, its binder is closer than the one we are shifting for and so its index remains
-- ↓ otherwise, we increase the index by one
shift n (TVar m) = TVar (punchIn n m)
shift n (a ⇒ b) = shift n a ⇒ shift n b
shift n (`∀ a) = `∀ (shift (suc n) a)
shift n (T x ts) = T x (shift' n ts)
shift n `ℕ = `ℕ
shift n `Bool = `Bool
-- mutual recursion so need to convince termination checker
shift' n [] = []
shift' n (x ∷ xs) = shift n x ∷ shift' n xs 

↑t : Type → Type
↑t = shift 0

-- | Substitution of types
substitute : ℕ → Type → Type → Type
substitute' : ℕ → Type → List Type → List Type

-- ↓ if n == m replace, n < m keep index the same since binder is closer than the one we removed
-- ↓ n > m decrease index by one to account for the removed abstraction
substitute n s (TVar m) with n ℕ≟ m
... | yes refl = s
... | no p = TVar (punchOut n m {p})
substitute n s (a ⇒ b) = substitute n s a ⇒ substitute n s b
--  ↓ shift free variables in substitution and increase index since we are substituting under a binder
substitute n s (`∀ a) = `∀ (substitute (suc n) (↑t s) a) 
substitute n s `ℕ = `ℕ
substitute n s `Bool = `Bool
substitute n s (T x ts) = T x (substitute' n s ts)
-- mutual recursion so need to convince termination checker
substitute' n s [] = []
substitute' n s (x ∷ xs) = substitute n s x ∷ substitute' n s xs

_⟦_⟧ : Type → Type → Type
t ⟦ s ⟧ = substitute 0 s t

-- | Series of substitutions
instantiateWith : Type → List Type → Type
instantiateWith (`∀ body) (t ∷ ts)  = instantiateWith (body ⟦ t ⟧) ts
instantiateWith t _ = t

------------------------------------------------------------
-- | Auxiliary functions for working with types

-- | Function for finding the result of a function or the type itself
target : Type → Type
target (_ ⇒ a) = target a
target a = a

-- | Function for finding the arguments of a function
args : Type → List Type
args (arg ⇒ a) = arg ∷ args a
args a = []

-- | Functions for showing types
show : Type → String
show' : List Type → String

show `ℕ = "ℕ"
show `Bool = "Bool"
show (a ⇒ b) = show a s++ " ⇒ " s++ show b
show (T x ts) = x s++ " [" s++ (show' ts) s++ "]"
show (`∀ body) = "∀ " s++ (show body)
show (TVar x) = "TVar " s++ showNat x

show' [] = ""
show' (x ∷ []) = show x
show' (x ∷ xs) = show x s++ ", " s++ show' xs 

infixr 5 _⇒_
infixr 5 `∀
infix 9 TVar
infix 9 T

-- | Decidability for types
_t≟_ : Decidable {A = Type} _≡_
_t≟'_ : Decidable {A = List Type} _≡_

`ℕ t≟ `ℕ = yes refl
`ℕ t≟ `Bool = no λ ()
`ℕ t≟ (_ ⇒ _) = no λ ()
`ℕ t≟ (T _ _) = no λ ()
`ℕ t≟ (`∀ _) = no λ ()
`ℕ t≟ (TVar _) = no λ ()

`Bool t≟ `Bool = yes refl
`Bool t≟ `ℕ = no λ ()
`Bool t≟ (_ ⇒ _) = no λ ()
`Bool t≟ (T _ _) = no λ ()
`Bool t≟ (`∀ _) = no λ ()
`Bool t≟ (TVar _) = no λ ()

(a₁ ⇒ b₁) t≟ (a₂ ⇒ b₂) with a₁ t≟ a₂ | b₁ t≟ b₂
... | yes refl | yes refl = yes refl
... | no p | _ = no λ { refl → p refl }
... | _ | no p = no λ { refl → p refl }
(_ ⇒ _) t≟ `ℕ = no λ ()
(_ ⇒ _) t≟ `Bool = no λ ()
(_ ⇒ _) t≟ (T _ _) = no λ ()
(_ ⇒ _) t≟ (`∀ _) = no λ ()
(_ ⇒ _) t≟ (TVar _) = no λ ()

(T x₁ ts₁) t≟ (T x₂ ts₂) with x₁ s≟ x₂ | ts₁ t≟' ts₂
... | yes refl | yes refl = yes refl
... | no p | _ = no λ { refl → p refl }
... | _ | no p = no λ { refl → p refl }
(T _ _) t≟ `ℕ = no λ ()
(T _ _) t≟ `Bool = no λ ()
(T _ _) t≟ (_ ⇒ _) = no λ ()
(T _ _) t≟ (`∀ _) = no λ ()
(T _ _) t≟ (TVar _) = no λ ()

(`∀ a₁) t≟ (`∀ a₂) with a₁ t≟ a₂
... | yes refl = yes refl
... | no p = no λ { refl → p refl }

(`∀ _) t≟ `ℕ = no λ ()
(`∀ _) t≟ `Bool = no λ ()
(`∀ _) t≟ (_ ⇒ _) = no λ ()
(`∀ _) t≟ (T _ _) = no λ ()
(`∀ _) t≟ (TVar _) = no λ ()

(TVar x₁) t≟ (TVar x₂) with x₁ ℕ≟ x₂
... | yes refl = yes refl
... | no p = no λ { refl → p refl }
(TVar _) t≟ `ℕ = no λ ()
(TVar _) t≟ `Bool = no λ ()
(TVar _) t≟ (_ ⇒ _) = no λ ()
(TVar _) t≟ (T _ _) = no λ ()
(TVar _) t≟ (`∀ _) = no λ ()

[] t≟' [] = yes refl
(x ∷ xs) t≟' (y ∷ ys) with x t≟ y | xs t≟' ys
... | yes refl | yes refl = yes refl
... | no p | _ = no λ {refl → p refl}
... | _ | no p = no λ {refl → p refl}
[] t≟' (y ∷ ys) = no λ ()
(x ∷ xs) t≟' [] = no λ ()
 