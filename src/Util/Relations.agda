module Util.Relations where

open import Prelude

private variable
  A : Set
  x y : A
  xs ys : List A
  n m : ℕ

data _∈_ (x : A) : List A -> Set where
  here  : x ∈ (x ∷ xs)
  there : x ∈ xs → x ∈ (y ∷ xs)

data _⊆_ {A : Set} : List A -> List A -> Set where
  ⊆empty  : [] ⊆ ys
  ⊆there  : x ∈ ys → xs ⊆ ys → (x ∷ xs) ⊆ ys

data _↭_ {A : Set} (xs ys : List A) : Set where
  pequiv : xs ⊆ ys → ys ⊆ xs → xs ↭ ys -- for this specific usecase we do not care about duplicates
 
data _∉_ {A : Set} (x : A) : List A → Set where
  ∉empty  : x ∉ []
  ∉there  : x ≢  y → x ∉ ys → x ∉ (y ∷ ys)
  
data UniqueList {A : Set} : List A -> Set where
  uniqueEmpty : UniqueList []
  uniqueCons  : x ∉ xs → UniqueList xs → UniqueList (x ∷ xs)

data IsTrue : Bool → Set where
  isTrue : IsTrue true

data _<_ : ℕ → ℕ → Set where
  <z : zero < suc n
  <s : n < m → suc n < suc m