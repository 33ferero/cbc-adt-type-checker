module Programs where

open import Prelude

open import Program.Term  
open import Program.Program
open import TypeChecker.ProgramWF
open import Program.TypeDeclaration
open import TypeChecker.TypeChecker
open import Program.Type
open import TypeChecker.TypingRules
open import Util.Context 
open import Util.Evaluator
open import Util.Scope
open import Util.Relations

private
  open import Agda.Builtin.Equality

  open import Effect.Monad
  open RawMonad ⦃ ... ⦄

  -- | Test case record for type checking tests
  record TestCase : Set where
    constructor test
    field
      description : String
      program : Program
      shouldPass : Bool
      expected : Maybe Type  -- Nothing for inference tests
      error : Maybe String  -- Expected error for failing tests

open TestCase

-- | Verification function that returns a type for proof obligations
verify : TestCase → Set
verify tc with TestCase.shouldPass tc | TestCase.expected tc | TestCase.error tc
... | true | just ty | _ = ∃[ proof ] (checkProgram (TestCase.program tc) ty ≡ inj₂ proof)
... | false | just ty | just err = checkProgram (TestCase.program tc) ty ≡ inj₁ err
... | false | just ty | nothing = ⊥  
... | true | nothing | _ = ∃[ result ] (inferProgram (TestCase.program tc) ≡ inj₂ result)
... | false | nothing | just err = inferProgram (TestCase.program tc) ≡ inj₁ err
... | false | nothing | nothing = ⊥  


-- | Test case definitions
module TestCases where

  test0 : TestCase
  test0 = record {
    description = "Complex List type with nested quantifiers" ;
    program = prog
    ((`data ⟨ "List" ^ 1 ⟩ `where 
      ((⟨ "Cons" ∣ (TVar 0 ∷ T "List" (TVar 0 ∷ []) ∷ []) ⟩) ∷ 
       (⟨ "Nil" ∣ [] ⟩) ∷ [])) ∷ [])
    (((Λ (Λ (Λ (ƛ "x" ∶ T "List" (((`∀ (TVar 2 ⇒ TVar 1)) ⇒ TVar 0) ∷ []) ⇒ (` "x" # here) ))) ◦ TVar 0)) ◦ `Bool ◦ `ℕ) ;
    shouldPass = true ;
    expected = just (T "List" (((`∀ (`Bool ⇒ `ℕ)) ⇒ `ℕ) ∷ []) ⇒ T "List" (((`∀ (`Bool ⇒ `ℕ)) ⇒ `ℕ) ∷ [])) ;
    error = nothing }
    
  check0 : verify test0
  check0 = (_ , refl)

  -- Correct programs
  {-
    program1 :: List a -> Maybe a
    program1 = \(x :: List a) -> case x of
      Cons v t -> Just v
      Nil -> Nothing  
  -}  
  test1 : TestCase
  test1 = record {
    description = "head" ;
    program = prog 
    ((`data ⟨ "Maybe" ^ 1 ⟩ `where 
        ⟨ "Just" ∣ (TVar 0 ∷ []) ⟩ ∷ 
        ⟨ "Nothing" ∣ [] ⟩ ∷ []) ∷ 
    (`data ⟨ "List" ^ 1 ⟩ `where 
      ((⟨ "Cons" ∣ (TVar 0 ∷ T "List" (TVar 0 ∷ []) ∷ []) ⟩) ∷ 
       (⟨ "Nil" ∣ [] ⟩) ∷ [])) ∷ [])
    (Λ (ƛ "x" ∶ T "List" (TVar 0 ∷ []) ⇒ 
      `case ` "x" # here of⟦ 
        ((` "Cons" # there (there (there here))  ∶ ("v" ∷ "t" ∷  []) ⟶ ((` "Just" # there (there (there here)) ◦ TVar 0) · ` "v" # there here)) ∷
        ((` "Nil" # there (there (there (there here)))  ∶ [] ⟶ ` "Nothing" # there (there here) ◦ TVar 0)
        ∷ [])) 
      ⟧)) ;
    shouldPass = true ;
    expected = just (`∀ ((T "List" (TVar 0 ∷ [])) ⇒ (T "Maybe" (TVar 0 ∷ [])))) ;
    error = nothing }
  
  check1 : verify test1  
  check1 = (_ , refl)

  {-
    program2 :: Either Bool Int -> Pair Bool Int
    program2 = \(x :: Either Bool Int) -> case x of
      Left a -> P a 0
      Right b -> P False b
   -}
  test2 : TestCase
  test2 = record {
    description = "Either Bool Int -> Pair Bool Int" ;
    program = prog 
    ((`data ⟨ "Either" ^ 2 ⟩ `where (⟨ "Left" ∣ (TVar 1 ∷ []) ⟩) ∷ (⟨ "Right" ∣ (TVar 0 ∷ []) ⟩ ∷ [])) ∷
    (`data ⟨ "Pair" ^ 2 ⟩ `where (⟨ "P" ∣ (TVar 1 ∷ TVar 0 ∷ []) ⟩ ∷ [])) ∷ [])
    
    (ƛ "x" ∶ T "Either" (`Bool ∷ `ℕ ∷ []) ⇒ 
      `case ` "x" # here of⟦ 
        ((` "Left" # there here  ∶ ("v" ∷  []) ⟶ (((` "P" # there (there (there (there here)))  ◦ `Bool) ◦ `ℕ) · ` "v" # here · `zero)) ∷
        ((` "Right" # there (there here) ∶ ("v" ∷  []) ⟶ (((` "P" # there (there (there (there here)))  ◦ `Bool) ◦ `ℕ) · `false · ` "v" # here))
        ∷ [])) 
      ⟧) ;
    shouldPass = true ;
    expected = just (T "Either" (`Bool ∷ `ℕ ∷ []) ⇒ T "Pair" (`Bool ∷ `ℕ ∷ [])) ;
    error = nothing }
  
  check2 : verify test2
  check2 = (_ , refl)

  {-
    program3 :: Int
    program3 = case program2 (Left True) of
      P a b -> if a then b else 0
  -}
  test3 : TestCase  
  test3 = record {
    description = "Case analysis with application returning Int" ;
    program = prog
    (declarations (program test2))
    (`case (term (program test2)) · ((((` "Left" # here ◦ `Bool) ◦ `ℕ) · `false)) of⟦
      ((` "P" # there (there here)  ∶ ("a" ∷ "b" ∷  []) ⟶ (`if ` "a" # there here then ` "b" # here else `zero ))  ∷ [])
    ⟧) ;
    shouldPass = true ;
    expected = just `ℕ ;
    error = nothing }
  
  check3 : verify test3
  check3 = (_ , refl)

  {-
    program29 :: List (List (List A)) -> Int
    program29 = \(x :: List (List (List A)) -> Int) -> case x of
      Nil -> 0
      Cons v t -> 
        case v of
          Nil -> 0
          Cons v t =>
            case v of
              Cons v t -> v
              Nil -> 0
  -}
  test4 : TestCase
  test4 = record {
    description = "Nested List processing" ;
    program = prog
    (declarations (program test1))
    (Λ ƛ "x" ∶ T "List" (T "List" (T "List" (TVar 0 ∷ []) ∷ []) ∷ []) ⇒ 
      `case ` "x" # here of⟦ 
        ((` "Nil" # there (there (there (there here)))  ∶ [] ⟶ ` "Nothing" # there (there here) ◦ TVar 0) ∷
        ((` "Cons" # there (there (there here))  ∶ ("v" ∷ "t" ∷  []) ⟶ 
          `case ` "v" # there here of⟦ 
            ((` "Nil" # there (there (there (there (there (there here)))))  ∶ [] ⟶ ` "Nothing" # there (there (there (there here))) ◦ TVar 0) ∷
            ((` "Cons" # there (there (there (there (there here)))) ∶ ("v" ∷ "t" ∷  []) ⟶ 
              `case ` "v" # there here of⟦ 
                ((` "Cons" # there (there (there (there (there (there (there here))))))  ∶ ("v" ∷ "t" ∷  []) ⟶ ` "Just" # there (there (there (there (there (there (there here)))))) ◦ TVar 0 · ` "v" # there here) ∷
                ((` "Nil" # there (there (there (there (there (there (there (there here)))))))  ∶ [] ⟶ ` "Nothing" # there (there (there (there (there (there here))))) ◦ TVar 0) ∷ [])) 
              ⟧) ∷ [])) 
          ⟧) ∷ [])) 
      ⟧) ;
    shouldPass = true ;
    expected = just (`∀ (T "List" (T "List" (T "List" (TVar 0 ∷ []) ∷ []) ∷ []) ⇒ T "Maybe" (TVar 0 ∷ []))) ;
    error = nothing }
  
  check4 : verify test4  
  check4 = (_ , refl)

  {-
    program30 :: List (List (List A)) -> Int
    program30 = program29 Cons (Cons (Cons 1 Nil) Nil) Nil
  -}
  test5 : TestCase
  test5 = record {
    description = "Application of nested List function" ;
    program = prog
    (declarations (program test4))
    ((term (program test4)) ◦ `ℕ 
    · (` "Cons" # there (there here) ◦ (T "List" (T "List" (`ℕ ∷ []) ∷ [])) 
    · (` "Cons" # there (there here) ◦ (T "List" (`ℕ ∷ [])) 
    · (` "Cons" # there (there here) ◦ `ℕ · `zero · (` "Nil" # there (there (there here)) ◦ `ℕ)) 
    · (` "Nil" # there (there (there here)) ◦ (T "List" (`ℕ ∷ [])))) · (` "Nil" # there (there (there here)) ◦ (T "List" (T "List" (`ℕ ∷ []) ∷ []))))) ;
    shouldPass = true ;
    expected = just (T "Maybe" (`ℕ ∷ [])) ;
    error = nothing }
  
  check5 : verify test5
  check5 = (_ , refl)

  -- INCORRECT PROGRAMS
  test6 : TestCase
  test6 = record {
    description = "Application to type abstracted function" ;
    program = prog
    (declarations (program test2))
    (` "Left" # here · `zero) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "application head should have a function type: ∀ ∀ TVar 1 ⇒ Either [TVar 1, TVar 0]" }
  
  check6 : verify test6
  check6 = refl
  
  test7 : TestCase  
  test7 = record {
    description = "Application with wrong type" ;
    program = prog
    (declarations (program test2))
    (((` "Left" # here ◦ `Bool) ◦ `ℕ) · `zero) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "unequal types: ℕ, Bool" }
  
  check7 : verify test7
  check7 = refl

  test8 : TestCase
  test8 = record {
    description = "Case match with non-ADT" ;
    program = prog 
    []
    `case `zero of⟦ [] ⟧ ;
    shouldPass = false ;
    expected = nothing ;
    error = just "can not pattern match on non-adt" }
  
  check8 : verify test8
  check8 = refl
  
  test9 : TestCase
  test9 = record {
    description = "Case match with constructor for wrong type" ;
    program = prog
    (declarations (program test2))
    (ƛ "x" ∶ T "Either" (`Bool ∷ `ℕ ∷ []) ⇒ 
      `case ` "x" # here of⟦ 
        ((` "Left" # there here  ∶ ("v" ∷  []) ⟶ (((` "P" # there (there (there (there here)))  ◦ `Bool) ◦ `ℕ) · ` "v" # here · `zero)) ∷
        ((` "P" # there (there (there here)) ∶ ("v" ∷ "b" ∷  []) ⟶ (((` "P" # there (there (there (there (there here))))  ◦ `Bool) ◦ `ℕ) · ` "v" # there here · ` "b" # here))
        ∷ [])) 
      ⟧) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "unequal types: Pair [Bool, ℕ], Either [Bool, ℕ]" }
  
  check9 : verify test9  
  check9 = refl

  test10 : TestCase
  test10 = record {
    description = "Case match with incomplete constructors" ;
    program = prog
    ((`data (⟨ "ADT" ^ 0 ⟩) `where ((⟨ "A" ∣ [] ⟩) ∷ (⟨ "B" ∣ [] ⟩) ∷ [])) ∷ [])
    (`case ` "A" # here of⟦ (
      (` "A" # here ∶ [] ⟶ `zero) ∷ [])
    ⟧) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "not found: B" }
  
  check10 : verify test10
  check10 = refl

  test11 : TestCase
  test11 = record {
    description = "Incorrect number of pattern variables" ;
    program = prog
    ((`data (⟨ "ADT" ^ 0 ⟩) `where ((⟨ "A" ∣ (`Bool ∷ []) ⟩) ∷ [])) ∷ [])
    (`case (` "A" # here · `false) of⟦
      ((` "A" # here  ∶ ("a" ∷ "b" ∷ []) ⟶ (`zero)) ∷ [])
    ⟧) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "Incorrect number of arguments in pattern" }
  
  check11 : verify test11
  check11 = refl

  test12 : TestCase  
  test12 = record {
    description = "Case branches with different return types" ;
    program = prog
    ((`data (⟨ "ADT" ^ 0 ⟩) `where ((⟨ "A" ∣ [] ⟩) ∷ (⟨ "B" ∣ [] ⟩) ∷ [])) ∷ [])
    (`case ` "A" # here of⟦ (
        (` "A" # here ∶ [] ⟶ `zero) ∷ 
        (` "B" # there here ∶ [] ⟶ `false) ∷ []) 
      ⟧) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "unequal types: ℕ, Bool" }
  
  check12 : verify test12
  check12 = refl

  -- DATA CONSTRUCTOR FAILURES
  test13 : TestCase
  test13 = record {
    description = "Free variables in constructor" ;
    program = prog
    ((`data (⟨ "ADT" ^ 1 ⟩) `where ((⟨ "A" ∣ (TVar 1 ∷ []) ⟩)∷ [])) ∷ [])
    `zero ;
    shouldPass = false ;
    expected = nothing ;
    error = just "Free type variable" }
  
  check13 : verify test13
  check13 = refl
  
  test14 : TestCase
  test14 = record {
    description = "Nonexistent type as constructor argument" ;
    program = prog
    ((`data (⟨ "ADT" ^ 0 ⟩) `where ((⟨ "A" ∣ (T "NonExistant" [] ∷ []) ⟩) ∷ [])) ∷ [])
    `zero ;
    shouldPass = false ;
    expected = nothing ;
    error = just "Type NonExistant not in scope" }
  
  check14 : verify test14  
  check14 = refl
  
  test15 : TestCase
  test15 = record {
    description = "Wrong number of type variables for type constructor" ;
    program = prog
    ((`data (⟨ "A" ^ 1 ⟩) `where ((⟨ "Construclctor1" ∣ [] ⟩)∷ [])) ∷
     (`data (⟨ "B" ^ 0 ⟩) `where ((⟨ "Constructor2" ∣ ((T "A" []) ∷ []) ⟩) ∷ [])) ∷ [])
    `zero ;
    shouldPass = false ;
    expected = nothing ;
    error = just "Type A not well formed" }
  
  check15 : verify test15
  check15 = refl

  test16 : TestCase
  test16 = record {
    description = "Nonexistent type in lambda" ;
    program = prog
    []
    (ƛ "x" ∶ T "List" [] ⇒ `zero) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "Type List not in scope" }
  
  check16 : verify test16
  check16 = refl

  test17 : TestCase
  test17 = record {
    description = "Wrong number of type arguments for ADT" ;
    program = prog
    ((`data (⟨ "List" ^ 1 ⟩) `where 
      ((⟨ "Cons" ∣ (TVar 0 ∷ T "List" (TVar 0 ∷ []) ∷ []) ⟩) ∷ 
      (⟨ "Nil" ∣ [] ⟩ ∷ [])))∷ [])
      
    (ƛ "x" ∶ T "List" [] ⇒ ` "x" # here) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "Type List not well formed" }
  
  check17 : verify test17
  check17 = refl
 
 -- KIND CHECK FAILURES
  test18 : TestCase  
  test18 = record {
    description = "Free type variable in lambda argument" ;
    program = prog
    []
    (ƛ "x" ∶ TVar 0 ⇒ `zero) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "Free type variable" }
  
  check18 : verify test18
  check18 = refl

  test19 : TestCase
  test19 = record {
    description = "Free type variable in lambda body" ;
    program = prog
    []
    (ƛ "x" ∶ `ℕ ⇒ (Λ `zero) ◦ TVar 0) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "Free type variable" }
  
  check19 : verify test19
  check19 = refl

  test20 : TestCase
  test20 = record {
    description = "Free type variable in forall" ;
    program = prog
    []
    (Λ (Λ `zero) ◦ TVar 1) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "Free type variable" }
  
  check20 : verify test20
  check20 = refl

  test21 : TestCase
  test21 = record {
    description = "Free type variable in type parameter" ;
    program = prog
    ((`data ⟨ "A" ^ 3 ⟩ `where ((⟨ "B" ∣ [] ⟩) ∷ [])) ∷ [])
    (ƛ "x" ∶ T "A" (`ℕ ∷ `ℕ ∷ TVar 1 ∷ []) ⇒ `zero) ;
    shouldPass = false ;
    expected = nothing ;
    error = just "Free type variable" }
  
  check21 : verify test21
  check21 = refl