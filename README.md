# Correct-by-Construction Type-Checking for Algebraic Data Types

This repository contains a correct-by-construction type-checker for a toy language involving algebraic data types (ADT), pattern matching and polymorphism. The toy language is based on System F, and the ADT syntax is based on the Haskell syntax. A paper detailing the type-checker can be found [here](https://resolver.tudelft.nl/uuid:91825f78-d97c-47ed-b0f1-7ce498e523d1). The code was changed slightly for clarity since the paper was written, but the core ideas remain the same.

## Repository Structure
The code is structured as follows:
- `Program/` contains the syntax of the toy language, as well as some helper functions.
  - `Program` contains the AST for top-level programs, consisting of a list of data type declarations and a term.
  - `Term` contains the AST for terms and patterns that are used to destruct ADTs.
  - `Type` contains the AST for types and some helper function, e.g. for De Bruijn indexing.
  - `TypeDeclaration` contains the AST for ADT type declarations.
- `TypeChecker/` contains the type-checker implementation.
  - `ProgramWF` contains the definition for full-program well-formedness, i.e. combining declarations and terms.
  - `TypeChecker` contains the main type-, kind- and program-checking algorithms.
  - `TypingRules` contains the typing rules as described in the paper.
- `Util/` contains various utility modules.
  - `Context` contains the definition of contexts that are used in typing rules.
  - `Converter` contains functions to convert between different representations of data.
  - `Evaluator` contains a monad for capturing possible failure.
  - `PropertyEvaluator` contains implementations of evaluators for various relations and properties.
  - `Relations` contains definitions for relations used in the type-checker.
  - `Scope` contains the definition of a context scope.

## Setup

To get the code working, follow these steps:

1. Install Agda by following [the instruction on the website](https://agda.readthedocs.io/en/latest/getting-started/installation.html).
2. Install the `standard-library` using the [installation guide](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md). 
3. To test that everything works, compile the `src/Programs.agda` file.

For development, Agda version 2.6.4.1 and standard library version 2.0 were used.

## Language Overview

A set of small example programs can be found in the `Programs` module.

### Syntax
```
Variables         x, y, z
Type variables    α, β
Type constructors T
Data constructors C

Programs    prog ::= d* t
Data types  d ::= data T α* where (C σ*)*
Atoms       v ::= x | C
Terms       t, u ::= v | λ x : σ . t | Λα.t | t u | t σ
              | zero | suc t | true | false
              | case t of ⟦ p* ⟧
Patterns    p ::= C x* → t

Types         σ, φ ::= ∀α.σ | σ → φ | T σ* | α | Bool | N
Type context  Γ, ∆ ::= ∅ | Γ, σ | Γ, v : σ
```
The syntax of the toy language is given above where * indicates a sequence of the element. Using Agda's Unicode support it was translated to one the closely resembles the original syntax, as can be seen in `Program.Type` and `Program.Term`. Note that type and data constructors must be capitalized, and (pattern) variables must be lower-case. This is assumed to be enforced in a preprocessing step, and is out of scope for this project.

### Declaration Conversion
Since the paper focussed on type-checking terms, we did not discuss the implementation of the conversion of declarations in detail. However, it was implemented as it allows for conciser example programs, as seen in the `Programs` module. The relevant data types can be found in `TypeChecker.ProgramWF`, and the conversion for a set of declarations to a context can be found in `Util.Convert`. 

We first make sure that all data constructors are valid, which is the case if all type variables used as arguments are present in their respective type constructor and if adts are declared. After that, we check that all types and constructors are unique. Finally, we convert these declarations to a `Context` and `TyContext`, and proceed as discussed in the paper. The style of programming is the same as for the type-checker itself, and we trust that using the information from the paper the implementation can be understood. 

## License

This source code is licensed under the MIT license. The full license text is available in the [LICENSE.md](./LICENSE.md) file