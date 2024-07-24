open import Data.Nat public using (ℕ;suc;zero;_+_;pred) renaming (_≟_ to _ℕ≟_)
open import Data.String public using (String;head) renaming (_≟_ to _s≟_;_++_ to _s++_)
open import Data.List public using (List; _∷_; []; _++_;reverse;map;concat;foldr;length) renaming (filterᵇ to filter)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl;_≢_;cong)
open import Relation.Nullary.Negation public using (contradiction; ¬_)
open import Function.Base public using (_∘_;flip;id)
open import Relation.Nullary.Decidable public using (Dec;yes; no)
open import Data.List.Relation.Unary.All public using (All;[]) renaming (_∷_ to _∷ₐ_)
open import Data.Sum.Base public using (inj₁; inj₂)
open import Effect.Monad public
open import Data.Product public using (_,_;Σ-syntax;∃-syntax)
open import Data.Bool public using (Bool;true;false;not;_∧_)
open import Data.Maybe public using (Maybe;just;nothing)
open import Data.Empty public using (⊥)
open import Data.Char public using (isLower;isAlpha)
open import Data.Nat.Show public renaming (show to showNat)
open import Relation.Binary.Definitions public using (Decidable)
open import Data.List.Base public using (downFrom)
open import Data.Product public using (uncurry; <_,_>)

open RawMonad ⦃ ... ⦄ public

-- | Whether a string is capitalized
isCapitalized : String → Bool
isCapitalized s with head s
...               | (just c) = not (isLower c) ∧ (isAlpha c)
...               | _ = false

-- | Whether first character of a string is lowercase
isLowerCase : String → Bool
isLowerCase s with head s
...               | (just c) = isLower c
...               | _ = false

-- | if b>a then b-1 else b (Taken from Data.Fin)
punchOut : (a b : ℕ) → {a ≢ b} → ℕ
punchOut zero zero {i≢j} = contradiction refl i≢j
punchOut zero (suc b) = b
punchOut (suc a) zero = zero
punchOut (suc a) (suc b) {i≢j} = suc (punchOut a b {i≢j ∘ cong suc})

-- | f(a,b) = if b≥a then b+1 else b (Taken from Data.Fin)
punchIn : (a b : ℕ) → ℕ
punchIn zero b = suc b
punchIn (suc a) zero = zero
punchIn (suc a) (suc b) = suc (punchIn a b)