module Util.Scope where

open import Prelude

-- Scope is defined as a list of names.
--
Scope : Set
Scope = List String

-- type \Phi to get Φ
Φ : Scope
Φ = []