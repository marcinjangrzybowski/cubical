{-# OPTIONS --safe #-}

module Cubical.Data.Nat.FinGenAut where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
-- open import Cubical.Functions.Involution

-- open import Cubical.Functions.Involution

open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order.Recursive

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Empty using (⊥)

isConstFrom : (ℕ → ℕ) → ℕ → hProp ℓ-zero
isConstFrom f k = (∀ x → k ≤ x → f x ≡ x) , isPropΠ2 λ _ _ → isSetℕ _ _  
