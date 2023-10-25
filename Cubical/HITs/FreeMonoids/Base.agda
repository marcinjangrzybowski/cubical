{-# OPTIONS --safe #-}

module Cubical.HITs.FreeMonoids.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

private variable
  ℓ : Level
  A : Type ℓ

data FreeMonoid (A : Type ℓ) : Type ℓ where
  ⟦_⟧       : A → FreeMonoid A
  ε         : FreeMonoid A
  _·_       : FreeMonoid A → FreeMonoid A → FreeMonoid A
  identityᵣ : ∀ x     → x · ε ≡ x
  identityₗ : ∀ x     → ε · x ≡ x
  assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
  trunc     : isSet (FreeMonoid A)
