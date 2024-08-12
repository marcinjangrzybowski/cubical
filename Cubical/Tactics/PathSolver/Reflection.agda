{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.Reflection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Agda.Builtin.Char
open import Agda.Builtin.String

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.List as L
open import Cubical.Data.Maybe as Mb

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.Reflection



R∙ : R.Term → R.Term → R.Term
R∙ x y = R.def (quote _∙_) (x v∷ y v∷ [] )

R∙' : R.Term → R.Term → R.Term
R∙' x y = R.def (quote _∙'_) (x v∷ y v∷ [] )


Rrefl : R.Term
Rrefl = R.def (quote refl) []

mapArg : ∀ {ℓ ℓ'} → {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) → R.Arg A → R.Arg B
mapArg f (R.arg i x) = R.arg i (f x)

unArg : ∀ {ℓ} → {A : Type ℓ} → R.Arg A → A
unArg (R.arg i x) = x

argInfo : ∀ {ℓ} → {A : Type ℓ} → R.Arg A → R.ArgInfo
argInfo (R.arg i x) = i
