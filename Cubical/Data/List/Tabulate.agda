{-# OPTIONS --safe #-}
module Cubical.Data.List.Tabulate where

open import Agda.Builtin.List
open import Cubical.Core.Everything
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function

open import Cubical.Data.List.Base

module _ {ℓ} {A : Type ℓ} where

  data Tab : Type ℓ where
    tab : List A → (ℕ → A) → Tab
    co : ∀ a l f → tab (a ∷ l) f  ≡ tab l (ℕ.cases a f)

  fromTab : Tab → ℕ → A
  fromTab (tab [] f) = f
  fromTab (tab (a ∷ l) f) = {!!}
  fromTab (co a l f i) x₁ = {!!}

  IsoTab : Iso Tab (ℕ → A)
  Iso.fun IsoTab = fromTab
  Iso.inv IsoTab = {!!}
  Iso.rightInv IsoTab = {!!}
  Iso.leftInv IsoTab = {!!}

  -- partialTabulateIso : Iso (ℕ → A) (List A × (ℕ → A))
  -- Iso.fun partialTabulateIso x = {!x!}
  -- Iso.inv partialTabulateIso = {!!}
  -- Iso.rightInv partialTabulateIso = {!!}
  -- Iso.leftInv partialTabulateIso = {!!}
