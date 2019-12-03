{-# OPTIONS --cubical --no-exact-split --safe #-}

module Cubical.DataDefinitions.Unit where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Logic

open import Cubical.Data.Sum

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.Data.Unit

open import Cubical.Data.Universe

import Cubical.Data.Unit as orgUnit

open import Cubical.DataDefinitions.Definition

record IsUnit (A : Type₀) : Type₁ where
  constructor isUnit
  field
    unit : A
    Unit-induction : (F : A → Type₀) → F unit → (x : A) → (F x)
    Unit-induction-unit : ∀ F → ∀ f → Unit-induction F f unit ≡ f

  isContr-Unit : isContr A
  isContr-Unit = unit , Unit-induction _ refl

IsUnit⊤ : IsUnit (fst ⊤)
IsUnit⊤ = isUnit
  _
  (λ F x x₁ → x)
  λ F f → refl

UnitDef : IsDefinition IsUnit
IsDefinition.ww1 UnitDef A₁ A₂ x y = IsUnit.Unit-induction x (λ _ → A₂) (IsUnit.unit y)
IsDefinition.ww-law UnitDef A ba x = isContr→isProp (IsUnit.isContr-Unit ba) _ _
IsDefinition.ww3 UnitDef A₁ A₂ A₃ x₁ x₂ x₃ b = isContr→isProp (IsUnit.isContr-Unit x₃) _ _

UnitDef₂ : IsDefinition (isContr ∘ Lift)
IsDefinition.ww1 UnitDef₂ A₁ A₂ x x₁ x₂ = lower (fst x₁)
IsDefinition.ww-law UnitDef₂ A ba x = isContr→isProp ((lower (fst ba)) , λ y → cong lower (snd ba (lift y))) _ _
IsDefinition.ww3 UnitDef₂ A₁ A₂ A₃ ba₁ ba₂ ba₃ x = isContr→isProp (((lower (fst ba₃)) , λ y → cong lower (snd ba₃ (lift y)))) _ _
 
IsUnit-Unit : IsUnit Unit
IsUnit-Unit = isUnit _ (λ F x x₁ → x) λ F f → refl

