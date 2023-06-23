{-# OPTIONS --safe #-}
module Cubical.HITs.GroupPresentation.Cubical where

import Cubical.Data.Nat.Base as ℕ
import Cubical.Data.Nat.Properties as ℕprops


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution

open import Cubical.Foundations.Everything
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive
-- open import Cubical.Data.Nat.Order.RecursiveMoreEquiv

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group

open import Cubical.Algebra.SymmetricGroup

import Cubical.Functions.Logic as L

open import Cubical.Functions.Embedding

open import Cubical.Data.List as Li

import Cubical.Data.Nat.FinGenAut2 as A

import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SequentialColimit as SC

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)


open import Cubical.Relation.Binary

-- import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint


record Relator {ℓ : Level} (A : Type ℓ) : Type ℓ where
 field
  a₀₋ a₁₋ a₋₀ a₋₁ : Maybe (Bool × A)
 
record Relators {ℓ : Level} (ℓ' : Level) (A : Type ℓ) :
     Type (ℓ-max ℓ (ℓ-suc ℓ')) where
 field
  R : Type ℓ'
  faces : R → Relator A

 
 open Relator

 data 𝔹 : Type (ℓ-max ℓ ℓ')

 𝕓base' : 𝔹
 𝕓loop' : A → 𝕓base' ≡ 𝕓base'

 fc : (Relator {ℓ} A → Maybe (Bool × A)) → R → 𝕓base' ≡ 𝕓base'
 fc aₓ = (Mb.rec refl
         (λ (b , a) → if b then (𝕓loop' a) else (sym (𝕓loop' a))))
          ∘' aₓ ∘' faces

 data 𝔹  where
  𝕓base : 𝔹
  𝕓loop : A → 𝕓base ≡ 𝕓base
  𝕓relation : (r : R) → Square {A = 𝔹}
                (fc a₀₋ r)
                (fc a₁₋ r)
                (fc a₋₀ r)
                (fc a₋₁ r)
  𝕓squash : isGroupoid 𝔹  

 𝕓base' = 𝕓base
 𝕓loop' = 𝕓loop
