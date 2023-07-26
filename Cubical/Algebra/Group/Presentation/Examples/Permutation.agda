{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Examples.Permutation where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Bool as 𝟚
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Bool using (false ; true) renaming (Bool to 𝟚) 
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.HITs.GroupoidTruncation as GT

open import Cubical.Algebra.Group.Presentation.RelIndex


commT : ℕ → ℕ → Type₀
commT x zero = ⊥
commT x (suc zero) = ⊥
commT zero (suc (suc x₁)) = Unit
commT (suc k) (suc (suc l)) = commT k (suc l)

module FinitelyGenerated-ℕ≃ℕ where

 data G : Type₀ where 
  σₖ : ℕ → G
  σₖₗ : ℕ → ℕ → G

 data R : Type₀ where 
  invol-σ : ℕ → R
  comp-σ : ℕ → ℕ → R
  comm-σ : ∀ k l → commT k l → R
  braid-σ : ℕ → R

 FGℕ≃-relations : R → Sq G
 FGℕ≃-relations (invol-σ x) =
   sq (fc true (σₖ x))
      (fc false (σₖ x))
      cns
      cns
 FGℕ≃-relations (comp-σ k l) =
   sq (fc true (σₖ k))
      (fc true (σₖ l))
      (fc true (σₖₗ k l))
      cns
 FGℕ≃-relations (comm-σ k l x) =
   sq (fc true (σₖₗ k l))
      (fc true (σₖₗ l k))
      (cns)
      (cns)
 FGℕ≃-relations (braid-σ k) =
  sq (fc true (σₖ (suc k)))
     (fc true (σₖ k))
     (fc true (σₖₗ k (suc k)))
     (fc true (σₖₗ k (suc k)))

 open Pres G FGℕ≃-relations

module Braid/Symmetric (hasInvol : 𝟚) (n : ℕ) where
 Inv? = (𝟚.Bool→Type hasInvol)


 data G : Type₀ where 
  σₖ : (Σ _ λ k → (suc k < n)) → G
  σₖₗ : (Σ _ λ k → (suc k < n)) → (Σ _ λ k → (suc k < n)) → G

 data R : Type₀ where 
  invol-σ : {Inv?} → (Σ _ λ k → (suc k < n)) → R
  comp-σ : (Σ _ λ k → (suc k < n)) → (Σ _ λ k → (suc k < n)) → R
  comm-σ : (k l : (Σ _ λ k → (suc k < n))) → commT (fst k) (fst l) → R
  braid-σ : (Σ _ λ k → (suc (suc k) < n)) → R


 σ-r : R → Sq G
 σ-r (invol-σ x) =
   sq (fc true (σₖ x))
      (fc false (σₖ x))
      cns
      cns
 σ-r (comp-σ k l) =
   sq (fc true (σₖ k))
      (fc true (σₖₗ k l))
      cns
      (fc true (σₖ l))
 σ-r (comm-σ k l x) =
   sq (fc true (σₖₗ k l))
      (fc true (σₖₗ l k))
      (cns)
      (cns)
      

 σ-r (braid-σ (k , sk<n)) = 
   sq (fc true (σₖ (suc k , sk<n)))
      (fc true (σₖ (k , <-weaken sk<n)))
      (fc true (σₖₗ (k , <-weaken sk<n) (suc k , sk<n)))
      (fc true (σₖₗ (k , <-weaken sk<n) (suc k , sk<n)))

 module PresB/S = Pres G {IxR = R} σ-r

 

module Braid = Braid/Symmetric false
