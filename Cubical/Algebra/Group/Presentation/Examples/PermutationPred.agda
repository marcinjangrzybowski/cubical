{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Examples.Permutation where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Powerset
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

import Cubical.Functions.Logic as L

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.HITs.GroupoidTruncation as GT

open import Cubical.Algebra.Group.Presentation.Base


commT : ℕ → ℕ → Type₀
commT x zero = ⊥
commT x (suc zero) = ⊥
commT zero (suc (suc x₁)) = Unit
commT (suc k) (suc (suc l)) = commT k (suc l)

adjℕ : ℕ → ℕ → hProp ℓ-zero
adjℕ x zero = L.⊥
adjℕ (suc x) (suc x₁) = adjℕ x x₁
adjℕ zero (suc zero) = L.⊤
adjℕ zero (suc (suc x₁)) = L.⊥


module FinitelyGenerated-ℕ≃ℕ where

 data G : Type₀ where 
  σₖ : ℕ → G
  σₖₗ : ℕ → ℕ → G

 data R : Type₀ where
  invol-σ comp-σ comm-σ braid-σ : R

  -- invol-σ : ℕ → R
  -- comp-σ : ℕ → ℕ → R
  -- comm-σ : ∀ k l → commT k l → R
  -- braid-σ : ℕ → R

 r' : R → ℙ (Sq G)
 r' invol-σ (sq (fc true x) (fc false x') cns cns) = {!!}
 r' invol-σ _ = L.⊥
 r' comp-σ x₁ = {!!}
 r' comm-σ x₁ = {!!}
 r' braid-σ x₁ = {!!}
 
 Rels : ℙ (Sq G)
 Rels s = L.∃[ x ∶ R ] (r' x) s

 open Pres G Rels




--  FGℕ≃-relations : R → Sq G
--  FGℕ≃-relations (invol-σ x) =
--    sq (fc true (σₖ x))
--       (fc false (σₖ x))
--       cns
--       cns
--  FGℕ≃-relations (comp-σ k l) =
--    sq (fc true (σₖ k))
--       (fc true (σₖ l))
--       (fc true (σₖₗ k l))
--       cns
--  FGℕ≃-relations (comm-σ k l x) =
--    sq (cns)
--       (cns)
--       (fc true (σₖₗ k l))
--       (fc true (σₖₗ l k))

--  FGℕ≃-relations (braid-σ k) =
--   sq (fc true (σₖ (suc k)))
--      (fc true (σₖ k))
--      (fc true (σₖₗ k (suc k)))
--      (fc true (σₖₗ k (suc k)))

--  open Pres G FGℕ≃-relations

-- module Braid/Symmetric (hasInvol : 𝟚) (n : ℕ) where
--  Inv? = (𝟚.Bool→Type hasInvol)


--     -- ∷A : 𝟚 → (Σ ℕ  λ k → (suc k < n)) → A → A
--     -- inv∷A : ∀ b k → ∀ x →
--     --                  ∷A (𝟚.not b) k (∷A b k  x) ≡ x    
--     -- braidA : ∀ b k → ∀ k< → ∀ x →
--     --      ∷A b (k , <-weaken {n = n} k<) (∷A b (suc k , k<)
--     --       (∷A b (k , <-weaken {n = n} k<) x))
--     --    ≡ ∷A b (suc k , k<) (∷A b (k , <-weaken {n = n} k<) (∷A b (suc k , k<) x))
--     -- commA : ∀ b b' k l → commT (fst k) (fst l) → ∀ x →
--     --                  ∷A b k (∷A b' l x) ≡ ∷A b' l (∷A b k x)


--  data G : Type₀ where 
--   σₖ : (Σ _ λ k → (suc k < n)) → G
--   σₖₗ : (Σ _ λ k → (suc k < n)) → (Σ _ λ k → (suc k < n)) → G

--  data R : Type₀ where 
--   invol-σ : Inv? → ℕ → R
--   comp-σ : ℕ → ℕ → R
--   comm-σ : ∀ k l → commT k l → R
--   braid-σ : ℕ → R

