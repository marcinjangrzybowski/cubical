{-# OPTIONS --cubical --safe  #-}
module Cubical.HITs.NCube.CubesZoo.CubicalImplementation where


import Agda.Primitive.Cubical

open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat renaming (elim to ℕ-elim)
open import Cubical.Data.Nat.Order

open import Cubical.Data.Vec
open import Cubical.Data.Fin renaming (elim to Fin-elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.HITs.Interval
open import Cubical.HITs.PropositionalTruncation renaming (map to mapₚ)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 hiding (_*_)
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
import Cubical.Functions.Logic as Lo

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.IntervalPrim




record CubicalImpl ℓ (A : Type ℓ) : Type (ℓ-suc ℓ) where

  field

   CubeIn : ℕ → Type ℓ

   CubeIn-0-≃-A : CubeIn 0 ≃ A 

   Boundary : ℕ → Type ℓ

   Boundary-0-≃-Unit* : Boundary 0 ≃ Unit* {ℓ} 
   
   bdOf : ∀ {n} → CubeIn n → Boundary n
   
   Bd-elim-Iso : ∀ {n} → Iso (Boundary (suc n))
                                 (Σ (CubeIn n × CubeIn n )
                                   λ x → bdOf (fst x) ≡ bdOf (snd x) )
   Cu-elim-Iso : ∀ {n} → Iso (CubeIn (suc n))
                                 (Σ (CubeIn n × CubeIn n )
                                   λ x → fst x ≡ snd x )







canocnical : ∀ {ℓ} → ∀ A → CubicalImpl ℓ A
canocnical {ℓ} A = record
                 { CubeIn = CubeIn
                 ; CubeIn-0-≃-A =  idEquiv _
                 ; Boundary = Boundary
                 ; Boundary-0-≃-Unit* = idEquiv _
                 ; bdOf = bdOf
                 ; Bd-elim-Iso = Bd-elim-Iso
                 ; Cu-elim-Iso = Cu-elim-Iso
                 }

  where

    CubeIn : ℕ → Type _
    CubeIn zero = A
    CubeIn (suc n) = (Σ (CubeIn n × CubeIn n )
                                   λ x → fst x ≡ snd x )


    Boundary : ℕ → Type _

    bdOf : ∀ {n} → CubeIn n → Boundary n

    Boundary zero = Unit*
    Boundary (suc n) = (Σ (CubeIn n × CubeIn n )
                                   λ x → bdOf {n} (fst x) ≡ bdOf {n} (snd x) )

    bdOf {zero} x = tt*
    bdOf {suc n} (_ , p) = _ , λ i → bdOf (p i)

    Bd-elim-Iso : ∀ {n} → Iso (Boundary (suc n))
                                 (Σ (CubeIn n × CubeIn n )
                                   λ x → bdOf {n} (fst x) ≡ bdOf {n} (snd x) )
    Bd-elim-Iso {zero} = idIso
    Bd-elim-Iso {suc n} = idIso

    Cu-elim-Iso :  ∀ {n} → Iso (CubeIn (suc n))
                                 (Σ (CubeIn n × CubeIn n )
                                   λ x → fst x ≡ snd x )
    Cu-elim-Iso {zero} = idIso
    Cu-elim-Iso {suc n} = idIso




-- CubicalImpl-iso : ∀ {ℓ} → ∀ n → ∀ A → (X Y : CubicalImpl ℓ A)
--                     → (CubicalImpl.Boundary X n) ≃ (CubicalImpl.Boundary Y n)
-- CubicalImpl-iso n A Xm Ym = {!x.CubeIn!}
--    where
--      module X = CubicalImpl Xm 
--      module Y = CubicalImpl Ym
