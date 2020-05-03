{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.BaseIn where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.List

open import Cubical.HITs.Interval
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.NCube.Base



-- data NBoundaryIn' {ℓ} {n} {A : Type ℓ} {X : Type ℓ} (injX : (NCube (n) → A) → X) : Type ℓ where
--    lid : NCube n → A → NBoundaryIn' injX
--    cyl : ?
--    -- cyl : ∀ x → lid false (injX x) ≡ lid true (injX x)



cubi-iso : ∀ {ℓ} → {A : Type ℓ} → ∀ n
            → Iso
             (NCube (suc n) → A )
             (Σ (NBoundary (suc n) → A) (InsideOf)) 

cubi-iso {A = A} (zero) = {!!}

cubi-iso {A = A} (suc n') = iso (to) (from) (ri) (li)

  where

    n = suc n'

    P : Iso _ _
    P = (cubi-iso {A = A} n') 

    open Iso

    to : (NCube (suc (suc n')) → A)
             → (Σ (NBoundary (suc (suc n')) → A) (InsideOf))  
    to = {!!}
    
    from : (Σ (NBoundary (suc (suc n')) → A) (InsideOf))
                 → (NCube (suc (suc n')) → A)             
    from = {!!}

    ri : section (to) (from)
    ri = {!!}

    
    li : retract (to) (from)
    li a = {!!}
