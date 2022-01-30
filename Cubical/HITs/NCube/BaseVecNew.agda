{-# OPTIONS --cubical --safe  #-}
module Cubical.HITs.NCube.BaseVecNew where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Data.NatMinusOne.Base

open import Cubical.HITs.Interval
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Susp.Properties


open import Cubical.HITs.S1

open import Cubical.HITs.Join


open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.IntervalPrim

-- NBoundary and boundaryInj are recursively defined


Bd : ℕ → Type₀

data BdS (n : ℕ) : Type₀ where
  bd : Bool → Bd n → BdS n
  bdP : {!Bd n!} → PathP ? ? ?


Bd zero = ⊥
Bd (suc n) = {!!}
