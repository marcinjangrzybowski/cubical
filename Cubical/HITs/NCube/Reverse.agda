{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.Reverse where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
-- open import Cubical.Data.Prod
open import Cubical.Data.List
open import Cubical.Data.Sigma

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

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.Base


reverseH : ∀ n → NCube n → NCube n
reverseH zero x = x
reverseH (suc zero) x = x
reverseH (suc (suc n)) (fst₁ , fst₂ , snd₁) = fst₂ , fst₁ , snd₁


reverse : ∀ n → NCube n → NCube n
reverse zero x = x
reverse (suc zero) x = x
reverse (suc (suc zero)) (fst₁ , fst₂ , snd₁) = fst₂ , fst₁ , snd₁
reverse (suc (suc (suc n))) x = {!!}
