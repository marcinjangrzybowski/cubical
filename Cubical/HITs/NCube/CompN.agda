{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.CompN where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
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


hcompⁿ-all : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n → ∀ k 
          → (c : Interval' → NBoundary (suc k) → A)
          → InsideOfₘ n (c (end false))
          → InsideOfₘ n (c (end true))
hcompⁿ-all n zero c x = {!!}
hcompⁿ-all n (suc k) c x = {!!}


  where

  -- {ℓ = i : I → Level} (x₁ : (i₁ : I) → Set (i i₁)) {φ : I} →
  --     ((i₁ : I) → .(IsOne φ) → x₁ i₁) → x₁ i0 → x₁ i1
 

  h0 : {!comp!}
  h0 = {!!}
