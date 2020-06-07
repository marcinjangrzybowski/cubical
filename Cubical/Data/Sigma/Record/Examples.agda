{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Record.Examples where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

-- open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)

open import Cubical.Data.Sigma.Record.Base



v-subst : ∀ {ℓ} → ∀ n → Sigᵣ ℓ n → Sigₗ ℓ n
v-subst = {!!}

-- ᵣtoₗ : ∀ {ℓ} → ∀ n → Sigᵣ ℓ n → Sigₗ ℓ n
-- ᵣtoₗ zero x = _
-- ᵣtoₗ (suc n) x = {!n!}


zzz : ∀ ℓ → ∀ n → Type (ℓ-suc ℓ)
zzz ℓ n = fromSigTypeₗ n corner0 (toₗ {n = n} corner1 (KindSig ℓ n)) (Type ℓ)


zzzTest : {!!} 
zzzTest = {! (KindSig ℓ-zero 3)!}
