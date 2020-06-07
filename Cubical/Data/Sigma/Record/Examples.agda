{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Record.Examples where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Fin

-- open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)

open import Cubical.Data.Sigma.Record.Base



-- v-subst : ∀ {ℓ} → ∀ {n} →   Sig* ℓ n → Sig* ℓ n
-- v-subst = {!!}

-- ᵣtoₗ : ∀ {ℓ} → ∀ n → Sigᵣ ℓ n → Sigₗ ℓ n
-- ᵣtoₗ zero x = _
-- ᵣtoₗ (suc n) x = {!n!}


zzz : ∀ ℓ → ∀ n → Type (ℓ-suc ℓ)
zzz ℓ n = fromSigTypeₗ n corner0 (toₗ {n = n} corner1 (KindSig ℓ n)) (Type ℓ)


zzzTest : {!!} 
zzzTest = {! (zzz ℓ-zero 5)!}


someSig-2 : Sigₗ ℓ-zero 6
someSig-2 = ℕ , λ n₁
          → ℕ , λ n₂
          → ((Vec (Fin n₂) n₁) → ℕ) , λ P
          → _ , λ x
          → Fin n₁ , λ k
          → P x ≡ toℕ k

zzz2 : ∀ ℓ → ∀ n → {!!}
zzz2 ℓ n = mkConstructor n corner0 (toₗ {n = n} corner1 (KindSig ℓ n))

someSigConstructor : constructorTypeₗ 6 corner0 someSig-2
someSigConstructor = mkConstructor 6 corner0 someSig-2

rec-from-constructor : Recₗ {n = 6} someSig-2
rec-from-constructor = someSigConstructor 1 2 (λ x → 0) (fzero ∷ []) fzero refl

-- Rec*-subst {n = 6} corner0 corner1 rec-from-constructor

someSigConstructor-implict : _
someSigConstructor-implict = {!toₗ {n = 4} !}

