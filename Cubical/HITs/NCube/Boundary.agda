{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.Boundary where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Fin

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

open import Cubical.HITs.NCube.BaseVec


2ⁿof : ∀ {ℓ} → ( A : Type ℓ) → ℕ → Type ℓ 
2ⁿof A zero = A
2ⁿof A (suc n) = (2ⁿof A n) × (2ⁿof A n)



data DVec {ℓ} (VTy : ℕ → Type ℓ) : ℕ → Type ℓ where
    _⟫ : VTy zero → DVec VTy zero 
    _ʻ,_ : ∀ {k} → VTy (suc k) → DVec VTy k → DVec VTy (suc k)

fromVec : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Vec A (suc n) → DVec (const A) n
fromVec {n = zero} (x ∷ x₁) = x ⟫ 
fromVec {n = suc n} (x ∷ x₁) = x ʻ, (fromVec x₁)



!! : ℕ → ℕ
!! zero = suc zero
!! (suc x) = (suc x) * !! x

2^ : ℕ → ℕ
2^ zero = suc zero
2^ (suc x) = (2^ x) * 2


_─_ :  ℕ → ℕ → ℕ
x ─ zero = x
zero ─ suc x₁ = zero
suc x ─ suc x₁ = x ─ x₁

facetsNo : ℕ → ℕ → ℕ
facetsNo x k = ((2^ (x ─ k)) * (!! k))

Skel : ∀ {ℓ} → (A : Type ℓ) →  ℕ → ℕ → Type ℓ

facetsBrdrs : ∀ {ℓ} → {A : Type ℓ}
              → ∀ n → ∀ k
              → Skel A n k
              → ℕ
              → (NBoundary (suc k) → A) 


Skel A x zero = 2ⁿof A x
Skel A zero (suc _) = Lift ⊥
Skel A (suc n) (suc k) = Σ (Skel A (suc n) k)
                          λ sk → DVec (InsideOf ∘ (facetsBrdrs (suc n) k sk))
                          (facetsNo n k)

facetsBrdrs {ℓ} {A} zero zero x x₁ _ = x
facetsBrdrs {ℓ} {A} (suc n) zero x x₁ (lid false x₃) = {!!}
facetsBrdrs {ℓ} {A} (suc n) zero x x₁ (lid true x₃) = {!!}
facetsBrdrs {ℓ} {A} n (suc k) x x₁ x₂ = {!!}
