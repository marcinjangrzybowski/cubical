{-# OPTIONS --cubical  #-}
module Cubical.HITs.NCube.Refl where


open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≟_ to _≟Nat_)
open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum as Sum

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

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint


open import Cubical.HITs.NCube.IntervalPrim
-- open import Cubical.HITs.NCube.Cub

open import Cubical.HITs.NCube.BaseVec
open import Cubical.HITs.NCube.CompN


InsConst : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
           → ℕ → Type ℓ

insRefl : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
           → ∀ n → InsConst a n


InsConst {A = A} a zero = A
InsConst {A = A} a (suc n) = (insRefl a n) ≡ (insRefl a n) 

insRefl a zero = a
insRefl a (suc n) = refl

InsConst=Σ : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A) → ∀ n →
             Σ (InsConst a n ≡ InsideOf {n = n} (const a))
                λ p → PathP (λ x → p x) (insRefl a _) (reflⁿ n a)
InsConst=Σ a zero = refl , refl
InsConst=Σ a (suc zero) = refl , refl
InsConst=Σ a (suc (suc n)) =
    (λ i → snd (InsConst=Σ a (suc n)) i ≡ snd (InsConst=Σ a (suc n)) i )
    , λ x → refl

InsConst= : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A) → ∀ n →
              InsConst a n ≡ InsideOf {n = n} (const a)
InsConst= a n = fst (InsConst=Σ a n)


Ins :  ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A) → ∀ n → Type ℓ
Ins a n = Σ (InsConst a n) ((insRefl a n) ≡_)

sqIns : ∀ {ℓ} → ∀ {A  : Type ℓ} → {a : A}
        → ∀ {n}
        → (x : Ins a n)
        → (insRefl a n , refl) ≡ x        
sqIns x i = snd x i  , λ i₁ → snd x (i₁ ∧ i)


-- insSq : ∀ {ℓ} → ∀ {A  : Type ℓ} → {a : A}
--         → ∀ {n}
--         → (Ins a n)
--         → {!Ins a (suc n)!}
-- insSq = {!!}

insApp : ∀ {ℓ} → ∀ {A  : Type ℓ} → {a : A}
        → ∀ {n}
        → (x : Ins a (suc n))
        → _≡_ {A = Ins a n} (fst x i0 , λ i → (snd x i i0)) ((fst x i1 , λ i → (snd x i i1)))
insApp x j = (fst x j , λ i → (snd x i j))

insToCub : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
           → ∀ n → InsConst a n
           → NCube n → A
insToCub a zero x x₁ = x
insToCub a (suc n) x (end x₁ ∷ x₂) = insToCub a n (x (Bool→I x₁)) x₂
insToCub a (suc n) x (inside i ∷ x₂) = insToCub a n (x i) x₂





data Refl (n : ℕ) : ℕ → Type₀  where
  rfl : ∀ m → Refl n m
  cmp : ∀ {m} → ((Bool × Fin n) → Refl n m) → Refl n m → Refl n (suc m) 


