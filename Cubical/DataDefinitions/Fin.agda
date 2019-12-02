{-# OPTIONS --cubical --no-exact-split --safe #-}

module Cubical.DataDefinitions.Fin where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Logic

open import Cubical.Data.Sum

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.Data.Bool

open import Cubical.Data.Universe

import Cubical.Data.Nat as orgℕ
import Cubical.Data.Fin as orgFin

open import Cubical.DataDefinitions.Definition
open import Cubical.DataDefinitions.Nat




record IsFin (ℕ : Set₀) (isNat-ℕ : isNat ℕ) (Fin : ℕ → Type₀) : Type (ℓ-suc ℓ-zero) where
  constructor isFin

  open isNat isNat-ℕ

  field
    fzero : {n : ℕ} →  Fin (suc n)
    fsuc : {n : ℕ} → (i : Fin n) → Fin (suc n)
    ¬Fin0 : Fin zero → (fst ⊥)
    finduction : ∀(P : ∀{k} → Fin k → Type₀)
                     → (∀{k} → P {suc k} fzero)
                     → (∀{k} {fn : Fin k} → P fn → P (fsuc fn))
                     → {k : ℕ} → (fn : Fin k) → P fn
    finduction-zero : ∀ (P : ∀{k} → Fin k → Type₀)
                        → (fz : ∀{k} → P {suc k} fzero)
                        → (fs : (∀{k} {fn : Fin k} → P fn → P (fsuc fn)))
                        → ∀ k
                         → finduction P fz fs {suc k} fzero ≡ fz
    finduction-suc : ∀ (P : ∀{k} → Fin k → Type₀)
                        → (fz : ∀{k} → P {suc k} fzero)
                        → (fs : (∀{k} {fn : Fin k} → P fn → P (fsuc fn)))
                        → ∀ k → ∀ fi
                         → finduction P fz fs {suc k} (fsuc fi) ≡  fs (finduction P fz fs {k} (fi))


IsFin-Fin : IsFin _ IsNat-ℕ orgFin.Fin
IsFin-Fin = isFin
  fzero
  fsuc
  ¬Fin0
  finduction
  (λ P fz fs k → {!!})
  λ P fz fs k fi → {!!}
  where open orgFin



