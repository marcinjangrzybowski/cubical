{-# OPTIONS --safe #-}

module Cubical.Data.Nat.EventuallyConst.Transposition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Functions.Involution

open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order.Recursive

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Empty using (⊥)

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Data.Nat.EventuallyConst.Base

_≤2+_ : ℕ → ℕ → Type₀
x ≤2+ zero = ⊥
x ≤2+ (suc zero) = ⊥
zero ≤2+ (suc (suc x₁)) = Unit
(suc k) ≤2+ (suc (suc l)) = k ≤2+  (suc l)

swap0and1 : ℕ → ℕ
swap0and1 zero = suc zero
swap0and1 (suc zero) = zero
swap0and1 k@(suc (suc _)) = k


adjTransposition : ℕ → ℕ → ℕ
adjTransposition zero = swap0and1
adjTransposition (suc x) = sucFun (adjTransposition x)


isInvolSwap0and1 : isInvolution swap0and1
isInvolSwap0and1 = cases refl (cases refl λ _ → refl)

swap0and1≃ : Iso ℕ ℕ
swap0and1≃ = involIso {f = swap0and1} isInvolSwap0and1

isInvolutionAdjTransposition : ∀ k → isInvolution (adjTransposition k)
isInvolutionAdjTransposition  =
  elim isInvolSwap0and1
    (sucFunRespIsInvolution ∘ adjTransposition)


adjTransposition≃ : ℕ → Iso ℕ ℕ
adjTransposition≃ k = involIso
  {f = adjTransposition k} (isInvolutionAdjTransposition k)

adjTranspositionBraid : ∀ k →
      adjTransposition k ∘
      adjTransposition (suc k) ∘
      adjTransposition k
      ≡
      adjTransposition (suc k) ∘
      adjTransposition k ∘
      adjTransposition (suc k)
adjTranspositionBraid =
  elim (refl =→ refl =→ refl =→ refl)
          λ _ x → refl =→ cong (suc ∘_) x
   
swap0and1SucSucComm : ∀ f → 
        swap0and1 ∘ sucFun (sucFun f)
      ≡ sucFun (sucFun f) ∘ swap0and1
swap0and1SucSucComm f = refl =→ refl =→ refl  

adjTranspositionComm : ∀ k l → k ≤2+ l →
      adjTransposition l ∘ adjTransposition k ≡
      adjTransposition k ∘ adjTransposition l
adjTranspositionComm zero (suc (suc l)) x = sym (swap0and1SucSucComm _)
adjTranspositionComm (suc k) (suc (suc l)) x =
  refl =→ cong (suc ∘_) (adjTranspositionComm k (suc l) x)

adjTranspositionComm' : ∀ k l → k ≤2+ l →
      adjTransposition k ∘ adjTransposition l ∘ adjTransposition k ≡
      adjTransposition l
adjTranspositionComm' zero (suc (suc l)) x = refl =→ refl =→ refl
adjTranspositionComm' (suc k) (suc (suc l)) x =
  refl =→ cong (suc ∘_) (adjTranspositionComm' k (suc l) x)

kAdjTlem : ∀ k → k ≡ adjTransposition k k → ⊥
kAdjTlem zero = znots
kAdjTlem (suc k) x = kAdjTlem k (cong predℕ x)

skAdjTlem : ∀ k → (suc k) ≡ adjTransposition k (suc k) → ⊥
skAdjTlem zero = snotz
skAdjTlem (suc k) x = skAdjTlem k (cong predℕ x)

swap<1lem : ∀ k → 1 ≤ k → 1 ≤ swap0and1 (suc k)
swap<1lem (suc k) x = _

EventuallyConstAdjTransposition :
 ∀ k →  ⟨ EventuallyConst (adjTransposition k) ⟩
EventuallyConstAdjTransposition k =
  ∣ suc (suc k) , w k ∣₁
 where
 w : ∀ k → (n : ℕ) → suc (suc k) ≤ n → adjTransposition k n ≡ n
 w zero (suc (suc n)) x = refl
 w (suc k) (suc (suc (suc n))) x = cong suc (w k (suc (suc n)) x)
