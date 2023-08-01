{-# OPTIONS --safe #-}

module Cubical.Data.Nat.Transposition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Involution

open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Empty using (⊥)

_≤2+_ : ℕ → ℕ → Type₀
x ≤2+ zero = ⊥
x ≤2+ (suc zero) = ⊥
zero ≤2+ (suc (suc x₁)) = Unit
(suc k) ≤2+ (suc (suc l)) = k ≤2+  (suc l)

swap0and1 : ℕ → ℕ
swap0and1 zero = suc zero
swap0and1 (suc zero) = zero
swap0and1 k@(suc (suc _)) = k

sucFun : (ℕ → ℕ) → (ℕ → ℕ)
sucFun x zero = zero
sucFun x (suc x₁) = suc (x x₁)

predFun : (ℕ → ℕ) → (ℕ → ℕ)
predFun f = predℕ ∘ f ∘ suc

isInjectiveSucFun : ∀ {f} {f'} → sucFun f ≡ sucFun f' → f ≡ f'
isInjectiveSucFun = cong ((predℕ ∘_) ∘ (_∘ suc))

sucIso : Iso ℕ ℕ → Iso ℕ ℕ
sucIso isom = w
  where
    module i = Iso isom
    open Iso
    w : Iso ℕ ℕ
    fun w = sucFun i.fun
    inv w = sucFun i.inv
    rightInv w = cases refl (cong suc ∘ i.rightInv)
    leftInv w = cases refl (cong suc ∘ i.leftInv)

sucFunResp∘ : ∀ f g → sucFun f ∘ sucFun g ≡ sucFun (f ∘ g)
sucFunResp∘ f g = refl =→ refl

adjTransposition : ℕ → ℕ → ℕ
adjTransposition zero = swap0and1
adjTransposition (suc x) = sucFun (adjTransposition x)


isInvolSwap0and1 : isInvolution swap0and1
isInvolSwap0and1 = cases refl (cases refl λ _ → refl)

swap0and1≃ : Iso ℕ ℕ
swap0and1≃ = involIso {f = swap0and1} isInvolSwap0and1


sucFunRespIsInvolution : ∀ f →
     isInvolution f → isInvolution (sucFun f)
sucFunRespIsInvolution f x =
  cases refl (cong suc ∘ x)

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
