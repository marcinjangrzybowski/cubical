{-# OPTIONS --safe #-}

module Cubical.Data.Nat.EventuallyConst.Base where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic
open import Cubical.Functions.Involution

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order.Recursive

open import Cubical.HITs.PropositionalTruncation as PT


EventuallyConst : (ℕ → ℕ) → hProp ℓ-zero
EventuallyConst f = Eventually λ k → f k ≡ k

EventuallyConstIso : Iso ℕ ℕ → hProp ℓ-zero
EventuallyConstIso = EventuallyConst ∘ Iso.fun


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


sucFunRespIsInvolution : ∀ f →
     isInvolution f → isInvolution (sucFun f)
sucFunRespIsInvolution f x =
  cases refl (cong suc ∘ x)


EventuallyConst-predFun : ∀ {f}
   → ⟨ EventuallyConst f ⟩
   → ⟨ EventuallyConst (predFun f) ⟩
EventuallyConst-predFun =
  PT.map λ (n , p) → predℕ n ,
     λ n' → cong predℕ ∘ (p (suc n')) ∘ predℕ≤→≤suc {n} {n'}

EventuallyConst-sucFun : ∀ {f}
   → ⟨ EventuallyConst f ⟩
   → ⟨ EventuallyConst (sucFun f) ⟩
EventuallyConst-sucFun =
  PT.map λ (n , p) → suc n ,
     cases (λ ()) λ n' → cong suc ∘ p n'

EventuallyConst-∘ : ∀ {f g} →
    ⟨ EventuallyConst f ⟩
  → ⟨ EventuallyConst g ⟩
  → ⟨ EventuallyConst (f ∘ g) ⟩
EventuallyConst-∘ =
 PT.map2 λ (nf , pf) (ng , pg) →
   max nf ng , λ n → (λ (nf≤n , ng≤n) →
        pf _ (subst (nf ≤_) (sym (pg n ng≤n)) nf≤n) ∙ pg n ng≤n)
     ∘ max≤→≤×≤ nf ng n 
