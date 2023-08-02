{-# OPTIONS --safe #-}

module Cubical.Data.Nat.EventuallyConst.Automorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

-- open import Cubical.Functions.Involution

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Nat.EventuallyConst.Transposition

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Empty using (⊥)

isConstFrom : (ℕ → ℕ) → ℕ → hProp ℓ-zero
isConstFrom f k = (∀ x → k ≤ x → f x ≡ x) , isPropΠ2 λ _ _ → isSetℕ _ _  

predFun-isConstFrom : ∀ f k
   → ⟨ isConstFrom f (suc k) ⟩
   → ⟨ isConstFrom (predFun f) k ⟩
predFun-isConstFrom f k X n x₂ =
  cong predℕ (X (suc n) (x₂))

sucFun-isConstFrom : ∀ f k
   → ⟨ isConstFrom f k ⟩
   → ⟨ isConstFrom (sucFun f) (suc k) ⟩
sucFun-isConstFrom f k X =
 cases (λ _ → refl) λ n → cong suc ∘ X n

isConstFrom∘ : ∀ f k g l →
   ⟨ isConstFrom f k ⟩ → ⟨ isConstFrom g l ⟩
   →  ⟨ isConstFrom (f ∘ g) (max l k) ⟩
isConstFrom∘ f l g k s r j j< =
     let j= = r j (≤-trans {k = k}
                {m = max k l} {n = j} (left-≤-max k l) j<)
     in s _ (subst (l ≤_) (sym j=)
      (≤-trans {l} {max k l} {j} (right-≤-max k l) j<)
      ) ∙ j= 
