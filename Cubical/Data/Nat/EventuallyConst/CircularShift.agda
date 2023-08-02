{-# OPTIONS --safe #-}

module Cubical.Data.Nat.EventuallyConst.CircularShift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
-- open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Functions.Logic hiding (¬_)
open import Cubical.Relation.Nullary

open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Structure

open import Cubical.Data.Nat.Base
-- open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order.Recursive
-- open import Cubical.Data.Nat.EventuallyConst.Transposition

-- import Cubical.Data.Empty as ⊥
open import Cubical.Data.Empty using (⊥)

open import Cubical.Data.Nat.EventuallyConst.Base
open import Cubical.Data.Nat.EventuallyConst.Transposition


rotIso : ℕ → Iso ℕ ℕ
rotIso zero = swap0and1≃
rotIso (suc n) = compIso swap0and1≃ (sucIso (rotIso n))

rot : ℕ → ℕ → ℕ
rot = Iso.fun ∘ rotIso
 
rotIso' : ℕ → Iso ℕ ℕ
rotIso' = cases idIso rotIso

rot' : ℕ → ℕ → ℕ
rot' = Iso.fun ∘ rotIso'

rot'-k : ∀ k → rot' k zero ≡ k
rot'-k = cases refl (elim refl λ _ → cong suc) 

rot'-zero : ∀ k →  (Iso.inv (rotIso' k)) k ≡ zero
rot'-zero = cases refl (elim refl λ _ → cong (swap0and1 ∘ suc)) 

rot'-≢k→≢0 : ∀ k n → ¬ k ≡ n → ¬ (zero ≡ (Iso.inv (rotIso' k)) n) 
rot'-≢k→≢0 k n p q =
   p (sym (rot'-k k)
    ∙ cong (Iso.fun (rotIso' k)) q ∙ (Iso.rightInv (rotIso' k) n))


lemmm>0 : ∀ e0 e1 → e1 ≤ e0 → 0 < (Iso.inv (rotIso e0) e1)
lemmm>0 zero zero x = _
lemmm>0 (suc e0) zero x = _
lemmm>0 (suc e0) (suc e1) x = swap<1lem (Iso.inv (rotIso e0) e1) (lemmm>0 e0 e1 x)



EventuallyConstCircularShift :
   ∀ k →  ⟨ EventuallyConst (rot k) ⟩
EventuallyConstCircularShift zero =
  EventuallyConstAdjTransposition 0
EventuallyConstCircularShift (suc k) =
  EventuallyConst-∘
    (EventuallyConst-sucFun
      (EventuallyConstCircularShift k))
    (EventuallyConstAdjTransposition 0) 

-- unwindIso : Iso ℕ ℕ → Iso ℕ ℕ
-- unwindIso isom =
--   predℕIso (compIso isom (invIso (rotIso' (Iso.fun isom zero))))
--            ((rot'-zero (Iso.fun isom zero)))

-- rot'-<k : ∀ k n → n < k → suc n ≡ (Iso.inv (rotIso' k) n)                   
-- rot'-<k (suc zero) zero x = refl
-- rot'-<k (suc (suc k)) zero x = refl
-- rot'-<k (suc (suc k)) (suc n) x =
--   cong suc (rot'-<k (suc k) n x) ∙
--     sym (isConstFrom-adjTransposition 0
--        _ (lemmm>0 k n x)) 
