{-# OPTIONS --cubical --safe  #-}
module Cubical.HITs.NCube.SigmaBoundary where


import Agda.Primitive.Cubical

open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat renaming (elim to ℕ-elim)
open import Cubical.Data.Nat.Order

open import Cubical.Data.Vec
open import Cubical.Data.Fin renaming (elim to Fin-elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum

open import Cubical.HITs.Interval
open import Cubical.HITs.PropositionalTruncation renaming (map to mapₚ)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 hiding (_*_)
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
import Cubical.Functions.Logic as Lo

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.IntervalPrim
open import Cubical.HITs.NCube.SigmaDone
open import Cubical.HITs.NCube.BaseVec

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying
open import Cubical.Data.Sigma.Nested.Path


-- bdb : ∀ n → Boundaryⁿ' n (NBoundary n)
-- bdb zero = _
-- bdb (suc n) = inv ((CIso.fun (lid false) , CIso.fun (lid true)) ,
--                  ( {!!} ∙∙ (λ i → Boundaryⁿ'-map n (cylEx i) (bdb n)) ∙∙ {!!}))

--   where
--     open Iso (Boundary'-elim-iso {A = NBoundary (suc n)} n)

--     module CIso = Iso (IsoCub' {A = NBoundary (suc n)} (n))







Iso-HIT-Σ : ∀ {A : Type ℓ} → ∀ n → Iso (Boundaryⁿ' n A) (NBoundary n → A )

h1 : ∀ {ℓ} (A : Type ℓ) n
       {x0 : Cubeⁿ' n A} {x1 : Cubeⁿ' n A}
       (p : cubeBd' n A x0 ≡ cubeBd' n A x1) → ∀ xx →
     (Iso.inv (IsoCub' n) x0 ∘ boundaryInj) xx ≡
     (Iso.inv (IsoCub' n) x1 ∘ boundaryInj) xx



h2 : ∀ {ℓ} (A : Type ℓ) n
       {x0 : NCube n → A} { x1 : NCube n → A}
       (p : x0 ∘ boundaryInj ≡ x1 ∘ boundaryInj) →
     cubeBd' n A (Iso.fun (IsoCub' n) x0) ≡
     cubeBd' n A (Iso.fun (IsoCub' n) x1)

Iso.fun (Iso-HIT-Σ zero) x ()
Iso.inv (Iso-HIT-Σ zero) x = _
Iso.rightInv (Iso-HIT-Σ zero) b i ()
Iso.leftInv (Iso-HIT-Σ zero) a i = _

Iso-HIT-Σ {A = A} (suc n) =
                   _ Iso⟨ Boundary'-elim-iso n ⟩
                   _ Iso⟨ h ⟩
                   _ Iso⟨ invIso NBoundary-rec-Iso ⟩ _ ∎Iso


  where

    module prevCu = Iso (IsoCub' {A = A} (n))


    module prev = Iso (Iso-HIT-Σ {A = A} (n))

    h : Iso
          (Σ (Cubeⁿ' n A × Cubeⁿ' n A)
           (λ a → cubeBd' n A (fst a) ≡ cubeBd' n A (snd a)))
          (Σ ((NCube n → A) × (NCube n → A))
           (λ x0x1 → fst x0x1 ∘ boundaryInj ≡ snd x0x1 ∘ boundaryInj))
    Iso.fun h ((x0 , x1) , p) = (prevCu.inv x0  , prevCu.inv x1) , funExt (h1 A n p)
    Iso.inv h ((x0 , x1) , p) = (prevCu.fun x0  , prevCu.fun x1) , h2 A n p

    Iso.rightInv h ((fst₁ , snd₂) , snd₁) = {!!}

    Iso.leftInv h = {!!}



h1 A (suc zero) p (lid false []) = cong fst p

h1 A (suc zero) p (lid true []) = cong snd p

h1 A (suc (suc zero)) p (lid b x₁) i = cong (Iso.fun (Iso-HIT-Σ (suc (suc zero)))) p i (lid b x₁)
h1 A (suc (suc zero)) p (cyl (lid false []) j) i = cong (Iso.fun (Iso-HIT-Σ (suc (suc zero)))) p i (cyl (lid false []) j)
h1 A (suc (suc zero)) p (cyl (lid true []) j) i = cong (Iso.fun (Iso-HIT-Σ (suc (suc zero)))) p i (cyl (lid true []) j)

--cong (Iso.fun (Iso-HIT-Σ (suc (suc zero)))) p i (cyl x j)




h1 A (suc (suc (suc n))) p xx i =
  let z = cong (Iso.fun (Iso-HIT-Σ (suc (suc (suc n))))) p
  in {!z i xx  !}


h2 A zero p = refl
h2 A (suc zero) = cong (Iso.inv (Iso-HIT-Σ (suc zero)))
h2 A (suc (suc n)) = {!cong (Iso.inv (Iso-HIT-Σ (suc zero)))!}
-- h2 A (suc (suc zero)) = cong (Iso.inv (Iso-HIT-Σ (suc (suc zero))))
-- h2 A (suc (suc (suc zero))) = cong (Iso.inv (Iso-HIT-Σ (suc (suc (suc zero)))))
-- h2 A (suc (suc (suc (suc n)))) = {!!}


