{-# OPTIONS --cubical --safe   #-}
module Cubical.HITs.NCube.SigmaDone where


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

open import Cubical.HITs.NCube.BaseVec

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying
open import Cubical.Data.Sigma.Nested.Path
open import Cubical.Data.Sigma.Nested.PathP

variable
  ℓ : Level



Iso-hlp : {A B : Type ℓ} → Iso A B → Iso (Σ[ (x₀ , x₁) ∈ A × A ] x₀ ≡ x₁ ) (Σ[ (x₀ , x₁) ∈ B × B ] x₀ ≡ x₁)
Iso-hlp isom = iso (fun' fun) (fun' inv) (sec' fun inv rightInv) (sec' inv fun leftInv)
  where

    open Iso isom

    fun' : {A B : Type ℓ} → (A → B) → (Σ[ (x₀ , x₁) ∈ A × A ] x₀ ≡ x₁ ) → (Σ[ (x₀ , x₁) ∈ B × B ] x₀ ≡ x₁)
    fun' f ((x0 , x1) , p) = ((f x0 , f x1) , cong f p)

    sec' : {A B : Type ℓ} → (f : A → B) → (g : B → A) → (section f g) → section (fun' f) (fun' g)  
    sec' f g x b i = ((x _ i) , (x _ i)) , (λ i₁ → x (snd b i₁) i)

IsoCub' : {A : Type ℓ} → ∀ n → Iso (NCube n → A ) (Cubeⁿ' n A)

Iso.fun (IsoCub' 0) x = x []
Iso.inv (IsoCub' 0) x _ = x
Iso.rightInv (IsoCub' 0) b = refl
Iso.leftInv (IsoCub' 0) a i [] = a []

IsoCub' {A = A} (suc n) = 
      _ Iso⟨ iso-NCube  ⟩
      _ Iso⟨ Iso-hlp (IsoCub' {A = A} n)  ⟩
      _ Iso⟨ invIso (Cubeⁿ'-elim-iso n) ⟩ _ ∎Iso






-- module transp-debug {A : Type} where


--   test2 : I → Cubeⁿ' 1 A → (NCube 1 → A )  →  Unit
--   test2 i x0 y0 = 
--     let z0 = {! (Iso.inv (IsoCub' 1) x0 ( boundaryInj (lid false []))) !}
--         z1 = {!!}
--         z2 = {!Iso.fun (IsoCub' 1) y0!}

--     in {!Iso.inv (IsoCub' 1) x0  (end false ∷ []) !}



-- IsoCub* : {A : Type ℓ} → ∀ n → Iso (NCube n → A ) (Cubeⁿ* n A)

-- Iso.fun (IsoCub* 0) x = x []
-- Iso.inv (IsoCub* 0) x _ = x
-- Iso.rightInv (IsoCub* 0) b = refl
-- Iso.leftInv (IsoCub* 0) a i [] = a []

-- IsoCub* {A = A} (suc n) =
--       _ Iso⟨ iso-NCube  ⟩
--       _ Iso⟨ equivToIso
--               (cong≃ (λ T → (Σ[ (x₀ , x₁) ∈ T × T ] x₀ ≡ x₁)) (isoToEquiv (IsoCub* {A = A} n)))  ⟩
--       _ Iso⟨ invIso (Cube*-elim-iso n)  ⟩ _ ∎Iso




Isoω-CubeΣ-Cubeω : ∀ {ℓ} → {A : Type ℓ}
                      → ∀ n → Isoω (Cubeⁿ' n A) (Cu A n)

Isoω.to (Isoω-CubeΣ-Cubeω zero) x _ = x
Isoω.toω (Isoω-CubeΣ-Cubeω zero) t₀ t₁ x _ i = lowerω (λ _ → x i) 
Isoω.from (Isoω-CubeΣ-Cubeω zero) x = x 1=1
-- Isoω.fromω (Isoω-CubeΣ-Cubeω zero) t₀ t₁ p = p 1=1
Isoω.sec (Isoω-CubeΣ-Cubeω zero) b = refl
Isoω.ret (Isoω-CubeΣ-Cubeω zero) a _ = refl

Isoω-CubeΣ-Cubeω {A = A} (suc n) = Isoω.precomp ww (Cubeⁿ'-elim-iso n)

   where

     module prev = Isoω (Isoω-CubeΣ-Cubeω {A = A} n)

     ww : Isoω (Σ (Cubeⁿ' n _ × Cubeⁿ' n _) (λ a → fst a ≡ snd a))
               (Cu _ (suc n))

     Isoω.to ww x i = prev.to (snd x i) 
     Isoω.toω ww t₀ t₁ x i = prev.toω (snd t₀ i) (snd t₁ i) λ j → snd (x j) i 
     Isoω.from ww x = _ , (λ i → prev.from (x i))
     Isoω.sec ww ((e0 , e1) , p) i = ((prev.sec e0 i) , prev.sec e1 i) , λ j → prev.sec (p j) i
     Isoω.ret ww a i = prev.ret (a i)







-- Isoω-CubePΣ-Cubeω : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' n (Type ℓ)) →
--                                 Isoω (CubePⁿ' n A)
--                                      (cu n (toCType n A))
-- Isoω.to (Isoω-CubePΣ-Cubeω zero A) x x₁ = x
-- Isoω.toω (Isoω-CubePΣ-Cubeω zero A) t₀ t₁ x x₁ = x
-- Isoω.from (Isoω-CubePΣ-Cubeω zero A) x = x 1=1
-- Isoω.sec (Isoω-CubePΣ-Cubeω zero A) b = refl
-- Isoω.ret (Isoω-CubePΣ-Cubeω zero A) a _ = refl

-- Isoω-CubePΣ-Cubeω (suc n) A = h
--   where

--     module ciso = Iso (CubePⁿ'-elim-iso n A)

--     h : Isoω (CubePⁿ' (suc n) A)
--           (cu (suc n) (toCType (suc n) A))

--     Isoω.to h x =
--       let ((e0 , e1) , p) = ciso.fun x
--       in λ i → Isoω.to (Isoω-CubePΣ-Cubeω n (Cubeⁿ'-elim n A i)) (p i)
--     Isoω.toω h t₀ t₁ x j =
--       let ((e0 , e1) , p) = ciso.fun (x j)
--       in {!!}
--     Isoω.from h x = ciso.inv (_ , λ i →  Isoω.from (Isoω-CubePΣ-Cubeω n (Cubeⁿ'-elim n A i)) (x i))
--     Isoω.sec h b = {!!}
--     Isoω.ret h a i = {!!}
