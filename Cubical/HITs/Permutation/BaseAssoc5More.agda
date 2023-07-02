{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.BaseAssoc5More where

import Cubical.Data.Nat.Base as ℕ
import Cubical.Data.Nat.Properties as ℕprops


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution

open import Cubical.Foundations.Everything
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive
-- open import Cubical.Data.Nat.Order.RecursiveMoreEquiv

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group

open import Cubical.Algebra.SymmetricGroup

import Cubical.Functions.Logic as L

open import Cubical.Functions.Embedding

open import Cubical.Data.List as Li

import Cubical.Data.Nat.FinGenAut2 as A

import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Implicit

open import Cubical.HITs.SequentialColimit as SC

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)


open import Cubical.Relation.Binary

-- import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint

import Cubical.HITs.Permutation.Base as B

open import Cubical.HITs.Permutation.BaseAssoc5

private
  variable
    ℓ : Level
    A : Type ℓ


𝕡·invol : ∀ {n m} → (x : ℙrmₐ {true} n)
         (y : ℙrmₐ {true} m)
         (s : +-sym n m ≡ sym (+-sym m n)) → 
     SquareP (λ j i → ℙrmₐ {true}
            (s j i))
       (𝕡·-comm x y)
       (symP (𝕡·-comm y x))
       (λ _ → 𝕡· x y)
       λ _ → 𝕡· y x
𝕡·invol = ℙrmElimProp₂.f₂ w
 where
 open AB
 open ℙrmElimProp₂
 w : ℙrmElimProp₂ λ {n m} (x : ℙrmₐ {true} n)
         (y : ℙrmₐ {true} m) →
         (s : +-sym n m ≡ sym (+-sym m n)) →
     SquareP (λ j i → ℙrmₐ {true}
            (s j i))
       (𝕡·-comm x y)
       (symP (𝕡·-comm y x))
       (λ _ → 𝕡· x y)
       λ _ → 𝕡· y x
 asquash₂ w _ _ = isPropΠ λ _ →
   isOfHLevelPathP' 1
    (isOfHLevelPathP' 2 (𝕡squash _) _ _) _ _
 abase₂ w {n} {m} s i j = 
  𝕡invol
    (𝕒𝕓 nothing n m nothing 
       (isSet→isSet' isSetℕₐ⁺¹
         (λ j' → +-sym n m (j' ∧ j))
         (λ j' → +-sym m n (~ j ∨ ~ j'))
         (λ _ → n + m)
         (λ i → s i j) i))

    (𝕒𝕓 nothing m n nothing
      (isSet→isSet' isSetℕₐ⁺¹
         (λ j' → +-sym n m (j ∨ ~ j'))
         (λ j' → +-sym m n (~ j ∧ j'))
         (λ _ → m + n)
         (λ i → s i j) i))

    (refl , (refl , refl , refl)) i j


lenFCSG⊥ : FCSG⊤ → ℕₐ⁺¹
lenFCSG⊥ = RecSetFCSG.f w
 where
 w : RecSetFCSG ℕₐ⁺¹
 RecSetFCSG.asquash w = isSetℕₐ⁺¹
 RecSetFCSG.●a w = one
 RecSetFCSG.·a w = _+_
 RecSetFCSG.·a-assoc w = +-assoc
 RecSetFCSG.·a-comm w = +-sym
 RecSetFCSG.·a-hexDiag w a b c =
  +-sym _ _ ∙∙ +-assoc _ _ _ ∙∙ +-sym _ _  
 RecSetFCSG.·a-pentagon-diag w _ _ _ _ =
   sym (+-assoc _ _ _) ∙ sym (+-assoc _ _ _)

fromFCSG : ∀ x → ℙrmₐ {true} (lenFCSG⊥ x)
fromFCSG = ElimFCSG.f w
 where
 w : ElimFCSG (λ z → ℙrmₐ (lenFCSG⊥ z))
 ElimFCSG.asquash w _ = 𝕡squash _
 ElimFCSG.●a w = 𝕡base
 ElimFCSG.·a w x y = 𝕡· x y
 ElimFCSG.·a-assoc w x y z = 𝕡·-assoc x y z
 ElimFCSG.·a-comm w x y = 𝕡·-comm x y
 ElimFCSG.·a-comminvol w x y = 𝕡·invol x y _
 ElimFCSG.·a-hexDiag w {n} {m} {o} a b c i =
   comp (λ k → ℙrmₐ {true} (
              (doubleCompPath-filler
                 (+-sym (lenFCSG⊥ n + lenFCSG⊥ m) (lenFCSG⊥ o))
                (+-assoc _ _ _)
                (+-sym _ _) k i)))
        (λ k → λ { (i = i0) → 𝕡·-comm (𝕡· a b) c (~ k)
                 ; (i = i1) → 𝕡·-comm (𝕡· c a) b k
               })
        (𝕡·-assoc c a b i)

 ElimFCSG.·a-hex-up w {n} {m} {o} a b c  = 
   {!zz!}           
 ElimFCSG.·a-hex-down w = {!!}
 ElimFCSG.·a-pentagon-diag w {n} {m} {o} {p}  xs ys zs ws i =
      comp (λ k → ℙrmₐ {true} (
              (compPath-filler
                 (sym (+-assoc _ (lenFCSG⊥ o) (lenFCSG⊥ p)))
                   (sym (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m) _)) k i)))
        (λ k → λ { (i = i0) → 𝕡· (𝕡· (𝕡· xs ys) zs) ws 
                 ; (i = i1) → 𝕡·-assoc xs ys (𝕡· zs ws) (~ k)
               })
        (𝕡·-assoc (𝕡· xs ys) zs ws (~ i))

 ElimFCSG.·a-pentagon-△ w = {!!}
 ElimFCSG.·a-pentagon-□ w = {!!}
