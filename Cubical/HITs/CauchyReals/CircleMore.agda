{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.CircleMore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad


open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationDer
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Uniform
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Summation

open import Cubical.Algebra.Ring.BigOps


open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.TrigonometricIdentities
open import Cubical.HITs.CauchyReals.ArcSin

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.Relation.Binary.Base
open import Cubical.HITs.CauchyReals.Circle

open import Cubical.Tactics.CommRingSolver



cDistInj : ∀ x y → cDist x y ≡ 0 → x ≡ y
cDistInj = SQ.ElimProp2.go w
 where
 w : ElimProp2 (λ z z₁ → cDist z z₁ ≡ 0 → z ≡ z₁)
 w .ElimProp2.isPropB _ _ = isPropΠ λ _ → isSetCircle _ _
 w .ElimProp2.f a a' 1-cosΔ=0 =
   let w = cos=1⇒ (a -ᵣ a') (cong cos (·ᵣAssoc _ _ _)
            ∙ sym (𝐑'.equalByDifference _ _ 1-cosΔ=0))
    in eq/ a a' (map-snd
         (λ p → solve! ℝring ∙ p) w) 


cDist≡ℝ²-dist : ∀ x y → 2 ·ᵣ cDist x y ≡
      (sinFromCircle x -ᵣ sinFromCircle y) ^ⁿ 2
   +ᵣ ((cosFromCircle x -ᵣ cosFromCircle y) ^ⁿ 2)
cDist≡ℝ²-dist = SQ.ElimProp2.go w
 where
 w : ElimProp2 _
 w .ElimProp2.isPropB _ _ = isSetℝ _ _
 w .ElimProp2.f x y = 
     𝐑'.·DistR- _ _ _
   ∙ cong₂ _-ᵣ_
     (sym (x+x≡2x _)
      ∙ cong₂ _+ᵣ_ (sym (sin·sin+cos·cos=1 (x CRℝ.· (2 ·ᵣ π-number))))
                   (sym (sin·sin+cos·cos=1 (y CRℝ.· (2 ·ᵣ π-number)))))
     (cong (2 ·ᵣ_) (cong cos (sym (·ᵣAssoc _ _ _)
          ∙ 𝐑'.·DistL- _ _ _) ∙
           cosOfSum _ _ ∙ cong₂ _-ᵣ_ 
             (cong₂ _·ᵣ_ refl (sym (cos-even _)) )
             (cong₂ _·ᵣ_ refl (sym (sin-odd _))))
       ∙ sym (x+x≡2x _)) 
   ∙ solve! ℝring
   ∙ cong₂ _+ᵣ_
    (cong₂ _·ᵣ_ (sym (·IdL _)) refl)
    (cong₂ _·ᵣ_ (sym (·IdL _)) refl)
    
Circle→[sin,cos]-inj : ∀ x y →
                ((sinFromCircle x ≡ sinFromCircle y)
                × (cosFromCircle x ≡ cosFromCircle y))
                 → x ≡ y
Circle→[sin,cos]-inj x y (sinx≡siny , cosx≡cosy) =
  cDistInj x y (
       (sym (𝐑'.·IdL' _ _ (sym (rat·ᵣrat _ _)
        ∙ decℚ≡ᵣ?)) ∙ sym (·ᵣAssoc _ _ _))
    ∙∙ cong (rat [ 1 / 2 ] ·ᵣ_) (cDist≡ℝ²-dist x y ∙
   cong₂ _+ᵣ_
    (cong (_^ⁿ 2) (𝐑'.+InvR' _ _ sinx≡siny) ∙ 0^ⁿ 1)
    (cong (_^ⁿ 2) (𝐑'.+InvR' _ _ cosx≡cosy) ∙ 0^ⁿ 1)
   ∙ +ᵣ-rat 0 0) ∙∙ (sym (rat·ᵣrat _ _)
        ∙ decℚ≡ᵣ?)) 
  

isEquivCircle→distCircle : isEquiv Circle→distCircle
isEquivCircle→distCircle =
  isEmbedding×isSurjection→isEquiv
    (injEmbedding isSetDistCircle
      (λ {x} {y} p →
         Circle→[sin,cos]-inj x y
           (PathPΣ (cong fst p)))
    , Circle→[sin,cos]-surj)


Circle≃distCircle : Circle ≃ distCircle
Circle≃distCircle = Circle→distCircle , isEquivCircle→distCircle


