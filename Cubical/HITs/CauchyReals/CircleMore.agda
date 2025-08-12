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

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
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


module Stiching {ℓ} (A : Type ℓ) (a b : ℝ) (a<b : a <ᵣ b)
           (f : ∀ x → x <ᵣ b → A)
           (g : ∀ x → a <ᵣ x → A)
            where


 w₂ : (∀ x x< <x → f x x< ≡ g x <x) → ∀ x → 2-Constant (⊎.rec (f x) (g x)) 
 w₂ f=g x (inl u) (inl v)  = cong (f x) (isProp<ᵣ _ _ u v)
 w₂ f=g x (inl u) (inr v) = f=g x u v
 w₂ f=g x (inr u) (inl v) = sym (f=g x v u)
 w₂ f=g x (inr u) (inr v) = cong (g x) (isProp<ᵣ _ _ u v)


 stichSetFns : isSet A → (∀ x x< <x → f x x< ≡ g x <x) → ℝ → A
 stichSetFns isSetA f=g x = PT.rec→Set isSetA
     (⊎.rec (f x) (g x))
     (w₂ f=g x)
    (Dichotomyℝ' a x b a<b)

open Stiching public using (stichSetFns)

CircleOverlap→Circle-inj : ∀ ε → ∀ x y → 
   CircleOverlap[ ε ]→Circle x ≡  CircleOverlap[ ε ]→Circle y
   → x ≡ y
CircleOverlap→Circle-inj ε = SQ.ElimProp2.go w
 where
 w : ElimProp2
      (λ z z₁ →
         CircleOverlap[ ε ]→Circle z ≡ CircleOverlap[ ε ]→Circle z₁ →
         z ≡ z₁)
 w .ElimProp2.isPropB _ _ = isPropΠ λ _ → squash/ _ _
 w .ElimProp2.f x y x₁ = eq/ _ _
   (SQ.effective isPropCircle-rel isEquivRelCircleRel _ _ x₁)


CircleOverlap→[sin,cos]-surj : ∀ ε → isSurjection
  (Circle→distCircle ∘ CircleOverlap[ ε ]→Circle)
CircleOverlap→[sin,cos]-surj ε ((x , y) , x²+y²≡1) = 
  PT.map (λ (φ , φ∈ , sinφ≡x , cosφ≡y) →
    [ (φ ／ᵣ₊ (2 ₊·ᵣ π-number₊) +ᵣ fst (invℝ₊ (ℚ₊→ℝ₊ 2))) ,
      subst2 _<ᵣ_
        (cong₂ _+ᵣ_ (-ᵣ· _ _ ∙ cong -ᵣ_
         (·ᵣComm _ _ ∙ [x/₊y]·yᵣ _ _))
          refl ∙ 𝐑'.+InvL' _ _ refl)
        (cong₂ _+ᵣ_ (cong₂ _·ᵣ_ refl (cong fst (sym (invℝ₊· _ _)))) refl
          )
        (<ᵣ-+o _ _ (fst (invℝ₊ (ℚ₊→ℝ₊ 2)))
          (<ᵣ-·ᵣo _ _ (invℝ₊ 2 ₊·ᵣ invℝ₊ π-number₊) (fst φ∈)))
     , isTrans<≡ᵣ _ _ _
        (<ᵣ-+o _ _ (fst (invℝ₊ (ℚ₊→ℝ₊ 2)))
          (<ᵣ-·ᵣo _ _ (invℝ₊ (2 ₊·ᵣ π-number₊)) (snd φ∈)))
          (cong₂ _+ᵣ_ (·DistR+ _ _ _ ∙ +ᵣComm _ _) refl  ∙
           sym (+ᵣAssoc _ _ _)
            ∙
            cong₂ _+ᵣ_ ([x·yᵣ]/₊y _ _)
             (cong₂ _+ᵣ_ (·ᵣComm _ _ ∙
               cong₂ _·ᵣ_ (cong fst (invℝ₊· 2 π-number₊)) refl
               ∙ [x/₊y]·yᵣ _ _ ∙ invℝ₊-rat 2) (invℝ₊-rat 2)
               ∙ +ᵣ-rat _ _ ∙ decℚ≡ᵣ?)
            ∙ +ᵣComm _ _)
          ]/ 
    ,
      Σ≡Prop (λ _ → isSetℝ _ _)
      (cong₂ _,_
       ((cong sin (·DistR+ _ _ _ ∙
         cong₂ _+ᵣ_ ([x/₊y]·yᵣ _ _) (cong₂ _·ᵣ_ refl (·ᵣComm _ _)
           ∙ ·ᵣComm _ _ ∙ [x·yᵣ]/₊y _ _)) ∙ sin[x]=-sin[x+π] _)
        ∙ cong -ᵣ_ sinφ≡x ∙ -ᵣInvol _)
       ((cong cos (·DistR+ _ _ _ ∙
         cong₂ _+ᵣ_ ([x/₊y]·yᵣ _ _) (cong₂ _·ᵣ_ refl (·ᵣComm _ _)
           ∙ ·ᵣComm _ _ ∙ [x·yᵣ]/₊y _ _)) ∙ cos[x]=-cos[x+π] _)
        ∙ cong -ᵣ_ cosφ≡y ∙ -ᵣInvol _)
       ))
    (distCircle→angle (ε ₊·ᵣ (2 ₊·ᵣ π-number₊)) (-ᵣ x) (-ᵣ y)
    (cong₂ _+ᵣ_ (sym (^ⁿ-even 1 x)) (sym (^ⁿ-even 1 y))  ∙
      cong₂ _+ᵣ_ (x^²=x·x _) (x^²=x·x _) ∙ x²+y²≡1))


CircleOverlap≃distCircle : ∀ ε → CircleOverlap[ ε ] ≃ distCircle
CircleOverlap≃distCircle ε = Circle→distCircle ∘ CircleOverlap[ ε ]→Circle
  , isEmbedding×isSurjection→isEquiv
   (snd (compEmbedding (Circle→distCircle , injEmbedding isSetDistCircle
      (λ {x} {y} p →
         Circle→[sin,cos]-inj x y
           (PathPΣ (cong fst p))))
           (_ , injEmbedding squash/
            (CircleOverlap→Circle-inj ε _ _)))
   , CircleOverlap→[sin,cos]-surj ε)


fromWeldedInterval : ∀ {ℓ} (A : Type ℓ) → Type ℓ
fromWeldedInterval A =
 Σ (∀ x → x ∈ intervalℙ 0 1 → A)
   λ f → f 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ f 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)

circle0 : distCircle
circle0  = (1 , 0) ,
  cong₂ _+ᵣ_ (sym (rat·ᵣrat _ _)) (sym (rat·ᵣrat _ _))
                                    ∙ +ᵣ-rat _ _


opaque

 -- injCircle0≡circle0 : Circle→distCircle (injCircle 0) ≡ circle0
 -- injCircle0≡circle0 = distCircle≡ {!!} {!!}
 circle+ : distCircle → distCircle → distCircle
 circle+ ((a , b) , p) ((c , d) , q) = 
   ((a ·ᵣ c -ᵣ b ·ᵣ d) , a ·ᵣ d +ᵣ b ·ᵣ c) ,
     (solve! ℝring)
       ∙ cong₂ _·ᵣ_
       (p)
       (q) ∙ sym (rat·ᵣrat 1 1)

 circleNeg : distCircle → distCircle
 circleNeg ((x , y) , p) =
  (x , -ᵣ y) , cong₂ _+ᵣ_ refl (-ᵣ·-ᵣ _ _) ∙ p

ℝS¹AbGroupStr : AbGroupStr distCircle
ℝS¹AbGroupStr .AbGroupStr.0g = circle0 
ℝS¹AbGroupStr .AbGroupStr._+_  = circle+
ℝS¹AbGroupStr .AbGroupStr.-_  = circleNeg
ℝS¹AbGroupStr .AbGroupStr.isAbGroup = IsAbGroupℝS¹
  where
  opaque
   unfolding circle+ circleNeg
   IsAbGroupℝS¹ : IsAbGroup
     circle0
     circle+
     circleNeg 
   IsAbGroupℝS¹ = 
      makeIsAbGroup isSetDistCircle
      (λ _ _ _ → distCircle≡ (solve! ℝring) (solve! ℝring))
      (λ _ → distCircle≡ (cong₂ _+ᵣ_ (·IdR _) (cong -ᵣ_ (𝐑'.0RightAnnihilates _)) 
          ∙ 𝐑'.+IdR' _ _ (-ᵣ-rat 0))
        (cong₂ _+ᵣ_ (𝐑'.0RightAnnihilates _ ) (·IdR _)
          ∙ +IdL _))
      (λ (_ , p) → distCircle≡ (solve! ℝring ∙ p) (solve! ℝring))
      λ _ _ → distCircle≡ (solve! ℝring) (solve! ℝring)


ℝS¹AbGroup : AbGroup ℓ-zero
ℝS¹AbGroup = _ , ℝS¹AbGroupStr


interpℝ0 : ∀ a b → interpℝ a b 0 ≡ a 
interpℝ0 a b = solve! ℝring

interpℝ1 : ∀ a b → interpℝ a b 1 ≡ b 
interpℝ1 a b = cong₂ _+ᵣ_ refl (·IdL _) ∙ solve! ℝring

pathFromToCircle∃ : (x₀ x₁ : Circle) →
              ∃[ p ∈ (∀ x → x ∈ intervalℙ 0 1 → Circle) ]
                (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ x₀)
                 × (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ x₁)
pathFromToCircle∃ = SQ.ElimProp2.go w
 where
 w : ElimProp2 _
 w .ElimProp2.isPropB _ _ = squash₁
 w .ElimProp2.f x y = ∣ (λ t _ → injCircle (interpℝ x y t)) ,
   cong injCircle (interpℝ0 x y) , cong injCircle (interpℝ1 x y) ∣₁


-- pathFromTo : (x₀ x₁ : distCircle) →
--               Σ[ p ∈ (∀ x → x ∈ intervalℙ 0 1 → distCircle) ]
--                 (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ x₀)
--                  × (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ x₀)
-- pathFromTo = {!!}

module ℝS¹ where
 open AbGroupStr ℝS¹AbGroupStr public


rotationIso : distCircle → Iso distCircle distCircle
rotationIso x .Iso.fun = ℝS¹._+ x
rotationIso x .Iso.inv = ℝS¹._- x
rotationIso x .Iso.rightInv a =
  sym (ℝS¹.+Assoc _ _ _) ∙ cong (a ℝS¹.+_) (ℝS¹.+InvL _) ∙ ℝS¹.+IdR _ 
rotationIso x .Iso.leftInv a =
  sym (ℝS¹.+Assoc _ _ _) ∙ cong (a ℝS¹.+_) (ℝS¹.+InvR _) ∙ ℝS¹.+IdR _ 

rotationEquiv : distCircle → distCircle ≃ distCircle
rotationEquiv x = isoToEquiv (rotationIso x)

opaque
 unfolding circle+ circleNeg
 rotationEquivPresDist : ∀ x y z →
    cartDist² (fst x) (fst y) ≡ cartDist² (fst (x ℝS¹.+ z)) (fst (y ℝS¹.+ z)) 
 rotationEquivPresDist x y z =
    sym (𝐑'.·IdR' _ _ (snd z)) ∙ solve! ℝring


-- extendUCAcrossIntervals : ∀ {a b c} → a <ᵣ b → b <ᵣ c
--    → ∀ f g
--    → IsUContinuousℙ (intervalℙ a b) f
--    → IsUContinuousℙ (intervalℙ b c) g
--    → Σ[ h ∈ _ ] (IsUContinuousℙ (intervalℙ a c) h ×
--        ((∀ x x∈ x∈' → f x x∈ ≡ h x x∈')
--         × (∀ x x∈ x∈' → g x x∈ ≡ h x x∈')))
   
-- extendUCAcrossIntervals = {!!}


-- fromFWI :  (fwi : fromWeldedInterval ℝ)
--         → (IsUContinuousℙ (intervalℙ 0 1) (fst fwi))
--         → Σ[ f ∈ (distCircle → ℝ) ]
--            (∀ x x∈ → f (Circle→distCircle (injCircle (fst fwi x x∈)))
--              ≡ fst fwi x x∈)
               
-- fromFWI fwi uc = {!!}
--  -- where
 

fromInterval→ℝ-uC : Type
fromInterval→ℝ-uC = Σ _ (IsUContinuousℙ (intervalℙ 0 1))


rotateToOrigin : ∀ D (x : distCircle) → Iso
       (Σ distCircle λ x' → cartDist² (fst x) (fst x') <ᵣ D)
       (Σ distCircle λ x' → cartDist² (fst circle0) (fst x') <ᵣ D)
rotateToOrigin D x@((X , Y) , _) = w
 where
 open GroupTheory (AbGroup→Group ℝS¹AbGroup)
 
 w : Iso (Σ distCircle (λ x' → cartDist² (fst x) (fst x') <ᵣ D))
         (Σ distCircle (λ x' → cartDist² (fst circle0) (fst x') <ᵣ D))
 w .Iso.fun (p@((X' , Y') , _) , d) = p ℝS¹.- x ,
  isTrans≡<ᵣ _ _ _ (cong₂ cartDist² (cong fst (sym (ℝS¹.+InvR x)) ) refl
    ∙ sym (rotationEquivPresDist x p (ℝS¹.- x))) d
   
 w .Iso.inv (p@((X' , Y') , _) , d) = p ℝS¹.+ x ,
   isTrans≡<ᵣ _ _ _ ((cong₂ cartDist² (cong fst (sym (ℝS¹.+IdL _)) ) refl
    ∙ sym (rotationEquivPresDist circle0 p x))) d 
 w .Iso.rightInv _ = Σ≡Prop (λ _ → isProp<ᵣ _ _)
                 (sym (ℝS¹.+Assoc _ x (ℝS¹.- x))
                   ∙ cong (_ ℝS¹.+_) (ℝS¹.+InvR _) ∙ ℝS¹.+IdR _)
 w .Iso.leftInv _ = Σ≡Prop (λ _ → isProp<ᵣ _ _)
                 (sym (ℝS¹.+Assoc _ (ℝS¹.- x) x)
                   ∙ cong (_ ℝS¹.+_) (ℝS¹.+InvL _) ∙ ℝS¹.+IdR _)


openHalfCircleIso : Iso
                     (Σ _ (_∈ ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ])))
                     (Σ distCircle λ ((_ , y) , _) → 0 <ᵣ y)
openHalfCircleIso = w
 where
 f : ∀ x →  x ∈ ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ]) →
      rat [ pos 0 / 1+ 0 ] <ᵣ
      cos
       (x ·ᵣ (rat [ pos 2 , (1+ 0) ]/ ·ᵣ
        (rat [ pos 2 , (1+ 0) ]/ ·ᵣ π-number/2))) 
 f x x∈ = ∣x∣<π/2→0<cos[x] _
    (subst2 (λ a b →
      x ·ᵣ a
      ∈ ointervalℙ (-ᵣ b) b )
      (cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl ∙ sym (·ᵣAssoc _ _ _) )
      ( (·ᵣAssoc _ _ _) ∙ 𝐑'.·IdL' _ _ (sym (rat·ᵣrat _ _) ∙ decℚ≡ᵣ?))
      (scale-sym-ointervalℙ (rat [ 1 / 4  ]) (4 ₊·ᵣ π-number/2₊) x x∈))

 inv∈ : ∀ x y → cartNorm² (x , y) ≡ rat [ pos 1 / 1+ 0 ]
       → 0 <ᵣ y → ∀ x∈ →  arcSin⟨⟩ x x∈ ·ᵣ fst (invℝ₊ (π-number/2₊ ₊·ᵣ 4)) ∈
      ointervalℙ (-ᵣ rat [ 1 / 4 ]) (rat [ 1 / 4 ])
 inv∈ x y p 0<y x∈ =
   subst {x = fst π-number/2₊ ·ᵣ
                 fst
                 (invℝ₊
                  ((π-number/2 , π-number/2₊ .snd) ₊·ᵣ
                   (rat (4 .fst) , ℚ₊→ℝ₊ 4 .snd)))}
      {y = fst (ℚ₊→ℝ₊ (invℚ₊ 4))}
      (λ b →
      arcSin⟨⟩ x x∈ ·ᵣ fst (invℝ₊ (π-number/2₊ ₊·ᵣ 4))
      ∈ ointervalℙ (-ᵣ b) b )
        (cong₂ _·ᵣ_ refl (·invℝ₊ _ _)
        ∙ ·ᵣAssoc _ _ _ ∙
         cong₂ _·ᵣ_ (x·invℝ₊[x] π-number/2₊ ) (invℝ₊-rat 4) ∙ ·IdL _)
         (scale-sym-ointervalℙ (fst π-number/2₊) (invℝ₊ (π-number/2₊ ₊·ᵣ 4 ))
         (arcSin⟨⟩ x x∈) (arcSin⟨⟩∈ x x∈))

 w : Iso _ _
 w .Iso.fun (t , t∈) = Circle→distCircle (injCircle t) , f t t∈
 w .Iso.inv (((x , y) , p) , 0<y) =
  arcSin⟨⟩ x x∈ ·ᵣ fst (invℝ₊ (π-number/2₊ ₊·ᵣ 4)) , inv∈ x y p 0<y x∈
  
       
  where
   x∈ : x ∈ ointervalℙ -1 1
   x∈ = subst (λ b → x ∈ ointervalℙ b 1)
     (-ᵣ-rat 1)
      (abs<→ointerval x 1
        (x²<1→∣x∣<1 _ (isTrans<≡ᵣ _ _ _
          (isTrans≡<ᵣ _ _ _ 
            (x^²=x·x x ∙ sym (+IdR _))
            (<ᵣ-o+ _ _ (x ·ᵣ x) (snd ((y , 0<y) ₊·ᵣ (y , 0<y))))
            )
          p)))


 w .Iso.rightInv (((x , y) , p) , 0<y) = Σ≡Prop (λ _ → isProp<ᵣ _ _)
   (distCircle≡ p-sin (
      cong fst (invEq (congEquiv {x = _ , f _ (inv∈ x y p 0<y _)}
       {_ , 0<y} (_ , isEquiv-₊^ⁿ 2))
       (ℝ₊≡ $ (x^²=x·x _ ∙
         cos·cos=1-sin·sin φ) ∙∙  cong (_-ᵣ_ 1)
        (cong₂ _·ᵣ_ p-sin p-sin)
       
        ∙ sym (cong (_-ᵣ (x ·ᵣ x))
         ( (+ᵣComm _ _ ∙ p))) ∙  (𝐑'.plusMinus _ _)
         ∙∙ sym (x^²=x·x y) ))))
  where
   φ = _
   p-sin : sin φ ≡ _
   p-sin = (cong sin (cong₂ _·ᵣ_ refl (
     (·ᵣAssoc _ _ _ ∙ cong₂ _·ᵣ_ (sym (rat·ᵣrat _ _)) refl)
    ∙ ·ᵣComm _ _ )
     ∙ [x/₊y]·yᵣ _ (π-number/2₊ ₊·ᵣ 4)) ∙
           sin∘arcSin⟨⟩ _ _)
 w .Iso.leftInv (t , t∈) =
  Σ≡Prop
      (∈-isProp (ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ])))
       (cong₂ _·ᵣ_ (arcSin⟨⟩∘sin _ _
        ((subst2 (λ a b →
      t ·ᵣ a
      ∈ ointervalℙ (-ᵣ b) b )
      (cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl ∙ sym (·ᵣAssoc _ _ _) )
      ( (·ᵣAssoc _ _ _) ∙ 𝐑'.·IdL' _ _ (sym (rat·ᵣrat _ _) ∙ decℚ≡ᵣ?))
      (scale-sym-ointervalℙ (rat [ 1 / 4  ]) (4 ₊·ᵣ π-number/2₊) t t∈))))
        (cong (fst ∘ invℝ₊) (ℝ₊≡ {y = 2 ₊·ᵣ (2 ₊·ᵣ π-number/2₊)}
         (·ᵣComm _ _
         ∙ cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl ∙ sym (·ᵣAssoc _ _ _))))
         ∙ [x·yᵣ]/₊y _ _)





record MetricSpaceStr {ℓ} (A : Type ℓ) : Type ℓ where

  constructor metricSpaceStr

  field
   is-set : isSet A
   𝑑[_,_] : A → A → ℝ
   𝑑-nonNeg : ∀ x y → 0 ≤ᵣ 𝑑[ x , y ]
   𝑑-sym : ∀ x y → 𝑑[ x , y ] ≡ 𝑑[ y , x ]
   𝑑-pos : ∀ x y → (0 <ᵣ 𝑑[ x , y ]) → x ≡ y → ⊥
   𝑑-zero→≡ : ∀ x y → 0 ≡ 𝑑[ x , y ] → x ≡ y
   𝑑-≡→zero : ∀ x y → x ≡ y → 0 ≡ 𝑑[ x , y ]
   𝑑-triangle : ∀ x y z → 𝑑[ x , z ] ≤ᵣ 𝑑[ x , y ] +ᵣ 𝑑[ y , z ]
   
MetricSpace : ∀ ℓ → Type (ℓ-suc ℓ)
MetricSpace ℓ = TypeWithStr ℓ MetricSpaceStr

MetricSpace₀ = MetricSpace ℓ-zero

ℝMetricSpace : MetricSpace₀
ℝMetricSpace .fst = ℝ
ℝMetricSpace .snd .MetricSpaceStr.is-set = isSetℝ
ℝMetricSpace .snd .MetricSpaceStr.𝑑[_,_] x y = absᵣ (x -ᵣ y)
ℝMetricSpace .snd .MetricSpaceStr.𝑑-nonNeg _ _ = 0≤absᵣ _
ℝMetricSpace .snd .MetricSpaceStr.𝑑-sym = minusComm-absᵣ
ℝMetricSpace .snd .MetricSpaceStr.𝑑-pos _ _ 0<d x=y =
  ≤ᵣ→≯ᵣ (absᵣ _) 0
   (≡ᵣWeaken≤ᵣ _ _ (cong absᵣ (𝐑'.+InvR' _ _ x=y) ∙ absᵣ0)) 0<d
ℝMetricSpace .snd .MetricSpaceStr.𝑑-zero→≡ _ _ 0=d =
  𝐑'.equalByDifference _ _ (absᵣx=0→x=0 _ (sym 0=d))
ℝMetricSpace .snd .MetricSpaceStr.𝑑-≡→zero _ _ 0=d =
  sym absᵣ0 ∙ cong absᵣ (sym (𝐑'.+InvR' _ _ 0=d))
ℝMetricSpace .snd .MetricSpaceStr.𝑑-triangle = absᵣ-triangle-midpt

MetricSubSpace : ∀ {ℓ} (A : Type ℓ) → (P : ℙ A)
  → MetricSpaceStr A
  → MetricSpaceStr (Σ A (_∈ P))
MetricSubSpace A P msp = w
 where
 open MetricSpaceStr msp
 w : MetricSpaceStr (Σ A (_∈ P))
 w .MetricSpaceStr.is-set = isSetΣ is-set (isProp→isSet ∘ ∈-isProp P)
 w .𝑑[_,_] (x , _) (y , _) = 𝑑[ x , y ] 
 w .𝑑-nonNeg _ _ = 𝑑-nonNeg _ _
 w .𝑑-sym _ _ = 𝑑-sym _ _
 w .𝑑-pos _ _ 0<d = 𝑑-pos _ _ 0<d ∘ cong fst
 w .𝑑-zero→≡ _ _ 0=d = Σ≡Prop (∈-isProp P) (𝑑-zero→≡ _ _ 0=d)
 w .𝑑-≡→zero _ _ = 𝑑-≡→zero _ _ ∘ cong fst
 w .𝑑-triangle _ _ _ = 𝑑-triangle _ _ _


IsUContMap : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
         (AM : MetricSpaceStr A) (f : A → B) (BM : MetricSpaceStr B)
         → Type ℓ
IsUContMap AM f BM =
 ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
   ∀ x y → AM.𝑑[ x , y ] <ᵣ rat (fst δ)
         → BM.𝑑[ f x , f y ] <ᵣ rat (fst ε)
 where
    module AM = MetricSpaceStr AM
    module BM = MetricSpaceStr BM

UContMap : ∀ {ℓ ℓ'} → MetricSpace ℓ → MetricSpace ℓ' → Type (ℓ-max ℓ ℓ')
UContMap (_ , A) (_ , B) = Σ _ λ f → ∥ IsUContMap A f B ∥₁



IntervalMetricSpace : MetricSpace₀
IntervalMetricSpace = _ , MetricSubSpace _  (intervalℙ 0 1) (snd ℝMetricSpace)


0≡NonNeg+NonNeg→both≡0 : ∀ (x y : ℝ₀₊) → 0 ≡ fst x +ᵣ fst y →
                          ((fst x ≡ 0) × (fst y ≡ 0)) 
0≡NonNeg+NonNeg→both≡0 = {!!}

𝐑²MetricSpaceStr : MetricSpaceStr (ℝ × ℝ)
𝐑²MetricSpaceStr .MetricSpaceStr.is-set = isSet× isSetℝ isSetℝ
𝐑²MetricSpaceStr .MetricSpaceStr.𝑑[_,_] x y = fst (root 2 {!!}) --nthcartDist²
𝐑²MetricSpaceStr .MetricSpaceStr.𝑑-nonNeg _ _ = {!!}
  -- isTrans≡≤ᵣ _ _ _ (solve! ℝring)
  --   (≤ᵣMonotone+ᵣ _ _ _ _
  --     (isTrans≤≡ᵣ _ _ _ (0≤ᵣx² _) (x^²=x·x _))
  --     (isTrans≤≡ᵣ _ _ _ (0≤ᵣx² _) (x^²=x·x _)))
𝐑²MetricSpaceStr .MetricSpaceStr.𝑑-sym = {!!} --cartDis²Comm
𝐑²MetricSpaceStr .MetricSpaceStr.𝑑-pos x y 0<D x≡y = {!!}
  -- isIrrefl<ᵣ _ (isTrans≡<ᵣ _ _ _
  --   (cong (cartDist² x) (sym x≡y) ∙ solve! ℝring)
  --   0<D)
𝐑²MetricSpaceStr .MetricSpaceStr.𝑑-zero→≡ x y 0≡d = {!!}
  -- let (p , q) = 0≡NonNeg+NonNeg→both≡0 (_ , 0≤x·ᵣx _) (_ , 0≤x·ᵣx _) 0≡d
  --     p' = 𝐑'.equalByDifference _ _ (x²≡0→x≡0 _ p)
  --     q' = 𝐑'.equalByDifference _ _ (x²≡0→x≡0 _ q)
  -- in cong₂ _,_ p' q'
𝐑²MetricSpaceStr .MetricSpaceStr.𝑑-≡→zero x y x≡y = {!!}
  -- solve! ℝring ∙ cong (cartDist² x) x≡y
𝐑²MetricSpaceStr .MetricSpaceStr.𝑑-triangle x y z = {!!}
  -- isTrans≤≡ᵣ _ _ _
  --   (≤ᵣMonotone+ᵣ _ (((x .fst +ᵣ -ᵣ y .fst) ·ᵣ (x .fst +ᵣ -ᵣ y .fst))
  --     +ᵣ
  --     ((y .fst +ᵣ -ᵣ z .fst) ·ᵣ (y .fst +ᵣ -ᵣ z .fst))) _ {!!}
  --     {!!}
  --     {!!})
  --   {!!}


-- distCircleMetricSpaceStr : MetricSpaceStr distCircle 
-- distCircleMetricSpaceStr =
--  MetricSubSpace (ℝ × ℝ)
--   (λ z → (cartNorm² z ≡ 1) , isSetℝ _ _)
--   𝐑²MetricSpaceStr


-- unwindDistCirclePath :
--    (f : IntervalMetricSpace .fst → distCircle)
--  → IsUContMap (snd IntervalMetricSpace) f distCircleMetricSpaceStr
--  → Σ ((fst IntervalMetricSpace) → ℝ)
--    λ g → ∀ x → f x ≡ f (0 , (decℚ≤ᵣ? , decℚ≤ᵣ?)) ℝS¹.+
--      Circle→distCircle (injCircle (g x)) 
-- unwindDistCirclePath = {!!}
