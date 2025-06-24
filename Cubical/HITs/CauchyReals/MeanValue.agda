{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.MeanValue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Fin

open import Cubical.HITs.PropositionalTruncation as PT

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
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationDer

open import Cubical.Tactics.CommRingSolver




Bishop-Proposition7 : ∀ n (f : Fin n → ℝ)
 → 0 <ᵣ foldlFin {n = n} (λ a k → a +ᵣ f k) 0 (idfun _)
 → ∃[ k ∈ Fin n ] 0 <ᵣ f k
Bishop-Proposition7 = {!!}

-- bishopDerivativeOfℙ_,_is_ : (P : ℙ ℝ) → (∀ r → r ∈ P → ℝ)
--                                     → (∀ r → r ∈ P → ℝ) → Type
-- bishopDerivativeOfℙ P , f is f' =
--   {!!}



-- uDerivativeOfℙ→at : ∀ P f f' x x∈
--    → uDerivativeOfℙ P , f is f'
--    → derivativeOfℙ P , f at (x , x∈) is (f' x x∈)
-- uDerivativeOfℙ→at P f f' x x∈ X ε =
--   PT.map (λ  λ X' h h∈ 0＃h ∣h∣<ε
--     → X' x x∈ h h∈ 0＃h
--       (isTrans≡<ᵣ _ _ _
--         (-absᵣ h ∙ cong absᵣ (sym (+IdL _)))
--         ∣h∣<ε)) {!X ?!}



Rolle'sTheorem : ∀ a b → a <ᵣ b → ∀ a∈ b∈ f f'
  → ∥ IsUContinuousℙ (intervalℙ a b) f' ∥₁
  → uDerivativeOfℙ (intervalℙ a b) , f is f'
  → f a a∈ ≡ f b b∈
  → ∀ (ε : ℚ₊) → ∃[ (x₀ , x∈) ∈ Σ _ (_∈ intervalℙ a b) ]
            absᵣ (f' x₀ x∈) <ᵣ rat (fst ε) 
Rolle'sTheorem a b a<b a∈ b∈ f f' ucf udf fa≡fb ε =
  PT.rec2 squash₁ w
    (PT.map (_$ (/2₊ ε)) ucf) (udf (/2₊ ε))
 
 where
 w : _ → _ → _
 w (δ , X) (δ' , X') = PT.rec squash₁ ww eqP
  where
  δ⊓δ' = ℚ.min₊ δ (/2₊ δ')
  eqP : ∥ Σ Partition[ a , b ] (λ pa → isStrictPartition pa × mesh≤ᵣ pa
                                  (rat (fst δ⊓δ'))) ∥₁
  eqP = {!!}
  
  ww : _
  ww (pa , str-pa , mesh-pa) = {!!}
   where
   module Pa = Partition[_,_] pa

   <f : (k : Fin (suc (suc Pa.len))) →
         f (Pa.pts' (fsuc k)) _ -ᵣ f (Pa.pts' (finj k)) _
         <ᵣ
         (f' (Pa.pts' (finj k)) _ +ᵣ rat (fst ε))
         ·ᵣ
         (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k))
   <f k = isTrans<ᵣ _ _ _ (isTrans<≡ᵣ _ _ _
     (fst (z/y<x₊≃z<y₊·x _ _ _) fromX') (·ᵣComm _ _))
          (<ᵣ-·ᵣo _ _
            (_ , x<y→0<y-x _ _ (str-pa k))
            (<ᵣ-o+ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.x/2<x ε))))
    where
    fromX' : _ <ᵣ f' (Pa.pts' (finj k)) _ +ᵣ rat (fst (/2₊ ε))
    fromX' = (isTrans≡<ᵣ _ _ _
      (cong₂ _·ᵣ_
        (cong₂ _-ᵣ_
          (cong (uncurry f) 
            (Σ≡Prop (∈-isProp (intervalℙ a b)) (sym L𝐑.lem--05)) )
          refl)
       (invℝ₊≡invℝ (_ , x<y→0<y-x _ _ (str-pa k)) _))
      (isTrans<≡ᵣ _ _ _ (a-b<c⇒a<c+b _ _ _
       (isTrans≤<ᵣ _ _ _
        (≤absᵣ _)
        (isTrans≡<ᵣ _ _ _
         (minusComm-absᵣ _ _)
           (X' (Pa.pts' (finj k)) (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
       (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k))
       (subst-∈ (intervalℙ a b)
         (sym L𝐑.lem--05)
          (Pa.a≤pts' (fsuc k) , Pa.pts'≤b (fsuc k)))
       (invEq (＃Δ _ _) (inl (str-pa k)))
       (isTrans≡<ᵣ _ _ _
         (absᵣNonNeg _ (x≤y→0≤y-x _ _ (Pa.pts'≤pts' k)))
         (isTrans≤<ᵣ _ _ _
           (isTrans≤ᵣ _ _ _
             (mesh-pa k)
             (≤ℚ→≤ᵣ (fst δ⊓δ')  (fst (/2₊ δ'))
               (ℚ.min≤' (fst δ) (fst (/2₊ δ')))))
           (<ℚ→<ᵣ _ _ (ℚ.x/2<x δ'))))))))
           (+ᵣComm _ _)))
           
   z : ∃-syntax (Fin (suc (suc Pa.len)))
        (λ k → (-ᵣ rat (fst ε))
          <ᵣ f' (Pa.pts' (finj k)) (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k)))
   z = PT.map (map-snd
           λ {l} X → 0<y-x→x<y _ _
             (isTrans<≡ᵣ _ _ _
              (isTrans≡<ᵣ _ _ _ (sym (𝐑'.0LeftAnnihilates _))
              (invEq (z/y<x₊≃z<y₊·x _ _ (_ , x<y→0<y-x _ _ (str-pa l)))
                (isTrans<≡ᵣ _ _ _ X
                (·ᵣComm _ _))))
                (cong₂ _+ᵣ_ refl
                 (sym (-ᵣInvol _)))))
        (Bishop-Proposition7 (suc (suc Pa.len))
        (λ k → (f' (Pa.pts' (finj k))
                     (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
                    +ᵣ rat (fst ε))
             ·ᵣ (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k)))
        (isTrans≡<ᵣ _ _ _
           (sym (𝐑'.+InvR' _ _ (sym fa≡fb))
             ∙ cong₂ _-ᵣ_
                (cong (f b) (∈-isProp (intervalℙ a b) _ _ _))
                (cong (f a) (∈-isProp (intervalℙ a b) _ _ _))
             ∙ sym (deltas-sum (suc (suc Pa.len))
               λ k → f (Pa.pts' k) (Pa.a≤pts' k , Pa.pts'≤b k)))
           (foldFin+< (suc Pa.len) 0 0
             _ _ (idfun _) (idfun _) (≤ᵣ-refl 0)
             <f)))
    

   z' : ∃-syntax (Fin (suc (suc Pa.len)))
        (λ k → f' (Pa.pts' (finj k)) (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
               <ᵣ rat (fst ε))
   z' = {!!} 


-- meanValue : ∀ a b → a <ᵣ b → ∀ a∈ b∈ f f'
--        → ∥ IsUContinuousℙ (intervalℙ a b) f ∥₁
--        →   uDerivativeOfℙ (intervalℙ a b) , f is f'
--        → (ε : ℚ₊) →
--           ∃[ (x₀ , x∈) ∈ Σ _ (_∈ intervalℙ a b) ]
--            absᵣ ((f b b∈ -ᵣ f a a∈)  -ᵣ f' x₀ x∈ ·ᵣ (b -ᵣ a)) <ᵣ rat (fst ε) 
-- meanValue a b a<b a∈ b∈ f f' ucf udf =
--   Rolle'sTheorem a b a<b a∈ b∈
--      h h' uch {!!} ha≡hb


--  where
--   h h' : (x : ℝ) → x ∈ intervalℙ a b → ℝ
--   h x x∈ = ((x -ᵣ a) ·ᵣ (f b b∈ -ᵣ f a a∈))
--                 -ᵣ f x x∈ ·ᵣ (b -ᵣ a)
  
--   h' x x∈ = (f b b∈ -ᵣ f a a∈) -ᵣ f' x x∈ ·ᵣ (b -ᵣ a)

--   uch : ∥ IsUContinuousℙ (intervalℙ a b) h ∥₁
--   uch = PT.map
--     {!!}
--     ucf

--   ha≡hb : h a a∈ ≡ h b b∈
--   ha≡hb = 𝐑'.+IdL' _ _ (𝐑'.0LeftAnnihilates' _ _ (+-ᵣ a))
--     ∙ sym (-ᵣ· _ _)
--     ∙ cong (_·ᵣ (b -ᵣ a)) (sym L𝐑.lem--063)
--     ∙ 𝐑'.·DistL- (f b b∈ -ᵣ f a a∈) (f b b∈) (b -ᵣ a)
--     ∙ cong₂ _-ᵣ_ (·ᵣComm _ _) refl 

-- nullDerivative→const : ∀ a b a∈ b∈ → a <ᵣ b → ∀ f 
--        → ∥ IsUContinuousℙ (intervalℙ a b) f ∥₁
--        → uDerivativeOfℙ (intervalℙ a b) , f is (λ _ _ → 0)
--        → f a a∈ ≡ f b b∈
-- nullDerivative→const a b a∈ b∈ a<b f ucf udf  =
--   eqℝ _ _ λ ε →
--     PT.rec (isProp∼ _ _ _)
--       (λ (_ , X) →
--         sym∼ _ _ _ (invEq (∼≃abs<ε _ _ _)
--           (isTrans≡<ᵣ _ _ _
--             (cong absᵣ
--               (sym (𝐑'.+IdR' _ _
--                 (cong -ᵣ_ (𝐑'.0LeftAnnihilates (b -ᵣ a))
--                  ∙ -ᵣ-rat 0))))
--             X)))
--       (meanValue a b a<b a∈ b∈ f
--         (λ _ _ → 0) ucf udf ε)
