{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.RealHomotopy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
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
-- open import Cubical.Data.Fin

import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos;ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.GroupoidTruncation as GT

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
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing.Base
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.TrigonometricIdentities
open import Cubical.HITs.CauchyReals.ArcSin

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.HITs.GroupoidQuotients as GQ renaming ([_] to [_]//)
open import Cubical.Relation.Binary.Base
open import Cubical.HITs.CauchyReals.Circle
open import Cubical.HITs.CauchyReals.CircleMore
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.Group.Instances.Int

open import Cubical.Categories.Category

open import Cubical.WildCat.Base

open import Cubical.Algebra.Group.ZAction

open import Cubical.Structures.Pointed
open import Cubical.Structures.Product

import Cubical.Homotopy.Loopspace as Lsp
import Cubical.Homotopy.Group.Base as HG

open import Cubical.HITs.SequentialColimit as Seq
open import Cubical.Data.Sequence
import Cubical.Foundations.Pointed as P


-- Iso.fun (PathIdTrunc₀Iso {b = b}) p =
--   transport (λ i → rec {B = TypeOfHLevel _ 1} (isOfHLevelTypeOfHLevel 1)
--                         (λ a → ∥ a ≡ b ∥₁ , squash₁) (p (~ i)) .fst)
--             ∣ refl ∣₁
-- Iso.inv PathIdTrunc₀Iso = pRec (squash₂ _ _) (cong ∣_∣₂)
-- Iso.rightInv PathIdTrunc₀Iso _ = squash₁ _ _
-- Iso.leftInv PathIdTrunc₀Iso _ = squash₂ _ _ _ _

congSq₂ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} →
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  {a'₀₀ a'₀₁ : A} {a'₀₋ : a'₀₀ ≡ a'₀₁}
  {a'₁₀ a'₁₁ : A} {a'₁₋ : a'₁₀ ≡ a'₁₁}
  {a'₋₀ : a'₀₀ ≡ a'₁₀} {a'₋₁ : a'₀₁ ≡ a'₁₁}
  → (f : A → A → B)
  → Square (a₀₋) (a₁₋) (a₋₀) (a₋₁)
  → Square (a'₀₋) (a'₁₋) (a'₋₀) (a'₋₁)
  → Square (λ i → f (a₀₋ i) (a'₀₋ i))
           (λ i → f (a₁₋ i) (a'₁₋ i))
           (λ i → f (a₋₀ i) (a'₋₀ i))
           (λ i → f (a₋₁ i) (a'₋₁ i))
congSq₂ f x x₁ i j = f (x i j) (x₁ i  j) 
{-# INLINE congSq₂ #-}

congSqP : ∀ {ℓ ℓ'} {A : I → I → Type ℓ} {B : I → I → Type ℓ'}
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
  {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
  → (f : ∀ i j → A i j → B i j)
  → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
  → SquareP B (congP (f i0) a₀₋) (congP (f i1) a₁₋)
              (congP (λ i → f i i0) a₋₀) (congP (λ i → f i i1) a₋₁)
congSqP f sq i j = f i j (sq i j)
{-# INLINE congSqP #-}

--  stichGpdFns : isGroupoid A → (∀ x x< <x → f x x< ≡ g x <x) → ℝ → A
--  stichGpdFns gpdA f=g x =
--    PT.rec→Gpd gpdA (⊎.rec (f x) (g x))
--     (w x)
--      (Dichotomyℝ' a x b a<b)
--   where

--   w-coh : ∀ x → (x₂ y z : (x <ᵣ b) ⊎ (a <ᵣ x)) →
--       Square (w₂ f=g x x₂ y) (w₂ f=g x x₂ z) refl (w₂ f=g x y z)
--   w-coh x (inl x₁) (inl x₂) (inl x₃) =
--     congP (λ _ → cong (f x)) (isProp→SquareP (λ _ _ → isProp<ᵣ _ _) _ _ _ _)
--   w-coh x (inl x₁) (inl x₂) (inr x₃) =
--     {!!} ▷ {!!} ∙
--      cong₂ _∙_ refl (λ _ j → f=g x {!isProp<ᵣ x b x₁ x₂ j  !} x₃ i1) ∙ sym (rUnit _)
--     -- f=g x {!!} x₃ (i ∧ j)
--     -- let zz = congSqP
--     --        (λ i j x< →
--     --        f=g x x< x₃ (i ∧ j))
--     --        (isSet→isSet' (isProp→isSet (isProp<ᵣ x b))
--     --           refl {!!} refl {!!})
--     -- in {!zz!}
--   w-coh x (inl x₁) (inr x₂) (inl x₃) = {!!}
--   w-coh x (inl x₁) (inr x₂) (inr x₃) = {!!}
--   w-coh x (inr x₁) (inl x₂) (inl x₃) = {!!}
--   w-coh x (inr x₁) (inl x₂) (inr x₃) = {!!}
--   w-coh x (inr x₁) (inr x₂) (inl x₃) = {!!}
--   w-coh x (inr x₁) (inr x₂) (inr x₃) =
--     congP (λ _ → cong (g x)) (isProp→SquareP (λ _ _ → isProp<ᵣ _ _) _ _ _ _)
  
--   w : ∀ x → 3-Constant (⊎.rec (f x) (g x))
--   w x .3-Constant.link = w₂ f=g x
--   w x .3-Constant.coh₁ = w-coh x
--   -- w x .3-Constant.coh₁ (inl x₁) (inl x₂) (inl x₃) =
--   --   congP (λ _ → cong (f x)) (isProp→SquareP (λ _ _ → isProp<ᵣ _ _) _ _ _ _)
--   -- w x .3-Constant.coh₁ (inl x₁) (inl x₂) (inr x₃) =
--   --  let z = congSqP
--   --          (λ i j x< →
--   --          f=g x x< x₃ (i ∧ j))
--   --          (isProp→SquareP (λ _ _ → isProp<ᵣ x b)
--   --            {!!}
--   --            {!!}
--   --            {!!}
--   --            {!!})
--   --  in {!z!}
--   --   -- congP (λ i → congP (λ j y → f=g x {!!} {!!} (i ∧ j)))
--   --   --      (isProp→SquareP (λ _ _ → isProp<ᵣ _ _) _ _ _ _)
--   -- w x .3-Constant.coh₁ (inl x₁) (inr x₂) (inl x₃) = {!!}
--   -- w x .3-Constant.coh₁ (inl x₁) (inr x₂) (inr x₃) = {!!}
--   -- w x .3-Constant.coh₁ (inr x₁) (inl x₂) (inl x₃) = {!!}
--   -- w x .3-Constant.coh₁ (inr x₁) (inl x₂) (inr x₃) = {!!}
--   -- w x .3-Constant.coh₁ (inr x₁) (inr x₂) (inl x₃) = {!!}
--   -- w x .3-Constant.coh₁ (inr x₁) (inr x₂) (inr x₃) =
--   --  congP (λ _ → cong (g x)) (isProp→SquareP (λ _ _ → isProp<ᵣ _ _) _ _ _ _)
-- -- stichGpdFns : ∀ {ℓ} (A : Type ℓ) → (isGroupoid A) → (a b : ℝ) → a <ᵣ b
-- --            → (f : ∀ x → x <ᵣ b → A)
-- --            → (g : ∀ x → a <ᵣ x → A)
-- --            → (∀ x x< <x → f x x< ≡ g x <x)
-- --            → ℝ → A
-- -- stichGpdFns A isGroupoidA a b a<b f g f=g x =
-- --   PT.rec→Gpd isGroupoidA
-- --     (⊎.rec (f x) (g x))
-- --     w
-- --    (Dichotomyℝ' a x b a<b)
-- --  where
-- --  w : 3-Constant (⊎.rec (f x) (g x))
-- --  w .3-Constant.link = {!!}
-- --  w .3-Constant.coh₁ = {!!}
-- --  -- w : 2-Constant (⊎.rec (f x) (g x))
-- --  -- w (inl u) (inl v) = cong (f x) (isProp<ᵣ _ _ u v)
-- --  -- w (inl u) (inr v) = f=g x u v
-- --  -- w (inr u) (inl v) = sym (f=g x v u)
-- --  -- w (inr u) (inr v) = cong (g x) (isProp<ᵣ _ _ u v)





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


isUContMap∘ : ∀ {ℓ ℓ' ℓ''}
  → (A : MetricSpace ℓ)
  → (B : MetricSpace ℓ')
  → (C : MetricSpace ℓ'')
  → ∀ f g
  → IsUContMap (snd B) f (snd C)
  → IsUContMap (snd A) g (snd B)
  → IsUContMap (snd A) (f ∘ g) (snd C)  
isUContMap∘ = {!!}

uContConstMap : ∀ {ℓ ℓ'}
  → (A : MetricSpace ℓ)
  → (B : MetricSpace ℓ')
  → (b : ⟨ B ⟩) → IsUContMap (snd A) (const b) (snd B) 
uContConstMap A B a = (λ ε → 1 , λ _ _ _ → isTrans≡<ᵣ _ _ _ {!!} {!!} )

Interval²MetricSpaceStr : MetricSpaceStr
 ((Σ ℝ (_∈ intervalℙ 0 1)) × (Σ ℝ (_∈ intervalℙ 0 1)))
Interval²MetricSpaceStr = {!!}

Interval²MetricSpace : MetricSpace₀
Interval²MetricSpace = (Σ ℝ (_∈ intervalℙ 0 1)) × (Σ ℝ (_∈ intervalℙ 0 1))
  , Interval²MetricSpaceStr
  --MetricSubSpace _  (intervalℙ 0 1) (snd ℝMetricSpace)


𝐿₁-Metric : ∀ {ℓ}
  → (A : MetricSpace ℓ)
  → UContMap IntervalMetricSpace A
  → UContMap IntervalMetricSpace A → ℝ 
𝐿₁-Metric A f g = {!!}

UContMapEq : ∀ {ℓ ℓ'} → (A : MetricSpace ℓ)
          → (A' : MetricSpace ℓ') →
            (f g : UContMap A A')
            → (∀ x → fst f x ≡ fst g x ) → f ≡ g
UContMapEq A A' f g x = Σ≡Prop (λ _ → squash₁) (funExt x)

𝐿₁-MetricSpace : ∀ {ℓ}
  → (A : MetricSpace ℓ)
  → MetricSpaceStr (UContMap IntervalMetricSpace A) 
𝐿₁-MetricSpace A = w
 where
 module AM = MetricSpaceStr (snd A)

 w : MetricSpaceStr (UContMap IntervalMetricSpace A)
 w .MetricSpaceStr.is-set =
   isSetΣ (isSet→ AM.is-set) λ _ → isProp→isSet squash₁
 w .MetricSpaceStr.𝑑[_,_] = 𝐿₁-Metric A
 w .MetricSpaceStr.𝑑-nonNeg = {!!}
 w .MetricSpaceStr.𝑑-sym = {!c!}
 w .MetricSpaceStr.𝑑-pos = {!!}
 w .MetricSpaceStr.𝑑-zero→≡ = {!!}
 w .MetricSpaceStr.𝑑-≡→zero = {!!}
 w .MetricSpaceStr.𝑑-triangle = {!!}

𝐿₁-MetricSpaceⁿ :  ∀ {ℓ} → ℕ → MetricSpace ℓ → MetricSpace ℓ 
𝐿₁-MetricSpaceⁿ zero A = A
𝐿₁-MetricSpaceⁿ (suc n) A = _ , 𝐿₁-MetricSpace (𝐿₁-MetricSpaceⁿ n A)


private
 variable
  ℓ ℓ' : Level

∙MetricSpaceStr : Type ℓ → Type ℓ
∙MetricSpaceStr = ProductStructure PointedStructure MetricSpaceStr

∙MetricSpace : ∀ ℓ → Type (ℓ-suc ℓ)
∙MetricSpace ℓ = TypeWithStr ℓ ∙MetricSpaceStr

∙MetricSpace→Pointed : ∀ {ℓ} → ∙MetricSpace ℓ → P.Pointed ℓ
∙MetricSpace→Pointed (A , a , _) = (A , a)

∙MetricSpace→MetricSpace : ∀ {ℓ} → ∙MetricSpace ℓ → MetricSpace ℓ
∙MetricSpace→MetricSpace (_ , _ , A) = (_ , A)


instance
  fromNatUnitInterval : HasFromNat (Σ _ (_∈ intervalℙ 0 1))
  fromNatUnitInterval .HasFromNat.Constraint zero = Unit
  fromNatUnitInterval .HasFromNat.Constraint (suc zero) = Unit
  fromNatUnitInterval .HasFromNat.Constraint (suc (suc x)) = ⊥
  fromNatUnitInterval .HasFromNat.fromNat zero = (0 , decℚ≤ᵣ? , decℚ≤ᵣ?)
  fromNatUnitInterval .HasFromNat.fromNat (suc zero) = (1 , decℚ≤ᵣ? , decℚ≤ᵣ?)
  -- record { Constraint = λ _ → Unit ; fromNat = λ n → rat [ pos n / 1 ] }


open BinaryRelation 


module ℝPaths {ℓ} (A : MetricSpace ℓ) where


 open MetricSpaceStr (snd A)

 data ℝPath  : ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ where
  𝕣path : (f : UContMap IntervalMetricSpace A) →
               ℝPath   (fst f 0)
                       (fst f 1) 


 𝐿₁-ℝPathsMetricSpaceStr : ∀ a₀ a₁ → MetricSpaceStr (ℝPath a₀ a₁)
 𝐿₁-ℝPathsMetricSpaceStr a₀ a₁ = {!!}
 
 ΣℝPath : ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ 
 ΣℝPath a₀ a₁ = Σ[ f ∈ (UContMap IntervalMetricSpace A) ]
    ((fst f 0 ≡ a₀) × (fst f 1 ≡ a₁))

 isTransΣℝPath : isTrans ΣℝPath
 isTransΣℝPath a b c x x₁ = {!!}
 
 module _ (a₀ a₁ : ⟨ A ⟩) where
  ΣℝPath→ℝPath : ΣℝPath a₀ a₁ → ℝPath a₀ a₁
  ΣℝPath→ℝPath (f , f0 , f1) = subst2 ℝPath f0 f1 (𝕣path f)

  ℝPath→ΣℝPath : ℝPath a₀ a₁ → ΣℝPath a₀ a₁
  ℝPath→ΣℝPath (𝕣path f) = f , refl , refl

  sec-IsoΣℝPathℝPath :
    section ℝPath→ΣℝPath ΣℝPath→ℝPath
  sec-IsoΣℝPathℝPath (f , f0 , f1) =
    Σ≡Prop (λ _ → isProp× (is-set _ _) (is-set _ _))
    (UContMapEq IntervalMetricSpace A _ _
     λ x →
       (transportRefl _ ∙ transportRefl _)
         ∙ cong (fst f) (transportRefl _ ∙ transportRefl x))

  IsoΣℝPathℝPath : Iso (ℝPath a₀ a₁) (ΣℝPath a₀ a₁)
  IsoΣℝPathℝPath .Iso.fun = ℝPath→ΣℝPath
  IsoΣℝPathℝPath .Iso.inv = ΣℝPath→ℝPath
  IsoΣℝPathℝPath .Iso.rightInv = sec-IsoΣℝPathℝPath
  IsoΣℝPathℝPath .Iso.leftInv (𝕣path _) = transportRefl _

 UpToℝPath₂ : Type ℓ
 UpToℝPath₂ = ⟨ A ⟩ / ℝPath

 𝕣refl : ∀ x → ℝPath x x 
 𝕣refl x = 𝕣path (const x , ∣ uContConstMap IntervalMetricSpace A x ∣₁)


 Loops : ⟨ A ⟩ → ∙MetricSpace ℓ
 Loops a = _ , 𝕣refl a , (𝐿₁-ℝPathsMetricSpaceStr a a)


module _ {ℓ} (A : MetricSpace ℓ) where

 data Shape : Type ℓ 


 constFromCube : ∀ n → ⟨ 𝐿₁-MetricSpaceⁿ n A ⟩ → ⟨ 𝐿₁-MetricSpaceⁿ (suc n) A ⟩
 constFromCube n a = (λ _ → a) , {!!}
 
 data Shape where
  σ : ∀ n → ⟨ 𝐿₁-MetricSpaceⁿ n A ⟩ → Shape
  σ↑ : ∀ n a x → σ n (fst a x) ≡ σ (suc n) a
  σ≡ : ∀ n a x x' →
          (σ↑ n (constFromCube n a) x)
       ≡  (σ↑ n (constFromCube n a) x') 

--  σ-↑ : ∀ n (a : ⟨ 𝐿₁-MetricSpaceⁿ (suc (suc n)) A ⟩) →
--              ⟨ IntervalMetricSpace ⟩
--             → (x : ⟨ IntervalMetricSpace ⟩ )
--             → σ (suc n) (((λ t → fst (fst a t) x) , {!!})) ≡ σ (suc (suc n)) a
--  σ-↑ n a t₀ x =
--    sym (σ↑ n ((λ t → fst (fst a t) x) , _) t₀) ∙∙
--       σ↑ n (fst a t₀) x ∙∙ σ↑ (suc n) a t₀
 
--  ends-path : ∀ n → (f : ⟨ 𝐿₁-MetricSpaceⁿ (suc n) A ⟩) →
--         σ n (fst f 0) ≡ σ n (fst f 1)
--  ends-path n f = σ↑ n f 0 ∙∙
--     refl {x = σ (suc n) f}
--    ∙∙ sym (σ↑ n f 1)

--  ends-Σpath : ∀ n {a} {b} → ℝPaths.ΣℝPath (𝐿₁-MetricSpaceⁿ n A) a b →
--         σ n a ≡ σ n b
--  ends-Σpath n (f , f0 , f1) =
--     cong (σ n) (sym f0) ∙∙
--      ends-path n f
--     ∙∙ cong (σ n) f1

--  σ↑-comm : ∀ n (a : ⟨ 𝐿₁-MetricSpaceⁿ (suc (suc n)) A ⟩) x t₀ →
--     (sym (σ↑ n ((λ v → fst (fst a v) x) , _) t₀) ∙∙
--       σ↑ n (fst a t₀) x ∙∙ σ↑ (suc n) a t₀) ≡
--        sym (σ↑ n ((λ v → fst (fst a v) x) , {!!}) x)
--          ∙∙ σ↑ n (fst a x) x ∙∙ σ↑ (suc n) a x 
--  σ↑-comm = {!!}
 
--  sq-shape : ∀ n (f : ⟨ 𝐿₁-MetricSpaceⁿ (suc (suc n)) A ⟩)
--    → Square
--       (ends-path n (fst f 0))
--       (ends-path n (fst f 1))
--       (ends-path n ((λ x → fst (fst f x) 0) , {!!}))
--       (ends-path n ((λ x → fst (fst f x) 1) , {!!}))
--  sq-shape n f i j =
--    hcomp
--      (λ k → λ {
--        (i = i0) →
--          hcomp
--            (λ k' → λ {
--              (k = i0) → σ↑ (suc n) f 0 k'
--             ;(j = i0) → {!!}
--             ;(j = i1) → {!!}
--             })
--             (σ (suc n) (fst f 0))
--       ;(i = i1) →
--          hcomp
--            (λ k' → λ {
--              (k = i0) → σ↑ (suc n) f 1 k'
--             ;(j = i0) → {!!}
--             ;(j = i1) → {!!}
--             })
--             (σ (suc n) (fst f 1))
--       ;(j = i0) →
--           hcomp
--            (λ k' → λ {
--              (k = i0) → σ-↑ n f 0 0 k'
--             ;(i = i0) → {!!}
--             ;(i = i1) → {!!}
--             })
--             (σ-↑ n f 0 0 i0)
--       ;(j = i1) →
--           hcomp
--            (λ k' → λ {
--              (k = i0) → σ-↑ n f 0 1 k'
--             ;(i = i0) → {!!}
--             ;(i = i1) → {!!}
--             })
--             (σ-↑ n f 0 1 i0)
--       })
--      (σ (suc (suc n)) f)
--   where
--    t₀ : ⟨ IntervalMetricSpace ⟩ 
--    t₀ = {!!}
   
-- --  ends-path-comp : ∀ n a b c
-- --     → (f : ℝPaths.ΣℝPath (𝐿₁-MetricSpaceⁿ n A) a b)
-- --     → (g : ℝPaths.ΣℝPath (𝐿₁-MetricSpaceⁿ n A) b c)
-- --     → Square (ends-Σpath n f)
-- --         (ends-Σpath n
-- --         (ℝPaths.isTransΣℝPath (𝐿₁-MetricSpaceⁿ n A) a b c f g))
-- --         refl
-- --         (ends-Σpath n g)
-- --  ends-path-comp = {!!}
 
-- -- -- module _ where
-- -- --  open ℝPaths

-- -- --  record ElimShape {ℓ'} (A : MetricSpace ℓ) (T : Shape A → Type ℓ') :
-- -- --    Type (ℓ-max ℓ ℓ') where
-- -- --   field
-- -- --    f-σ : ∀ n a → T (σ n a)
-- -- --    f-σ↑ :  ∀ n a x →
-- -- --      PathP (λ i → T (σ↑ n a x i))
-- -- --        (f-σ n (fst a x))
-- -- --        (f-σ (suc n) a)
-- -- --    f-σ-refl : ∀ n a x x' →
-- -- --      SquareP (λ i j → T (σ-refl n a x x' i j))
-- -- --        (f-σ↑ n (constFromCube A n a) x)
-- -- --        (f-σ↑ n (constFromCube A n a) x')
-- -- --        refl
-- -- --        refl

-- -- --   go : ∀ x → T x
-- -- --   go (σ n x) = f-σ n x
-- -- --   go (σ↑ n a x i) = f-σ↑ n a x i
-- -- --   go (σ-refl n a x x' i i₁) = f-σ-refl n a x x' i i₁

-- -- --  record ElimShape2Groupoid {ℓ'} (A : MetricSpace ℓ)
-- -- --      (T : Shape A → Shape A → Type ℓ') :
-- -- --    Type (ℓ-max ℓ ℓ') where
-- -- --   field
-- -- --    isGroupoidT : ∀ x y → isGroupoid (T x y)
-- -- --    f-σ-σ : ∀ n a n' a' → T (σ n a) (σ n' a')
-- -- --    -- f-σ↑ :  ∀ n a x →
-- -- --    --   PathP (λ i → T (σ↑ n a x i))
-- -- --    --     (f-σ n (fst a x))
-- -- --    --     (f-σ (suc n) a)
-- -- --    -- f-σ-refl : ∀ n a x x' →
-- -- --    --   SquareP (λ i j → T (σ-refl n a x x' i j))
-- -- --    --     (f-σ↑ n (constFromCube A n a) x)
-- -- --    --     (f-σ↑ n (constFromCube A n a) x')
-- -- --    --     refl
-- -- --    --     refl

-- -- --   go : ∀ x y → T x y
-- -- --   go = ElimShape.go w
-- -- --    where
-- -- --    w : ElimShape A (λ z → (y : Shape A) → T z y)
-- -- --    w .ElimShape.f-σ n a = ElimShape.go ww
-- -- --     where
-- -- --     ww : ElimShape A (λ z → T (σ n a) z)
-- -- --     ww .ElimShape.f-σ = f-σ-σ n a
-- -- --     ww .ElimShape.f-σ↑ = {!!}
-- -- --     ww .ElimShape.f-σ-refl = {!!}
-- -- --    w .ElimShape.f-σ↑ = {!!}
-- -- --    w .ElimShape.f-σ-refl = {!!}


-- -- --   -- path : (p : UContMap IntervalMetricSpace A)
-- -- --   --          → pt (fst p 0) ≡ pt (fst p 1)
-- -- --   -- sq : (s : UContMap Interval²MetricSpace A)
-- -- --   --          → Square
-- -- --   --              (path ((λ x → fst s (0 , x)) , {!!}))
-- -- --   --              (path ((λ x → fst s (1 , x)) , {!!}))
-- -- --   --              (path ((λ x → fst s (x , 0)) , {!!}))
-- -- --   --              (path ((λ x → fst s (x , 1)) , {!!}))
-- -- --   -- const≡refl : ∀ a icid → path ((λ _ → a) , icid) ≡ λ _ → pt a




-- -- -- -- isUContMap∘ : ∀ {ℓ ℓ' ℓ''}
-- -- -- --   → (A : MetricSpace ℓ)
-- -- -- --   → (B : MetricSpace ℓ')
-- -- -- --   → (C : MetricSpace ℓ'')
-- -- -- --   → ∀ f g
-- -- -- --   → IsUContMap (snd B) f (snd C)
-- -- -- --   → IsUContMap (snd A) g (snd B)
-- -- -- --   → IsUContMap (snd A) (f ∘ g) (snd C)  
-- -- -- -- isUContMap∘ = {!!}

-- -- -- -- uContConstMap : ∀ {ℓ ℓ'}
-- -- -- --   → (A : MetricSpace ℓ)
-- -- -- --   → (B : MetricSpace ℓ')
-- -- -- --   → (b : ⟨ B ⟩) → IsUContMap (snd A) (const b) (snd B) 
-- -- -- -- uContConstMap A B a = (λ ε → 1 , λ _ _ _ → isTrans≡<ᵣ _ _ _ {!!} {!!} )

-- -- -- -- IntervalMetricSpace : MetricSpace₀
-- -- -- -- IntervalMetricSpace = _ , MetricSubSpace _  (intervalℙ 0 1) (snd ℝMetricSpace)

-- -- -- -- Interval²MetricSpaceStr : MetricSpaceStr
-- -- -- --  ((Σ ℝ (_∈ intervalℙ 0 1)) × (Σ ℝ (_∈ intervalℙ 0 1)))
-- -- -- -- Interval²MetricSpaceStr = {!!}

-- -- -- -- Interval²MetricSpace : MetricSpace₀
-- -- -- -- Interval²MetricSpace = (Σ ℝ (_∈ intervalℙ 0 1)) × (Σ ℝ (_∈ intervalℙ 0 1))
-- -- -- --   , Interval²MetricSpaceStr
-- -- -- --   --MetricSubSpace _  (intervalℙ 0 1) (snd ℝMetricSpace)


-- -- -- -- 𝐿₁-Metric : ∀ {ℓ}
-- -- -- --   → (A : MetricSpace ℓ)
-- -- -- --   → UContMap IntervalMetricSpace A
-- -- -- --   → UContMap IntervalMetricSpace A → ℝ 
-- -- -- -- 𝐿₁-Metric A f g = {!!}

-- -- -- -- UContMapEq : ∀ {ℓ ℓ'} → (A : MetricSpace ℓ)
-- -- -- --           → (A' : MetricSpace ℓ') →
-- -- -- --             (f g : UContMap A A')
-- -- -- --             → (∀ x → fst f x ≡ fst g x ) → f ≡ g
-- -- -- -- UContMapEq A A' f g x = Σ≡Prop (λ _ → squash₁) (funExt x)


-- -- -- -- private
-- -- -- --  variable
-- -- -- --   ℓ ℓ' : Level

-- -- -- -- ∙MetricSpaceStr : Type ℓ → Type ℓ
-- -- -- -- ∙MetricSpaceStr = ProductStructure PointedStructure MetricSpaceStr

-- -- -- -- ∙MetricSpace : ∀ ℓ → Type (ℓ-suc ℓ)
-- -- -- -- ∙MetricSpace ℓ = TypeWithStr ℓ ∙MetricSpaceStr

-- -- -- -- ∙MetricSpace→Pointed : ∀ {ℓ} → ∙MetricSpace ℓ → P.Pointed ℓ
-- -- -- -- ∙MetricSpace→Pointed (A , a , _) = (A , a)

-- -- -- -- ∙MetricSpace→MetricSpace : ∀ {ℓ} → ∙MetricSpace ℓ → MetricSpace ℓ
-- -- -- -- ∙MetricSpace→MetricSpace (_ , _ , A) = (_ , A)


-- -- -- -- instance
-- -- -- --   fromNatUnitInterval : HasFromNat (Σ _ (_∈ intervalℙ 0 1))
-- -- -- --   fromNatUnitInterval .HasFromNat.Constraint zero = Unit
-- -- -- --   fromNatUnitInterval .HasFromNat.Constraint (suc zero) = Unit
-- -- -- --   fromNatUnitInterval .HasFromNat.Constraint (suc (suc x)) = ⊥
-- -- -- --   fromNatUnitInterval .HasFromNat.fromNat zero = (0 , decℚ≤ᵣ? , decℚ≤ᵣ?)
-- -- -- --   fromNatUnitInterval .HasFromNat.fromNat (suc zero) = (1 , decℚ≤ᵣ? , decℚ≤ᵣ?)
-- -- -- --   -- record { Constraint = λ _ → Unit ; fromNat = λ n → rat [ pos n / 1 ] }

-- -- -- -- PathIdTrunc₁Iso : {A : Type ℓ} {a b : A} → Iso (∣ a ∣₃ ≡ ∣ b ∣₃) ∥ a ≡ b ∥₂
-- -- -- -- PathIdTrunc₁Iso = {!!}

-- -- -- -- module ℝPaths {ℓ} (A : MetricSpace ℓ) where

-- -- -- --  open MetricSpaceStr (snd A)

-- -- -- --  data ℝPath  : ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ where
-- -- -- --   𝕣path : (f : UContMap IntervalMetricSpace A) →
-- -- -- --                ℝPath   (fst f 0)
-- -- -- --                        (fst f 1) 



-- -- -- --  data Pieces : Type ℓ where
-- -- -- --   pt : ⟨ A ⟩ → Pieces
-- -- -- --   path : (p : UContMap IntervalMetricSpace A)
-- -- -- --            → pt (fst p 0) ≡ pt (fst p 1)
-- -- -- --   sq : (s : UContMap Interval²MetricSpace A)
-- -- -- --            → Square
-- -- -- --                (path ((λ x → fst s (0 , x)) , {!!}))
-- -- -- --                (path ((λ x → fst s (1 , x)) , {!!}))
-- -- -- --                (path ((λ x → fst s (x , 0)) , {!!}))
-- -- -- --                (path ((λ x → fst s (x , 1)) , {!!}))
-- -- -- --   const≡refl : ∀ a icid → path ((λ _ → a) , icid) ≡ λ _ → pt a



 
-- -- -- --  ΣℝPath : ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ 
-- -- -- --  ΣℝPath a₀ a₁ = Σ[ f ∈ (UContMap IntervalMetricSpace A) ]
-- -- -- --     ((fst f 0 ≡ a₀) × (fst f 1 ≡ a₁))

-- -- -- --  module _ (a₀ a₁ : ⟨ A ⟩) where
-- -- -- --   ΣℝPath→ℝPath : ΣℝPath a₀ a₁ → ℝPath a₀ a₁
-- -- -- --   ΣℝPath→ℝPath (f , f0 , f1) = subst2 ℝPath f0 f1 (𝕣path f)

-- -- -- --   ℝPath→ΣℝPath : ℝPath a₀ a₁ → ΣℝPath a₀ a₁
-- -- -- --   ℝPath→ΣℝPath (𝕣path f) = f , refl , refl

-- -- -- --   sec-IsoΣℝPathℝPath :
-- -- -- --     section ℝPath→ΣℝPath ΣℝPath→ℝPath
-- -- -- --   sec-IsoΣℝPathℝPath (f , f0 , f1) =
-- -- -- --     Σ≡Prop (λ _ → isProp× (is-set _ _) (is-set _ _))
-- -- -- --     (UContMapEq IntervalMetricSpace A _ _
-- -- -- --      λ x →
-- -- -- --        (transportRefl _ ∙ transportRefl _)
-- -- -- --          ∙ cong (fst f) (transportRefl _ ∙ transportRefl x))

-- -- -- --   IsoΣℝPathℝPath : Iso (ℝPath a₀ a₁) (ΣℝPath a₀ a₁)
-- -- -- --   IsoΣℝPathℝPath .Iso.fun = ℝPath→ΣℝPath
-- -- -- --   IsoΣℝPathℝPath .Iso.inv = ΣℝPath→ℝPath
-- -- -- --   IsoΣℝPathℝPath .Iso.rightInv = sec-IsoΣℝPathℝPath
-- -- -- --   IsoΣℝPathℝPath .Iso.leftInv (𝕣path _) = transportRefl _

-- -- -- --  UpToℝPath₂ : Type ℓ
-- -- -- --  UpToℝPath₂ = ⟨ A ⟩ / ℝPath

-- -- -- --  open BinaryRelation 

-- -- -- --  opaque
-- -- -- --   isTransℝPath : isTrans ℝPath
-- -- -- --   isTransℝPath a b c d x₁ = {!!}

-- -- -- --   isTransℝPath-const : ∀ x cid → isTransℝPath x x x (𝕣path ((λ _ → x) , cid))
-- -- -- --        (𝕣path ((λ _ → x) , cid))
-- -- -- --        ≡ 𝕣path ((λ _ → x) , cid) 
-- -- -- --   isTransℝPath-const = {!!}


-- -- -- --  𝕣path→path : ∀ {a₀ a₁} → ℝPath a₀ a₁ → pt a₀ ≡ pt a₁ 
-- -- -- --  𝕣path→path (𝕣path f) = path f
 
-- -- -- --  comp-𝕣paths : ∀ {a} {b} {c}
-- -- -- --    (r : ℝPath a b)
-- -- -- --    (s : ℝPath b c) →
-- -- -- --     Square
-- -- -- --      (𝕣path→path r )
-- -- -- --       (𝕣path→path (isTransℝPath _ _ _ r s))
-- -- -- --       refl
-- -- -- --       (𝕣path→path s)
-- -- -- --  comp-𝕣paths r s = {!r !}


-- -- -- --   --  cong (cong ∣_∣₃ ∘ 𝕣path→path)
-- -- -- --   --       (sym ((IsoΣℝPathℝPath _  _ .Iso.leftInv) r))
-- -- -- --   --      ◁ congP (λ _ → cong ∣_∣₃) (ww (ℝPath→ΣℝPath a b r) s) ▷
-- -- -- --   --         cong (cong ∣_∣₃ ∘ 𝕣path→path ∘ flip (isTransℝPath a b c) s)
-- -- -- --   --          ((IsoΣℝPathℝPath _  _ .Iso.leftInv) r)

-- -- -- --   -- where
-- -- -- --   -- -- w : {a b : ⟨ A ⟩} → ℝPath a b → pt a ≡ pt b
-- -- -- --   -- -- w (ℝPaths.𝕣path f) = (path f)

-- -- -- --   -- ww : {a b c : ⟨ A ⟩} (r : ΣℝPath a b) (s : ℝPath b c) →
-- -- -- --   --     Square (𝕣path→path (ΣℝPath→ℝPath a b r))
-- -- -- --   --            (𝕣path→path (isTransℝPath a b c (ΣℝPath→ℝPath a b r) s))
-- -- -- --   --       refl (𝕣path→path s)
-- -- -- --   -- ww {a} {b} {c} (f , f0 , f1) (ℝPaths.𝕣path g) =
-- -- -- --   --   wwwL ◁ {!!}
-- -- -- --   --     ▷ {!!}
-- -- -- --   -- -- www
-- -- -- --   --  where
-- -- -- --   --  wwwL : 𝕣path→path (subst2 ℝPath f0 f1 (𝕣path f))
-- -- -- --   --           ≡ (cong pt (sym f0) ∙∙
-- -- -- --   --                path f
-- -- -- --   --                ∙∙ cong pt f1)
-- -- -- --   --  wwwL = {!!}
-- -- -- --   --  www : {!!}
-- -- -- --   --  www = {!!}


-- -- -- --  UpToℝPath₃ : Type ℓ
-- -- -- --  UpToℝPath₃ = ⟨ A ⟩ // isTransℝPath



-- -- -- --  𝐿₁-ℝPathsMetricSpaceStr : ∀ a₀ a₁ → MetricSpaceStr (ℝPath a₀ a₁)
-- -- -- --  𝐿₁-ℝPathsMetricSpaceStr a₀ a₁ = {!!}

-- -- -- --  𝕣refl : ∀ x → ℝPath x x 
-- -- -- --  𝕣refl x = 𝕣path (const x , ∣ uContConstMap IntervalMetricSpace A x ∣₁)

-- -- -- --  -- 𝕣sym : ∀ x y → ℝPath x y →  ℝPath y x 
-- -- -- --  -- 𝕣sym x y (𝕣path (f , fc)) = 𝕣path ({!!} , {!!})

-- -- -- -- -- module ℝLoopspace {ℓ} (A : ∙MetricSpace ℓ) where

-- -- -- --  Loops : ⟨ A ⟩ → ∙MetricSpace ℓ
-- -- -- --  Loops a = _ , 𝕣refl a , (𝐿₁-ℝPathsMetricSpaceStr a a)

-- -- -- -- module _ where
-- -- -- --  open ℝPaths

-- -- -- --  record ElimPieces {ℓ'} (A : MetricSpace ℓ) (T : Pieces A → Type ℓ') :
-- -- -- --    Type (ℓ-max ℓ ℓ') where
-- -- -- --   field
-- -- -- --    pt-f : ∀ x → T (pt x) 
-- -- -- --    path-f : ∀ p → PathP (λ i → T (path p i))
-- -- -- --      (pt-f (fst p 0))
-- -- -- --      (pt-f (fst p 1))
-- -- -- --    sq-f : ∀ s →
-- -- -- --      SquareP (λ i j → T (sq s i j))
-- -- -- --        (path-f ((λ x → fst s (0 , x)) , {!!}))
-- -- -- --        (path-f ((λ x → fst s (1 , x)) , {!!}))
-- -- -- --        (path-f ((λ x → fst s (x , 0)) , {!!}))
-- -- -- --        (path-f ((λ x → fst s (x , 1)) , {!!}))
       
-- -- -- --    const≡refl-f : ∀ x cid →
-- -- -- --      SquareP (λ i j → T (const≡refl x cid i j))
-- -- -- --        (path-f ((λ _ → x) , cid))
-- -- -- --        refl
-- -- -- --        refl
-- -- -- --        refl

-- -- -- --   go : ∀ x → T x
-- -- -- --   go (pt x) = pt-f x
-- -- -- --   go (path p i) = path-f p i
-- -- -- --   go (sq s i j) = sq-f s i j  
-- -- -- --   go (const≡refl a cid i i₁) = const≡refl-f a cid i i₁

-- -- -- --  record ElimPiecesSet {ℓ'} (A : MetricSpace ℓ) (T : Pieces A → Type ℓ') :
-- -- -- --    Type (ℓ-max ℓ ℓ') where
-- -- -- --   no-eta-equality
-- -- -- --   field
-- -- -- --    pt-f : ∀ x → T (pt x) 
-- -- -- --    path-f : ∀ p → PathP (λ i → T (path p i))
-- -- -- --      (pt-f (fst p 0))
-- -- -- --      (pt-f (fst p 1))
-- -- -- --    isSetT : ∀ x → isSet (T x)

-- -- -- --   go : ∀ x → T x
-- -- -- --   go = ElimPieces.go w
-- -- -- --    where
-- -- -- --    w : ElimPieces A T
-- -- -- --    w .ElimPieces.pt-f = pt-f
-- -- -- --    w .ElimPieces.path-f = path-f
-- -- -- --    w .ElimPieces.sq-f s =
-- -- -- --      isSet→SquareP {A = λ i j → T (sq s i j)}
-- -- -- --       (λ i j → isSetT (sq s i j))
-- -- -- --        (path-f ((λ x → fst s (0 , x)) , {!!}))
-- -- -- --        (path-f ((λ x → fst s (1 , x)) , {!!}))
-- -- -- --        (path-f ((λ x → fst s (x , 0)) , {!!}))
-- -- -- --        (path-f ((λ x → fst s (x , 1)) , {!!})) 

-- -- -- --    w .ElimPieces.const≡refl-f x _ =
-- -- -- --      isSet→SquareP (λ _ _ → isSetT _) _ _ _ _ 

-- -- -- --  record ElimPiecesProp {ℓ'} (A : MetricSpace ℓ) (T : Pieces A → Type ℓ') :
-- -- -- --    Type (ℓ-max ℓ ℓ') where
-- -- -- --   no-eta-equality
-- -- -- --   field
-- -- -- --    pt-f : ∀ x → T (pt x) 
-- -- -- --    isPropT : ∀ x → isProp (T x)

-- -- -- --   go : ∀ x → T x
-- -- -- --   go = ElimPiecesSet.go w
-- -- -- --    where
-- -- -- --    w : ElimPiecesSet A (λ z → T z)
-- -- -- --    w .ElimPiecesSet.pt-f = pt-f
-- -- -- --    w .ElimPiecesSet.path-f _ = isProp→PathP (λ _ → isPropT _) _ _ 
-- -- -- --    w .ElimPiecesSet.isSetT _ = isProp→isSet (isPropT _)

-- -- -- --  record ElimPiecesSet₂ {ℓ'} (A B : MetricSpace ℓ)
-- -- -- --    (T : Pieces A → Pieces B → Type ℓ') :
-- -- -- --    Type (ℓ-max ℓ ℓ') where
-- -- -- --   no-eta-equality
-- -- -- --   field
-- -- -- --    pt-pt-f : ∀ a b → T (pt a) (pt b)
-- -- -- --    pt-path-f : ∀ a p
-- -- -- --      → PathP (λ i → T (pt a) (path p i))
-- -- -- --      (pt-pt-f a (fst p 0))
-- -- -- --      (pt-pt-f a (fst p 1))
-- -- -- --    path-pt-f : ∀ p b
-- -- -- --      → PathP (λ i → T (path p i) (pt b))
-- -- -- --      (pt-pt-f (fst p 0) b)
-- -- -- --      (pt-pt-f (fst p 1) b)
-- -- -- --    isSetT : ∀ x y → isSet (T x y)

-- -- -- --   go : ∀ x y → T x y
-- -- -- --   go = ElimPiecesSet.go w
-- -- -- --    where
-- -- -- --     w : ElimPiecesSet A (λ z → (y : Pieces B) → T z y)
-- -- -- --     w .ElimPiecesSet.pt-f x = ElimPiecesSet.go ww
-- -- -- --      where
-- -- -- --      ww : ElimPiecesSet B (λ z → T (pt x) z)
-- -- -- --      ww .ElimPiecesSet.pt-f = pt-pt-f x
-- -- -- --      ww .ElimPiecesSet.path-f = pt-path-f x
-- -- -- --      ww .ElimPiecesSet.isSetT _ = isSetT _ _

-- -- -- --     w .ElimPiecesSet.path-f p = funExt (ElimPiecesProp.go ww)
-- -- -- --      where
-- -- -- --      ww : ElimPiecesProp B
-- -- -- --            (λ z →
-- -- -- --               PathP (λ z₁ → T (path p z₁) z)
-- -- -- --               (w .ElimPiecesSet.pt-f (fst p 0) z)
-- -- -- --               (w .ElimPiecesSet.pt-f (fst p 1) z))
-- -- -- --      ww .ElimPiecesProp.pt-f b = path-pt-f p b
-- -- -- --      ww .ElimPiecesProp.isPropT x = isOfHLevelPathP' 1 (isSetT _ _) _ _
-- -- -- --     w .ElimPiecesSet.isSetT _ = isSetΠ λ _ → isSetT _ _

-- -- -- -- module _ (A : MetricSpace ℓ) where
-- -- -- --  open ℝPaths A
-- -- -- --  ∥Pieces∥₂→UpToℝPath⟨A⟩ : ∥ Pieces ∥₂ → UpToℝPath₂
-- -- -- --  ∥Pieces∥₂→UpToℝPath⟨A⟩ = ST.rec squash/
-- -- -- --    (ElimPiecesSet.go w)
-- -- -- --   where
-- -- -- --   w : ElimPiecesSet _ _
-- -- -- --   w .ElimPiecesSet.pt-f x = [ x ]/  
-- -- -- --   w .ElimPiecesSet.path-f p = eq/ _ _ (𝕣path p)
-- -- -- --   w .ElimPiecesSet.isSetT _ = squash/ 

-- -- -- --  UpToℝPath⟨A⟩→∥Pieces∥₂ : UpToℝPath₂ → ∥ Pieces ∥₂
-- -- -- --  UpToℝPath⟨A⟩→∥Pieces∥₂ = SQ.Rec.go w 
-- -- -- --   where
-- -- -- --   w : Rec _
-- -- -- --   w .Rec.isSetB = squash₂
-- -- -- --   w .Rec.f = ∣_∣₂ ∘ pt
-- -- -- --   w .Rec.f∼ a a' (𝕣path f) = cong ∣_∣₂ (path f)

-- -- -- --  IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ : Iso ∥ Pieces ∥₂ UpToℝPath₂
-- -- -- --  IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ .Iso.fun = ∥Pieces∥₂→UpToℝPath⟨A⟩
-- -- -- --  IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ .Iso.inv = UpToℝPath⟨A⟩→∥Pieces∥₂
-- -- -- --  IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ .Iso.rightInv =
-- -- -- --    SQ.ElimProp.go w
-- -- -- --   where
-- -- -- --   w : ElimProp _
-- -- -- --   w .ElimProp.isPropB _ = squash/ _ _
-- -- -- --   w .ElimProp.f _ = refl
-- -- -- --  IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ .Iso.leftInv =
-- -- -- --   ST.elim (λ _ → isProp→isSet (squash₂ _ _))
-- -- -- --    (ElimPiecesProp.go w)
-- -- -- --    where
-- -- -- --    w : ElimPiecesProp _ _
-- -- -- --    w .ElimPiecesProp.pt-f _ = refl
-- -- -- --    w .ElimPiecesProp.isPropT _ = squash₂ _ _

-- -- -- --  -- ∥Pieces∥₃→UpToℝPath⟨A⟩ : ∥ Pieces ∥₃ → UpToℝPath₃
-- -- -- --  -- ∥Pieces∥₃→UpToℝPath⟨A⟩ = GT.rec squash//
-- -- -- --  --   (ElimPieces.go w)
-- -- -- --  --  where
-- -- -- --  --  ww : ∀ p → _ ≡ _
-- -- -- --  --  ww p = eq// (𝕣path p)
-- -- -- --  --  w : ElimPieces _ _
-- -- -- --  --  w .ElimPieces.pt-f x = [ x ]// 
-- -- -- --  --  w .ElimPieces.path-f = ww
-- -- -- --  --  w .ElimPieces.sq-f s =
-- -- -- --  --    compPath→Square
-- -- -- --  --      (sym (comp'// _ isTransℝPath _ _) ∙∙
-- -- -- --  --       {!
-- -- -- --  --       !}
-- -- -- --  --       ∙∙ comp'// _ isTransℝPath _ _)
-- -- -- --  --  w .ElimPieces.const≡refl-f x cid =
-- -- -- --  --   refl≡Id isTransℝPath (𝕣path ((λ _ → x) , cid)) (isTransℝPath-const x cid) 
    
  
-- -- -- --  -- UpToℝPath₃⟨A⟩→∥Pieces∥₃ : UpToℝPath₃ → ∥ Pieces ∥₃
-- -- -- --  -- UpToℝPath₃⟨A⟩→∥Pieces∥₃ = GQ.rec
-- -- -- --  --   isTransℝPath
-- -- -- --  --   squash₃
-- -- -- --  --   (∣_∣₃ ∘ pt)
-- -- -- --  --   (cong ∣_∣₃ ∘ 𝕣path→path)
-- -- -- --  --   λ {a} {b} {c} r s i j →
-- -- -- --  --     ∣ comp-𝕣paths r s i j ∣₃

-- -- -- -- --  IsoUpToℝPath₃⟨A⟩→∥Pieces∥₃ : Iso ∥ Pieces ∥₃ UpToℝPath₃
-- -- -- -- --  IsoUpToℝPath₃⟨A⟩→∥Pieces∥₃ .Iso.fun = ∥Pieces∥₃→UpToℝPath⟨A⟩
-- -- -- -- --  IsoUpToℝPath₃⟨A⟩→∥Pieces∥₃ .Iso.inv = UpToℝPath₃⟨A⟩→∥Pieces∥₃
-- -- -- -- --  IsoUpToℝPath₃⟨A⟩→∥Pieces∥₃ .Iso.rightInv =
-- -- -- -- --    GQ.elimSet isTransℝPath
-- -- -- -- --     (λ _ → squash// _ _)
-- -- -- -- --     (λ _ → refl)
-- -- -- -- --     λ { (ℝPaths.𝕣path f) i j → eq// (𝕣path f) i }
   
-- -- -- -- --  IsoUpToℝPath₃⟨A⟩→∥Pieces∥₃ .Iso.leftInv =
-- -- -- -- --   GT.elim (λ _ → isSet→isGroupoid (squash₃ _ _))
-- -- -- -- --    (ElimPiecesSet.go w)
   
-- -- -- -- --   where
-- -- -- -- --   w : ElimPiecesSet _ _
-- -- -- -- --   w .ElimPiecesSet.pt-f _ = refl
-- -- -- -- --   w .ElimPiecesSet.path-f p i _ = ∣ path p i ∣₃
-- -- -- -- --   w .ElimPiecesSet.isSetT _ = squash₃ _ _

-- -- -- -- -- -- record ElimPiecesGroupoid₂ {ℓ'} (A B : Type ℓ) (T : Pieces A → Pieces B → Type ℓ') :
-- -- -- -- -- --   Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- --  no-eta-equality
-- -- -- -- -- --  field
-- -- -- -- -- --   pt-pt-f : ∀ a b → T (pt a) (pt b)
-- -- -- -- -- --   pt-path-f : ∀ a p
-- -- -- -- -- --     → PathP (λ i → T (pt a) (path p i))
-- -- -- -- -- --     (pt-pt-f a (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
-- -- -- -- -- --     (pt-pt-f a (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
-- -- -- -- -- --   path-pt-f : ∀ p b
-- -- -- -- -- --     → PathP (λ i → T (path p i) (pt b))
-- -- -- -- -- --     (pt-pt-f (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) b)
-- -- -- -- -- --     (pt-pt-f (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)) b)
-- -- -- -- -- --   path-path-f : ∀ p p' → SquareP (λ j i → T (path p i) (path p' j))

-- -- -- -- -- --         (path-pt-f p (p' 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
-- -- -- -- -- --         (path-pt-f p (p' 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
-- -- -- -- -- --         (pt-path-f (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) p')
-- -- -- -- -- --         (pt-path-f (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)) p')
-- -- -- -- -- --   const-refl≡-Left : ∀ a (x : B) →
-- -- -- -- -- --      SquareP (λ i j → T (pt a) (const≡refl x i j))
-- -- -- -- -- --      (pt-path-f a (λ _ _ → x)) refl refl refl
-- -- -- -- -- --   const-refl≡-Right : ∀ a (x : B) →
-- -- -- -- -- --      SquareP (λ i j → T (const≡refl a i j) (pt x))
-- -- -- -- -- --      (path-pt-f (λ _ _ → a) x) refl refl refl
-- -- -- -- -- --   isGroupoidT : ∀ x y → isGroupoid (T x y)

-- -- -- -- -- --  go : ∀ x y → T x y
-- -- -- -- -- --  go = ElimPieces.go w
-- -- -- -- -- --   where
-- -- -- -- -- --    w : ElimPieces A (λ z → (y : Pieces B) → T z y)
-- -- -- -- -- --    w .ElimPieces.pt-f a = ElimPieces.go ww
-- -- -- -- -- --      where
-- -- -- -- -- --       ww : ElimPieces B (λ z → T (pt a) z)
-- -- -- -- -- --       ww .ElimPieces.pt-f = pt-pt-f a
-- -- -- -- -- --       ww .ElimPieces.path-f = pt-path-f a
-- -- -- -- -- --       ww .ElimPieces.const≡refl-f = const-refl≡-Left a
-- -- -- -- -- --    w .ElimPieces.path-f p = funExt (ElimPiecesSet.go ww)
-- -- -- -- -- --      where
-- -- -- -- -- --       ww : ElimPiecesSet B _
-- -- -- -- -- --       ww .ElimPiecesSet.pt-f = path-pt-f p
-- -- -- -- -- --       ww .ElimPiecesSet.path-f = path-path-f p 
-- -- -- -- -- --       ww .ElimPiecesSet.isSetT _ = isOfHLevelPathP' 2 (isGroupoidT _ _) _ _

-- -- -- -- -- --    w .ElimPieces.const≡refl-f x = congP (λ _ → funExt)
-- -- -- -- -- --      (funExt (ElimPiecesProp.go ww))
-- -- -- -- -- --     where
-- -- -- -- -- --     ww : ElimPiecesProp B _
-- -- -- -- -- --     ww .ElimPiecesProp.pt-f b = const-refl≡-Right x b
-- -- -- -- -- --     ww .ElimPiecesProp.isPropT _ =
-- -- -- -- -- --       isOfHLevelPathP' 1 (isGroupoidT _ _ _ _) _ _

-- -- -- -- module _ where
-- -- -- --  open ℝPaths
-- -- -- --  mapPieces : ∀ {ℓ} (A B : MetricSpace ℓ) → UContMap A B → Pieces A → Pieces B
-- -- -- --  mapPieces A B (f , ucf) = ElimPieces.go w
-- -- -- --   where
-- -- -- --   w : ElimPieces _ _
-- -- -- --   w .ElimPieces.pt-f = pt ∘ f
-- -- -- --   w .ElimPieces.path-f p = path (f ∘ fst p , {!!})
-- -- -- --   w .ElimPieces.sq-f s = sq (f ∘ fst s , {!!})
-- -- -- --   w .ElimPieces.const≡refl-f x cid = const≡refl _ _

-- -- -- -- -- --  isoPieces : Iso A B → Iso (Pieces A) (Pieces B)
-- -- -- -- -- --  isoPieces isoAB = w
-- -- -- -- -- --    where
-- -- -- -- -- --    open Iso isoAB

-- -- -- -- -- --    secMap : {f : A → B} {g : B → A} → section f g
-- -- -- -- -- --               → section (mapPieces f) (mapPieces g)
-- -- -- -- -- --    secMap s = ElimPieces.go ww
-- -- -- -- -- --     where
-- -- -- -- -- --        ww : ElimPieces _ _
-- -- -- -- -- --        ww .ElimPieces.pt-f x = cong pt (s _)
-- -- -- -- -- --        ww .ElimPieces.path-f p i j = path (λ t t∈ → s (p t t∈) j) i
-- -- -- -- -- --        ww .ElimPieces.const≡refl-f a i j k = const≡refl (s a k) i j
       
-- -- -- -- -- --    w : Iso (Pieces _) (Pieces _)
-- -- -- -- -- --    w .Iso.fun = mapPieces fun
-- -- -- -- -- --    w .Iso.inv = mapPieces inv
-- -- -- -- -- --    w .Iso.rightInv = secMap rightInv
-- -- -- -- -- --    w .Iso.leftInv = secMap leftInv



-- -- -- -- {- loop space of a pointed metric space -}
-- -- -- -- Ω : ∙MetricSpace ℓ → ∙MetricSpace ℓ
-- -- -- -- Ω (_ , a , m) = ℝPaths.Loops (_ , m) a


-- -- -- -- Ω^_ : ∀ {ℓ} → ℕ → ∙MetricSpace ℓ → ∙MetricSpace ℓ
-- -- -- -- (Ω^ 0) p = p
-- -- -- -- (Ω^ (suc n)) p = Ω ((Ω^ n) p)

-- -- -- -- module _ {ℓ} (A : MetricSpace ℓ) where

-- -- -- --  open ℝPaths A 
 
-- -- -- --  ℝPathGroupoid : Category ℓ ℓ
-- -- -- --  ℝPathGroupoid .Category.ob = ⟨ A ⟩
-- -- -- --  ℝPathGroupoid .Category.Hom[_,_] x y =
-- -- -- --    ℝPaths.UpToℝPath₂ (_ , 𝐿₁-ℝPathsMetricSpaceStr x y)
-- -- -- --  ℝPathGroupoid .Category.id = [ 𝕣refl _ ]/
-- -- -- --  ℝPathGroupoid .Category._⋆_ = {!!}
-- -- -- --  ℝPathGroupoid .Category.⋆IdL = {!!}
-- -- -- --  ℝPathGroupoid .Category.⋆IdR = {!!}
-- -- -- --  ℝPathGroupoid .Category.⋆Assoc = {!!}
-- -- -- --  ℝPathGroupoid .Category.isSetHom = squash/

-- -- -- --  ℝLoopGroup : ⟨ A ⟩ → Group ℓ
-- -- -- --  ℝLoopGroup x .fst = ℝPaths.UpToℝPath₂ (_ , 𝐿₁-ℝPathsMetricSpaceStr x x)
-- -- -- --  ℝLoopGroup x .snd .GroupStr.1g = [ 𝕣refl _ ]/
-- -- -- --  ℝLoopGroup x .snd .GroupStr._·_ = {!!}
-- -- -- --  ℝLoopGroup x .snd .GroupStr.inv = {!!}
-- -- -- --  ℝLoopGroup x .snd .GroupStr.isGroup = {!!}
 
-- -- -- -- -- module n-fold-ℝLoopspace {ℓ} (A : ∙MetricSpace ℓ) where

-- -- -- -- πGr : ∀ {ℓ} (n : ℕ) (A : ∙MetricSpace ℓ) → Group ℓ
-- -- -- -- πGr n A₀ =
-- -- -- --  let (_ , a , A) = (Ω^ (suc n)) A₀
-- -- -- --  in ℝLoopGroup (_ , A) a

-- -- -- -- Piecesₙ : ℕ → MetricSpace ℓ → Type ℓ
-- -- -- -- Piecesₙ = {!!}

-- -- -- -- -- ℝⁿ-MetricSpaceStr : {!!}
-- -- -- -- -- ℝⁿ-MetricSpaceStr = {!!}

-- -- -- -- -- Intervalⁿ-MetricSpace : ℕ → MetricSpace₀
-- -- -- -- -- Intervalⁿ-MetricSpace = {!!}

-- -- -- -- module _ {ℓ} (A : MetricSpace ℓ) where


-- -- -- --  Π-seqₙ : ℕ → Type ℓ
-- -- -- --  Π-seqₙ n = ℝPaths.Pieces (𝐿₁-MetricSpaceⁿ n A)
-- -- -- --  -- UContMap (Intervalⁿ-MetricSpace n) A

-- -- -- --  Π-seqₙ-map : ∀ n → Π-seqₙ n → Π-seqₙ (suc n)
-- -- -- --  Π-seqₙ-map n = mapPieces (𝐿₁-MetricSpaceⁿ n A)
-- -- -- --   (𝐿₁-MetricSpaceⁿ (suc n) A)
-- -- -- --    ((λ x → _ ,
-- -- -- --     ∣ uContConstMap IntervalMetricSpace (𝐿₁-MetricSpaceⁿ n A) x ∣₁) ,
-- -- -- --      ∣ {!!} ∣₁)
 
-- -- -- --  Π-seq : Sequence ℓ
-- -- -- --  Π-seq .Sequence.obj = Π-seqₙ
-- -- -- --  Π-seq .Sequence.map = Π-seqₙ-map _

-- -- -- --  Π : Type ℓ 
-- -- -- --  Π = SeqColim Π-seq

-- -- -- --  ∙Π : ⟨ A ⟩ → P.Pointed ℓ
-- -- -- --  ∙Π a = Π , incl {n = 0} (ℝPaths.pt a)

-- -- -- --  -- UpToℝPath⟨A⟩→∥Π∥₂ : ∥ ? ∥₂  → ∥ Π ∥₂ 
-- -- -- --  -- UpToℝPath⟨A⟩→∥Π∥₂ = SQ.Rec.go w 
-- -- -- --  --  where
-- -- -- --  --  w : Rec _
-- -- -- --  --  w .Rec.isSetB = squash₂
-- -- -- --  --  w .Rec.f = ∣_∣₂ ∘ incl {n = 0} ∘ (ℝPaths.pt)
-- -- -- --  --  w .Rec.f∼ a a' (ℝPaths.𝕣path f) = 
-- -- -- --  --   cong (∣_∣₂ ∘ incl) (ℝPaths.path f)

             
                 
 
-- -- -- --  evalFromCubeDiag : ∀ n → ⟨ IntervalMetricSpace ⟩
-- -- -- --                         → UContMap (𝐿₁-MetricSpaceⁿ n A) A
-- -- -- --  evalFromCubeDiag zero _ = {!!}
-- -- -- --  evalFromCubeDiag (suc n) t = {!!}


-- -- -- --  liftPath : ∀ (p : UContMap IntervalMetricSpace A) → Square {A = Π}
-- -- -- --               (cong (incl {n = 0}) (ℝPaths.path p))
-- -- -- --               (cong (incl {n = 1}) (ℝPaths.path ((λ x → (λ _ → fst p x) ,
-- -- -- --                  {!!}) , {!!})))
-- -- -- --               (push (ℝPaths.pt (p .fst 0)))
-- -- -- --               (push (ℝPaths.pt (p .fst 1)))
-- -- -- --  liftPath p i j = push {n = 0} (ℝPaths.path p j ) i


-- -- -- --  liftPath' : ∀ (p : UContMap IntervalMetricSpace A) → Square {A = Π}
-- -- -- --               (cong (incl {n = 0}) (ℝPaths.path p))
-- -- -- --               (cong (incl {n = 1}) (ℝPaths.path ((λ x → (λ _ → fst p x) ,
-- -- -- --                  {!!}) , {!!})))
-- -- -- --               {!!}
-- -- -- --               {!!}
-- -- -- --  liftPath' p i j = {!!}


-- -- -- --  -- a = evalFromCubeDiag n t (fst a t)
 
-- -- -- --  -- ∥Πₙ∥₂→UpToℝPath⟨A⟩ : ∀ n → ∥ Π-seqₙ n ∥₂ → ℝPaths.UpToℝPath A
-- -- -- --  -- ∥Πₙ∥₂→UpToℝPath⟨A⟩ n = ST.rec squash/
-- -- -- --  --   (ElimPiecesSet.go w)
-- -- -- --  --  where
-- -- -- --  --  w : ElimPiecesSet (𝐿₁-MetricSpaceⁿ n A) (λ _ → ℝPaths.UpToℝPath A)
-- -- -- --  --  w .ElimPiecesSet.pt-f = [_]/ ∘ fst (evalFromCubeDiag n 0)
-- -- -- --  --  w .ElimPiecesSet.path-f p = eq/ _ _ (ℝPaths.𝕣path {!!})
-- -- -- --  --  w .ElimPiecesSet.isSetT _ = squash/ 
  
-- -- -- --  -- ∥Π∥₂→UpToℝPath⟨A⟩ : ∥ Π ∥₂ → ∥ ℝPaths.Pieces A ∥₂
-- -- -- --  -- ∥Π∥₂→UpToℝPath⟨A⟩ = ST.rec squash/
-- -- -- --  --   (Seq.elim _ _ (elimdata (λ {n} → ElimPiecesSet.go (w n))
-- -- -- --  --     {!!}))
-- -- -- --  --   where
-- -- -- --  --   w : ∀ n → ElimPiecesSet _ _
-- -- -- --  --   w n .ElimPiecesSet.pt-f = [_]/ ∘ fst (evalFromCubeDiag n 0)
-- -- -- --  --   w n .ElimPiecesSet.path-f p = eq/ _ _ (ℝPaths.𝕣path {!p!})
-- -- -- --  --   w n .ElimPiecesSet.isSetT _ = squash/
   
-- -- -- --  -- Π₁≃ : ℝPaths.UpToℝPath A ≃ ∥ Π ∥₂
-- -- -- --  -- Π₁≃ = isoToEquiv (invIso (IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ A)) ∙ₑ
-- -- -- --  --   {!!} 

-- -- -- --  Π-isInfGpd₂-fun : ∀ (a : ⟨ A ⟩) n →  ∥
-- -- -- --       ℝPaths.Pieces
-- -- -- --       ((Ω^ n) (fst A , a , snd A) .fst ,
-- -- -- --        (Ω^ n) (fst A , a , snd A) .snd .snd)
-- -- -- --       ∥₂ →
-- -- -- --       ∥ fst ((Lsp.Ω^ n) (∙Π a)) ∥₂
-- -- -- --  Π-isInfGpd₂-fun a zero = {!!}
-- -- -- --  Π-isInfGpd₂-fun a (suc n) = {!!}
 
-- -- -- --  Π-isInfGpd₂ : ∀ (a : ⟨ A ⟩) n → Iso ∥
-- -- -- --       ℝPaths.Pieces
-- -- -- --       ((Ω^ n) (fst A , a , snd A) .fst ,
-- -- -- --        (Ω^ n) (fst A , a , snd A) .snd .snd)
-- -- -- --       ∥₂
-- -- -- --       ∥ fst ((Lsp.Ω^ n) (∙Π a)) ∥₂
-- -- -- --  Π-isInfGpd₂ a zero = {!!}
-- -- -- --  Π-isInfGpd₂ a (suc n) =
-- -- -- --    compIso {!!}  PathIdTrunc₁Iso
  
-- -- -- --  Π-isInfGpd : ∀ (a : ⟨ A ⟩) n →
-- -- -- --    -- fst ((Ω^ n) (_ , a , snd A))
-- -- -- --    ℝPaths.UpToℝPath₂ (∙MetricSpace→MetricSpace ((Ω^ n) (_ , a , snd A)))
-- -- -- --      ≃ ∥ fst ((Lsp.Ω^ n) (∙Π a)) ∥₂
-- -- -- --  Π-isInfGpd a n = isoToEquiv (invIso (IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ _))
-- -- -- --   ∙ₑ isoToEquiv (Π-isInfGpd₂ a n)
-- -- -- -- -- -- -- --  {- n-fold loop space of a pointed type -}
-- -- -- -- -- -- -- --  Ω^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Pointed ℓ
-- -- -- -- -- -- -- --  (Ω^ 0) p = p
-- -- -- -- -- -- -- --  (Ω^ (suc n)) p = Ω ((Ω^ n) p)



-- -- -- -- -- -- -- -- -- 𝐑²MetricSpaceStr : MetricSpaceStr (ℝ × ℝ)
-- -- -- -- -- -- -- -- -- 𝐑²MetricSpaceStr = {!!}

-- -- -- -- -- -- -- -- -- distCircleMetricSpaceStr : MetricSpaceStr distCircle 
-- -- -- -- -- -- -- -- -- distCircleMetricSpaceStr =
-- -- -- -- -- -- -- -- --  MetricSubSpace (ℝ × ℝ)
-- -- -- -- -- -- -- -- --   (λ z → (cartNorm² z ≡ 1) , isSetℝ _ _)
-- -- -- -- -- -- -- -- --   𝐑²MetricSpaceStr

-- -- -- -- -- -- -- -- -- unwindDistCirclePath :
-- -- -- -- -- -- -- -- --    (f : IntervalMetricSpace .fst → distCircle)
-- -- -- -- -- -- -- -- --  → IsUContMap (snd IntervalMetricSpace) f distCircleMetricSpaceStr
-- -- -- -- -- -- -- -- --  → Σ ((fst IntervalMetricSpace) → ℝ)
-- -- -- -- -- -- -- -- --    λ g → ∀ x → f x ≡ f (0 , (decℚ≤ᵣ? , decℚ≤ᵣ?)) ℝS¹.+
-- -- -- -- -- -- -- -- --      Circle→distCircle (injCircle (g x)) 
-- -- -- -- -- -- -- -- -- unwindDistCirclePath = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- ℝMetricSpace

-- -- -- -- -- -- -- -- -- -- -- -- isEquivInjCircleRestr : ∀ c₀ →
-- -- -- -- -- -- -- -- -- -- -- --   isEquiv {A = Σ distCircle λ (c , _) → cartDist² c₀ c <ᵣ 2}
-- -- -- -- -- -- -- -- -- -- -- --           {B = Σ _ (_∈ ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ]))}
          
-- -- -- -- -- -- -- -- -- -- -- --         {!!}
-- -- -- -- -- -- -- -- -- -- -- -- isEquivInjCircleRestr = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- distCircleLocallyIsomorphicToInterval :
-- -- -- -- -- -- -- -- -- -- -- -- -- --   ∀ (x : distCircle)
-- -- -- -- -- -- -- -- -- -- -- -- -- --    → Iso (Σ distCircle λ x' → cartDist² (fst x) (fst x') <ᵣ 2)
-- -- -- -- -- -- -- -- -- -- -- -- -- --          (Σ _ (_∈ ointervalℙ -1 1)) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- distCircleLocallyIsomorphicToInterval x =
-- -- -- -- -- -- -- -- -- -- -- -- -- --   compIso (rotateToOrigin x) {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- distCircleLocallyFromℝ : ∀ x₀ →
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Σ ℝ (_∈ ointervalℙ (x₀ -ᵣ rat [ 1 / 2 ]) (x₀ +ᵣ rat [ 1 / 2 ]))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   → Σ distCircle (λ x → cartDist² (fst x)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                (fst (Circle→distCircle (injCircle x₀))) <ᵣ 4)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- distCircleLocallyFromℝ x₀ (x , x∈) .fst = Circle→distCircle (injCircle x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- distCircleLocallyFromℝ x₀ (x , x∈) .snd = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- distCircleLocallyIsomorphicToInterval :
-- -- -- -- -- -- -- -- -- -- -- -- -- --   ∀ x₀ → isEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- --     {A = Σ ℝ (_∈ ointervalℙ (x₀ -ᵣ rat [ 1 / 2 ]) (x₀ +ᵣ rat [ 1 / 2 ]) )}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     {B = Σ distCircle λ x → cartDist² (fst x)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                (fst (Circle→distCircle (injCircle x₀))) <ᵣ 4}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                (distCircleLocallyFromℝ x₀)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- distCircleLocallyIsomorphicToInterval = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- uContCircleMap : (distCircle → distCircle) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- uContCircleMap f =
-- -- -- -- -- -- -- -- -- -- -- -- --   IsUContinuousℙ (intervalℙ 0 1)
-- -- -- -- -- -- -- -- -- -- -- -- --     (const ∘ (fst ∘ fst ∘ f ∘ Circle→distCircle ∘ injCircle))
-- -- -- -- -- -- -- -- -- -- -- -- --     ×
-- -- -- -- -- -- -- -- -- -- -- -- --  IsUContinuousℙ (intervalℙ 0 1)
-- -- -- -- -- -- -- -- -- -- -- -- --     (const ∘ (snd ∘ fst ∘ f ∘ Circle→distCircle ∘ injCircle))


-- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-S¹→S¹ : Type 
-- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-S¹→S¹ = Σ[ f ∈ _ ] ∥ uContCircleMap f ∥₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- record Piecewise a b (a<b : a <ᵣ b) (p : Partition[ a , b ]) : Type where
-- -- -- -- -- -- -- -- -- -- -- -- -- --  field
-- -- -- -- -- -- -- -- -- -- -- -- -- --   fns : ∀ k x → x ∈ intervalℙ (pts' p (finj k)) (pts' p (fsuc k)) → ℝ
-- -- -- -- -- -- -- -- -- -- -- -- -- --   fnsEnds : ∀ k →
-- -- -- -- -- -- -- -- -- -- -- -- -- --     fns (finj k) (pts' p (fsuc (finj k))) ({!!} , (≤ᵣ-refl _))
-- -- -- -- -- -- -- -- -- -- -- -- -- --      ≡ fns (fsuc k) (pts' p (fsuc (finj k)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --          ((≡ᵣWeaken≤ᵣ _ _ {!!}) , {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- --   fnsUC : ∀ k → 
-- -- -- -- -- -- -- -- -- -- -- -- -- --      IsUContinuousℙ (intervalℙ (pts' p (finj k)) (pts' p (fsuc k)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --        (fns k)
   
-- -- -- -- -- -- -- -- -- -- -- -- -- --  piecewise : ∀ x → x ∈ intervalℙ a b → ℝ
-- -- -- -- -- -- -- -- -- -- -- -- -- --  piecewise = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --  piecewiseUC : IsUContinuousℙ (intervalℙ a b) piecewise
-- -- -- -- -- -- -- -- -- -- -- -- -- --  piecewiseUC = {!!}


  
-- -- -- -- -- -- -- -- -- -- -- -- -- const-ℝ-S¹→S¹ : ℝ-S¹→S¹
-- -- -- -- -- -- -- -- -- -- -- -- -- const-ℝ-S¹→S¹ .fst _ = circle0
-- -- -- -- -- -- -- -- -- -- -- -- -- const-ℝ-S¹→S¹ .snd =
-- -- -- -- -- -- -- -- -- -- -- -- --  ∣  IsUContinuousℙ-const (intervalℙ 0 1) _
-- -- -- -- -- -- -- -- -- -- -- -- --   , IsUContinuousℙ-const (intervalℙ 0 1) _ ∣₁




-- -- -- -- -- -- -- -- -- -- -- -- -- id-ℝ-S¹→S¹ : ℝ-S¹→S¹
-- -- -- -- -- -- -- -- -- -- -- -- -- id-ℝ-S¹→S¹ .fst x = x
-- -- -- -- -- -- -- -- -- -- -- -- -- id-ℝ-S¹→S¹ .snd = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   ∣ (IsUContinuousℙ∘ℙ (intervalℙ 0 1) (intervalℙ 0 1)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!} (uContSin (intervalℙ 0 1)) {!!}) , {!!} ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (IsUContinuous∘ {!!} {!!}) , {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- homotopy between maps
-- -- -- -- -- -- -- -- -- -- -- -- -- _∼_ : (distCircle → distCircle) → (distCircle → distCircle) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- f ∼ g = ∃ (∀ t → t ∈ intervalℙ 0 1 → ℝ-S¹→S¹)
-- -- -- -- -- -- -- -- -- -- -- -- --    λ h → ((fst (h 0 (≤ᵣ-refl 0 , decℚ≤ᵣ? {0} {1})) ≡ f)
-- -- -- -- -- -- -- -- -- -- -- -- --        × (fst (h 1 (decℚ≤ᵣ? {0} {1} , ≤ᵣ-refl 1)) ≡ g))
-- -- -- -- -- -- -- -- -- -- -- -- --        × ((∀ x → IsUContinuousℙ (intervalℙ 0 1)
-- -- -- -- -- -- -- -- -- -- -- -- --            (λ t t∈ → fst (fst (fst (h t t∈) x))))
-- -- -- -- -- -- -- -- -- -- -- -- --          × ((∀ x → IsUContinuousℙ (intervalℙ 0 1)
-- -- -- -- -- -- -- -- -- -- -- -- --            (λ t t∈ → snd (fst (fst (h t t∈) x))))))


-- -- -- -- -- -- -- -- -- -- -- -- -- isEquivRel∼ : BinaryRelation.isEquivRel {A = ℝ-S¹→S¹}
-- -- -- -- -- -- -- -- -- -- -- -- --  (λ (x , _) (y , _) → x ∼ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- isEquivRel∼ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-S¹→S¹/∼ : Type
-- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-S¹→S¹/∼ = ℝ-S¹→S¹ / λ (x , _) (y , _) → x ∼ y

-- -- -- -- -- -- -- -- -- -- -- -- -- eff-ℝ-S¹→S¹/∼ : (a b : ℝ-S¹→S¹) → [ a ]/ ≡ [ b ]/ → a .fst ∼ b .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- eff-ℝ-S¹→S¹/∼ = SQ.effective {A = ℝ-S¹→S¹}
-- -- -- -- -- -- -- -- -- -- -- -- --   {R = λ (x , _) (y , _) → x ∼ y} (λ _ _ → squash₁) isEquivRel∼

-- -- -- -- -- -- -- -- -- -- -- -- -- S¹→S¹· : ℝ-S¹→S¹ → ℝ-S¹→S¹ → ℝ-S¹→S¹
-- -- -- -- -- -- -- -- -- -- -- -- -- S¹→S¹· f g = (λ x → fst f x ℝS¹.+ fst g x) ,
-- -- -- -- -- -- -- -- -- -- -- -- --              PT.map2 (λ cf cg → {!!}) (snd f) (snd g)



-- -- -- -- -- -- -- -- -- -- -- -- -- invS¹→S¹· : ℝ-S¹→S¹ → ℝ-S¹→S¹
-- -- -- -- -- -- -- -- -- -- -- -- -- invS¹→S¹· (f , _) .fst = f ∘ circleNeg
-- -- -- -- -- -- -- -- -- -- -- -- -- invS¹→S¹· (f , fc) .snd = {!!} --PT.map (λ (xC , yC) → yC , xC) fc



-- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-π₁S¹ : AbGroup ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-π₁S¹ .fst = ℝ-S¹→S¹/∼
-- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-π₁S¹ .snd .AbGroupStr.0g = [ const-ℝ-S¹→S¹ ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-π₁S¹ .snd .AbGroupStr._+_ = SQ.Rec2.go w
-- -- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- -- --  w : Rec2 (ℝ-π₁S¹ .fst)
-- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec2.isSetB = squash/
-- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec2.f x y = [ S¹→S¹· x y ]/
-- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec2.f∼ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec2.∼f = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- AbGroupStr.- ℝ-π₁S¹ .snd = SQ.Rec.go w
-- -- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- -- --  w : Rec (ℝ-π₁S¹ .fst)
-- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec.isSetB = squash/
-- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec.f = [_]/ ∘ invS¹→S¹·
-- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec.f∼ a a' = {!!} -- (h , (px , py) , (t0 , t1)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --   -- eq/ _ _
-- -- -- -- -- -- -- -- -- -- -- -- --   --  ((λ t t∈ → (flipCircle ∘ (fst (h t t∈))) ,
-- -- -- -- -- -- -- -- -- -- -- -- --   --    snd (snd (h t t∈)) , fst (snd (h t t∈)))
-- -- -- -- -- -- -- -- -- -- -- -- --   --    , ((funExt λ x →
-- -- -- -- -- -- -- -- -- -- -- -- --   --      Σ≡Prop (λ _ → isSetℝ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- --   --      (cong₂ _,_
-- -- -- -- -- -- -- -- -- -- -- -- --   --      (cong (snd ∘ fst) (px ≡$ x))
-- -- -- -- -- -- -- -- -- -- -- -- --   --      (cong (fst ∘ fst) (px ≡$ x))))
-- -- -- -- -- -- -- -- -- -- -- -- --   --    , (funExt λ x →
-- -- -- -- -- -- -- -- -- -- -- -- --   --      Σ≡Prop (λ _ → isSetℝ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- --   --      (cong₂ _,_
-- -- -- -- -- -- -- -- -- -- -- -- --   --      (cong (snd ∘ fst) (py ≡$ x))
-- -- -- -- -- -- -- -- -- -- -- -- --   --      (cong (fst ∘ fst) (py ≡$ x)))))
-- -- -- -- -- -- -- -- -- -- -- -- --   --    , {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-π₁S¹ .snd .AbGroupStr.isAbGroup =
-- -- -- -- -- -- -- -- -- -- -- -- --   makeIsAbGroup {!!} {!!} {!!} {!!} {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- module ℝπ₁S¹ where
-- -- -- -- -- -- -- -- -- -- -- -- --  open AbGroupStr (snd ℝ-π₁S¹) public



-- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ→ℝ-Circle→Circle : ℤ → Circle → Circle 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ→ℝ-Circle→Circle k = SQ.Rec.go w 
-- -- -- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- -- -- --  w : Rec Circle
-- -- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec.isSetB = isSetCircle
-- -- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec.f x = injCircle (rat [ k / 1 ] ·ᵣ x) 
-- -- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec.f∼ a a' (z , p) = eq/ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- --    (k ℤ.· z ,
-- -- -- -- -- -- -- -- -- -- -- -- -- --     (sym (𝐑'.·DistR- _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      ∙∙ cong (rat [ k / 1 ] ·ᵣ_) p ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- --      sym (rat·ᵣrat _ _)))
 




-- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ→ℝ-S¹→S¹/ : ℤ → ℝ-S¹→S¹/∼ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ→ℝ-S¹→S¹/ = _ℤ[ AbGroup→Group ℝ-π₁S¹ ]· [ id-ℝ-S¹→S¹ ]/

-- -- -- -- -- -- -- -- -- -- -- -- -- -- opaque
-- -- -- -- -- -- -- -- -- -- -- -- -- --  -- unfolding circle0
-- -- -- -- -- -- -- -- -- -- -- -- -- --  ℤ→ℝ-S¹→S¹* : ℤ → ℝ-S¹→S¹ 
-- -- -- -- -- -- -- -- -- -- -- -- -- --  ℤ→ℝ-S¹→S¹* z = (λ x → z ℤ[ AbGroup→Group ℝS¹AbGroup ]· x) , {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --  ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* : ∀ z → ℤ→ℝ-S¹→S¹/ z ≡ [ ℤ→ℝ-S¹→S¹* z ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- --  ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (pos zero) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --    cong [_]/ (Σ≡Prop (λ _ → squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- --  ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (pos (suc n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --    cong ([ id-ℝ-S¹→S¹ ]/ ℝπ₁S¹.+_) (ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (pos n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --     ∙ cong [_]/ (Σ≡Prop (λ _ → squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- --       (funExt λ x → distCircle≡ refl refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- --  ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (ℤ.negsuc zero) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --   cong [_]/ (Σ≡Prop (λ _ → squash₁) refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- --  ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (ℤ.negsuc (suc n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --    cong (ℝπ₁S¹.- [ id-ℝ-S¹→S¹  ]/  ℝπ₁S¹.+_) (ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (ℤ.negsuc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --     ∙ cong [_]/ (Σ≡Prop (λ _ → squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- --       (funExt λ x → distCircle≡ refl refl))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- opaque
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-S¹→S¹-winding : ∀ f → uContCircleMap f →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Σ ℤ.ℤ λ k →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Σ (fromInterval→ℝ-uC) λ (g , _) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((rat [ k / 1 ] ≡ g 1 (decℚ≤ᵣ? , decℚ≤ᵣ?) -ᵣ g 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        × (((∀ x x∈ →  Circle→distCircle (injCircle (g x x∈)) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              f (Circle→distCircle (injCircle x))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              × (fst (ℤ→ℝ-S¹→S¹* k) ∼ f))) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-S¹→S¹-winding f  (ucX , ucY) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (fst pcwΔ) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ((fst pcwN , fst (snd pcwN)) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ((snd pcwΔ) , snd (snd pcwN) , ∼f))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ε : ℚ₊
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ε = 1

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   uc-x : Σ ℚ₊ λ δ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (u v : ℝ) (u∈ : u ∈ intervalℙ 0 1) (v∈ : v ∈ intervalℙ 0 1) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  u ∼[ δ ] v →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  fst (fst (f (Circle→distCircle (injCircle u)))) ∼[ ε ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  fst (fst (f (Circle→distCircle (injCircle v))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   uc-x = ucX ε

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   uc-y : Σ ℚ₊ λ δ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (u v : ℝ) (u∈ : u ∈ intervalℙ 0 1) (v∈ : v ∈ intervalℙ 0 1) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  u ∼[ δ ] v →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  snd (fst (f (Circle→distCircle (injCircle u)))) ∼[ ε ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  snd (fst (f (Circle→distCircle (injCircle v))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   uc-y = ucY ε

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   δ : ℚ₊
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   δ = ℚ.min₊ 1 (ℚ.min₊ (fst uc-x) (fst uc-y))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   n,n< : Σ (ℕ × ℚ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ (n , q) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (fromNat n ℚ.+ q ≡ fst (invℚ₊ δ)) × (0 ℚ.≤ q) × (q ℚ.< 1))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   n,n< = ℚ.floor-fracℚ₊ (invℚ₊ δ)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   n : ℕ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   n = fst (fst n,n<)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pcw : ∀ k → k ℕ.≤ n →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            Σ[ g ∈ (∀ x → x ∈ intervalℙ 0 (rat [ pos (suc k) / 1+ n ]) → ℝ) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (IsUContinuousℙ (intervalℙ 0 (rat [ pos (suc k) / 1+ n ])) g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  × (∀ x x∈ → Circle→distCircle (injCircle (g x x∈)) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       f (Circle→distCircle (injCircle x))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pcw zero x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pcw (suc k) x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pcwN : Σ[ g ∈ (∀ x → x ∈ intervalℙ 0 1 → ℝ) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ((IsUContinuousℙ (intervalℙ 0 1) g) × 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (∀ x x∈ → Circle→distCircle (injCircle (g x x∈)) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       f (Circle→distCircle (injCircle x))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pcwN = subst (λ u → Σ[ g ∈ (∀ x → x ∈ intervalℙ 0 u → ℝ) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (IsUContinuousℙ (intervalℙ 0 u) g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  × (∀ x x∈ → Circle→distCircle (injCircle (g x x∈)) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       f (Circle→distCircle (injCircle x)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        (cong rat (ℚ.[/]≡· (pos (suc n)) (1+ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         ∙ ℚ.x·invℚ₊[x] ([ pos (suc n) / 1 ] , _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (pcw n (ℕ.≤-refl {n}))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- f (Circle→distCircle (injCircle (fst fwi x x∈)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ≡ fst fwi x x∈

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pcwΔ : Σ[ k ∈ ℤ ] (rat [ k / 1 ] ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           fst pcwN 1 (decℚ≤ᵣ? , decℚ≤ᵣ?) -ᵣ fst pcwN 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pcwΔ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    let p : Circle→distCircle (injCircle (pcwN .fst 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             Circle→distCircle (injCircle (pcwN .fst 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        p = (snd (snd pcwN) 0 (decℚ≤ᵣ? , decℚ≤ᵣ? ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ∙∙ cong (f ∘ Circle→distCircle)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (eq/ _ _ (-1 , -ᵣ-rat₂ 0 1)) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             sym (snd (snd pcwN) 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        p' = invEq (congEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --               {x = injCircle (pcwN .fst 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --               {y = injCircle (pcwN .fst 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                Circle≃distCircle) p  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        z = fromCircle≡ _ _ (sym p')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    in fst z , sym (snd z)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- 𝒈 : CircleOverlap[ ℚ₊→ℝ₊ ([ 1 / 2 ] , _) ] → distCircle
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- 𝒈 = SQ.Rec.go
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {A = Σ-syntax ℝ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          (λ x → x ∈ ointervalℙ 0 (1 +ᵣ fst (ℚ₊→ℝ₊ ([ 1 / 2 ] , tt))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {R = circle-rel-overlap (ℚ₊→ℝ₊ ([ 1 / 2 ] , tt))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    ww
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  -- www : (x : ℝ) → distCircle
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  -- www = stichFns' distCircle isSetDistCircle
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  --   (rat [ 1 / 2 ]) 1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  --    decℚ<ᵣ?
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  --      (λ x x<1 → Circle→distCircle (injCircle (fst pcwN (maxᵣ 0 x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  --        ((≤maxᵣ 0 x) , max≤-lem 0 x 1 decℚ≤ᵣ? (<ᵣWeaken≤ᵣ _ _ x<1)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  --      (λ x 1/2<x → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  --      {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  ww : Rec
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {A = Σ-syntax ℝ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          (λ x → x ∈ ointervalℙ 0 (1 +ᵣ fst (ℚ₊→ℝ₊ ([ 1 / 2 ] , tt))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {R = circle-rel-overlap (ℚ₊→ℝ₊ ([ 1 / 2 ] , tt))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    distCircle
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  ww .Rec.isSetB = isSetDistCircle
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  ww .Rec.f (x , x∈) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  ww .Rec.f∼ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝒉 : (t : ℝ) → t ∈ intervalℙ 0 1 → ℝ-S¹→S¹
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝒉 t t∈ = Circle→distCircle ∘ injCircle ∘ fst zz ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zz : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zz = fromFWI ({!!} , {!!}) {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- fromFWI
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∼f : fst (ℤ→ℝ-S¹→S¹* (fst pcwΔ)) ∼ f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∼f = ∣ (𝒉 , {!!}) ∣₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ-ℝ-S¹→S¹-Hom : GroupHom ℤGroup (AbGroup→Group ℝ-π₁S¹)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ-ℝ-S¹→S¹-Hom .fst = ℤ→ℝ-S¹→S¹/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ-ℝ-S¹→S¹-Hom .snd = makeIsGroupHom 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (distrℤ· (AbGroup→Group ℝ-π₁S¹) [ id-ℝ-S¹→S¹ ]/)
  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ-ℝ-S¹→S¹-inj : ∀ k → ℤ→ℝ-S¹→S¹/ k ≡ [ const-ℝ-S¹→S¹ ]/ → k ≡ 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ-ℝ-S¹→S¹-inj k p = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let w = eff-ℝ-S¹→S¹/∼ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (sym (ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* k) ∙ p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in PT.rec
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (ℤ.isSetℤ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ (h , (h0 , h1) , _) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          {!!}) w

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ-ℝ-S¹→S¹-BijectionIso : BijectionIso ℤGroup (AbGroup→Group ℝ-π₁S¹)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ-ℝ-S¹→S¹-BijectionIso .BijectionIso.fun = ℤ-ℝ-S¹→S¹-Hom
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ-ℝ-S¹→S¹-BijectionIso .BijectionIso.inj = ℤ-ℝ-S¹→S¹-inj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℤ-ℝ-S¹→S¹-BijectionIso .BijectionIso.surj = SQ.ElimProp.go w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w : ElimProp (isInIm ℤ-ℝ-S¹→S¹-Hom)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w .ElimProp.isPropB _ = squash₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w .ElimProp.f (f , fc) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PT.map
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (map-snd (λ {z} w →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* z ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (eq/ (ℤ→ℝ-S¹→S¹* z) (f , fc) (snd (snd (snd w)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∘ ℝ-S¹→S¹-winding f) fc

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-π₁S¹ : Group ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-π₁S¹ .fst = ℝ-S¹→S¹/∼
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-π₁S¹ .snd .GroupStr.1g = [ const-ℝ-S¹→S¹ ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-π₁S¹ .snd .GroupStr._·_ = SQ.Rec2.go w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w : Rec2 (ℝ-π₁S¹ .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec2.isSetB = squash/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec2.f x y = [ S¹→S¹· x y ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec2.f∼ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec2.∼f = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-π₁S¹ .snd .GroupStr.inv = SQ.Rec.go w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w : Rec (ℝ-π₁S¹ .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec.isSetB = squash/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec.f = [_]/ ∘ invS¹→S¹·
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w .Rec.f∼ a a' (h , (px , py) , (t0 , t1)) = eq/ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ((λ t t∈ → (flipCircle ∘ (fst (h t t∈))) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      snd (snd (h t t∈)) , fst (snd (h t t∈)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , ((funExt λ x →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        Σ≡Prop (λ _ → isSetℝ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong₂ _,_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (snd ∘ fst) (px ≡$ x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (fst ∘ fst) (px ≡$ x))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , (funExt λ x →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        Σ≡Prop (λ _ → isSetℝ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong₂ _,_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (snd ∘ fst) (py ≡$ x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (fst ∘ fst) (py ≡$ x)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ℝ-π₁S¹ .snd .GroupStr.isGroup =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   makeIsGroup squash/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} {!!} {!!} {!!} {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- concatProp : fromWeldedInterval ℝ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    fromWeldedInterval ℝ → fromWeldedInterval ℝ  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- concatProp = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (ε : ℝ₊) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  circle-rel-overlap : 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (x y : (Σ[ x ∈ ℝ ] x ∈ ointervalℙ 0 (1 +ᵣ fst ε))) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  circle-rel-overlap (x , _) (y , _) = circle-rel x y

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  CircleOverlap[_] : Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  CircleOverlap[_] =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (Σ[ x ∈ ℝ ] x ∈ ointervalℙ 0 (1 +ᵣ fst ε))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    / circle-rel-overlap


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  CircleOverlap[_]→Circle : CircleOverlap[_] → Circle
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  CircleOverlap[_]→Circle = SQ.Rec.go w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   w : Rec _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   w .Rec.isSetB = isSetCircle
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   w .Rec.f (a , _) = [ a ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   w .Rec.f∼ _ _ = eq/ _ _



