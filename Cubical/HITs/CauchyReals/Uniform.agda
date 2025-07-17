{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

import Cubical.Functions.Logic as L
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


Integral'≡ : ∀ a b → (a ≤ᵣ b) → ∀ f g s
  → (∀ x → x ∈ intervalℙ a b → f x ≡ g x)
  → on[ a , b ]IntegralOf f is' s
  → on[ a , b ]IntegralOf g is' s
Integral'≡ a b x f g s p =
  (λ {ε} → PT.map (map-snd λ X tp msh≤ →
    isTrans≡<ᵣ _ _ _ (cong (absᵣ ∘ (_-ᵣ s))
      (sym (riemannSum'≡ (snd tp) f g p)))
     (X tp msh≤))) ∘_


IsUContinuousℙ-transl : ∀ P Δ f
 → IsUContinuousℙ (P ∘ (_-ᵣ Δ)) f
 → IsUContinuousℙ P λ x x∈ → f (x +ᵣ Δ) (subst-∈ P (sym (𝐑'.plusMinus _ _)) x∈)
IsUContinuousℙ-transl P Δ f =
 map-snd (λ X u v u∈ v∈ u∼v →
   X _ _ _ _ (+ᵣ-∼ _ _ _ _ u∼v)) ∘_

IsUContinuousℙ+ᵣ₂ : ∀ P f g → IsUContinuousℙ P f → IsUContinuousℙ P g →
   IsUContinuousℙ P λ x x∈ → f x x∈ +ᵣ g x x∈
IsUContinuousℙ+ᵣ₂ P f g fuc guc ε =
  let (δ , X) = fuc (/2₊ ε)
      (δ' , X') = guc (/2₊ ε)
  in ℚ.min₊ δ δ' ,
      λ u v u∈ v∈ u∼v →
       subst∼ (ℚ.ε/2+ε/2≡ε _)
         (triangle∼
            (+ᵣ-∼ _ _ _ (/2₊ ε)
             (X u v u∈ v∈ (∼-monotone≤ (ℚ.min≤ _ _) u∼v)))
            (+ᵣ-∼' _ _ _ (/2₊ ε)
             (X' u v u∈ v∈ (∼-monotone≤ (ℚ.min≤' _ _) u∼v))))

<ε-lemma : ∀ x (y : ℝ)  (ε y' : ℚ₊)
                   → absᵣ y <ᵣ rat (fst y')
                   → absᵣ x <ᵣ rat (fst ε ℚ.· fst (invℚ₊ y'))
                   → absᵣ (x ·ᵣ y)  <ᵣ rat (fst ε) 
<ε-lemma x y ε y' ∣y∣<y' ∣x∣<ε/y' =
  let z = <ᵣ₊Monotone·ᵣ _ _ _ _ (0≤absᵣ _) (0≤absᵣ _)
              ∣x∣<ε/y' ∣y∣<y' 
   in subst2 _<ᵣ_
         (sym (·absᵣ _ _))
         (sym (rat·ᵣrat _ _)
        ∙ cong rat
          (   sym (ℚ.·Assoc _ _ _)
           ∙ 𝐐'.·IdR' _ _ (ℚ.invℚ₊[x]·x _)))
         z


IsUContinuousℙ·ᵣ₂ : ∀ P f g →
   Bounded P f →
   Bounded P g →
   IsUContinuousℙ P f →
   IsUContinuousℙ P g →
   IsUContinuousℙ P λ x x∈ → f x x∈ ·ᵣ g x x∈
IsUContinuousℙ·ᵣ₂ P f g (bf , <bf) (bg , <bg) fuc guc ε =
  let δ  , X  = fuc (/2₊ ε ℚ₊· (invℚ₊ bg))
      δ' , X' = guc (/2₊ ε ℚ₊· (invℚ₊ bf))
      
  in ℚ.min₊ δ δ' ,
    λ u v u∈ v∈ u∼v → subst∼ {ε = /2₊ ε ℚ₊+ /2₊ ε}
           {ε' = ε} (ℚ.ε/2+ε/2≡ε (fst ε)) $
      let Y = isTrans≡<ᵣ _ _ _ (cong absᵣ (sym (𝐑'.·DistL- _ _ _))
             ∙ ·absᵣ _ _)
            (isTrans≤<ᵣ _ _ _
              (((≤ᵣ-o·ᵣ _ _ _ (0≤absᵣ _) (<bg u u∈))))
              (isTrans≡<ᵣ _ _ _ (·ᵣComm _ _)
               $ fst (z<x/y₊≃y₊·z<x _ _ _) (isTrans<≡ᵣ _ _ _
              (fst (∼≃abs<ε _ _ _) $ X u v u∈ v∈
                  (∼-monotone≤ (ℚ.min≤ (fst δ) (fst δ')) u∼v))
              (rat·ᵣrat _ _ ∙ cong₂ _·ᵣ_ refl
                (sym (invℝ₊-rat _))))))

          Y' = isTrans≡<ᵣ _ _ _ (cong absᵣ (sym (𝐑'.·DistR- _ _ _))
             ∙ (·absᵣ _ _))
            (isTrans≤<ᵣ _ _ _
              (≤ᵣ-·ᵣo _ _ _ (0≤absᵣ _) (<bf v v∈))
              (fst (z<x/y₊≃y₊·z<x _ _ _) (isTrans<≡ᵣ _ _ _
              (fst (∼≃abs<ε _ _ _) $ X' u v u∈ v∈
              (∼-monotone≤ (ℚ.min≤' (fst δ) (fst δ')) u∼v))
              (rat·ᵣrat _ _ ∙ cong₂ _·ᵣ_ refl
                (sym (invℝ₊-rat _))))))
      in invEq (∼≃abs<ε _ _ _)
         (isTrans≤<ᵣ _ _ _
           (isTrans≡≤ᵣ _ _ _
             (cong absᵣ (sym L𝐑.lem--060))
             (absᵣ-triangle _ _))
           (isTrans<≡ᵣ _ _ _
             (<ᵣMonotone+ᵣ _ _ _ _
             
             Y
             Y')
             (+ᵣ-rat _ _)))


IsUContinuousℙC·ᵣ : ∀ P (C : ℚ) f → IsUContinuousℙ P f → 
   IsUContinuousℙ P λ x x∈ → f x x∈ ·ᵣ rat C
IsUContinuousℙC·ᵣ P C f X = 
  map-snd (λ X u v u∈ v∈ → ·ᵣ-∼ _ _ _ _ _
   (isTrans≡≤ᵣ _ _ _
     (absᵣ-rat C ∙ cong rat (sym (ℚ.+IdR _)))
     (≤ℚ→≤ᵣ _ _ (ℚ.≤-o+ _ _ _ (ℚ.decℚ≤? {0} {1}))))
    ∘ X u v u∈ v∈ )
    ∘ X ∘ (_ℚ₊· invℚ₊ (ℚ.abs C ℚ.+ 1 ,
      ℚ.<→0< _ ((ℚ.≤<Monotone+ 0 _ 0 _
        (ℚ.0≤abs C) (ℚ.decℚ<? {0} {1})))))


IsUContinuousℙ-ᵣ∘ : ∀ P f → IsUContinuousℙ P f → 
   IsUContinuousℙ P λ x x∈ → -ᵣ (f x x∈)
IsUContinuousℙ-ᵣ∘ P f X = 
 subst (IsUContinuousℙ P)
   (funExt₂ λ _ _ → ·ᵣComm _ _ ∙ sym (-ᵣ≡[-1·ᵣ] _)) (IsUContinuousℙC·ᵣ P -1 f X) 





IsUContinuousId : IsUContinuous (idfun _)
IsUContinuousId = _, λ _ _ → idfun _

IsUContinuousℙ-const : ∀ P C → IsUContinuousℙ P λ _ _ → C
IsUContinuousℙ-const P C ε = 1 , λ _ _ _ _ _ → refl∼ _ _


FTOC⇒' : ∀ a b → a ≤ᵣ b 
          → (f : ∀ x → x ∈ intervalℙ a b →  ℝ)

          → (ucf : IsUContinuousℙ (intervalℙ a b) f)
          → (uDerivativeOfℙ (intervalℙ a b) ,
                        (λ x (a≤x , x≤b) →
                          fst (Integrate-UContinuousℙ a x a≤x
                             (λ x x∈ → f x (fst x∈ , isTrans≤ᵣ _ _ _
                               (snd x∈) x≤b))
                           (map-snd
                             (λ X → λ u v u∈ v∈ u∼v →
                              X u v ((fst u∈ , isTrans≤ᵣ _ _ _
                               (snd u∈) x≤b))
                               (((fst v∈ , isTrans≤ᵣ _ _ _
                               (snd v∈) x≤b))) u∼v)
                             ∘ ucf)))
                        is f)
FTOC⇒' a b a≤b f ucf ε = do 
 (δ , X) ← FTOC⇒ a (λ x → f (clampᵣ a b x)
       (clampᵣ∈ℚintervalℙ a b a≤b x))
       (map-snd (λ X u v u∼v →
        X _ _ (clampᵣ∈ℚintervalℙ a b a≤b u)
              (clampᵣ∈ℚintervalℙ a b a≤b v)
               (clampᵣ∼ u∼v)) ∘ ucf) ε
 ∣ δ , (λ x x∈ h h∈ 0＃h ∣h∣<δ →
    let z = X x (fst x∈) h (fst h∈)
            0＃h ∣h∣<δ
     in isTrans≡<ᵣ _ _ _
         (cong absᵣ
            (cong₂ _-ᵣ_
              (cong (uncurry f)
                (Σ≡Prop (∈-isProp (intervalℙ a b))
                 (∈ℚintervalℙ→clampᵣ≡  a b x x∈)))
              (cong₂ _·ᵣ_
               (cong₂ _-ᵣ_
                 (Integrate-UContinuous-≡-∈ a _ _ _ _ _ _
                   λ x' x'∈ → cong (uncurry f)
                       (Σ≡Prop (∈-isProp _)
                         (sym (∈ℚintervalℙ→clampᵣ≡  a _ x' x'∈)
                           ∙ ∈ℚintervalℙ→clampᵣ≡  a b x' (fst x'∈ ,
                             isTrans≤ᵣ _ _ _ (snd x'∈) (snd h∈)))))
                 
                        ((Integrate-UContinuous-≡-∈ a _ _ _ _ _ _
                   λ x' x'∈ → cong (uncurry f)
                       (Σ≡Prop (∈-isProp _)
                         (sym (∈ℚintervalℙ→clampᵣ≡  a _ x' x'∈)
                           ∙ ∈ℚintervalℙ→clampᵣ≡  a b x' (fst x'∈ ,
                             isTrans≤ᵣ _ _ _ (snd x'∈) (snd x∈)))))))
                refl)))
         z) ∣₁

isCauchySequence-∘+ : ∀ s k
 → IsCauchySequence' s
 → IsCauchySequence' (s ∘ (k ℕ.+_))
isCauchySequence-∘+ s k =
  map-snd (λ X m n <n <m →
    X (k ℕ.+ m) (k ℕ.+ n)
      (ℕ.≤-trans <n ℕ.≤SumRight)
      (ℕ.≤-trans <m ℕ.≤SumRight)) ∘_



-1ⁿ : ℕ → ℚ
-1ⁿ zero = 1
-1ⁿ (suc zero) = -1
-1ⁿ (suc (suc x)) = -1ⁿ x

absᵣ[-1ⁿ]≡1 : ∀ n → absᵣ (rat (-1ⁿ n)) ≡ 1
absᵣ[-1ⁿ]≡1 zero = absᵣ-rat _
absᵣ[-1ⁿ]≡1 (suc zero) = absᵣ-rat _
absᵣ[-1ⁿ]≡1 (suc (suc n)) = absᵣ[-1ⁿ]≡1 n

-1ⁿ· : ℕ → ℝ → ℝ
-1ⁿ· zero x = x
-1ⁿ· (suc zero) = -ᵣ_
-1ⁿ· (suc (suc n)) = -1ⁿ· n

-1ⁿ·-suc : ∀ n x → -1ⁿ· (suc n) x ≡ -ᵣ (-1ⁿ· n x)
-1ⁿ·-suc zero x = refl
-1ⁿ·-suc (suc zero) x = sym (-ᵣInvol x)
-1ⁿ·-suc (suc (suc n)) x = -1ⁿ·-suc n x

-1ⁿ·-·2 : ∀ n x → -1ⁿ· (n ℕ.· 2) x ≡ x
-1ⁿ·-·2 zero x = refl
-1ⁿ·-·2 (suc n) x = -1ⁿ·-·2 n x

-1ⁿ-suc : ∀ n → rat (-1ⁿ (suc n)) ≡ -ᵣ (rat (-1ⁿ n))
-1ⁿ-suc zero = sym (-ᵣ-rat _)
-1ⁿ-suc (suc zero) = sym (-ᵣ-rat _)
-1ⁿ-suc (suc (suc n)) = -1ⁿ-suc n

-1ⁿ·≡· : ∀ n x → -1ⁿ· n x ≡ rat (-1ⁿ n) ·ᵣ x
-1ⁿ·≡· zero x = sym (·IdL _)
-1ⁿ·≡· (suc zero) x = -ᵣ≡[-1·ᵣ] _
-1ⁿ·≡· (suc (suc n)) x = -1ⁿ·≡· n x

absᵣ∘-1ⁿ· : ∀ n x → absᵣ (-1ⁿ· n x) ≡ absᵣ x  
absᵣ∘-1ⁿ· zero x = refl
absᵣ∘-1ⁿ· (suc zero) x = sym (-absᵣ _)
absᵣ∘-1ⁿ· (suc (suc n)) x = absᵣ∘-1ⁿ· n x


^ⁿ-odd : ∀ n x → -ᵣ (x ^ⁿ suc (n ℕ.· 2)) ≡ ((-ᵣ x) ^ⁿ suc (n ℕ.· 2))
^ⁿ-even : ∀ n x → (x ^ⁿ (n ℕ.· 2)) ≡ ((-ᵣ x) ^ⁿ (n ℕ.· 2))

^ⁿ-even zero x = refl
^ⁿ-even (suc n) x =
      sym (·ᵣAssoc _ _ _)
   ∙∙ cong₂ _·ᵣ_ (^ⁿ-even n x) (sym (-ᵣ·-ᵣ _ _))
   ∙∙ ·ᵣAssoc _ _ _

^ⁿ-odd n x =  sym (·-ᵣ _ _) ∙ cong₂ _·ᵣ_ (^ⁿ-even n x) refl

x·x≡∣x∣·∣x∣ : ∀ x →  x ·ᵣ x ≡ absᵣ x ·ᵣ absᵣ x
x·x≡∣x∣·∣x∣ x = cong₂ _·ᵣ_ (sym (·IdL _)) refl ∙ ≡Continuous _ _
  (IsContinuous^ⁿ 2)
  (IsContinuous∘ _ _ (IsContinuous^ⁿ 2) IsContinuousAbsᵣ)
   (λ q →
    ^ⁿ-ℚ^ⁿ 2 q
     ∙∙ cong rat
         (sym (ℚ.·Assoc 1 _  _)
        ∙∙ cong₂ ℚ._·_ refl
         ( cong₂ ℚ._·_ refl (
          (sym (ℚ.sign·abs q) ∙
            (cong₂ ℚ._·_ (ℚ.abs≡sign· q) refl))
          ∙ ℚ.·Comm _ _) 
         ∙ ℚ.·Assoc _ _ _)
        ∙∙ ℚ.·Assoc 1 _ _)
     ∙ sym (^ⁿ-ℚ^ⁿ 2 _)
     ∙∙ cong (_^ⁿ 2) (cong rat (sym (ℚ.abs≡sign· q)) ∙ sym (absᵣ-rat q)))
    x
   ∙ cong₂ _·ᵣ_ (·IdL _) refl

abs[x^²ⁿ] : ∀ n x → x ^ⁿ (n ℕ.· 2) ≡ absᵣ (x ^ⁿ (n ℕ.· 2))  
abs[x^²ⁿ] zero x = sym (absᵣ-rat 1)
abs[x^²ⁿ] (suc n) x = sym (·ᵣAssoc _ _ _) ∙
   cong₂ _·ᵣ_ (abs[x^²ⁿ] n x)
    (x·x≡∣x∣·∣x∣ x)
 ∙ ·ᵣAssoc _ _ _  
 ∙ cong₂ _·ᵣ_ (sym (·absᵣ _ _)) refl
 ∙ sym (·absᵣ _ _)
  


sinSeries cosSeries : ℕ → ℝ → ℝ
sinSeries n x = -1ⁿ· n (expSeq x (suc (n ℕ.· 2)))
cosSeries n x = -1ⁿ· n (expSeq x (n ℕ.· 2))

seqΣ∘·2 : ∀ s n → seqΣ s (n ℕ.· 2) ≡
                  seqΣ (λ n → s (n ℕ.· 2) +ᵣ s (suc (n ℕ.· 2))) n 
seqΣ∘·2 s zero = refl
seqΣ∘·2 s (suc n) =
    sym (+ᵣAssoc _ _ _)
  ∙ cong₂ _+ᵣ_ (seqΣ∘·2 _ n) refl


expSeq' : ℝ → Seq
expSeq' x n =  (x ^ⁿ n) ／ᵣ₊ ℚ₊→ℝ₊ ([ pos (n !) / 1 ] ,
  ℚ.<→0< ([ pos (n !) / 1 ])
   (ℚ.<ℤ→<ℚ 0 _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.0<! n))))


expSeq'≡expSeq : ∀ x n → expSeq' x n ≡ expSeq x n
expSeq'≡expSeq x zero = cong₂ _·ᵣ_ refl (cong fst (invℝ₊1)) ∙ ·IdR 1
expSeq'≡expSeq x (suc n) =
    cong₂ _·ᵣ_ refl
     (cong (fst ∘ invℝ₊)
          (ℝ₊≡ (cong rat (sym (ℚ.ℕ·→ℚ· (suc n) (n !)))
          ∙ rat·ᵣrat _ _))
      ∙ cong fst (invℝ₊· (ℚ₊→ℝ₊ _)
       (ℚ₊→ℝ₊ (_ , ℚ.<→0< ([ pos (n !) / 1 ])
         (ℚ.<ℤ→<ℚ (pos 0) _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.0<! n))))))
      ∙ ·ᵣComm _ _)
  ∙ cong₂ _·ᵣ_ refl (cong₂ _·ᵣ_ refl (cong (fst ∘ invℝ₊) (ℝ₊≡ refl))) 
  ∙ L𝐑.lem--086
  ∙ cong₂ _·ᵣ_ (expSeq'≡expSeq x n) refl
  ∙ ·ᵣAssoc _ _ _ 
  ∙ sym (/nᵣ-／ᵣ₊ _ _)


-- expSeqMon : ∀ n → ∀ x y → x ≤ᵣ y → expSeq' x n ≤ᵣ expSeq' y n
-- expSeqMon zero x y x≤y = ≤ᵣ-refl _
-- expSeqMon (suc n) x y x≤y = {!_^ⁿ_!}

expSeq'NonNeg : ∀ x → 0 ≤ᵣ x → ∀ n → 0 ≤ᵣ expSeq' x n
expSeq'NonNeg x 0≤x n =
 isTrans≡≤ᵣ _ _ _
   (rat·ᵣrat 0 0)
   (≤ᵣ₊Monotone·ᵣ _ _ _ _
     (0≤x^ⁿ x n 0≤x) (≤ᵣ-refl 0)
     (0≤x^ⁿ x n 0≤x)
      (<ᵣWeaken≤ᵣ _ _ $ snd (invℝ₊
       (ℚ₊→ℝ₊
        ([ pos (n !) / 1+ 0 ] ,
         ℚ.<→0< [ pos (n !) / 1+ 0 ]
         (ℚ.<ℤ→<ℚ (pos 0) (pos (n !)) (ℤ.ℕ≤→pos-≤-pos 1 (n !) (ℕ.0<! n))))))))

expSeqNonNeg : ∀ x → 0 ≤ᵣ x → ∀ n → 0 ≤ᵣ expSeq x n
expSeqNonNeg x 0≤x n = isTrans≤≡ᵣ _ _ _
  (expSeq'NonNeg x 0≤x n) (expSeq'≡expSeq _ _)

absᵣ^ⁿ : ∀ x n → absᵣ (x ^ⁿ n) ≡ (absᵣ x ^ⁿ n)
absᵣ^ⁿ x zero = absᵣ-rat 1
absᵣ^ⁿ x (suc n) =
  ·absᵣ _ _ ∙ cong₂ _·ᵣ_ (absᵣ^ⁿ x n) refl

absᵣ∘expSeq≡expSeq∘absᵣ : ∀ n x →
   absᵣ (expSeq x n) ≡ expSeq (absᵣ x) n
absᵣ∘expSeq≡expSeq∘absᵣ n x =
     cong absᵣ (sym (expSeq'≡expSeq _ _))
  ∙∙ ·absᵣ _ _
     ∙ cong₂ _·ᵣ_
       (absᵣ^ⁿ x n)
       (absᵣPos _
         (snd (invℝ₊
                  (ℚ₊→ℝ₊
           ([ pos (n !) / 1 ] ,
            ℚ.<→0< [ pos (n !) / 1 ]
            (ℚ.<ℤ→<ℚ 0 (pos (n !))
            (ℤ.ℕ≤→pos-≤-pos (suc 0) (n !) (ℕ.0<! n))))))))
  ∙∙ expSeq'≡expSeq _ _


sinSeq≤expSeq-1 : ∀ n x → seqΣ (flip sinSeries x) n ≤ᵣ
                             seqΣ (expSeq (absᵣ x) ∘ suc) (n ℕ.· 2)
sinSeq≤expSeq-1 n x =
   isTrans≤≡ᵣ _ _ _
     (Seq'≤→Σ≤ _ _
      (λ n →
         isTrans≤ᵣ _ _ _
         (≤absᵣ _) (isTrans≡≤ᵣ _ _ _
           (absᵣ∘-1ⁿ· _ _ ∙ sym (+IdR _))
           (≤ᵣMonotone+ᵣ _ _ _ _
            (≡ᵣWeaken≤ᵣ _ _ (absᵣ∘expSeq≡expSeq∘absᵣ _ _))
            (expSeqNonNeg _ (0≤absᵣ _) _)))) n)
     (sym (seqΣ∘·2 _ _))


cosSeq≤expSeq : ∀ n x → seqΣ (flip cosSeries x) n ≤ᵣ
                             seqΣ (expSeq (absᵣ x)) (n ℕ.· 2)
cosSeq≤expSeq n x =
   isTrans≤≡ᵣ _ _ _
     (Seq'≤→Σ≤ _ _
      (λ n →
         isTrans≤ᵣ _ _ _
         (≤absᵣ _) (isTrans≡≤ᵣ _ _ _
           (absᵣ∘-1ⁿ· _ _ ∙ sym (+IdR _))
           (≤ᵣMonotone+ᵣ _ _ _ _
            (≡ᵣWeaken≤ᵣ _ _ (absᵣ∘expSeq≡expSeq∘absᵣ _ _))
            (expSeqNonNeg _ (0≤absᵣ _) _)))) n)
     (sym (seqΣ∘·2 _ _))

-cosSeq≤expSeq : ∀ n x → -ᵣ (seqΣ (flip cosSeries x) n) ≤ᵣ
                             seqΣ (expSeq (absᵣ x)) (n ℕ.· 2)
-cosSeq≤expSeq n x =
   isTrans≡≤ᵣ _ _ _
     (-seqΣ' _ _ )
    (isTrans≤≡ᵣ _ _ _
     (Seq'≤→Σ≤ _ _
      (λ n →
         isTrans≤ᵣ _ _ _
         (isTrans≤≡ᵣ _ _ _
           (≤absᵣ _) (sym (-absᵣ _)))
         (isTrans≡≤ᵣ _ _ _
           (absᵣ∘-1ⁿ· _ _ ∙ sym (+IdR _))
           (≤ᵣMonotone+ᵣ _ _ _ _
            (≡ᵣWeaken≤ᵣ _ _ (absᵣ∘expSeq≡expSeq∘absᵣ _ _))
            (expSeqNonNeg _ (0≤absᵣ _) _)))) n)
     (sym (seqΣ∘·2 _ _)))

expSeq'der : ∀ n x →
           derivativeOf flip expSeq' (suc n) at x is
             expSeq' x n
expSeq'der n x =
  let z = C·Derivative (fst 1/n!) x (_^ⁿ suc n) _ (derivative-^ⁿ n x)
  in substDer₂ (λ x → ·ᵣComm _ (x ^ⁿ suc n))
     (·ᵣAssoc _ _ _  ∙ ·ᵣComm _ _ ∙
       cong₂ _·ᵣ_ refl
        (cong₂ _·ᵣ_ (cong (fst ∘ invℝ₊)
           ((ℝ₊≡ (cong rat (sym (ℚ.ℕ·→ℚ· (suc n) (n !)))
             ∙ rat·ᵣrat _ _)))
           ∙ cong fst (invℝ₊· (ℚ₊→ℝ₊ _)
             ((ℚ₊→ℝ₊ (_ , ℚ.<→0< ([ pos (n !) / 1 ])
               (ℚ.<ℤ→<ℚ (pos 0) _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.0<! n)))))))
                ∙ ·ᵣComm _ _) refl
         ∙ [x/₊y]·yᵣ _ _)) z
 where
 1/n! = invℝ₊ $ ℚ₊→ℝ₊ ([ pos (suc n !) / 1 ] ,
  ℚ.<→0< ([ pos ((suc n) !) / 1 ])
   (ℚ.<ℤ→<ℚ (pos 0) _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.0<! (suc n)))))

expSerDer : ∀ n x →
    derivativeOf (λ x → expSeq x (suc n))
               at x is (expSeq x      n)
expSerDer n x = substDer₂
  (λ x → expSeq'≡expSeq x (suc n))
  (expSeq'≡expSeq x n)
  (expSeq'der n x)


∃ℚ₊LargerThanℝ₊ : ∀ (x : ℝ₊) → ∃[ q ∈ ℚ₊ ] fst x <ᵣ rat (fst q)
∃ℚ₊LargerThanℝ₊ x = PT.map
  (λ (q , x<q , _) →
     (q , ℚ.<→0< _ (<ᵣ→<ℚ 0 q (isTrans<ᵣ _ _ _ (snd x) x<q))) , x<q)
   (denseℚinℝ (fst x) (fst x +ᵣ 1)
     (isTrans≡<ᵣ _ _ _
        (sym (+IdR (fst x)))
        (<ᵣ-o+ _ _ (fst x) (decℚ<ᵣ? {0} {1}))))

∃ℚ₊LargerThanℝ₀₊ : ∀ (x : ℝ₀₊) → ∃[ q ∈ ℚ₊ ] fst x <ᵣ rat (fst q)
∃ℚ₊LargerThanℝ₀₊ x = PT.map
  (λ (q , x<q , _) →
     (q , ℚ.<→0< _ (<ᵣ→<ℚ 0 q (isTrans≤<ᵣ _ _ _ (snd x) x<q))) , x<q)
   (denseℚinℝ (fst x) (fst x +ᵣ 1)
     (isTrans≡<ᵣ _ _ _
        (sym (+IdR (fst x)))
        (<ᵣ-o+ _ _ (fst x) (decℚ<ᵣ? {0} {1}))))

fromCauchySequence'₁-≡-lem : ∀ s ics ics' →
 fromCauchySequence'₁ s ics ≡ fromCauchySequence'₁ s ics'
fromCauchySequence'₁-≡-lem s =
  PT.elim2 (λ _ _ → isSetℝ _ _)
   (fromCauchySequence'-≡-lem s)

fromCauchySequence'₁-≡ : ∀ s s' ics ics' →
  (∀ n → s n ≡ s' n) →
 fromCauchySequence'₁ s ics ≡ fromCauchySequence'₁ s' ics'
fromCauchySequence'₁-≡ s s' ics ics' p = PT.elim2
  (λ ics ics' → isSetℝ
      (fromCauchySequence'₁ s ics)
      (fromCauchySequence'₁ s' ics'))
  (λ ics ics' → fromCauchySequence'-≡ s s' ics ics' p)
  ics ics'

open ℚ.HLP

module _ (P : ℙ ℝ) where
 FSeq : Type
 FSeq = ℕ → ∀ x → x ∈ P  → ℝ


 IsUConvFSeries' : FSeq → Type
 IsUConvFSeries' s =
     ∀ (ε : ℚ₊) →
      Σ[ N ∈ ℕ ] ∀ x x∈ n m →
        absᵣ (seqΣ (flip (flip s x) x∈ ∘ (ℕ._+ (n ℕ.+ (suc N)))) m) <ᵣ rat (fst ε)

 IsUCauchyFSequence : FSeq → Type
 IsUCauchyFSequence s =
   ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ x x∈ m n → N ℕ.< n → N ℕ.< m →
     absᵣ ((flip (flip s x) x∈ n) +ᵣ (-ᵣ (flip (flip s x) x∈  m))) <ᵣ rat (fst ε))



 isCauchyFSequenceAt : ∀ s → IsUCauchyFSequence s →
      ∀ x x∈ → IsCauchySequence' (flip (flip s x) x∈)
 isCauchyFSequenceAt s icfs x x∈ ε =
   map-snd ((_$ x∈)∘(_$ x)) (icfs ε)


 IsUConvSeries' : FSeq → Type
 IsUConvSeries' s =
     ∀ (ε : ℚ₊) →
      Σ[ N ∈ ℕ ] ∀ x x∈ n m →
        absᵣ (seqΣ ((flip (flip s x) x∈)
          ∘ (ℕ._+ (n ℕ.+ (suc N)))) m) <ᵣ rat (fst ε)

    
 IsUConvSeries'SubSeq : ∀ s
  → (spd : ∀ n → Σ _ (n ℕ.≤_))
  → (∀ k → (fst (spd k) ℕ.< fst (spd (suc k))))
  → (∀ n x x∈ → 0 ≤ᵣ s n x x∈) 
  → IsUConvSeries' s
  → IsUConvSeries' (s ∘ fst ∘ spd) 
 IsUConvSeries'SubSeq s spd sIncr 0≤s =
   (map-snd (λ {N} X x x∈ m m' →
     let k , p = snd (spd (predℕ m' ℕ.+ (m ℕ.+ suc N)))
     in isTrans≤<ᵣ _ _ _
          (subst2 _≤ᵣ_
            (sym (abs[seqΣ]≡seqΣ _ _
               λ n → 0≤s (fst (spd (n ℕ.+ (m ℕ.+ suc N)))) _ _))
            (sym (abs[seqΣ]≡seqΣ _ _ λ n → 0≤s (n ℕ.+ (m ℕ.+ suc N)) _ _))
            
            ((series-subSeqLemma (λ n → s n x x∈)
              (λ n → 0≤s n x x∈) spd sIncr (m ℕ.+ suc N) m'))
              )
        (X x x∈ m (m' ℕ.+ k)))) ∘_


 IsUConvSeries'-fromConvBound : ∀ fs fs'
    → (∀ n x x∈ → absᵣ (fs' n x x∈) ≤ᵣ fs n x x∈)
    → IsUConvSeries' fs
    → IsUConvSeries' fs'
 IsUConvSeries'-fromConvBound fs fs' ∣fs'∣<fs =
   map-snd (λ X x x∈ n m →
     isTrans≤<ᵣ _ _ _
      (isTrans≤ᵣ _ _ _
        (abs[seqΣ]≤seqΣ[abs] _ _)
        (isTrans≤≡ᵣ _ _ _
          (Seq'≤→Σ≤ _ _ (λ n' → ∣fs'∣<fs (n' ℕ.+ (n ℕ.+ suc _)) x x∈) _)
          (sym (abs[seqΣ]≡seqΣ _ _
           λ n → isTrans≤ᵣ _ _ _ (0≤absᵣ _)
            (∣fs'∣<fs _ _ _)))))
      (X x x∈ n m))
    ∘_
 
 IsUContFSequence : FSeq → Type
 IsUContFSequence s = ∀ n → IsUContinuousℙ _ (s n)

 IsUContFSequenceΣSeq : ∀ s → IsUContFSequence s →
             IsUContFSequence λ n x x∈ → seqΣ (flip (flip s x) x∈ ) n
 IsUContFSequenceΣSeq s x zero =
  restrIsUContinuousℙ _ _ (IsUContinuousConst _)
 IsUContFSequenceΣSeq s x (suc n) =
   IsUContinuousℙ+ᵣ₂ P _ _
    (IsUContFSequenceΣSeq s x n) (x n)



 opaque
  fromUCauchyFSequence : ∀ s
        → IsUCauchyFSequence s
        → IsUContFSequence s
        → Σ[ f ∈ (∀ x → x ∈ P → ℝ) ] (IsUContinuousℙ P f)
  fromUCauchyFSequence s icfs iucs = f , icf

   where
   f : ∀ x → x ∈ P → ℝ
   f x x∈ = fromCauchySequence' (λ z → s z x x∈) (isCauchyFSequenceAt s icfs x x∈)

   icf : IsUContinuousℙ P f
   icf ε =
     let N , X = h (/2₊ (/2₊ ε))
         (δ , Y) = iucs (suc N) (/2₊ ε)
         
     in δ , λ u v u∈ v∈ u∼v →
          subst∼
            (cong₂ ℚ._+_ refl (ℚ.+Comm _ _) ∙ ℚ.+Assoc _ _ _ ∙
              cong₂ ℚ._+_ (ℚ.ε/2+ε/2≡ε (fst (/2₊ ε))) refl
               ∙ ℚ.ε/2+ε/2≡ε (fst ε))
            (triangle∼ (sym∼ _ _ _ (X u u∈ (suc N) ℕ.≤-refl))
            (triangle∼ (Y u v u∈ v∈ u∼v) (X v v∈ (suc N) ℕ.≤-refl)))
    where

     h : ∀ ε → Σ[ N ∈ ℕ ]
            (∀ x x∈ n → N ℕ.< n →
              s n x x∈ ∼[ ε ] f x x∈)
     h ε =
      let (N' , X') = icfs (/2₊ (/2₊ ε))
      in N' , λ x x∈ n N<n →
            
         let u = (𝕣-lim-self _
                (fromCauchySequence'-isCA _
                  (isCauchyFSequenceAt s icfs x x∈))
                  (/2₊ (/2₊ ε)) (/2₊ ε))
            
         in subst∼ (ℚ.+Assoc _ _ _ ∙
               cong₂ ℚ._+_ (ℚ.ε/2+ε/2≡ε (fst (/2₊ ε))) refl
               ∙ ℚ.ε/2+ε/2≡ε (fst ε))
              (triangle∼ (invEq (∼≃abs<ε _ _ (/2₊ (/2₊ ε)))
                    ((X'  x x∈ _ _  N<n (ℕ.≤-refl {suc N'})) )) u)

  fromCauchySequence'₁≡fromUCauchyFSequence : ∀ (fs : ℕ → ∀ x → x ∈ P  → ℝ) x x∈ →
     ∀ fucsₙ fcₙ fcs  →   
     fromCauchySequence'₁ (flip (flip fs x ) x∈) fcs ≡
      fst (fromUCauchyFSequence fs fucsₙ fcₙ) x x∈
  fromCauchySequence'₁≡fromUCauchyFSequence fs x x∈ fucsₙ fcₙ = 
   PT.elim (λ _ → isSetℝ _ _)
    λ fcs → fromCauchySequence'-≡-lem _ _ _


  IsUCauchyFSequence-lim :
    ∀ s → ∀ iufs iucs → 
        ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ]
    (∀ x x∈ n → N ℕ.< n → 
      absᵣ ((s n x x∈) -ᵣ (fst (fromUCauchyFSequence s iufs iucs) x x∈))
        <ᵣ (rat (fst ε)))

  IsUCauchyFSequence-lim s iufs iucs ε =
     let (N , X) = iufs (/4₊ ε)
     in N , λ x x∈ n N<n →
       let u = (𝕣-lim-self _ (fromCauchySequence'-isCA (λ n → s n x x∈)
                  (isCauchyFSequenceAt s iufs x x∈)) (/4₊ ε) (/4₊ ε))
           u' = fst (∼≃abs<ε _ _ _)
                (triangle∼ (invEq (∼≃abs<ε _ _ (/4₊ ε))
                  ((X  _ _  (suc N) n N<n (ℕ.≤-refl {suc N})) )) u)
       in isTrans<ᵣ _ _ _ u'
                (<ℚ→<ᵣ _ _
                  distℚ<! ε [ ge[ ℚ.[ 1 / 4 ] ]
                                +ge  (ge[ ℚ.[ 1 / 4 ] ]
                                +ge ge[ ℚ.[ 1 / 4 ] ]) < ge1 ])
       
  opaque
   unfolding _+ᵣ_
   fromUCauchyFSequence-+ : ∀ s uca uc s' uca' uc' uca+ uc+
      → ∀ x x∈ →
        fst (fromUCauchyFSequence s uca uc) x x∈
          +ᵣ fst (fromUCauchyFSequence s' uca' uc') x x∈ ≡
            fst (fromUCauchyFSequence
              (λ n x x∈ → s n x x∈ +ᵣ s' n x x∈ )
              uca+
              uc+)
              x x∈
   fromUCauchyFSequence-+ s uca uc s' uca' uc' uca+ uc+ x x∈ =
     snd (mapNE-fromCauchySequence' sumR _ _ _ _)
      ∙ fromCauchySequence'-≡-lem _ _ _


  IsoIsUConvSeries'IsCauchy'SequenceSum : (s : FSeq) →
    Iso (IsUConvSeries' s)
        (IsUCauchyFSequence
           λ n x x∈ → seqΣ (flip (flip s x) x∈) n)
  IsoIsUConvSeries'IsCauchy'SequenceSum fs =
     codomainIsoDep λ ε →
       Σ-cong-iso-snd λ N →
         isProp→Iso (isPropΠ4 λ _ _ _ _ → isProp<ᵣ _ _)
         (isPropΠ6 λ _ _ _ _ _ _ → isProp<ᵣ _ _)

         (λ f x x∈ → let s = (flip (flip fs x) x∈) in
            ℕ.elimBy≤
           (λ n n' X <n <n' → subst (_<ᵣ rat (fst ε))
             (minusComm-absᵣ _ _) (X <n' <n))
           λ n n' n≤n' N<n' N<n →
              subst ((_<ᵣ rat (fst ε)) ∘ absᵣ)
                 (cong (λ x → seqΣ (s ∘ (ℕ._+ x)) (n' ∸ n))
                    (ℕ.[n-m]+m (suc N) n N<n)
                   ∙∙ sym (seriesDiff s n (n' ∸ n)) ∙∙
                   cong (_+ᵣ (-ᵣ seqΣ s n))
                     (cong (seqΣ s)
                       (ℕ.[n-m]+m n n' n≤n')))
                 (f x x∈ (n ∸ (suc N)) (n' ∸ n)))

         λ f x x∈ n m → let s = (flip (flip fs x) x∈) in
           subst ((_<ᵣ rat (fst ε)) ∘ absᵣ)
             (seriesDiff s (n ℕ.+ suc N) m)
               (f x x∈ (n ℕ.+ (suc N)) (m ℕ.+ (n ℕ.+ suc N))
               (subst (N ℕ.<_) (sym (ℕ.+-assoc _ _ _))
                 (ℕ.≤SumRight {suc N} {m ℕ.+ n}))
               (ℕ.≤SumRight {suc N} {n}))

 isUCauchyFSequence-ᵣ : ∀ s → IsUCauchyFSequence s
                            → IsUCauchyFSequence (λ n x x∈ → -ᵣ (s n x x∈))
 isUCauchyFSequence-ᵣ s =
    map-snd (λ X _ _ _ _ n< m<
      → isTrans≡<ᵣ _ _ _ (cong absᵣ (sym (-ᵣDistr _ _))
        ∙ sym (-absᵣ _))
        (X _ _ _ _ n< m<)) ∘_

 isUCauchyFSequence+ᵣ : ∀ s s'
    → IsUCauchyFSequence s
    → IsUCauchyFSequence s'
    → IsUCauchyFSequence (λ n x x∈ → (s n x x∈) +ᵣ (s' n x x∈))
 isUCauchyFSequence+ᵣ s s' iucs iucs' ε =
   let (N  , X) = iucs (/2₊ ε)
       (N' , X') = iucs' (/2₊ ε)
       N⊔N' = ℕ.max N N'
   in N⊔N' , λ x x∈ m n <n <m →
     isTrans≡<ᵣ _ _ _
      (cong absᵣ (L𝐑.lem--041))
      (isTrans≤<ᵣ _ _ _
       (absᵣ-triangle _ _)
       (isTrans<≡ᵣ _ _ _
         (<ᵣMonotone+ᵣ _ _ _ _          
          (X _ _ _ _ (ℕ.≤<-trans (ℕ.left-≤-max {N} {N'}) <n)
           (ℕ.≤<-trans (ℕ.left-≤-max {N} {N'}) <m))
          (X' _ _ _ _
            (ℕ.≤<-trans (ℕ.right-≤-max {N'} {N}) <n)
            (ℕ.≤<-trans (ℕ.right-≤-max {N'} {N}) <m)))
         (+ᵣ-rat _ _ ∙
          cong rat (ℚ.ε/2+ε/2≡ε (fst ε))))) 




x∈interval-bound : ∀ a b → ∀ x (x∈ : x ∈ intervalℙ a b) →
                   absᵣ x ≤ᵣ maxᵣ (absᵣ a) (absᵣ b)
x∈interval-bound a b x (a≤x , x≤b) =
   isTrans≡≤ᵣ _ _ _ (abs-max x)
     (max≤-lem _ _ _
       ((isTrans≤ᵣ _ _ _
         x≤b
         (isTrans≤ᵣ _ _ _
           (≤absᵣ _) (isTrans≤≡ᵣ _ _ _ (≤maxᵣ _ _) (maxᵣComm _ _)))))
       (isTrans≤ᵣ _ _ _
         (-ᵣ≤ᵣ  _ _ a≤x)
         (isTrans≤ᵣ _ _ _
           (≤absᵣ _) (isTrans≡≤ᵣ _ _ _ (sym (-absᵣ _)) (≤maxᵣ _ _)))))


bounded-id : ∀ a b → 
             Bounded (intervalℙ (rat a) (rat b)) (λ x _ → x)
bounded-id a b = 
 (ℚ.max (ℚ.abs a) (ℚ.abs b) ℚ.+ 1 ,
           ℚ.<→0< _ (<ᵣ→<ℚ _ _
             ((isTrans≡<ᵣ _ _ _
         (sym (+IdR 0))
         (isTrans<≡ᵣ _ _ _
           (≤<ᵣMonotone+ᵣ _ _ _ _
          (isTrans≤ᵣ _ _ _ (0≤absᵣ (rat a)) (≤maxᵣ _ _ ))
          (decℚ<ᵣ? {0} {1}))
          (cong₂ _+ᵣ_ (cong₂ maxᵣ (absᵣ-rat a)
            ((absᵣ-rat b))) refl  ∙ +ᵣ-rat _ _)))))) ,
   λ x x∈ → isTrans≤≡ᵣ _ _ _ (isTrans≤ᵣ _ _ _
     (x∈interval-bound (rat a) (rat b) x x∈)
     (isTrans≡≤ᵣ _ _ _
         (sym (+IdR _))
         (≤ᵣ-o+ _ _ _ (decℚ≤ᵣ? {0} {1}))))
          (cong₂ _+ᵣ_ (cong₂ maxᵣ (absᵣ-rat _) (absᵣ-rat _)) refl
           ∙  (+ᵣ-rat _ _) )

bounded-+ : ∀ P f g
           → Bounded P f
           → Bounded P g
           → Bounded P (λ x x∈ → f x x∈ +ᵣ g x x∈)
bounded-+ P f g (bf , <bf) (bg , <bg) =
  (bf ℚ₊+ bg) , λ x x∈ → 
     isTrans≤≡ᵣ _ _ _ (isTrans≤ᵣ _ _ _
      (absᵣ-triangle _ _)
      (≤ᵣMonotone+ᵣ _ _ _ _ (<bf x x∈) (<bg x x∈)))
      (+ᵣ-rat _ _)

bounded-ᵣ : ∀ P f g
           → Bounded P f
           → Bounded P g
           → Bounded P (λ x x∈ → f x x∈ -ᵣ g x x∈)
bounded-ᵣ P f g (bf , <bf) (bg , <bg) =
  (bf ℚ₊+ bg) , λ x x∈ → 
     isTrans≤≡ᵣ _ _ _ (isTrans≤ᵣ _ _ _
      (isTrans≤≡ᵣ _ _ _ (absᵣ-triangle _ _)
        (cong₂ _+ᵣ_ refl (sym (-absᵣ _))))
      (≤ᵣMonotone+ᵣ _ _ _ _ (<bf x x∈) (<bg x x∈)))
      (+ᵣ-rat _ _)

-ᵣbounded : ∀ P f
           → Bounded P f
           → Bounded P λ x x∈ → -ᵣ (f x x∈)
-ᵣbounded P f (bf , <bf) =
  bf , λ x x∈ → isTrans≡≤ᵣ _ _ _ (sym (-absᵣ _)) (<bf x x∈)

bounded-· : ∀ P f g
           → Bounded P f
           → Bounded P g
           → Bounded P (λ x x∈ → f x x∈ ·ᵣ g x x∈)
bounded-· P f g (bf , <bf) (bg , <bg) =
  (bf ℚ₊· bg) , (λ x x∈ →
    isTrans≡≤ᵣ _ _ _
      (·absᵣ _ _)
      (isTrans≤≡ᵣ _ _ _
       (≤ᵣ₊Monotone·ᵣ _ _ _ _
         (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ bf)) (0≤absᵣ _)
         (<bf x x∈) (<bg x x∈))
       (sym (rat·ᵣrat _ _))))

bounded-^ⁿ : ∀ a b → rat a ≤ᵣ rat b → ∀ n →
             Bounded (intervalℙ (rat a) (rat b)) (λ x _ → (x ^ⁿ n))
bounded-^ⁿ a b a≤b zero = 1 ,
 λ _ _ → ≡ᵣWeaken≤ᵣ _ _ (absᵣPos _ (decℚ<ᵣ? {0} {1}))
bounded-^ⁿ a b a≤b (suc n) =
  bounded-· (intervalℙ (rat a) (rat b)) _ _
    (bounded-^ⁿ a b a≤b n) (bounded-id a b)





IsUContinuousℙ^ⁿ : ∀ a b → rat a ≤ᵣ rat b → ∀ n →
  IsUContinuousℙ (intervalℙ (rat a) (rat b))
  (λ x _ → x ^ⁿ n)
IsUContinuousℙ^ⁿ a b _ zero = restrIsUContinuousℙ _ _ (IsUContinuousConst _)
IsUContinuousℙ^ⁿ a b a≤b (suc n) =
  IsUContinuousℙ·ᵣ₂ (intervalℙ (rat a) (rat b)) _ _
    (bounded-^ⁿ a b a≤b n)
    (bounded-id a b)
    (IsUContinuousℙ^ⁿ a b a≤b n)
    (restrIsUContinuousℙ _ _ IsUContinuousId)

uConvExpSer : ∀ a b → a <ᵣ b →
  ∥ IsUConvSeries' (intervalℙ a b) (λ n x _ → expSeq x n) ∥₁
uConvExpSer a b a<b = do
  (b' , b<b') ← ∃ℚ₊LargerThanℝ₀₊ ((maxᵣ (absᵣ a) (absᵣ b)) ,
     isTrans≤ᵣ _ _ _ (0≤absᵣ _) (≤maxᵣ _ _))
  return
     ((λ {u} → map-snd λ X x x∈ →
           (expℝ-convSeriesF x _ (isTrans≤<ᵣ _ _ _
              (x∈interval-bound a b x x∈) b<b')
             u _ X))
       ∘ expSeriesConvergesAtℚ₊ (fst b') (ℚ.0<ℚ₊ b'))

uConvExpSer<ℚ : ∀ a b → 
  IsUConvSeries' (intervalℙ (rat a) (rat b)) (λ n x _ → expSeq x n) 
uConvExpSer<ℚ a b =
 let b' : ℚ₊
     b' = ℚ.max (ℚ.abs a) (ℚ.abs b) ℚ.+ 1 ,
           ℚ.<→0< _
            ((ℚ.≤<Monotone+ 0 _ 0 _
             (ℚ.≤MonotoneMax
              0 _ 0 _
              (ℚ.0≤abs a) (ℚ.0≤abs b))
             (ℚ.decℚ<? {0} {1})))
     b<b' : ℚ.max (ℚ.abs a) (ℚ.abs b) ℚ.< fst b'
     b<b' = ℚ.<+ℚ₊' _ _ 1 (ℚ.isRefl≤ _)
  in (λ {u} → map-snd λ X x x∈ →
           (expℝ-convSeriesF x _ 
             (isTrans≤<ᵣ _ _ _
              (x∈interval-bound (rat a) (rat b) x x∈)
               (isTrans≡<ᵣ _ _ _ (cong₂ maxᵣ
                 (absᵣ-rat _) (absᵣ-rat _))
                (<ℚ→<ᵣ _ _ b<b')))
             u _ X))
       ∘ expSeriesConvergesAtℚ₊ (fst b') (ℚ.0<ℚ₊ b')

uConvExpSer<ℚ-absᵣ : ∀ a b 
  → IsUConvSeries' (intervalℙ (rat a) (rat b))
      (λ n x _ → expSeq (absᵣ x) n)
uConvExpSer<ℚ-absᵣ a b =
 let b' : ℚ₊
     b' = ℚ.max (ℚ.abs a) (ℚ.abs b) ℚ.+ 1 ,
           ℚ.<→0< _
            ((ℚ.≤<Monotone+ 0 _ 0 _
             (ℚ.≤MonotoneMax
              0 _ 0 _
              (ℚ.0≤abs a) (ℚ.0≤abs b))
             (ℚ.decℚ<? {0} {1})))
     b<b' : ℚ.max (ℚ.abs a) (ℚ.abs b) ℚ.< fst b'
     b<b' = ℚ.<+ℚ₊' _ _ 1 (ℚ.isRefl≤ _)
  in (λ {u} → map-snd λ X x x∈ →
           (expℝ-convSeriesF (absᵣ x) _ 
             (isTrans≤<ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
              (absᵣIdemp x)
              (x∈interval-bound (rat a) (rat b) x x∈))
               (isTrans≡<ᵣ _ _ _ (cong₂ maxᵣ
                 (absᵣ-rat _) (absᵣ-rat _))
                (<ℚ→<ᵣ _ _ b<b')))
             u _ X))
       ∘ expSeriesConvergesAtℚ₊ (fst b') (ℚ.0<ℚ₊ b')

IsUCauchyFSequence-∘+ : ∀ P fs m
  → IsUCauchyFSequence P fs
  → IsUCauchyFSequence P (fs ∘ (m ℕ.+_))
IsUCauchyFSequence-∘+ P fs k X =
  map-snd (λ X x x∈ n m <m <n →
    X x x∈ _ _
     (ℕ.≤-+-< ℕ.zero-≤ <m)
     (ℕ.≤-+-< ℕ.zero-≤ <n)) ∘ X

IsUContFSequence-∘+ : ∀ P fs m
  → IsUContFSequence P fs
  → IsUContFSequence P (fs ∘ (m ℕ.+_))
IsUContFSequence-∘+ P fs k = _∘ (k ℕ.+_)
  

IsUCauchyFSequenceExp : ∀ a b → a <ᵣ b → 
               ∥ (IsUCauchyFSequence (intervalℙ a b)
                      λ n x _ → seqΣ (expSeq x) n) ∥₁
IsUCauchyFSequenceExp a b a<b =
 PT.map (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ a b) (λ n x _ → expSeq x n))) (uConvExpSer a b a<b )


uCauchy∫ : ∀ a b → a ≤ᵣ b →
              (fₙ Fₙ : ℕ → ∀ x → x ∈ intervalℙ a b → ℝ)  
            → (∀ n x x∈ →
                on[ a , x ]IntegralOf (λ x ≤x x≤ → fₙ n x (≤x ,
                  isTrans≤ᵣ _ _ _ x≤ (snd x∈)))
                  is (Fₙ n) x x∈)
            → (icf : IsUCauchyFSequence (intervalℙ a b) fₙ)
            → ∀ ucf 
            → ∀ iucF ucF → ∀ x x∈
            → on[ a , x ]IntegralOf
                    (λ x ≤x x≤ →
                       fst (fromUCauchyFSequence _ _ icf ucf) x
                        (≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)))
                   is
                 (fst (fromUCauchyFSequence (intervalℙ a b) Fₙ iucF ucF) x x∈)
                 
uCauchy∫ a b a≤b fₙ Fₙ fₙ≡∫Fₙ icf ucf iucF uF x x∈ ε = do
  (η₊ , b-a<η₊) ← ∃ℚ₊LargerThanℝ₀₊ ((b -ᵣ a) , x≤y→0≤y-x _ _ a≤b)
  let Nf , Xf = IsUCauchyFSequence-lim (intervalℙ a b)
              fₙ icf ucf 
        ((/2₊ (/2₊ ε)) ℚ₊· invℚ₊ η₊)
      NF , XF = IsUCauchyFSequence-lim (intervalℙ a b) _
                 iucF uF (/2₊ (/2₊ ε))
      Nf⊔NF = ℕ.max Nf NF
  (δ , Xδ) ← fₙ≡∫Fₙ (suc Nf⊔NF) x x∈ (/2₊ ε)
  return
    (δ , λ tp msh≤ →
          fst (∼≃abs<ε _ _ ε)
              (subst∼ (ℚ.+Comm _ _ ∙  (ℚ.+Assoc _ _ _)
                ∙ cong₂ ℚ._+_ (ℚ.ε/2+ε/2≡ε (fst (/2₊ ε))) refl
                 ∙ ℚ.ε/2+ε/2≡ε (fst ε))
                (triangle∼
                  (triangle∼ {ε = (/2₊ (/2₊ ε))}
                     (sym∼ _ _ _ $ invEq (∼≃abs<ε _ _ (/2₊ (/2₊ ε)))
                        (isTrans≡<ᵣ _ _ _
                          (cong absᵣ (riemannSum- (snd tp) _ _
                           ∙ riemannSum-clamp (snd tp) _))
                          (isTrans≤<ᵣ _ _ _
                            (isTrans≤ᵣ _ _ _
                             (riemannSum'-absᵣ≤ (snd tp) _)
                             (riemannSum'≤ (snd tp) _ _
                               λ r ≤x x≤ →
                                <ᵣWeaken≤ᵣ _ _
                                  (Xf _ _ (suc Nf⊔NF)
                                  (ℕ.left-≤-max {suc Nf} {suc NF}))))
                            (isTrans≡<ᵣ _ _ _
                              (riemannSum'Const (snd tp) _
                               ∙ cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl
                               ∙ sym (·ᵣAssoc _ _ _)
                               ∙ cong₂ _·ᵣ_ refl (·ᵣComm _ _))
                              (isTrans<≡ᵣ _ _ _
                                 (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ (/2₊ (/2₊ ε)))
                                  (isTrans≡<ᵣ _ _ _
                                    (cong₂ _·ᵣ_ refl (sym (invℝ₊-rat η₊)))
                                    (invEq (z/y<x₊≃z<y₊·x _ _ _)
                                     (isTrans<≡ᵣ _ _ _
                                       (isTrans≤<ᵣ _ _ _
                                         (≤ᵣ-+o _ _ (-ᵣ a) (snd x∈)) b-a<η₊)
                                       (sym (·IdR _))))))
                                 (·IdR _))))))
                    (invEq (∼≃abs<ε _ _ (/2₊ ε)) (Xδ tp msh≤)))
                  (invEq (∼≃abs<ε _ _ (/2₊ (/2₊ ε))) (XF x x∈ (suc Nf⊔NF)
                    (ℕ.right-≤-max {suc NF} {suc Nf}))))))

Integral-additive : ∀ a b c a≤b b≤c → ∀ f s s' s+s' →
  on[ a , b ]IntegralOf (λ x ≤x x≤ → f x ≤x (isTrans≤ᵣ _ _ _ x≤ b≤c)) is s →
  on[ b , c ]IntegralOf (λ x ≤x x≤ → f x (isTrans≤ᵣ _ _ _ a≤b ≤x ) x≤) is s' →
  on[ a , c ]IntegralOf f is s+s' →
  s +ᵣ s' ≡ s+s'
Integral-additive a b c a≤b b≤c f s s' s+s' ∫ab ∫bc ∫ac =
  Integral'-additive a b c a≤b b≤c
   (λ x → f (clampᵣ a c x)
     (≤clampᵣ a c x (isTrans≤ᵣ _ _ _ a≤b b≤c))
     (clamp≤ᵣ a c x))
   s s' s+s'
     (Integral'≡ _ _ a≤b  _ _ 
         s (λ x x∈@(≤x , x≤) →
              cong (uncurry (uncurry ∘ f))
         (Σ≡Prop (∈-isProp (intervalℙ a c))
           (sym (∈ℚintervalℙ→clampᵣ≡  a b x x∈) ∙
             ∈ℚintervalℙ→clampᵣ≡  a c x
               (≤x , isTrans≤ᵣ _ _ _ x≤ b≤c))))
         (invEq (clampᵣ-IntegralOf' a b a≤b _ s) ∫ab))
        (Integral'≡ _ _ b≤c  _ _ 
         s' (λ x x∈@(≤x , x≤) →
              cong (uncurry (uncurry ∘ f))
         (Σ≡Prop (∈-isProp (intervalℙ a c))
           ((sym (∈ℚintervalℙ→clampᵣ≡  b c x x∈) ∙
             ∈ℚintervalℙ→clampᵣ≡  a c x
               (isTrans≤ᵣ _ _ _ a≤b ≤x , x≤ )))))
          (invEq (clampᵣ-IntegralOf' b c b≤c _ s') ∫bc))
    (invEq (clampᵣ-IntegralOf' a c (isTrans≤ᵣ _ _ _ a≤b b≤c)
     (uncurry ∘ f) s+s') ∫ac)

FTOC⇐'' : ∀ a b (a<b : a <ᵣ b) (f F : ∀ x → x ∈ intervalℙ a b → ℝ)
          → (ucf : IsUContinuousℙ (intervalℙ a b) f)
          → uDerivativeOfℙ (intervalℙ a b) , F is f
          → ∀ x x∈
          → on[ a , x ]IntegralOf
              (λ x₁ ≤x x≤ → f x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈))) is
              (F x x∈ -ᵣ F a (≤ᵣ-refl a , <ᵣWeaken≤ᵣ _ _ a<b ))
FTOC⇐'' a b a<b f F ucf fd x x∈ =
  PT.rec (isPropΠ λ _ → squash₁)
    (⊎.rec
     (λ x<b →
       let zz = FTOC⇐ x b x<b 
                (λ x₁ (≤x , x≤)
                  → f x₁ (isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤))
                (λ x₁ (≤x , x≤)
                  → F x₁ (isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤))
                  (IsUContinuousℙ-restr _ _ _
                    (λ x (≤x , x≤) → isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤) ucf)
                   (uDerivativeOfℙ-restr _ _ _ _
                    (λ x (≤x , x≤) → isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤) fd)
           zzzW = (snd (Integrate-UContinuousℙ a x (fst x∈) _
                           ((IsUContinuousℙ-restr _ _ _
                        (λ x (≤x , x≤) →
                         ≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)) ucf))))
           zzz = Integral-additive a x b (fst x∈) (snd x∈)
                        _ _ _ _
                        zzzW
                        zz
                        (FTOC⇐ a b a<b _ _ ucf fd)
       in subst (on[ a , x ]IntegralOf
              (λ x₁ ≤x x≤ → f x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈))) is_)
               (sym (𝐑'.plusMinus _ _)
                ∙∙ cong₂ _-ᵣ_ zzz
                   (cong₂ _-ᵣ_
                     ((cong (uncurry F)
                        (Σ≡Prop (∈-isProp (intervalℙ a b))
                         refl)))
                     ((cong (uncurry F)
                        (Σ≡Prop (∈-isProp (intervalℙ a b))
                         refl))))
                ∙∙ L𝐑.lem--062)
               zzzW)
      λ a<x →
       subst (on[ a , x ]IntegralOf _ is_)
        (cong₂ _-ᵣ_
         (cong (uncurry F)
                (Σ≡Prop (∈-isProp (intervalℙ a b))
                 refl))
        (cong (uncurry F)
                (Σ≡Prop (∈-isProp (intervalℙ a b))
                 refl)))
        (FTOC⇐ a x a<x 
         (λ x₁ (≤x , x≤)
           → f x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈)))
         (λ x₁ (≤x , x≤)
           → F x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈)))
           (IsUContinuousℙ-restr _ _ _
             (λ x (≤x , x≤) → ≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)) ucf)
            (uDerivativeOfℙ-restr _ _ _ _
             (λ x (≤x , x≤) → ≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)) fd)))
    (Dichotomyℝ' a x b a<b)


ointervalℙ⊆intervalℙ : ∀ a b → ointervalℙ a b ⊆ intervalℙ a b
ointervalℙ⊆intervalℙ a b x z =
 <ᵣWeaken≤ᵣ a x (z .fst) , <ᵣWeaken≤ᵣ x b (z .snd)

uCauchyDer : ∀ a b → a <ᵣ b → ∀ fₙ Fₙ → 
             ∀ (icf : IsUCauchyFSequence (intervalℙ a b) fₙ)
               
             uf uF
             (icF : IsUCauchyFSequence (intervalℙ a b) Fₙ)
             → (∀ n → uDerivativeOfℙ (intervalℙ a b) , Fₙ n is fₙ n)
             → uDerivativeOfℙ (intervalℙ a b) ,
                  (fst (fromUCauchyFSequence _ _ icF uF))
                  is
                  (fst (fromUCauchyFSequence _ _ icf uf))
uCauchyDer a b a<b fₙ Fₙ  icf uf uF icF Fₙ'=fₙ = 
   uDerivativeℙ-cancelConst
   _ _ _ _ uzu2
 where
 a≤b = <ᵣWeaken≤ᵣ a b a<b
 F-F-ucfs : IsUContFSequence (intervalℙ a b)
      (λ n x₁ x∈₁ → Fₙ n x₁ x∈₁ -ᵣ Fₙ n a (≤ᵣ-refl a , a≤b))
 F-F-ucfs n = IsUContinuousℙ+ᵣ₂ _ _ _
    (uF n)
    (IsUContinuousℙ-const _ _)

 icf-a = isUCauchyFSequence-ᵣ _ _
                   (map-snd (λ X _ _ m n x₃ x₄ →
                     X _ _ m n x₃ x₄)
                     ∘ icF)

 F-F-uchfs : IsUCauchyFSequence (intervalℙ a b)
      (λ n x₁ x∈₁ → Fₙ n x₁ x∈₁ -ᵣ Fₙ n a (≤ᵣ-refl a , a≤b))
 F-F-uchfs = isUCauchyFSequence+ᵣ _ _ _
    icF icf-a
 
 icaFa : 
      IsCauchySequence' (λ z → -ᵣ Fₙ z a (≤ᵣ-refl a , a≤b))
 icaFa = 
   fst (map-fromCauchySequence'
  1 _ (isCauchyFSequenceAt _ _ icF a (≤ᵣ-refl a , a≤b))
   _ -ᵣ-lip)

 uzu2 : uDerivativeOfℙ intervalℙ a b ,
        (λ r z → fst
           (fromUCauchyFSequence (intervalℙ a b)
            Fₙ icF uF)
           r z +ᵣ _)
        is
        (fromUCauchyFSequence (intervalℙ a b) fₙ icf uf .fst)
 uzu2 = subst2 (uDerivativeOfℙ (intervalℙ a b) ,_is_)
           (funExt₂ λ x x∈@(≤x , x≤) →
              IntegralUniq a x (≤x) _ _ _ 
             (snd ((Integrate-UContinuousℙ a x ≤x 
              (λ x₁ x∈₁ →
                 fromUCauchyFSequence (intervalℙ a b) fₙ icf uf .fst x₁
                 (fst x∈₁ , isTrans≤ᵣ x₁ x b (snd x∈₁) x≤))
              (map-snd
               (λ X u v u∈ v∈ →
                  X u v (fst u∈ , isTrans≤ᵣ u x b (snd u∈) x≤)
                  (fst v∈ , isTrans≤ᵣ v x b (snd v∈) (x∈ .snd)))
               ∘ snd (fromUCauchyFSequence (intervalℙ a b) fₙ icf uf)))))
             (uCauchy∫ _ _ a≤b fₙ
                     (λ n x x∈ → Fₙ n x x∈ -ᵣ Fₙ n a (≤ᵣ-refl _ , a≤b))
                    (λ n x x∈ →
                       FTOC⇐'' a b a<b (fₙ n) (Fₙ n) (uf n)
                     (Fₙ'=fₙ n) x x∈)
                      icf uf
                      F-F-uchfs
                      F-F-ucfs
                      x x∈)
               ∙ sym (fromUCauchyFSequence-+ (intervalℙ a b) _ _ _ _
                 icf-a
                 (λ n → IsUContinuousℙ-const _ _ )
                 _ _
                    x _)
                 ∙ cong₂ _+ᵣ_ refl
                  (sym
                   (fromCauchySequence'₁≡fromUCauchyFSequence
                    _ _ _ _ _ _ ∣ icaFa ∣₁))) 
           refl
           (FTOC⇒' a b a≤b _
            (snd (fromUCauchyFSequence (intervalℙ a b) fₙ icf
                 uf)))

1+expSeq : ∀ n x → 1 +ᵣ (seqΣ (expSeq x ∘ suc) n) ≡ (seqΣ (expSeq x) (suc n))
1+expSeq n x = (cong (1 +ᵣ_) (seqSumUpTo≡seqSumUpTo' _ _)
     ∙∙ (sym (seqSumUpTo-suc (expSeq x) n))
     ∙∙ (cong₂ (_+ᵣ_)
       (sym (seqSumUpTo≡seqSumUpTo' _ _))
       refl))

0^ⁿ :  ∀ n → 0 ^ⁿ (suc n) ≡ 0
0^ⁿ n = 𝐑'.0RightAnnihilates _ 

1^ⁿ :  ∀ n → 1 ^ⁿ n ≡ 1
1^ⁿ zero = refl
1^ⁿ (suc n) = ·IdR _ ∙ 1^ⁿ n


expℝ0=1 : expℝ 0 ≡ 1
expℝ0=1 = fromCauchySequence'₁≡
  (seqΣ (expSeq 0)) _ 1
   λ ε → ∣ 0 , (λ n (n' , p) →
    isTrans≡<ᵣ _ _ _
     (cong absᵣ (𝐑'.+InvR' _ _
       ((cong (seqΣ (expSeq 0)) (sym p ∙ ℕ.+-suc _ _))
          ∙ sym (1+expSeq _ _)  ∙
          𝐑'.+IdR' _ _
            (seqSumUpTo≡seqSumUpTo' _ _ ∙
              (cong seqΣ' (funExt λ k → sym (expSeq'≡expSeq _ _) ∙
                𝐑'.0LeftAnnihilates' _ _ (0^ⁿ _))
               ≡$ (n' ℕ.+ 0)) ∙ seqSumUpToConst 0 _ ∙
                𝐑'.0LeftAnnihilates _) )) ∙ absᵣ0)
     (snd (ℚ₊→ℝ₊ ε))) ∣₁
     

expℚ-bound : ∀ (x : ℚ) → 0 ℚ.≤ x → Σ[ q ∈ ℚ₊ ] expℝ (rat x) <ᵣ rat (fst q)
expℚ-bound x = ⊎.rec
   (λ 0=x → 2 , isTrans≡<ᵣ _ _ _
     (cong (expℝ ∘ rat) (sym 0=x) ∙ expℝ0=1)
       (decℚ<ᵣ? {1} {2}))
   (λ 0<x →
     let N , X = fromCauchySequence'-lim _
             (fst (IsConvSeries'≃IsCauchySequence'Sum (expSeq (rat x)))
               (expSeriesConvergesAtℚ₊ x 0<x)) 1
         
         q , p = expSeries-rat x (suc N)
         Z : ℚ.0< (1 ℚ.+ ℚ.abs q)
         Z = ℚ.<→0< (1 ℚ.+ ℚ.abs q) (ℚ.<≤Monotone+ 0 _ 0 _
            (ℚ.decℚ<? {0} {1}) (ℚ.0≤abs q))
         ZZ = isTrans<≡ᵣ _ _ _
                
                 (isTrans<≤ᵣ _ _ _(a-b<c⇒a<c+b _ _ _ (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                  (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _)
                   (X (suc N) (ℕ.≤-refl {suc N}))
                   )))
                   (≤ᵣ-o+ _ _ _ (≤absᵣ _)))
                   (cong (1 +ᵣ_) (cong absᵣ p ∙
                     absᵣ-rat _)
                   ∙ +ᵣ-rat _ _ ) 
     in (_ , Z) ,
         isTrans≡<ᵣ _ _ _
          (fromCauchySequence'₁-≡-lem (seqΣ (expSeq (rat x))) _ ∣ _ ∣₁) ZZ)
   ∘ (ℚ.≤→<⊎≡ 0 x)


monotone-expℝ : ∀ a b → 0 ≤ᵣ a → a ≤ᵣ b → expℝ a ≤ᵣ expℝ b
monotone-expℝ a b 0≤a a≤b =
  fromCauchySequence'₁≤ _ _ _ _
   λ n → subst2 _≤ᵣ_
      (λ i → seqSumUpTo≡seqSumUpTo' (λ n → expSeq'≡expSeq a n i) n (~ i))
      (λ i → seqSumUpTo≡seqSumUpTo' (λ n → expSeq'≡expSeq b n i) n (~ i))
      (seqSumUpTo≤ _ _
       (λ n →
         ≤ᵣ-·ᵣo _ _ _ (<ᵣWeaken≤ᵣ _ _ (snd (invℝ₊ _)))
          (^ⁿ-Monotone n 0≤a a≤b))
       n)

1≤expℝ[pos] : ∀ x → 0 ≤ᵣ x → 1 ≤ᵣ expℝ x
1≤expℝ[pos] x 0≤x =
  isTrans≡≤ᵣ _ _ _
    (sym expℝ0=1) (monotone-expℝ 0 x (≤ᵣ-refl 0) 0≤x)


expℝ-pos : ∀ x → 0 ≤ᵣ x → 0 <ᵣ expℝ x
expℝ-pos x 0≤x = isTrans<≤ᵣ _ _ _
  (decℚ<ᵣ? {0} {1}) (1≤expℝ[pos] x 0≤x)

expBounded : ∀ a b → 0 ≤ᵣ rat a →  rat a ≤ᵣ rat b →
  Bounded (intervalℙ (rat a) (rat b))
          (λ x _  → expℝ x)
expBounded a b 0≤a a≤b =
  let q₊ , X = expℚ-bound b (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _ 0≤a a≤b) ) 
  in q₊ , λ x x∈ → isTrans≤ᵣ _ _ _
        (isTrans≡≤ᵣ _ _ _
          (absᵣPos _ (expℝ-pos x (isTrans≤ᵣ _ _ _ 0≤a (fst x∈)) ))
          (monotone-expℝ _ _ (isTrans≤ᵣ _ _ _ 0≤a (fst x∈))
            (snd x∈)))
        (<ᵣWeaken≤ᵣ _ _ X) 
  



uDerivativeOfℙ^n : ∀ a b → rat a <ᵣ rat b
  → ∀ n
  → uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → x ^ⁿ (suc n))
    is λ x _ → fromNat (suc n) ·ᵣ (x ^ⁿ n)
uDerivativeOfℙ^n a b a<b zero =
  subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
    (funExt₂ λ _ _ → sym (·IdL _))
    (funExt₂ λ _ _ → sym (·IdL _))
    (uDerivativeℙ-id _) 
uDerivativeOfℙ^n a b a<b (suc n) =
 subst (uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → x ^ⁿ (suc (suc n))) is_)    
    (funExt₂ λ x _ →
      (+ᵣComm _ _ ∙ cong₂ _+ᵣ_
       refl (sym (·ᵣAssoc _ _ _)) ∙
       sym (·DistR+ _ _ _) ∙
        cong (_·ᵣ ((x ^ⁿ n) ·ᵣ idfun ℝ x))
         (+ᵣ-rat _ _ ∙ cong rat (ℚ.ℕ+→ℚ+ _ _))))
    (uDerivativeOfℙ· (rat a) (rat b) a<b
      _ _ _ _ (bounded-^ⁿ a b (<ᵣWeaken≤ᵣ (rat a) (rat b) a<b) (suc n))
              (bounded-id a b)
              (IsUContinuousℙ^ⁿ a b (<ᵣWeaken≤ᵣ (rat a) (rat b) a<b) (suc n))
              (1 , λ _ _ → ≡ᵣWeaken≤ᵣ _ _ (absᵣ-rat 1)) 
      (uDerivativeOfℙ^n a b a<b n)
      (uDerivativeℙ-id _)) 


expSer'UDer : ∀ a b → rat a <ᵣ rat b → ∀ n →
      uDerivativeOfℙ intervalℙ (rat a) (rat b)
                           , (λ r _ → expSeq' r (suc n)) is
                             (λ r _ → expSeq' r n)
expSer'UDer a b a<b n =
  let z = C·uDerivativeℙ _ (fst 1/n!)
            _ _
            (uDerivativeOfℙ^n a b a<b n)
  in subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
    (funExt₂ λ _ _ → ·ᵣComm _ _)
    (funExt₂ λ _ _ →
      ·ᵣAssoc _ _ _  ∙ ·ᵣComm _ _ ∙
       cong₂ _·ᵣ_ refl
        (cong₂ _·ᵣ_ (cong (fst ∘ invℝ₊)
           ((ℝ₊≡ (cong rat (sym (ℚ.ℕ·→ℚ· (suc n) (n !)))
             ∙ rat·ᵣrat _ _)))
           ∙ cong fst (invℝ₊· (ℚ₊→ℝ₊ _)
             ((ℚ₊→ℝ₊ (_ , ℚ.<→0< ([ pos (n !) / 1 ])
               (ℚ.<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.0<! n)))))))
                ∙ ·ᵣComm _ _) refl
         ∙ [x/₊y]·yᵣ _ _))
    z

     
 where
 1/n! = invℝ₊ $ ℚ₊→ℝ₊ ([ pos (suc n !) / 1 ] ,
  ℚ.<→0< ([ pos ((suc n) !) / 1 ])
   (ℚ.<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.0<! (suc n)))))


expSerUDer : ∀ a b → rat a <ᵣ rat b → ∀ n → 
      uDerivativeOfℙ intervalℙ (rat a) (rat b)
                           , (λ r _ → expSeq r (suc n)) is
                             (λ r _ → expSeq r n)
expSerUDer a b a<b n =
  subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
   (funExt₂ (λ x _ → expSeq'≡expSeq x (suc n)))
   (funExt₂ (λ x _ → expSeq'≡expSeq x n))
   (expSer'UDer a b a<b n)

expSeqUDer : ∀ a b → rat a <ᵣ rat b → ∀ n → 
      uDerivativeOfℙ intervalℙ (rat a) (rat b)
                           , (λ r _ → seqΣ (expSeq r) (suc n)) is
                             (λ r _ → seqΣ (expSeq r) n)
expSeqUDer a b a<b zero = uDerivativeℙ-const _ _
expSeqUDer a b a<b (suc n) =
  +uDerivativeℙ _ _ _ _ _
   (expSeqUDer a b a<b n) (expSerUDer a b a<b n)


isUContFSequenceExpSer : ∀ a b → rat a ≤ᵣ rat b →
   IsUContFSequence (intervalℙ (rat a) (rat b))
      (λ z x _ → expSeq x z)
isUContFSequenceExpSer a b a≤b n =
  subst (IsUContinuousℙ (intervalℙ (rat a) (rat b)))
    (funExt₂ λ _ _ → cong₂ _·ᵣ_ refl (sym (invℝ₊-rat  _))
       ∙ expSeq'≡expSeq _ _)
    (IsUContinuousℙC·ᵣ (intervalℙ (rat a) (rat b)) _ _
      (IsUContinuousℙ^ⁿ a b a≤b n))


isUContFSequenceExp : ∀ a b → rat a ≤ᵣ rat b →
   IsUContFSequence (intervalℙ (rat a) (rat b))
      (λ z x _ → seqΣ (expSeq x) z)
isUContFSequenceExp a b a≤b = IsUContFSequenceΣSeq 
 _ (λ z x _ → expSeq x z) (isUContFSequenceExpSer a b a≤b)

uDerivativeOfℙ-expℝ : ∀ a b → (rat a) <ᵣ (rat b)
  
  → uDerivativeOfℙ (intervalℙ (rat a) (rat b))
        , (λ x _ → expℝ x) is (λ x _ → expℝ x)
uDerivativeOfℙ-expℝ a b a<b = PT.rec (isPropΠ λ _ → squash₁) (λ x → x) $ do
  z ← IsUCauchyFSequenceExp (rat a) (rat b) a<b
  let f = λ n x _ → seqΣ (expSeq x) n
      zz = uCauchyDer
           (rat a)
           (rat b)
           a<b
           f
            _
           
           z
           (isUContFSequenceExp a b (<ᵣWeaken≤ᵣ (rat a) (rat b) a<b))
           (IsUContFSequence-∘+ _ _ 1
             (isUContFSequenceExp a b (<ᵣWeaken≤ᵣ (rat a) (rat b) a<b)))
           (IsUCauchyFSequence-∘+ _ _ 1 z)
           (expSeqUDer a b a<b)
  return (subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
    (funExt₂ λ _ _ → let ics = _ in
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _
          
          (PT.map (isCauchySequence-∘+ _ 1) ics))
       ∙ sym (fromCauchySequence'₁-∘+ _ 1 ics _))
    (funExt₂ λ _ _ →
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _))
    zz)
  

cosSer'=-sinSer : ∀ a b → rat a <ᵣ rat b → ∀ n →
   uDerivativeOfℙ intervalℙ (rat a) (rat b) ,
      (λ r _ → flip cosSeries r (suc n)) is
      (λ r _ → -ᵣ (flip sinSeries r n))
cosSer'=-sinSer a b a<b n = 
  subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
    (funExt₂ λ _ _ → sym (-1ⁿ·≡· _ _))
    (funExt₂ λ _ _ → cong₂ _·ᵣ_  (-1ⁿ-suc n) refl
      ∙ -ᵣ· _ _ ∙ cong -ᵣ_ (sym (-1ⁿ·≡· n _)))
    (C·uDerivativeℙ _ (rat (-1ⁿ (suc n))) _ _
     (expSerUDer a b a<b (suc (n ℕ.· 2))))
  


sinSer'=cosSer : ∀ a b → rat a <ᵣ rat b → ∀ n →
 uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → (flip sinSeries x) n)
                             is (λ x _ → (flip cosSeries x) n)
sinSer'=cosSer a b a<b n =
  subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
    (funExt₂ λ _ _ → sym (-1ⁿ·≡· _ _))
    (funExt₂ λ _ _ → sym (-1ⁿ·≡· _ _))
    (C·uDerivativeℙ _ (rat (-1ⁿ n)) _ _
     (expSerUDer a b a<b (n ℕ.· 2)))



sinSeq'=cosSeq : ∀ a b → rat a <ᵣ rat b → ∀ n →
 uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → seqΣ (flip sinSeries x) n)
                      is (λ x _ → seqΣ (flip cosSeries x) n)
sinSeq'=cosSeq a b a<b zero = uDerivativeℙ-const _ _ 
sinSeq'=cosSeq a b a<b (suc n) =
  +uDerivativeℙ _ _ _ _ _
    (sinSeq'=cosSeq a b a<b n) (sinSer'=cosSer a b a<b n)

cosSeq'=-sinSeq : ∀ a b → rat a <ᵣ rat b → ∀ n →
 uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → seqΣ (flip cosSeries x) (suc n))
                      is (λ x _ → -ᵣ (seqΣ (flip sinSeries x) n))
cosSeq'=-sinSeq a b a<b zero = 
   subst (uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ _ _ → 0 +ᵣ 1) is_)
    (funExt₂ λ _ _ → sym (-ᵣ-rat 0))
    (uDerivativeℙ-const _ (0 +ᵣ 1))  
cosSeq'=-sinSeq a b a<b (suc n) =
   subst (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,
     (λ x _ → seqΣ (flip cosSeries x) (suc (suc n))) is_)
    (funExt₂ λ _ _ → sym (-ᵣDistr _ _))
  (+uDerivativeℙ _ _ _ _ _
    (cosSeq'=-sinSeq a b a<b n) (cosSer'=-sinSer a b a<b n))

sin-conv : ∀ a b → (rat a) <ᵣ (rat b) → 
  IsUConvSeries' (intervalℙ (rat a) (rat b))
    λ n x _ → sinSeries n x
sin-conv a b a<b  =
  IsUConvSeries'-fromConvBound
    (intervalℙ (rat a) (rat b))
      (λ n x _ → expSeq (absᵣ x) (suc (n ℕ.· 2))) (λ n x _ → sinSeries n x)
     (λ n x x∈ →
       ≡ᵣWeaken≤ᵣ _ _
         (absᵣ∘-1ⁿ· _ _ ∙ absᵣ∘expSeq≡expSeq∘absᵣ _ _))
     (IsUConvSeries'SubSeq (intervalℙ (rat a) (rat b))
       (λ n x _ → expSeq (absᵣ x) n)
       (λ n → (suc (n ℕ.· 2)) ,
           subst (ℕ._≤ (suc (n ℕ.· 2))) (·-identityʳ n)
            (ℕ.≤-suc (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1}))))
        (λ k → ℕ.suc-≤-suc ℕ.≤-sucℕ)
            (λ n x x∈ → expSeqNonNeg _ (0≤absᵣ x) n) (uConvExpSer<ℚ-absᵣ a b))

cos-conv : ∀ a b → (rat a) <ᵣ (rat b) → 
  IsUConvSeries' (intervalℙ (rat a) (rat b))
    λ n x _ → cosSeries n x
cos-conv a b a<b =
  IsUConvSeries'-fromConvBound
    (intervalℙ (rat a) (rat b))
      (λ n x _ → expSeq (absᵣ x) ((n ℕ.· 2))) (λ n x _ → cosSeries n x)
     (λ n x x∈ →
       ≡ᵣWeaken≤ᵣ _ _
         (absᵣ∘-1ⁿ· _ _ ∙
          absᵣ∘expSeq≡expSeq∘absᵣ _ _))
     (IsUConvSeries'SubSeq (intervalℙ (rat a) (rat b))
       (λ n x _ → expSeq (absᵣ x) n) 
       (λ n → (n ℕ.· 2) ,
           subst (ℕ._≤ (n ℕ.· 2)) (·-identityʳ n)
            ( (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1}))))
       (λ k → ℕ.≤-sucℕ)
            (λ n x x∈ → expSeqNonNeg _ (0≤absᵣ x) n) (uConvExpSer<ℚ-absᵣ a b))



IsUConvSeries'onℚIntervals→IsCauchySequence' :
  (s : ℕ → ℝ → ℝ) → (∀ a b → (rat a) <ᵣ (rat b) →
     IsUConvSeries'
       (intervalℙ (rat a) (rat b)) λ n x∈ _ → s n x∈)
  → ∀ x → ∥ IsCauchySequence' (seqΣ (flip s x)) ∥₁ 
IsUConvSeries'onℚIntervals→IsCauchySequence' s ucs x = do
  (a , b) , _ , (a< , <b) ← ∃rationalApprox x 1
  ∣ isCauchyFSequenceAt (intervalℙ (rat a) (rat b))
     (λ n x _ → (seqΣ (flip s x)) n)
       (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) λ z x₁ _ → s z x₁)
         (ucs a b (isTrans<ᵣ _ _ _ a< <b)))
     x (<ᵣWeaken≤ᵣ _ _ a< , <ᵣWeaken≤ᵣ _ _ <b) ∣₁


sin-ch : ∀ x → ∥ IsCauchySequence' (seqΣ (λ x₁ → sinSeries x₁ x)) ∥₁
sin-ch = IsUConvSeries'onℚIntervals→IsCauchySequence' _ sin-conv

cos-ch : ∀ x → ∥ IsCauchySequence' (seqΣ (λ x₁ → cosSeries x₁ x)) ∥₁
cos-ch = IsUConvSeries'onℚIntervals→IsCauchySequence' _ cos-conv

sin cos : ℝ → ℝ
sin x = fromCauchySequence'₁ (seqΣ (flip sinSeries x)) (sin-ch x)                
cos x = fromCauchySequence'₁ (seqΣ (flip cosSeries x)) (cos-ch x)

cos0=1 : cos 0 ≡ 1
cos0=1 = fromCauchySequence'₁≡ (seqΣ (λ x → cosSeries x 0))
  (cos-ch 0) 1
   λ ε → ∣ 0 ,
    (λ { zero <0 → ⊥.rec (ℕ.¬-<-zero <0)
       ; (suc n) _ → isTrans≡<ᵣ _ _ _
               (cong absᵣ (𝐑'.+InvR' _ _
                ( seqSumUpTo≡seqSumUpTo' (λ x → cosSeries x 0) (suc n)
                 ∙ 𝐑'.+IdR' _ _
                  (seqΣ'0≡0 _ _
                    λ n →
                      -1ⁿ·≡· _ _ ∙
                       cong₂ _·ᵣ_ refl (sym (expSeq'≡expSeq _ _))
                       ∙ 𝐑'.0RightAnnihilates' _ _
                        (𝐑'.0LeftAnnihilates' _ _
                         (0^ⁿ (suc (n ℕ.· 2)))))))
                ∙ absᵣ0)
               (snd (ℚ₊→ℝ₊ ε))
       }) ∣₁

sin0=0 : sin 0 ≡ 0
sin0=0 = fromCauchySequence'₁≡ (seqΣ (λ x → sinSeries x 0))
  (sin-ch 0) 0
   λ ε → ∣ 0 ,
     (λ n _ →
       isTrans≡<ᵣ _ _ _
               (cong absᵣ (𝐑'.+InvR' _ _
                ( seqSumUpTo≡seqSumUpTo' (λ x → sinSeries x 0) n
                 ∙ (seqΣ'0≡0 _ _
                    λ n →
                      -1ⁿ·≡· _ _ ∙
                       cong₂ _·ᵣ_ refl (sym (expSeq'≡expSeq _ _))
                       ∙ 𝐑'.0RightAnnihilates' _ _
                        (𝐑'.0LeftAnnihilates' _ _
                         (0^ⁿ (n ℕ.· 2))))))
                ∙ absᵣ0)
               (snd (ℚ₊→ℝ₊ ε))) ∣₁


sin-odd : ∀ x → -ᵣ (sin x) ≡ sin (-ᵣ x)
sin-odd x =
  snd (map-fromCauchySequence'₁ _ _ _ (-ᵣ_) -ᵣ-lip)
   ∙
   fromCauchySequence'₁-≡ _ _ _ _
        λ n →
          (-ᵣ_ ∘ seqΣ (λ x₁ → sinSeries x₁ x)) n
            ≡⟨ -seqΣ' (λ x₁ → sinSeries x₁ x) n ⟩ 
          (seqΣ (λ x₁ → -ᵣ (sinSeries x₁ x))) n ≡⟨
            
           cong seqΣ (funExt
             (λ k →  
                 cong (-ᵣ_) (cong (-1ⁿ· k)
                     ((sym (expSeq'≡expSeq x (suc (k ℕ.· 2)))))
                      ∙ -1ⁿ·≡· _ _ )
               ∙ sym (·-ᵣ _ _) 
               ∙ sym (-1ⁿ·≡· _ _)               
               ∙ cong (-1ⁿ· k) (
                   (sym (-ᵣ· _ _))
                 ∙ cong₂ _·ᵣ_ (^ⁿ-odd k x) refl
                 ∙ expSeq'≡expSeq (-ᵣ x) (suc (k ℕ.· 2)))
              ))
             ≡$ n
             ⟩
           seqΣ (λ x₁ → sinSeries x₁ (-ᵣ x)) n ∎

cos-even : ∀ x → cos x ≡ cos (-ᵣ x)
cos-even x = fromCauchySequence'₁-≡ _ _ _ _
        (cong seqΣ (funExt
         (λ k → cong (-1ⁿ· k)
          (sym (expSeq'≡expSeq x (k ℕ.· 2)) ∙∙
           cong₂ _·ᵣ_
            ( ^ⁿ-even k x)
            refl
           ∙∙ expSeq'≡expSeq (-ᵣ x) (k ℕ.· 2))))
         ≡$_)


IsUContFSequenceSin :  ∀ a b → (a<b : rat a <ᵣ rat b) →
   IsUContFSequence (intervalℙ (rat a) (rat b))
      (λ z x _ → seqΣ (λ x₁ → sinSeries x₁ x) z)
IsUContFSequenceSin a b a<b =
  IsUContFSequenceΣSeq _ _
   (subst (IsUContFSequence (intervalℙ (rat a) (rat b)))
     (funExt₃ λ _ _ _ → ·ᵣComm _ _ ∙ sym (-1ⁿ·≡· _ _))
     λ n → IsUContinuousℙC·ᵣ _ (-1ⁿ n) _
      (isUContFSequenceExpSer a b (<ᵣWeaken≤ᵣ _ _ a<b) (suc (n ℕ.· 2))))

IsUContFSequenceCos :  ∀ a b → (a<b : rat a <ᵣ rat b) →
   IsUContFSequence (intervalℙ (rat a) (rat b))
      (λ z x _ → seqΣ (λ x₁ → cosSeries x₁ x) z)
IsUContFSequenceCos a b a<b =
  IsUContFSequenceΣSeq _ _
   (subst (IsUContFSequence (intervalℙ (rat a) (rat b)))
     (funExt₃ λ _ _ _ → ·ᵣComm _ _ ∙ sym (-1ⁿ·≡· _ _))
     λ n → IsUContinuousℙC·ᵣ _ (-1ⁿ n) _
      (isUContFSequenceExpSer a b (<ᵣWeaken≤ᵣ _ _ a<b) (n ℕ.· 2)))

sin'=cos-uder : ∀ a b → (a<b : rat a <ᵣ rat b) →
      uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,
       (λ x _ → sin x) is (λ x _ → cos x)
sin'=cos-uder a b a<b =
   subst2 (uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,_is_)
    (funExt₂ λ _ _ →
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _))
    (funExt₂ λ _ _ →
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _))
    (uCauchyDer (rat a) (rat b) a<b
         (λ z x _ → seqΣ (flip cosSeries x) z)
         (λ z x _ → seqΣ (flip sinSeries x) z)
         uconvcos uccos ucsin uconvsin
        (sinSeq'=cosSeq a b a<b))

    where
    ucsin : IsUContFSequence (intervalℙ (rat a) (rat b)) _
    ucsin = IsUContFSequenceSin a b a<b


    uconvcos : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    uconvcos = 
      Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (cos-conv a b a<b)

    uconvsin : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    uconvsin =
      Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (sin-conv a b a<b)


    uccos : IsUContFSequence (intervalℙ (rat a) (rat b)) _
    uccos = IsUContFSequenceCos a b a<b


cos'=-sin-uder : ∀ a b → (a<b : rat a <ᵣ rat b) →
      uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,
                (λ x _ → cos x)
              is (λ x _ → -ᵣ (sin x))
cos'=-sin-uder a b a<b =
  subst2 (uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,_is_)
    (funExt₂ λ x x∈ →
      
        sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _
          uconvcos
          _
          (PT.map (fst ∘ (cauchySequenceFaster
            (seqΣ λ n → cosSeries n x)
            λ n → (suc n) , (ℕ.≤-sucℕ {n})))
           (cos-ch x)))
        ∙
        sym (fromCauchySequence'₁-∘+  _ 1 _ _)
      )
    (funExt₂ λ x x∈ →
       sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)
       ∙ 
       sym (snd (map-fromCauchySequence'₁
      1 (λ n → seqΣ (flip sinSeries x) n)
       (sin-ch x)
        _ -ᵣ-lip)))
      
    (uCauchyDer (rat a) (rat b) a<b _ _
         (isUCauchyFSequence-ᵣ _ _ uconvsin)
         (λ n →
           subst (IsUContinuousℙ (intervalℙ (rat a) (rat b)))
              (funExt₂ λ _ _ → ·ᵣComm _ _ ∙ sym (-ᵣ≡[-1·ᵣ] _))
            (IsUContinuousℙC·ᵣ (intervalℙ (rat a) (rat b)) -1
            _ (IsUContFSequenceSin a b a<b n)) )
         (IsUContFSequenceCos a b a<b ∘ suc)
         uconvcos
        (cosSeq'=-sinSeq a b a<b))

    where
    ucsin : IsUContFSequence (intervalℙ (rat a) (rat b)) _
    ucsin = IsUContFSequenceSin a b a<b


    uconvcos : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    uconvcos = map-snd
      (λ X x x∈ m n <n <m →
        X x x∈ (suc m) (suc n) (ℕ.≤-suc <n) (ℕ.≤-suc <m))
      ∘ (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (cos-conv a b a<b))

    uconvsin : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    uconvsin =
      Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (sin-conv a b a<b)


cos'=-sin-uder' : ∀ a b → (a<b : a <ᵣ b) →
      uDerivativeOfℙ (intervalℙ a b) ,
                (λ x _ → cos x)
              is (λ x _ → -ᵣ (sin x))
cos'=-sin-uder' a b a<b =
  PT.rec2
     (isPropΠ λ _ → squash₁)
     (λ (a' , _ , a'<a) (b' , b<b' , _) →
       uDerivativeOfℙ-restr (intervalℙ (rat a') (rat b'))
         (intervalℙ a b) _ _
         (λ x x∈ → isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ a'<a) (fst x∈) ,
                   isTrans≤ᵣ _ _ _ (snd x∈) (<ᵣWeaken≤ᵣ _ _ b<b'))
         (cos'=-sin-uder a' b' (isTrans<ᵣ _ _ _ a'<a
           (isTrans<ᵣ _ _ _ a<b b<b')))
         
           )
   (denseℚinℝ (a +ᵣ (rat -1)) a (isTrans<≡ᵣ _ _ _
        
        (<ᵣ-o+ _ _ a (decℚ<ᵣ? { -1 } {0}))
        (+IdR a)))
   (denseℚinℝ b (b +ᵣ 1) (isTrans≡<ᵣ _ _ _
        (sym (+IdR b))
        (<ᵣ-o+ _ _ b (decℚ<ᵣ? {0} {1}))) )

sin'=cos-uder' : ∀ a b → (a<b : a <ᵣ b) →
      uDerivativeOfℙ (intervalℙ (a) (b)) ,
       (λ x _ → sin x) is (λ x _ → cos x)
sin'=cos-uder' a b a<b =
  PT.rec (isPropΠ λ _ → squash₁)
    (λ ((a' , b') , (a'≤a , b≤b')) →
      uDerivativeOfℙ-restr
        (intervalℙ (rat a') (rat b'))
        (intervalℙ a b)
        (λ x _ → sin x)
        (λ r _ → cos r)
       (λ x x∈ →
          (isTrans≤ᵣ _ _ _ a'≤a (fst x∈))
         , (isTrans≤ᵣ _ _ _ (snd x∈) b≤b' ))
       (sin'=cos-uder a' b'
         ((isTrans≤<ᵣ _ _ _ a'≤a
           (isTrans<≤ᵣ _ _ _ a<b b≤b')))))
   (∃enclosingℚInterval a b)

sinSeq≤expSeq : ∀ n x → seqΣ (flip sinSeries x) n ≤ᵣ
                             seqΣ (expSeq (absᵣ x)) (suc (n ℕ.· 2))
sinSeq≤expSeq n x = isTrans≤ᵣ _ _ _
  (sinSeq≤expSeq-1 n x)
  (isTrans≤≡ᵣ _ _ _
    (isTrans≡≤ᵣ _ _ _
      (sym (+IdL _))
      (≤ᵣ-+o _ _ _ (decℚ≤ᵣ? {0} {1}) )) --(≤ᵣMonotone+ᵣ _ _ _ _ ? ?)
    (1+expSeq (n ℕ.· 2) (absᵣ x) ))

sin≤exp : ∀ x → sin x ≤ᵣ expℝ (absᵣ x)
sin≤exp x =
  PT.elim2
    (λ ich ich' →
       isProp≤ᵣ
        (fromCauchySequence'₁ _ ich)
        (fromCauchySequence'₁ (seqΣ (expSeq (absᵣ x))) ich'))
    (λ ich ich' →
      isTrans≤≡ᵣ _ _ _
        (fromCauchySequence'≤ _ _ _ _
          (flip sinSeq≤expSeq x))
        (sym (snd (cauchySequenceFaster (seqΣ (expSeq (absᵣ x)))
          (λ n → suc (n ℕ.· 2) ,
           subst (ℕ._≤ suc (n ℕ.· 2)) (·-identityʳ n)
            (ℕ.≤-suc (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1})))) ich'))))
    (sin-ch x)
    (expℝ-cauchySeq (absᵣ x)) 

cos≤exp : ∀ x → cos x ≤ᵣ expℝ (absᵣ x)
cos≤exp x =
   PT.elim2
    (λ ich ich' →
       isProp≤ᵣ
        (fromCauchySequence'₁ _ ich)
        (fromCauchySequence'₁ (seqΣ (expSeq (absᵣ x))) ich'))
    (λ ich ich' →
      isTrans≤≡ᵣ _ _ _
        (fromCauchySequence'≤ _ _ _ _
          (flip cosSeq≤expSeq x))
        (sym (snd (cauchySequenceFaster (seqΣ (expSeq (absᵣ x)))
          (λ n → (n ℕ.· 2) ,
           subst (ℕ._≤ (n ℕ.· 2)) (·-identityʳ n)
            ( (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1})))) ich'))))
    (cos-ch x)
    (expℝ-cauchySeq (absᵣ x)) 


-cos≤exp : ∀ x → -ᵣ (cos x) ≤ᵣ expℝ (absᵣ x)
-cos≤exp x =
   isTrans≡≤ᵣ _ _ _
    (snd (map-fromCauchySequence'₁
      1 _ _
        _ -ᵣ-lip))
    (PT.elim2
    (λ ich ich' →
       isProp≤ᵣ
        (fromCauchySequence'₁ _ ich)
        (fromCauchySequence'₁ (seqΣ (expSeq (absᵣ x))) ich'))
    (λ ich ich' →
      isTrans≤≡ᵣ _ _ _
        (fromCauchySequence'≤ _ _ _ _
          (flip -cosSeq≤expSeq x))
        (sym (snd (cauchySequenceFaster (seqΣ (expSeq (absᵣ x)))
          (λ n → (n ℕ.· 2) ,
           subst (ℕ._≤ (n ℕ.· 2)) (·-identityʳ n)
            ( (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1})))) ich'))))
    (fst (map-fromCauchySequence'₁
      1 _ _
        _ -ᵣ-lip))
    (expℝ-cauchySeq (absᵣ x)))



pre-bounded-sin : ∀ a b → rat a <ᵣ rat b → 
             Bounded (intervalℙ (rat a) (rat b)) (λ x _ → sin x)
pre-bounded-sin a b a<b =
  let (bd , ≤bd) = expBounded 0 (ℚ.max (ℚ.abs a) (ℚ.abs b))
                    (≤ᵣ-refl _)
                    (≤ℚ→≤ᵣ _ _
                      (ℚ.isTrans≤ _ _ _ (ℚ.0≤abs a) (ℚ.≤max _ _)))
  in bd , λ x x∈ → isTrans≤ᵣ _ _ _
           (isTrans≤ᵣ _ _ _
             (isTrans≡≤ᵣ _ _ _ (abs-max (sin x))
               (max≤-lem _ _ _
                 (sin≤exp x)
                 (subst2 _≤ᵣ_
                   (sym (sin-odd x))
                   (cong expℝ (sym (-absᵣ x)))
                   (sin≤exp (-ᵣ x)))))
             (≤absᵣ _))
          (≤bd (absᵣ x) (0≤absᵣ x ,
            isTrans≤≡ᵣ _ _ _
              (x∈interval-bound _ _ x x∈)
              (cong₂ maxᵣ (absᵣ-rat a) (absᵣ-rat b))))


pre-bounded-cos : ∀ a b → rat a <ᵣ rat b → 
             Bounded (intervalℙ (rat a) (rat b)) (λ x _ → cos x)
pre-bounded-cos a b a<b =
  let (bd , ≤bd) = expBounded 0 (ℚ.max (ℚ.abs a) (ℚ.abs b))
                    (≤ᵣ-refl _)
                    (≤ℚ→≤ᵣ _ _
                      (ℚ.isTrans≤ _ _ _ (ℚ.0≤abs a) (ℚ.≤max _ _)))
  in bd , λ x x∈ → isTrans≤ᵣ _ _ _
           (isTrans≤ᵣ _ _ _
             (isTrans≡≤ᵣ _ _ _ (abs-max (cos x))                
               (max≤-lem _ _ _
                 (cos≤exp x)
                 (-cos≤exp x)))
             (≤absᵣ _))
           
          (≤bd (absᵣ x) (0≤absᵣ x ,
            isTrans≤≡ᵣ _ _ _
              (x∈interval-bound _ _ x x∈)
              (cong₂ maxᵣ (absᵣ-rat a) (absᵣ-rat b))))

pre-uContSin : ∀ a b → rat a <ᵣ rat b →
  IsUContinuousℙ (intervalℙ (rat a) (rat b)) (λ x₁ _ → sin x₁)
pre-uContSin a b a<b =
 subst (IsUContinuousℙ (intervalℙ (rat a) (rat b)))
   ((funExt₂ λ _ _ →
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)))
   (snd (fromUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (sin-conv a b a<b))
    (IsUContFSequenceSin a b a<b)))


pre-uContCos : ∀ a b → rat a <ᵣ rat b →
  IsUContinuousℙ (intervalℙ (rat a) (rat b)) (λ x₁ _ → cos x₁)
pre-uContCos a b a<b =
 subst (IsUContinuousℙ (intervalℙ (rat a) (rat b)))
   ((funExt₂ λ _ _ →
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)))
   (snd (fromUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (cos-conv a b a<b))
    (IsUContFSequenceCos a b a<b)))

IsUContinuousℙ→IsContinuous : ∀ f →
 (∀ a b → rat a <ᵣ rat b →
  IsUContinuousℙ (intervalℙ (rat a) (rat b)) (λ x _ → f x)) 
       → IsContinuous f
IsUContinuousℙ→IsContinuous f ucf x ε = do
  (a , b) , _ , (a< , <b) ← ∃rationalApprox x 1
  let x∈ = (isTrans<ᵣ _ _ _
             (isTrans<≡ᵣ _  _ _ (<ℚ→<ᵣ _ _
               ((ℚ.<-o+ _ _ a (ℚ.decℚ<? { -1 } {0}))))
              (cong rat (ℚ.+IdR a))) a<) ,
             (isTrans<ᵣ _ _ _ <b
              (isTrans≡<ᵣ _  _ _ (cong rat (sym (ℚ.+IdR b)))
                (<ℚ→<ᵣ _ _  (ℚ.<-o+ _ _ b (ℚ.decℚ<? {0} {1})))))

      (δ , X) = ucf (a ℚ.- 1) (b ℚ.+ 1)
            (isTrans<ᵣ _ _ _ (fst x∈) (snd x∈)) ε  
  ∣ ℚ.min₊ δ 1 , (λ y x∼y →
    let zz = fst (∼≃abs<ε _ _ _) x∼y
    in X x y
       (ointervalℙ⊆intervalℙ (rat (a ℚ.- 1)) (rat (b ℚ.+ 1)) x x∈)
        (isTrans≤ᵣ _ _ _
          (isTrans≡≤ᵣ _ _ _
           (sym (+ᵣ-rat _ _))
           (≤ᵣMonotone+ᵣ _ _ _ _
             (<ᵣWeaken≤ᵣ _ _ a<)
             (isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat 1))
              (-ᵣ≤ᵣ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) 1))))))
          (<ᵣWeaken≤ᵣ _ _ (a-b<c⇒a-c<b _ _ _
           (isTrans≤<ᵣ _ _ _ (≤absᵣ _) zz)))
       , isTrans≤ᵣ _ _ _ (isTrans≤≡ᵣ _ _ _
        (a-b≤c⇒a≤c+b _ _ _
        (isTrans≤ᵣ _ _ _ (≤absᵣ _)
         (isTrans≡≤ᵣ _ _ _ (minusComm-absᵣ _ _) (<ᵣWeaken≤ᵣ _ _ zz))))
         (+ᵣComm _ _))
           (isTrans≤≡ᵣ _ _ _
             (≤ᵣMonotone+ᵣ _ _ _ _
              (<ᵣWeaken≤ᵣ _ _ <b)
              (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) 1)))
             (+ᵣ-rat _ _)))
       (∼-monotone≤ (ℚ.min≤ _ _) x∼y)) ∣₁

isContinuousSin : IsContinuous sin
isContinuousSin = IsUContinuousℙ→IsContinuous _ pre-uContSin

isContinuousCos : IsContinuous cos
isContinuousCos = IsUContinuousℙ→IsContinuous _ pre-uContCos


sin²+cos²=1 : ∀ x → ((sin x) ^ⁿ 2) +ᵣ ((cos x) ^ⁿ 2) ≡ 1 
sin²+cos²=1 = ≡Continuous _ _
  (cont₂+ᵣ  _ _
    (IsContinuous∘ _ _ (IsContinuous^ⁿ 2) isContinuousSin)
    (IsContinuous∘ _ _ (IsContinuous^ⁿ 2) isContinuousCos))
   (IsContinuousConst 1)
  ((_∙ sin0²+cos0²≡1) ∘ ℚ.byTrichotomy 0 h)

  where

  h' : ∀ a b → rat a <ᵣ rat b →
    (sin (rat a) ^ⁿ 2) +ᵣ (cos (rat a) ^ⁿ 2)
      ≡ (sin (rat b) ^ⁿ 2) +ᵣ (cos (rat b) ^ⁿ 2)
  h' a b a<b =
    nullDerivative→const (rat a) (rat b)
       (≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ a<b)
       (<ᵣWeaken≤ᵣ _ _ a<b , ≤ᵣ-refl _)
      a<b
      _
      h

    where
    h : uDerivativeOfℙ intervalℙ (rat a) (rat b) ,
          (λ x _ → ((sin x) ^ⁿ 2) +ᵣ ((cos x) ^ⁿ 2)) is
        (λ _ _ → rat [ pos 0 / 1+ 0 ])
    h = subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
      (funExt₂ λ _ _ →
        cong₂ _+ᵣ_
          (cong₂ _·ᵣ_ (sym (·IdL _)) refl)
          (cong₂ _·ᵣ_ (sym (·IdL _)) refl))
      (funExt₂ λ _ _ →
        cong₂ _+ᵣ_ (cong₂ _+ᵣ_ (·ᵣComm _ _) (·ᵣComm _ _))
           (cong₂ _+ᵣ_ (-ᵣ· _ _) (-ᵣ· _ _)
             ∙ sym (-ᵣDistr _ _))
          ∙ 𝐑'.+InvR' _ _ refl)
      (+uDerivativeℙ _ _ _ _ _
        h1 h2)

       where
       h1 = (uDerivativeOfℙ· (rat a) (rat b) a<b
          _ _ _ _
          (pre-bounded-sin a b a<b)
          (pre-bounded-sin a b a<b)
          (pre-uContSin a b a<b)
          (pre-bounded-cos a b a<b)
        (sin'=cos-uder a b a<b)
        (sin'=cos-uder a b a<b)
        )
       h2 = (uDerivativeOfℙ· (rat a) (rat b) a<b
          _ _ _ _
          (pre-bounded-cos a b a<b) (pre-bounded-cos a b a<b)
          (pre-uContCos a b a<b)
          (map-snd (λ X x x∈ → isTrans≡≤ᵣ _ _ _
               (sym (-absᵣ _)) (X x x∈)) (pre-bounded-sin a b a<b))
        (cos'=-sin-uder a b a<b) (cos'=-sin-uder a b a<b))

  sin0²+cos0²≡1 : (sin 0 ^ⁿ 2) +ᵣ (cos 0 ^ⁿ 2) ≡ 1
  sin0²+cos0²≡1 = 𝐑'.+IdL' _ _ (cong (_^ⁿ 2) sin0=0 ∙ (0^ⁿ 1))
    ∙ cong (_^ⁿ 2) cos0=1 ∙ 1^ⁿ 2
  
  h : ℚ.TrichotomyRec 0
       (λ z → (sin (rat z) ^ⁿ 2) +ᵣ (cos (rat z) ^ⁿ 2) ≡
        (sin 0 ^ⁿ 2) +ᵣ (cos 0 ^ⁿ 2))
  h .ℚ.TrichotomyRec.lt-case x x<0 =
    h' x 0 (<ℚ→<ᵣ _ _ x<0)
  h .ℚ.TrichotomyRec.eq-case = refl 
  h .ℚ.TrichotomyRec.gt-case x 0<x =
    sym (h' 0 x (<ℚ→<ᵣ _ _ 0<x)) 
