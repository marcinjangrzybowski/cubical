{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.ExponentiationMore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos; ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

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
open import Cubical.HITs.CauchyReals.Bisect
open import Cubical.HITs.CauchyReals.BisectApprox
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Derivative

open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationDer

import Cubical.Algebra.CommRing.Instances.Int as ℤCRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties 
import Cubical.Algebra.CommRing as CR


intervalℙ→dist< : ∀ a b x y → x ∈ intervalℙ a b → y ∈ intervalℙ a b
                   → absᵣ (x -ᵣ y) ≤ᵣ b -ᵣ a
intervalℙ→dist< a b x y (a≤x , x≤b) (a≤y , y≤b) =
  isTrans≡≤ᵣ _ _ _ (abs-max _ ∙ cong (maxᵣ _) (-[x-y]≡y-x _ _) )
    (max≤-lem _ _ _ (≤ᵣMonotone+ᵣ _ _ _ _ x≤b (-ᵣ≤ᵣ _ _ a≤y))
                    ((≤ᵣMonotone+ᵣ _ _ _ _ y≤b (-ᵣ≤ᵣ _ _ a≤x))))

clampDistᵣ' : ∀ L L' x y →
    absᵣ (clampᵣ (rat L) (rat L') y -ᵣ clampᵣ (rat L) (rat L') x) ≤ᵣ absᵣ (y -ᵣ x)
clampDistᵣ' L L' = ≤Cont₂
          (cont∘₂ IsContinuousAbsᵣ
            (contNE₂∘ sumR ((λ _ → IsContinuousClamp (rat L) (rat L')) , λ _ → IsContinuousConst _)
              ((λ _ → IsContinuousConst _) , λ _ → IsContinuous∘ _ _ IsContinuous-ᵣ (IsContinuousClamp (rat L) (rat L')))))
          (cont∘₂ IsContinuousAbsᵣ
             (contNE₂∘ sumR ((λ _ → IsContinuousId) , λ _ → IsContinuousConst _)
              ((λ _ → IsContinuousConst _) , λ _ → IsContinuous-ᵣ )))
          λ u u' →
             subst2 _≤ᵣ_ (cong rat (ℚ.abs'≡abs _)) (cong rat (ℚ.abs'≡abs _))
               (≤ℚ→≤ᵣ _ _ (ℚ.clampDist L L' u u'))



ℚ1≤x⊔1/x : ∀ x → 1 ℚ.≤ ℚ.max (fst x) (fst (invℚ₊ x))
ℚ1≤x⊔1/x x = 
  ⊎.rec
     (λ 1≤x →
       ℚ.isTrans≤ _ _ _ 1≤x (ℚ.≤max (fst x) (fst (invℚ₊ x))) )
     (λ x<1 →
       ℚ.isTrans≤ _ _ _ (ℚ.invℚ≤invℚ 1 _
         (ℚ.<Weaken≤ _ _ x<1))
         (ℚ.≤max' (fst x) (fst (invℚ₊ x))))
   (ℚ.Dichotomyℚ 1 (fst x))



1≤x⊔1/x : ∀ x → 1 ≤ᵣ maxᵣ (fst x) (fst (invℝ₊ x))
1≤x⊔1/x = 
  uncurry (<→≤ContPos'pred {0}
    (AsContinuousWithPred _ _
      (IsContinuousConst _))
       (contDiagNE₂WP maxR _ _ _
         (AsContinuousWithPred _ _
           IsContinuousId) (snd invℝ'))
             λ u 0<u →
               subst (1 ≤ᵣ_) (cong (maxᵣ (rat u))
                 (sym (invℝ'-rat _ _ _)))
                 (≤ℚ→≤ᵣ _ _ (
                  (ℚ1≤x⊔1/x (u , ℚ.<→0< u (<ᵣ→<ℚ _ _ 0<u))))))


0<pos[sucN]² : ∀ n → 0 ℤ.< (ℤ.pos (suc n)) ℤ.· (ℤ.pos (suc n))
0<pos[sucN]² n = ℤ.<-·o {0} {ℤ.pos (suc n)} {n} (ℤ.suc-≤-suc ℤ.zero-≤pos)

0<x² : ∀ n → ¬ (n ≡ 0) → 0 ℤ.< n ℤ.· n
0<x² (pos zero) x = ⊥.elim (x refl)
0<x² (pos (suc n)) _ = 0<pos[sucN]² n
0<x² (ℤ.negsuc n) _ = subst (0 ℤ.<_) (sym (ℤ.negsuc·negsuc n n))
  (0<pos[sucN]² n)

mn<m²+n² : (a b : ℕ) → pos (suc a) ℤ.· pos (suc b) ℤ.<
                    (pos (suc a) ℤ.· pos (suc a))
                      ℤ.+ (pos (suc b) ℤ.· pos (suc b))
mn<m²+n² a b =
  ℤ.<-+pos-trans {k = a ℕ.· suc b} h'
 where
 a' = pos (suc a)
 b' = pos (suc b)
 h : ((a' ℤ.· b') ℤ.+ (a' ℤ.· b')) ℤ.≤
         (a' ℤ.· a' ℤ.+ b' ℤ.· b')
 h = subst2 (ℤ._≤_)
       (𝐙'.+IdL' _ _ refl)
       (cong (ℤ._+ ((a' ℤ.· b') ℤ.+ (a' ℤ.· b'))) (L𝐙.lem--073 {a'} {b'})
        ∙ 𝐙'.minusPlus _ _)
       (ℤ.≤-+o {o = ((a' ℤ.· b') ℤ.+ (a' ℤ.· b'))} (ℤ.0≤x² (a' ℤ.- b')))

 h' = ℤ.<≤-trans (ℤ.<-o+ (subst (ℤ._< a' ℤ.· b')
     (sym (ℤ.pos·pos _ _)) (ℤ.<-·o {k = b}
       ℤ.isRefl≤))) h 


ℚ1<x+1/x : ∀ x → 1 ℚ.< fst x ℚ.+ fst (invℚ₊ x) 
ℚ1<x+1/x = uncurry (SQ.ElimProp.go w)
 where
 w : ElimProp (λ z → (y : 0< z) → 1 ℚ.< z ℚ.+ fst (invℚ₊ (z , y)))
 w .ElimProp.isPropB _ = isPropΠ λ _ → ℚ.isProp< _ _
 w .ElimProp.f (pos (suc n) , (1+ m)) y =
    subst2 ℤ._<_
      (sym (ℤ.pos·pos  _ _)) (ℤ.+Comm _ _ ∙ sym (ℤ.·IdR _))
     (mn<m²+n² m n)

1≤x+1/x : ∀ x → 1 ≤ᵣ fst x +ᵣ fst (invℝ₊ x) 
1≤x+1/x =
  uncurry (<→≤ContPos'pred {0}
    (AsContinuousWithPred _ _
      (IsContinuousConst _))
       (contDiagNE₂WP sumR _ _ _
         (AsContinuousWithPred _ _
           IsContinuousId) (snd invℝ'))
             λ u 0<u →
               subst (1 ≤ᵣ_) (cong (rat u +ᵣ_)
                 (sym (invℝ'-rat _ _ _)))
                 (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ 1 _
                  (ℚ1<x+1/x (u , ℚ.<→0< u (<ᵣ→<ℚ _ _ 0<u))))))

pasting : (x₀ : ℝ) → (f< : ∀ x → x ≤ᵣ x₀ → ℝ)
                  → (<f : ∀ x → x₀ ≤ᵣ x → ℝ)
                  → f< x₀ (≤ᵣ-refl x₀) ≡ <f x₀ (≤ᵣ-refl x₀) 
                  → Σ[ f ∈ (ℝ → ℝ) ]
                        (∀ x x≤x₀ → f x ≡ f< x x≤x₀)
                         × (∀ x x₀≤x → f x ≡ <f x x₀≤x)
pasting x₀ f< <f p =
  (λ x → (<f (maxᵣ x₀ x) (≤maxᵣ _ _)
      +ᵣ f< (minᵣ x₀ x) (min≤ᵣ _ _))
       -ᵣ f< x₀ (≤ᵣ-refl x₀))
  , (λ x x≤x₀ → 
      let z = minᵣComm _ _ ∙ ≤→minᵣ _ _ x≤x₀
      in cong₂ _-ᵣ_ (cong₂ _+ᵣ_
             (cong (uncurry <f) (Σ≡Prop (λ _ → isSetℝ _ _)
               (maxᵣComm _ _ ∙ x≤x₀)))
             (cong (uncurry f<) (Σ≡Prop (λ _ → isSetℝ _ _) z)) ) p ∙
          L𝐑.lem--063)
  , λ x x₀≤x →
       𝐑'.plusMinus' _ _ _ (cong (uncurry f<)
        (Σ≡Prop (λ _ → isSetℝ _ _) (≤→minᵣ _ _ x₀≤x))) ∙
        (cong (uncurry <f)
        (Σ≡Prop (λ _ → isSetℝ _ _) x₀≤x))   




pasting≤ : ∀ b x₀ b≤x₀  
                  → (f< : ∀ x → b ≤ᵣ x → x ≤ᵣ x₀ → ℝ)
                  → (<f : ∀ x → x₀ ≤ᵣ x → ℝ)
                  → f< x₀ b≤x₀ (≤ᵣ-refl x₀) ≡ <f x₀ (≤ᵣ-refl x₀) 
                  → Σ[ f ∈ (∀ x → b ≤ᵣ x → ℝ) ]
                        (∀ x b≤x x≤x₀ → f x b≤x ≡ f< x b≤x x≤x₀)
                         × (∀ x b≤x x₀≤x → f x b≤x ≡ <f x x₀≤x)
pasting≤ b x₀ b≤x₀ f< <f p =
  (λ x _ → (fst h) x)
  , (λ x b≤x x≤x₀ → fst (snd h) x x≤x₀ ∙ q b≤x)
  ,  const ∘ snd (snd h)
 where

 q : ∀ {y y' : Σ[ x ∈ ℝ ] (b ≤ᵣ x) × (x ≤ᵣ x₀)}
         → (a : (fst y) ≡ (fst y')) → _ ≡ _
 q {y} {y'} = cong {x = y} {y = y'} (uncurry $ uncurry ∘ f<) ∘
         (Σ≡Prop (λ _ → isProp× (isSetℝ _ _) (isSetℝ _ _)))
         
 h = pasting x₀
       (λ x x≤x₀ → f< (maxᵣ b x) (≤maxᵣ _ _)
         (max≤-lem _ _ _ b≤x₀ x≤x₀))
       <f (q b≤x₀ ∙ p)



slope-lower-bound : (z : ℝ₊) (B : ℚ₊) (1<z : 1 <ᵣ fst z) → (y₀ y₁ : ℚ )
  → (y₀<y₁ : y₀ ℚ.< y₁)
  → (y₀∈ : y₀ ∈ ℚintervalℙ (ℚ.- (fst B)) (fst B))
  → (y₁∈ : y₁ ∈ ℚintervalℙ (ℚ.- (fst B)) (fst B)) →     
  fst (z ^ℚ (ℚ.- fst B)) ·ᵣ
       ((fst z -ᵣ 1) ／ᵣ₊ z)
      <ᵣ
  ((fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  y₀<y₁ ))
slope-lower-bound z B 1<z y₀ y₁ y₀<y₁ (-B≤y₀ , y₀≤B) (-B≤y₁ , y₁≤B) =
  isTrans<≡ᵣ _ _ _
    (≤<ᵣ₊Monotone·ᵣ
      ((z ^ℚ (ℚ.- (fst B)))) (fst (z ^ℚ y₀))
      (_ ,
        isTrans≡≤ᵣ _ _ _ (sym (𝐑'.0LeftAnnihilates _))
           (≤ᵣ-·ᵣo 0 _ _
            (<ᵣWeaken≤ᵣ _ _ (snd (invℝ₊ (fst z , z .snd))))
             (<ᵣWeaken≤ᵣ _ _ (x<y→0<y-x _ _ 1<z))))
              ((fst (z ^ℚ (fst h₊)) -ᵣ 1) ／ᵣ₊ ℚ₊→ℝ₊ h₊)
       
      (^ℚ-MonotoneR {z} (ℚ.- (fst B)) y₀ -B≤y₀ (<ᵣWeaken≤ᵣ _ _ 1<z))
      
       (invEq (z/y'<x/y≃y₊·z<y'₊·x _ _ _ _)
          brn )
       )   
      (·ᵣAssoc _ _ _
       ∙ cong (_·ᵣ
        fst (invℝ₊ (ℚ₊→ℝ₊ h₊)))
         (sym (factor-xᵃ-xᵇ z _ _) ))

 where
  h₊ = ℚ.<→ℚ₊ _ _ y₀<y₁

  brn : fst (ℚ₊→ℝ₊ h₊) ·ᵣ (fst z -ᵣ 1)   <ᵣ
        fst z ·ᵣ (fst (z ^ℚ fst h₊) -ᵣ rat [ pos 1 / 1+ 0 ])
         
  brn = isTrans<≡ᵣ _ _ _ (a+c<b⇒a<b-c _ _ _ (isTrans≡<ᵣ _ _ _ (sym (·DistR+ (fst (ℚ₊→ℝ₊ h₊)) 1 _))
         (a+c<b⇒a<b-c _ _ 1
          (isTrans≡<ᵣ _ _ _
           (+ᵣComm (rat (fst h₊ ℚ.+ [ pos 1 / 1+ 0 ]) ·ᵣ
      (fst z -ᵣ rat [ pos 1 / 1+ 0 ])) 1) (bernoulli's-ineq-^ℚ z (fst h₊ ℚ.+ 1)
            1<z (subst (1 ℚ.<_) (ℚ.+Comm 1 (fst h₊))
             (ℚ.<+ℚ₊' _ _ h₊ (ℚ.isRefl≤ 1))) )))))
            (sym (+ᵣAssoc (fst (z ^ℚ (fst h₊ ℚ.+ 1))) _ _) ∙
             cong₂ _+ᵣ_
               (cong fst (sym (^ℚ-+ z (fst h₊) 1))
                 ∙ ·ᵣComm _ _ ∙
                   cong (_·ᵣ (z ^ℚ fst h₊) .fst) (cong fst (^ℚ-1 _) ))
               ((sym (-ᵣDistr _ _) ∙
                 cong (-ᵣ_) (cong (1 +ᵣ_) (·IdL _)
                  ∙ L𝐑.lem--05 ∙ sym (·IdL _))
                 ) ∙ sym (-ᵣ· _ _) ∙ ·ᵣComm _ _)
              ∙ sym (·DistL+ _ _ _) )


slope-upper-bound : (z : ℝ₊) (B : ℚ₊) (1<z : 1 <ᵣ fst z) → (y₀ y₁ : ℚ )
  → (y₀<y₁ : y₀ ℚ.< y₁)
  → (y₀∈ : y₀ ∈ ℚintervalℙ (ℚ.- (fst B)) (fst B))
  → (y₁∈ : y₁ ∈ ℚintervalℙ (ℚ.- (fst B)) (fst B)) →     
  ((fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  y₀<y₁ ))
     <ᵣ fst (z ^ℚ (fst B)) ·ᵣ (fst z -ᵣ 1)
slope-upper-bound z B 1<z y₀ y₁ y₀<y₁ (-B≤y₀ , y₀≤B) (-B≤y₁ , y₁≤B) =
  isTrans<≡ᵣ _ _ _
    (slope-monotone-strict z 1<z
      y₀ y₁ (fst B) (fst B ℚ.+ 1)
       y₀<y₁ B<B+1 y₀≤B
         (ℚ.isTrans≤< _ _ _ y₁≤B B<B+1))
    (𝐑'.·IdR' _ _ (cong (fst ∘ invℝ₊)
      (ℝ₊≡ (cong rat lem--063)) ∙ cong fst invℝ₊1) ∙
       factor-xᵃ-xᵇ z (fst B ℚ.+ 1) (fst B) ∙
         cong (λ u → fst (z ^ℚ fst B) ·ᵣ (fst u -ᵣ 1))
           (cong (z ^ℚ_) lem--063 ∙ ^ℚ-1 z))
  
 where
  h₊ = ℚ.<→ℚ₊ _ _ y₀<y₁
  B<B+1 = ℚ.<+ℚ₊' _ _ 1 (ℚ.isRefl≤ (fst B))

-- ℚ^-lipsh : {!!}
-- ℚ^-lipsh = {!!}


-- lowBnd-1/ℕ : (ε : ℝ₊) → ∃[ k ∈ ℕ₊₁ ] rat [ 1 / k ] <ᵣ fst ε 
-- lowBnd-1/ℕ = {!!}


-- ceilℚ₊ q = 1+ (fst (fst (floor-fracℚ₊ q))) ,
--    subst2 (_<_) --  (fromNat (suc (fst (fst (floor-fracℚ₊ q)))))
--       (ℚ.+Comm _ _ ∙ fst (snd (floor-fracℚ₊ q)))
--       (ℚ.ℕ+→ℚ+ _ _)
--        (<-+o _ _ (fromNat (fst (fst (floor-fracℚ₊ q))))
--          (snd (snd (snd (floor-fracℚ₊ q)))))



module BDL (z : ℝ₊) (Z : ℕ)
          (z<Z : fst z <ᵣ fromNat (suc (suc Z)))
          (1+1/Z<z : rat (1 ℚ.+ [ 1 / 1+ (suc Z) ]) <ᵣ fst z )where


 monotone^ℚ' : ∀ q q' q'' 
  → q ℚ.≤ q'
  → q' ℚ.≤ q''
  → ∀ u 0<u
  → minᵣ (fst ((rat u , 0<u) ^ℚ q)) (fst ((rat u , 0<u) ^ℚ q'')) ≤ᵣ
    fst ((rat u , 0<u) ^ℚ q')
 monotone^ℚ' q q' q'' q≤q' q'≤q'' u 0<u =
  ⊎.rec
    (λ 1≤u →
      isTrans≤ᵣ _ _ _ (min≤ᵣ (fst ((rat u , 0<u) ^ℚ q))
             (fst ((rat u , 0<u) ^ℚ q'')))
         (^ℚ-MonotoneR {(rat u , 0<u)} q q'
            q≤q'
         (≤ℚ→≤ᵣ _ _ 1≤u)))
    (λ u<1 → isTrans≤ᵣ _ _ _
      (min≤ᵣ' (fst ((rat u , 0<u) ^ℚ q))
             (fst ((rat u , 0<u) ^ℚ q'')))
        let xx = (^ℚ-MonotoneR {invℝ₊ (rat u , 0<u)}
                _ _  (ℚ.minus-≤ _ _ q'≤q'')
                    (isTrans≤≡ᵣ _ _ _
                     (invEq (z≤x/y₊≃y₊·z≤x 1 1 (rat u , 0<u))
                       (isTrans≡≤ᵣ _ _ _ (·IdR _)
                         (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ u<1))))
                     (·IdL _)))
        in subst2 _≤ᵣ_
             (cong fst (sym (^ℚ-minus _ _)))
             (cong fst (sym (^ℚ-minus _ _)))
             xx)
    (ℚ.Dichotomyℚ 1 u)


 monotone^ℚ : ∀ q q' q'' 
  → q ℚ.≤ q'
  → q' ℚ.≤ q''
  → ∀ z 
  → minᵣ (fst (z ^ℚ q)) (fst (z ^ℚ q'')) ≤ᵣ fst (z ^ℚ q')
 monotone^ℚ q q' q'' q≤q' q'≤q'' =
   uncurry (<→≤ContPos'pred {0}
     (contDiagNE₂WP minR _ _ _
       (IsContinuous^ℚ q)
       (IsContinuous^ℚ q''))
     (IsContinuous^ℚ q')
     λ u 0<u → monotone^ℚ' q q' q'' q≤q' q'≤q'' u 0<u)


 slUpBd : ℕ → ℚ₊
 slUpBd m = (fromNat (suc (suc Z)) ℚ₊^ⁿ (suc m)) ℚ₊· fromNat (suc Z)  

 slUpBdInv : ℕ → ℚ₊
 slUpBdInv m = (fromNat (suc (suc Z))) ℚ₊^ⁿ (suc (suc (suc m)))
     -- ℚ₊· ((invℚ₊ (fromNat (suc (suc Z)))) ℚ₊· invℚ₊ (fromNat (suc (suc Z))))  
-- ((fst z -ᵣ 1) ／ᵣ₊ z)

 slpBdIneq : ∀ n → fst (invℚ₊ (slUpBdInv n)) ℚ.≤
    fst (slUpBd n)
 slpBdIneq n = ℚ.isTrans≤ _ 1 _
   (fst (ℚ.invℚ₊-≤-invℚ₊ 1 _)
     (ℚ.1≤x^ⁿ (fromNat (suc (suc Z)))
          (suc (suc (suc n)))
          (ℚ.≤ℤ→≤ℚ 1 (pos (suc (suc Z)))
            (ℤ.suc-≤-suc {0} {pos (suc Z)}
             (ℤ.zero-≤pos {suc Z})))))
   (ℚ.≤Monotone·-onNonNeg 1 _ 1 _
    ((ℚ.1≤x^ⁿ (fromNat (suc (suc Z)))
          ((suc n))
          (ℚ.≤ℤ→≤ℚ 1 (pos (suc (suc Z)))
            (ℤ.suc-≤-suc {0} {pos (suc Z)}
             (ℤ.zero-≤pos {suc Z})))))
    ((ℚ.≤ℤ→≤ℚ 1 (pos (suc Z))
            (ℤ.suc-≤-suc {0} {pos Z}
             (ℤ.zero-≤pos {Z}))))
    (ℚ.decℚ≤? {0} {1})
    (ℚ.decℚ≤? {0} {1}))
 
 1<z : 1 <ᵣ (fst z)
 1<z = isTrans<ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' _ _ _ (ℚ.isRefl≤ 1))) 1+1/Z<z

 bdl : boundedLipschitz (fst ∘ z ^ℚ_) slUpBd
 bdl n = ℚ.elimBy≡⊎<
  (λ x y X y∈ x∈ → subst2 _≤ᵣ_
       (minusComm-absᵣ _ _)
       (cong (rat ∘ (fst (slUpBd n) ℚ.·_)) (ℚ.absComm- _ _))
       (X x∈ y∈)  )
  (λ x _ _ → subst2 _≤ᵣ_
     (cong absᵣ (sym (+-ᵣ _)))
     (cong rat (sym (𝐐'.0RightAnnihilates' _ _ (cong ℚ.abs (ℚ.+InvR x)))))
     (≤ᵣ-refl 0))
  λ y₀ y₁ y₀<y₁ y₀∈ y₁∈ →
   isTrans≡≤ᵣ _ _ _ (absᵣNonNeg _ (x≤y→0≤y-x _ _
         (^ℚ-MonotoneR _ _ (ℚ.<Weaken≤ _ _ y₀<y₁) (<ᵣWeaken≤ᵣ _ _ 1<z) )))
     (isTrans≤≡ᵣ _ _ _ (isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _
    (fst (z/y<x₊≃z<y₊·x _ _ _) (slope-upper-bound z (fromNat (suc n))
    1<z y₀ y₁ y₀<y₁
     (ℚ.absTo≤×≤ (fromNat (suc n)) y₀ y₀∈)
     (ℚ.absTo≤×≤ (fromNat (suc n)) y₁ y₁∈))))
      (≤ᵣ-o· _ _ _ (ℚ.<Weaken≤ 0 _ (ℚ.-< _ _ y₀<y₁))
       (≤ᵣ₊Monotone·ᵣ _ _ _ _
         (<ᵣWeaken≤ᵣ _ _ $ snd (fromNat (suc (suc Z)) ^ℚ fst (fromNat (suc n))))
         (x≤y→0≤y-x _ _ (<ᵣWeaken≤ᵣ _ _ 1<z))
         (^ℚ-Monotone {y = fromNat (suc (suc Z))}
          (fromNat (suc n)) (<ᵣWeaken≤ᵣ _ _ z<Z))
         (≤ᵣ-+o _ _ (-1) (<ᵣWeaken≤ᵣ _ _ z<Z)))))
      (·ᵣComm _ _ ∙
       cong₂ (_·ᵣ_)
         (cong₂ (_·ᵣ_) (^ⁿ-ℚ^ⁿ _ _) (cong rat (ℚ.ℤ+→ℚ+ _ _))
          ∙ sym (rat·ᵣrat _ _) )
         (cong rat (sym (ℚ.absPos _ (ℚ.-< _ _ y₀<y₁))))
        ∙ sym (rat·ᵣrat _ _)))
     

 open BoundedLipsch (fst ∘ z ^ℚ_) slUpBd bdl public

 bdlInv-lem : ( fst (fromNat (suc (suc Z))
                   ^ℚ -2)) ≤ᵣ ((fst z -ᵣ 1) ／ᵣ₊ z)
 bdlInv-lem = isTrans≡≤ᵣ _ _ _
   (cong fst (^ℚ-minus' _ 2 ∙ sym (^ℚ-+ _ 1 1)) ∙
    cong₂ _·ᵣ_ (
        cong fst (^ℚ-1 (invℝ₊ (fromNat (suc (suc Z)))))
      ∙ cong (fst ∘ invℝ₊) (fromNatℝ≡fromNatℚ _) 
     ∙ invℝ₊-rat (fromNat (suc (suc Z))))
        (cong fst (^ℚ-1 (invℝ₊ (fromNat (suc (suc Z)))))
      ∙ cong (fst ∘ invℝ₊) (fromNatℝ≡fromNatℚ _)) )
   (≤ᵣ₊Monotone·ᵣ (rat _) _ _ _
    (<ᵣWeaken≤ᵣ _ _ (x<y→0<y-x _ _ 1<z))
    (<ᵣWeaken≤ᵣ _ _ $
     snd (invℝ₊ (ℚ₊→ℝ₊ ([ pos (suc (suc Z)) , 1 ] , tt)))) (
    <ᵣWeaken≤ᵣ _ _
     (a+c<b⇒a<b-c _ _ _
       (isTrans≡<ᵣ _ _ _ (+ᵣComm (rat [ 1 / 1+ (suc Z) ]) 1) 1+1/Z<z)))
     (invEq (invℝ₊-≤-invℝ₊ (ℚ₊→ℝ₊ _) _) (<ᵣWeaken≤ᵣ _ _ z<Z))) 
 
 bdlInv : boundedInvLipschitz slUpBdInv
 bdlInv n = ℚ.elimBy≡⊎<
  (λ x y X y∈ x∈ → subst2 _≤ᵣ_
       (cong rat (ℚ.absComm- _ _))
       (cong (rat (fst (slUpBdInv n)) ·ᵣ_) (minusComm-absᵣ _ _))
       (X x∈ y∈)  )
  ((λ x _ _ → subst2 _≤ᵣ_
     (cong rat (sym (cong ℚ.abs (ℚ.+InvR x))))
     (sym (𝐑'.0RightAnnihilates' _ _ (cong absᵣ (+-ᵣ _))))
     (≤ᵣ-refl 0)))
  λ y₀ y₁ y₀<y₁ y₀∈ y₁∈ →
   subst2 _≤ᵣ_
     (cong rat (sym (ℚ.absPos _ (ℚ.-< _ _ y₀<y₁))))
     (cong (rat (fst (slUpBdInv n)) ·ᵣ_)
      (sym (absᵣNonNeg _ (x≤y→0≤y-x _ _
         (^ℚ-MonotoneR _ _ (ℚ.<Weaken≤ _ _ y₀<y₁) (<ᵣWeaken≤ᵣ _ _ 1<z) )))))
     (isTrans≡≤ᵣ _ _ _ (sym (·IdR _))
      (fst (z/y'≤x/y≃y₊·z≤y'₊·x _ _ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ y₀<y₁))
            (ℚ₊→ℝ₊ (slUpBdInv n)))
        (isTrans≡≤ᵣ _ _ _ (·IdL _)
         (isTrans≤ᵣ _ _ _
           (isTrans≡≤ᵣ _ _ _
             (invℝ₊-rat _ ∙ cong fst (
               ( (sym (^ℤ-rat (fromNat (suc (suc Z)))
                   (ℤ.negsuc (1 ℕ.+ suc n)))
                   ∙ cong (_^ℚ [ ℤ.negsuc (1 ℕ.+ suc n) / 1 ])
                    (ℝ₊≡ refl))
           ∙ cong (fromNat (suc (suc Z)) ^ℚ_)
            (cong [_/ 1 ] (ℤ.negsuc+ _ _) ∙ sym (ℚ.ℤ+→ℚ+ _ _)))
               ∙ sym (^ℚ-+ _ _ _)) ∙ ·ᵣComm _ _)
             (≤ᵣ₊Monotone·ᵣ
               (fst (fromNat (suc (suc Z))
                   ^ℚ (ℚ.- [ pos (suc n) , (1+ 0) ])))
               _
               _
               _
               (<ᵣWeaken≤ᵣ _ _
                 $ snd (z ^ℚ (ℚ.- [ pos (suc n) , (1+ 0) ])))
               (<ᵣWeaken≤ᵣ _ _
                 $ snd (fromNat (fromNat (suc (suc Z))) ^ℚ -2))
               (subst2 _≤ᵣ_
                 (cong fst (sym (^ℚ-minus' _ _)))
                 (cong fst (sym (^ℚ-minus' _ _)))
                 (^ℚ-Monotone (fromNat (suc n))
                  (invEq (invℝ₊-≤-invℝ₊ _ _)
                   (<ᵣWeaken≤ᵣ _ _ z<Z))))
               bdlInv-lem))
          (<ᵣWeaken≤ᵣ _ _
           (slope-lower-bound z (fromNat (suc n)) 1<z
            _ _ y₀<y₁
            (ℚ.absTo≤×≤ (fromNat (suc n)) y₀ y₀∈)
            (ℚ.absTo≤×≤ (fromNat (suc n)) y₁ y₁∈))
     )))))

 open BoundedInvLipsch slUpBdInv bdlInv public

 mid-𝒇 : ∀ q q' q'' → q ℚ.≤ q' → q' ℚ.≤ q'' →
    minᵣ (𝒇 (rat q))
         (𝒇 (rat q'')) ≤ᵣ 𝒇 (rat q')
 mid-𝒇 q q' q'' q≤q' q'≤q'' =
   subst2 _≤ᵣ_
     (cong₂ minᵣ (sym (𝒇-rat q)) (sym (𝒇-rat q'')))
     (sym (𝒇-rat q'))
     (monotone^ℚ q q' q'' q≤q' q'≤q'' _)


 0<powBL : ∀ x → 0 <ᵣ 𝒇 x
 0<powBL x = PT.rec squash₁
  (λ ((q , q') , q'-q<1 , q<x , x<q') →
    let q⊓q' = (minᵣ₊ (z ^ℚ q) (z ^ℚ q')) 
    in PT.rec squash₁
       (λ (ε , 0<ε , ε<q⊓q') →
         PT.rec squash₁
         (λ (δ , X) →
          PT.rec squash₁
            (λ (r , r-x≤δ , x≤r) →
               let r' = ℚ.clamp q q' r
                   r'-x≤δ = isTrans≤ᵣ _ _ _
                             (≤ᵣ-+o _ _ (-ᵣ x)
                               (≤ℚ→≤ᵣ _ _
                            (ℚ.clamped≤ q q' r
                              (ℚ.<Weaken≤ _ _
                                (<ᵣ→<ℚ _ _ (isTrans<≤ᵣ _ _ _ q<x x≤r))))) ) r-x≤δ
                   x≤r' = ≤min-lem _ (rat (ℚ.max q r)) (rat q')
                            (isTrans≤ᵣ _ _ _ x≤r
                             (≤ℚ→≤ᵣ _ _ (ℚ.≤max' q r)))
                            (<ᵣWeaken≤ᵣ _ _ x<q')
                   |fx-fr|<ε = fst (∼≃abs<ε _ _ _)
                       (sym∼ _ _ _ (X (rat r') (sym∼ _ _ _
                         ((invEq (∼≃abs<ε _ _ _)
                        (isTrans≡<ᵣ _ _ _
                          (absᵣNonNeg _ (x≤y→0≤y-x _ _ x≤r'))
                           (isTrans≤<ᵣ _ _ _
                               r'-x≤δ (<ℚ→<ᵣ _ _ (x/2<x δ))))))) ))
                   zzz =
                        mid-𝒇 q r' q'
                         (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
                          (<ᵣWeaken≤ᵣ _ _ q<x) x≤r'))
                         (ℚ.clamp≤ q q' r)
                   zzz' = isTrans<≤ᵣ _ _ _
                            (isTrans<≡ᵣ _ _ _ ε<q⊓q'
                              (cong₂ minᵣ
                                (sym (𝒇-rat _)) (sym (𝒇-rat _))))
                             zzz
               in isTrans≡<ᵣ _ _ _ (sym (CRℝ.+InvR _)) (a-b<c⇒a-c<b _ _ _
                     (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                    (isTrans<ᵣ _ _ _ |fx-fr|<ε zzz')))
              ) (∃rationalApprox≤ x (/2₊ δ)))
         
         (𝒇-cont x (ε , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<ε)))
         )
      (denseℚinℝ 0 _ (snd q⊓q')) )
   (∃rationalApprox x 1)


 flₙ≡𝒇 : ∀ x n → (x ∈ intervalℙ (fromNeg (suc n)) (fromNat (suc n)))
           →  fst (fst (flₙ n)) x ≡ 𝒇 x 
 flₙ≡𝒇 x n x∈ = ≡Continuous (fst (fst (flₙ n)))
           (𝒇 ∘ clampᵣ (fromNeg (suc n)) (fromNat (suc n)))
     (snd (flₙ n)) (IsContinuous∘ _ _ 𝒇-cont
          (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n))))
       (λ r → sym (𝒇-rat _))
       x
   ∙ cong 𝒇 (sym (∈ℚintervalℙ→clampᵣ≡ _ _ x x∈))


 𝒇-monotone : ∀ x y → x ≤ᵣ y → 𝒇 x ≤ᵣ 𝒇 y
 𝒇-monotone x y x≤y =
  (≡Cont₂ (cont₂∘ (contNE₂ maxR) 𝒇-cont 𝒇-cont)
    (cont∘₂ 𝒇-cont (contNE₂ maxR) )
    (ℚ.elimBy≤
       (λ u u' X → maxᵣComm _ _ ∙∙ X ∙∙ cong 𝒇 (maxᵣComm _ _))
       λ u u' u≤u' →
         cong₂ maxᵣ (𝒇-rat _) (𝒇-rat _)
          ∙∙ ^ℚ-MonotoneR u u' u≤u' (<ᵣWeaken≤ᵣ _ _ 1<z) ∙
           cong (fst ∘ (z ^ℚ_)) (sym (ℚ.≤→max u u' u≤u')) ∙∙
          sym (𝒇-rat _))
        x y)
   ∙ cong 𝒇 x≤y


 𝒇-monotone-str : ∀ x y → x <ᵣ y → 𝒇 x <ᵣ 𝒇 y
 𝒇-monotone-str x y = PT.rec squash₁
    λ ((q , q') , (≤q , q<q' , q'≤)) →
      isTrans≤<ᵣ _ _ _ (𝒇-monotone x (rat q) ≤q)
        (isTrans<≤ᵣ _ _ _ (
           subst2 _<ᵣ_ (sym (𝒇-rat _)) (sym (𝒇-rat _))
            (^ℚ-StrictMonotoneR 1<z q q' q<q'))
          (𝒇-monotone (rat q') y q'≤))


 module _ (n : ℕ) where


  incr^ : isIncrasingℙᵣ
            (intervalℙ (rat (ℚ.- fromNat (suc n))) (rat (fromNat (suc n))))
            (λ x _ → fst (fst (flₙ n)) x)
  incr^ x x∈ y y∈ x<y =
    subst2 _<ᵣ_
      (sym (flₙ≡𝒇 x n x∈))
      (sym (flₙ≡𝒇 y n y∈))
      (𝒇-monotone-str  x y x<y)


  nondecr^ : isNondecrasingℙᵣ
      (intervalℙ (rat (ℚ.- [ pos (suc n) / 1+ 0 ]))
       (rat [ pos (suc n) / 1+ 0 ]))
      (λ x _ → fst (fst (flₙ n)) x)
  nondecr^ x x∈ y y∈ x≤y =
    subst2 _≤ᵣ_
      (sym (flₙ≡𝒇 x n x∈))
      (sym (flₙ≡𝒇 y n y∈))
      (𝒇-monotone x y x≤y)



 open expPreDer Z z z<Z 1<z public

 expDerAt0 : derivativeOf 𝒇 at 0 is preLn
 expDerAt0 ε =
  PT.rec
    squash₁
    (λ (ε' , 0<ε' , <ε) →
      let ε'₊ = (ε' , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<ε'))
          
          (N , X) =  seqΔ ε'₊ 
      in  ∣ ℚ₊→ℝ₊ ([ 1 / 2+ (suc N) ] , _) ,
             (λ r 0＃r ∣r∣<1/N →
               let d≤lnSeq : differenceAt 𝒇 0 r 0＃r ≤ᵣ lnSeq z (suc N)
                   d≤lnSeq = ≤ContWP＃≤ [ 1 / 2+ suc N ] (ℚ.0<pos 0 (2+ (suc N)))
                             (IsContinuousWithPred-differenceAt 0 _ 𝒇-cont)
                             ((AsContinuousWithPred _ _
                              (IsContinuousConst (lnSeq z (suc N)))))
                             (λ u u∈ u≤ →
                               subst2 _≤ᵣ_
                                ((cong₂ _·ᵣ_ (cong₂ _-ᵣ_
                             (cong (fst ∘ (z ^ℚ_)) (sym (ℚ.+IdL _)) ∙ sym (𝒇-rat _))
                             (sym (𝒇-rat _)))
                                ((cong₂ invℝ (+IdR _) (toPathP (isProp＃ _ _ _ _))))))
                                (cong₂ _·ᵣ_
                                  refl ((invℝ₊-rat _ ∙ cong rat
                              (cong (fst ∘ invℚ₊) (ℚ₊≡ {y = [ 1 / 2+ (suc N) ] , _ }
                                 (ℚ.+IdR _))))))
                                (slope-monotone＃ ((z)) 1<z 0 u
                                  0 [ 1 / 2+ (suc N) ]
                                  u∈ (ℚ.0<pos 0 _) (ℚ.isRefl≤ 0) u≤))
                             r 0＃r
                             (isTrans≤ᵣ _ _ _ (≤absᵣ r)
                                (isTrans≡≤ᵣ _ _ _ (cong absᵣ (sym (+IdR _))
                                 ∙ minusComm-absᵣ _ _) (<ᵣWeaken≤ᵣ (absᵣ (0 -ᵣ r)) _ ∣r∣<1/N)))


                   lnSeq'≤d : lnSeq' z (suc N) ≤ᵣ differenceAt 𝒇 0 r 0＃r
                   lnSeq'≤d = ≤ContWP＃≤' (ℚ.- [ 1 / 2+ suc N ])
                                  ((ℚ.minus-< 0 [ 1 / 2+ suc N ] (ℚ.0<pos 0 (2+ (suc N)))))
                              ((AsContinuousWithPred _ _
                              (IsContinuousConst (lnSeq' z (suc N)))))
                              (IsContinuousWithPred-differenceAt 0 _ 𝒇-cont)
                               (λ u u∈ u≤ → subst2 _≤ᵣ_
                                  ((cong₂ _·ᵣ_ refl ((invℝ₊-rat _ ∙ cong rat
                                    (cong (fst ∘ invℚ₊)
                                      (ℚ₊≡ {x = (0 ℚ.- (ℚ.- [ 1 / 2+ suc N ])) , _}
                                           {y = [ 1 / 2+ (suc N) ] , _ }
                                        (ℚ.+IdL _ ∙ ℚ.-Invol _)))))))
                                  (sym (-ᵣ·-ᵣ _ _) ∙ cong₂ _·ᵣ_
                                    (-[x-y]≡y-x _ _ ∙
                                      cong₂ _-ᵣ_ (sym (𝒇-rat _) ∙ cong 𝒇 (sym (+IdL _)))
                                        (sym (𝒇-rat _)))
                                    (-invℝ _ _ ∙ cong₂ invℝ (cong -ᵣ_ (+IdL _) ∙ -ᵣInvol _)
                                      (toPathP (isProp＃ _ _ _ _))))
                                   
                                  (slope-monotone＃' ((z)) 1<z
                                    (ℚ.- [ 1 / 2+ (suc N) ]) 0 u 0                                    
                                    ((ℚ.minus-< 0 [ 1 / 2+ suc N ] (ℚ.0<pos 0 (2+ (suc N)))))
                                    (isSym＃ _ _ u∈) u≤ (ℚ.isRefl≤ 0)))
                               r 0＃r
                             (isTrans≤ᵣ _ _ _
                               (-ᵣ≤ᵣ _ _ (<ᵣWeaken≤ᵣ (absᵣ (0 -ᵣ r)) _ ∣r∣<1/N))
                               (≤ᵣ-ᵣ _ _ (isTrans≤≡ᵣ _ _ _ (≤absᵣ (-ᵣ r))
                                 (cong absᵣ (sym (+IdL _)) ∙ sym (-ᵣInvol _)))))
                   

               in isTrans≤<ᵣ _ _ _
                    (intervalℙ→dist< _ _ _ _
                       (<ᵣWeaken≤ᵣ _ _ (lnSeq'<preLn _) , (preLn≤lnSeq _))
                       (lnSeq'≤d , d≤lnSeq))
                    (isTrans<ᵣ _ _ _ (X (suc N) ℕ.≤-refl) <ε)

                ) ∣₁ )
    (denseℚinℝ 0 _ (snd ε)) 

 𝒇· : ∀ x y → 𝒇 x ·ᵣ 𝒇 y ≡ 𝒇 (x +ᵣ y) 
 𝒇· = ≡Cont₂
      (cont₂∘ IsContinuous₂·ᵣ 𝒇-cont 𝒇-cont )
      (cont∘₂ 𝒇-cont (contNE₂ sumR))
      λ u u' → cong₂ _·ᵣ_ (𝒇-rat _) (𝒇-rat _)
         ∙ cong fst (^ℚ-+ _ _ _) ∙ sym (𝒇-rat _) 
 

 differenceAt𝒇-Δ : ∀ x r 0＃r → 𝒇 x ·ᵣ differenceAt 𝒇 0 r 0＃r ≡ (differenceAt 𝒇 x r 0＃r)
 differenceAt𝒇-Δ x r 0＃r = ·ᵣAssoc _ _ _ ∙
   cong (_／ᵣ[ r , 0＃r ]) (𝐑'.·DistR- _ _ _ ∙
     cong₂ _-ᵣ_
       (𝒇· _ (0 +ᵣ r) ∙ cong 𝒇 (cong (x +ᵣ_) (+IdL r)))
       (𝒇· _ _ ∙ cong 𝒇 (+IdR x)))
 

 expDerA : ∀ x → derivativeOf 𝒇 at x is (𝒇 x ·ᵣ preLn)
 expDerA x = 
  subst (at (rat [ pos zero / 1+ zero ]) limitOf_is (𝒇 x ·ᵣ preLn))
   (funExt₂ λ r 0＃r →
     differenceAt𝒇-Δ _ _ _ )
   (·-lim
   _ _ _ _ _
   (const-lim (𝒇 x) 0) expDerAt0)  



seq-^-intervals : Seq⊆
seq-^-intervals .Seq⊆.𝕡 Z =
 ointervalℙ
   (rat (1 ℚ.+ [ 1 / 1+ (suc Z) ]))
   (fromNat (suc (suc Z)))
seq-^-intervals .Seq⊆.𝕡⊆ Z x (<x , x<) =
     isTrans<ᵣ _ _ _
      (<ℚ→<ᵣ _ _  (ℚ.<-o+ [ pos 1 / 2+ (suc Z) ] _ _
        (fst (ℚ.invℚ₊-<-invℚ₊
            (fromNat (suc (suc Z)))
            (fromNat (suc (suc (suc Z))))) (ℚ.<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.≤-refl)) )))
      <x
  , isTrans<ᵣ _ _ _ x< (<ℚ→<ᵣ _ _ (ℚ.<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.≤-refl)))

seq-^-intervals∈Pos : seq-^-intervals Seq⊆.s⊇ pred1<
seq-^-intervals∈Pos x x<1 =
  PT.map2 (λ (1+ n , N) (1+ m , M) →
        let m⊔n = ℕ.max n m
            M' = isTrans≡<ᵣ _ _ _ (·IdL _
              ∙ sym (absᵣPos _ (snd (invℝ₊ (x -ᵣ 1 , x<y→0<y-x 1 x x<1)))))
                   (isTrans<≤ᵣ _ _ _ M
                     ((≤ℚ→≤ᵣ (fromNat (suc m)) (fromNat (suc (suc m⊔n))) 
                      (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-suc (ℕ.right-≤-max {suc m} {suc n})))))))
            
            ii = isTrans≡<ᵣ _ _ _ (( sym (invℝ₊-rat _) ∙ cong (fst ∘ invℝ₊) (ℝ₊≡ refl))
                    ∙ sym (·IdL _))
                 (invEq (z/y<x₊≃z<y₊·x _ _ (fromNat (ℕ₊₁→ℕ (2+ m⊔n))))
                 (isTrans<≡ᵣ _ _ _ (fst (z/y<x₊≃z<y₊·x _ _ _) M') (·ᵣComm _ _)))
        in m⊔n
            , b<c-b⇒a+b<c _ _ _ ii
            , isTrans<≤ᵣ _ _ _
               (isTrans≤<ᵣ _ _ _
                 (≤absᵣ _) 
                 N) ((≤ℚ→≤ᵣ (fromNat (suc n)) _
                      (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-suc ((ℕ.left-≤-max {suc n} {suc m})))))))
        )
    (getClamps x)
    (getClamps (fst (invℝ₊ ((x -ᵣ 1) , x<y→0<y-x _ _ x<1))))
  

-- -- FnWith


Seq-^ : Seq⊆→ ((ℝ → ℝ) × ℝ) seq-^-intervals
Seq-^ .Seq⊆→.fun x Z (<x , x<) = F.𝒇 , F.preLn
 where
 module F = BDL (x , isTrans<ᵣ _ _ _ (snd (ℚ₊→ℝ₊ (1 ℚ₊+ ([ pos 1 / 2+ Z ] , _)))) <x) Z x< <x
Seq-^ .Seq⊆→.fun⊆ x n m (<x , x<) (<x' , x<') n<m = cong₂ _,_ 
  (funExt (≡Continuous _ _ F.𝒇-cont F'.𝒇-cont
       λ r → F.𝒇-rat r ∙∙ cong (fst ∘ (_^ℚ r)) (ℝ₊≡ refl) ∙∙ sym (F'.𝒇-rat r)))
        λ i → fromCauchySequence'-≡-lem (lnSeq (x , xp i))
              (icP i) (icP' i) i
        
 where
 module F = BDL (x , isTrans<ᵣ _ _ _ (snd (ℚ₊→ℝ₊ (1 ℚ₊+ ([ pos 1 / 2+ n ] , _)))) <x) n x< <x
 module F' = BDL (x , isTrans<ᵣ _ _ _ (snd (ℚ₊→ℝ₊ (1 ℚ₊+ ([ pos 1 / 2+ m ] , _)))) <x')
             m x<' <x'

 0<x = isTrans<ᵣ (rat [ pos 0 / 1+ 0 ])
         (ℚ₊→ℝ₊ (([ pos 1 , (1+ 0) ] , tt) ℚ₊+ ([ pos 1 / 2+ n ] , tt))
          .fst)
         x
         (snd
          (ℚ₊→ℝ₊ (([ pos 1 , (1+ 0) ] , tt) ℚ₊+ ([ pos 1 / 2+ n ] , tt))))
         <x
 0<x' = isTrans<ᵣ (rat [ pos 0 / 1+ 0 ])
         (ℚ₊→ℝ₊ (([ pos 1 , (1+ 0) ] , tt) ℚ₊+ ([ pos 1 / 2+ m ] , tt))
          .fst)
         x
         (snd
          (ℚ₊→ℝ₊ (([ pos 1 , (1+ 0) ] , tt) ℚ₊+ ([ pos 1 / 2+ m ] , tt))))
         <x'
 xp : 0<x ≡ 0<x'        
 xp = isProp<ᵣ 0 x 0<x 0<x'

 icP : PathP (λ i → IsCauchySequence' (lnSeq (x , xp i))) F.ca-lnSeq _
 icP = toPathP refl

 icP' : PathP (λ i → IsCauchySequence' (lnSeq (x , xp i))) _ F'.ca-lnSeq
 icP' = symP (toPathP refl)



module Seq-^-FI = Seq⊆→.FromIntersection Seq-^
   (isSet× (isSet→ isSetℝ) isSetℝ) pred1< seq-^-intervals∈Pos

module Pos^ where
 open Seq-^-FI

 pre^ : ∀ x → 1 <ᵣ x → ℝ → ℝ 
 pre^ x 1<x = fst (∩$ x 1<x)

 preLn' : ∀ x → 1 <ᵣ x → ℝ
 preLn' x 1<x = snd (∩$ x 1<x)

 pre^-der : ∀ x x∈ y → derivativeOf (pre^ x x∈) at y is (pre^ x x∈ y ·ᵣ preLn' x x∈)
 pre^-der x x∈ = ∩$-elimProp x x∈
     {λ (g , d) → (y : ℝ) →
       derivativeOf g at y is (g y ·ᵣ d)}
    (λ _ → isPropΠ2 λ _ _ → squash₁)
     λ n (a , b) → BDL.expDerA (x , _) n b a 

-- -- -- 

-- -- -- Seq-^-rat : ?
-- -- -- Seq-^-rat = ?


-- -- module PowBL⁻¹ Z (z : ℚ₊)
-- --           (z<Z : fst z ℚ.< fromNat (suc (suc Z)))
-- --           (1/Z<z : 1 ℚ.+ [ 1 / 1+ (suc Z) ] ℚ.< fst z )
          
-- --            where

-- --  open BDL (ℚ₊→ℝ₊ z) Z (<ℚ→<ᵣ _ _ z<Z) (<ℚ→<ᵣ _ _ 1/Z<z)

-- --  approx-^ : ℚApproxℙ' ⊤Pred (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , squash₁)
-- --       (λ x _ → 𝒇 x , 0<powBL x)
-- --  approx-^ y =
-- --       let ((p , q) , (_ , p/q≡y)) = ℚ.reduced y
-- --       in subst (λ y → (q∈P : rat y ∈ ⊤Pred) → 
-- --       ℚApproxℙ'Num ⊤Pred (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , squash₁)
-- --            (λ x _ → 𝒇 x , 0<powBL x) y q∈P)
-- --            p/q≡y (w p q)
-- --   where
-- --     w : ∀ p q → (q∈P : rat [ p / q ] ∈ ⊤Pred)
-- --           → ℚApproxℙ'Num ⊤Pred (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , squash₁)
-- --              (λ x _ → 𝒇 x , 0<powBL x) [ p / q ] q∈P 
-- --     w p q q∈P =
-- --        fst wwW
-- --      , fst (snd wwW)
-- --      , fst (snd (snd wwW))
-- --      , snd (snd (snd wwW)) ∙∙ cong fst (sym (pow-root-comm (ℚ₊→ℝ₊ z) p q))
-- --             ∙∙ sym (𝒇-rat [ p / q ])

-- --      where
-- --      www : ℚApproxℙ' (λ x → (0 <ᵣ x) , squash₁) (λ x → (0 <ᵣ x) , squash₁)
-- --              (curry
-- --               (((λ p₁ → fst (root q (p₁ .fst , p₁ .snd)) , root q p₁ .snd))
-- --                ∘ uncurry (curry (_^ℤ p))))
-- --      www = ℚApproxℙ''→ℚApproxℙ' _ _ _
-- --        (ℚApproxℙ∘ (λ x → (0 <ᵣ x) , squash₁) _ (λ x → (0 <ᵣ x) , squash₁)
-- --         (curry (root q))
-- --         (curry (_^ℤ p))
-- --         (uContRoot q)
-- --         (ℚApproxℙ'→ℚApproxℙ'' _ _ _ (ℚApproxℙ-root q))
-- --         (^ℤ-ℚApproxℙ'' p)) 

-- --      wwW = www (fst z) (snd (ℚ₊→ℝ₊ z))




-- --  z^n : ∀ z n → fst ((ℚ₊→ℝ₊ z) ^ℚ (fromNat (suc n))) ≡
-- --            rat (fst z ℚ^ⁿ (suc n))
-- --  z^n z zero = sym (rat·ᵣrat _ _)
-- --  z^n z (suc n) = cong (_·ᵣ rat (fst z)) (z^n z n) ∙ sym (rat·ᵣrat _ _)


-- -- -- -- -- -- -- -- --  module Invₙ (n : ℕ) where




-- -- -- -- -- -- -- -- --   open IsBilipschitz' (ℚ.- (fromNat (suc n))) (fromNat (suc n))
-- -- -- -- -- -- -- -- --          (ℚ.<ℤ→<ℚ _ _ ℤ.negsuc<pos)
-- -- -- -- -- -- -- -- --          (λ x _ → fst (fst (flₙ n)) x)
-- -- -- -- -- -- -- -- --          (AsContinuousWithPred _ _ (snd (flₙ n)))
-- -- -- -- -- -- -- -- --          (incr^ n)
-- -- -- -- -- -- -- -- --          (nondecr^  n)
-- -- -- -- -- -- -- -- --          public

-- -- -- -- -- -- -- -- --   fa' = fst (invℚ₊ z) ℚ^ⁿ suc n

-- -- -- -- -- -- -- -- --   fa≡ : fa ≡ rat fa'
-- -- -- -- -- -- -- -- --   fa≡ =  flₙ≡𝒇 (fromNeg (suc n)) n a∈
-- -- -- -- -- -- -- -- --        ∙ 𝒇-rat (fromNeg (suc n))
-- -- -- -- -- -- -- -- --         ∙ cong fst (^ℚ-minus (ℚ₊→ℝ₊ z) (fromNeg (suc n))
-- -- -- -- -- -- -- -- --           ∙ cong (_^ℚ fromNat (suc n)) (ℝ₊≡
-- -- -- -- -- -- -- -- --            (invℝ₊≡invℝ (ℚ₊→ℝ₊ z) (inl (snd (ℚ₊→ℝ₊ z)))
-- -- -- -- -- -- -- -- --            ∙ invℝ-rat _ _ (inl (ℚ.0<ℚ₊ z)) ∙
-- -- -- -- -- -- -- -- --              cong rat (ℚ.invℚ₊≡invℚ _ _))))
-- -- -- -- -- -- -- -- --         ∙ z^n (invℚ₊ z) n

-- -- -- -- -- -- -- -- --   fb' = (fst z ℚ^ⁿ suc n)
 
-- -- -- -- -- -- -- -- --   fb≡ : fb ≡ rat fb'
-- -- -- -- -- -- -- -- --   fb≡ =  flₙ≡𝒇  (fromNat (suc n)) n b∈
-- -- -- -- -- -- -- -- --     ∙ 𝒇-rat _ ∙ z^n z n

-- -- -- -- -- -- -- -- --   1<ℚz : 1 ℚ.< (fst z)
-- -- -- -- -- -- -- -- --   1<ℚz = <ᵣ→<ℚ 1 (fst z) 1<z

-- -- -- -- -- -- -- -- --   fa'≤fb' : fa' ℚ.≤ fb'
-- -- -- -- -- -- -- -- --   fa'≤fb' = ℚ.isTrans≤ _ 1 _
-- -- -- -- -- -- -- -- --     (ℚ.x^ⁿ≤1 _ (suc n) (ℚ.0≤ℚ₊ (invℚ₊ z)) (fst (ℚ.invℚ₊-≤-invℚ₊ 1 z)
-- -- -- -- -- -- -- -- --      (ℚ.<Weaken≤ 1 (fst z) 1<ℚz)))
-- -- -- -- -- -- -- -- --     (ℚ.1≤x^ⁿ _ (suc n) (ℚ.<Weaken≤ 1 (fst z) 1<ℚz) ) 
  
-- -- -- -- -- -- -- -- --   approx-^ℙ : ℚApproxℙ'
-- -- -- -- -- -- -- -- --      ((intervalℙ (rat (ℚ.- fromNat (suc n))) (rat (fromNat (suc n)))))
-- -- -- -- -- -- -- -- --      (intervalℙ fa fb)
-- -- -- -- -- -- -- -- --      f'
-- -- -- -- -- -- -- -- --   approx-^ℙ x x∈ =
-- -- -- -- -- -- -- -- --       ℚ.clamp (fst (invℚ₊ z) ℚ^ⁿ suc n) (fst z ℚ^ⁿ suc n) ∘ fst ww
-- -- -- -- -- -- -- -- --     , (λ ε → subst2
-- -- -- -- -- -- -- -- --        (λ fa fb →
-- -- -- -- -- -- -- -- --          (rat (ℚ.clamp (fst (invℚ₊ z) ℚ^ⁿ suc n) (fst z ℚ^ⁿ suc n) (fst ww ε)))
-- -- -- -- -- -- -- -- --           ∈ (intervalℙ fa fb))
-- -- -- -- -- -- -- -- --           (sym fa≡ ) (sym fb≡)
-- -- -- -- -- -- -- -- --         (∈ℚintervalℙ→∈intervalℙ _ _ _
-- -- -- -- -- -- -- -- --           (clam∈ℚintervalℙ fa' fb' fa'≤fb' (fst ww ε)) ))
-- -- -- -- -- -- -- -- --     , (λ δ ε → invEq (∼≃abs<ε _ _ _)
-- -- -- -- -- -- -- -- --          let u = (<ᵣ→<ℚ _ _ (fst (∼≃abs<ε _ _ _) (fst (snd (snd ww)) δ ε)))
-- -- -- -- -- -- -- -- --          in <ℚ→<ᵣ _ _
-- -- -- -- -- -- -- -- --                (ℚ.isTrans≤< _ _ _ (
-- -- -- -- -- -- -- -- --                   subst2 ℚ._≤_ (ℚ.abs'≡abs _) (ℚ.abs'≡abs _)
-- -- -- -- -- -- -- -- --                    (ℚ.clampDist _ _ _ _) ) u))
-- -- -- -- -- -- -- -- --     , ssw

-- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- --     ww = approx-^ x _


-- -- -- -- -- -- -- -- --     z^clmp-x = fst (ℚ₊→ℝ₊ z ^ℚ
-- -- -- -- -- -- -- -- --              ℚ.clamp (ℚ.- [ pos (suc n) / 1+ 0 ]) [ pos (suc n) / 1+ 0 ] x)

-- -- -- -- -- -- -- -- --     ssww' : lim (λ x₁ → rat (fst ww x₁)) _ ≡ z^clmp-x
-- -- -- -- -- -- -- -- --     ssww' = snd (snd (snd ww))
-- -- -- -- -- -- -- -- --       ∙ 𝒇-rat _ ∙ cong (fst ∘ (ℚ₊→ℝ₊ z ^ℚ_))
-- -- -- -- -- -- -- -- --         (∈ℚintervalℙ→clam≡ _ _ x (∈intervalℙ→∈ℚintervalℙ _ _ _ x∈))

-- -- -- -- -- -- -- -- --     ssw-lem1 : fst (ℚ₊→ℝ₊ z ^ℚ [ ℤ.negsuc n / 1+ 0 ]) ≤ᵣ z^clmp-x
-- -- -- -- -- -- -- -- --     ssw-lem1 = ((^ℚ-MonotoneR {ℚ₊→ℝ₊ z} (fromNeg (suc n))
-- -- -- -- -- -- -- -- --                                  (ℚ.clamp (ℚ.- [ pos (suc n) / 1+ 0 ]) [ pos (suc n) / 1+ 0 ] x)
-- -- -- -- -- -- -- -- --                                    (ℚ.≤clamp _ _ _ (ℚ.neg≤pos (suc n) (suc n))) 
-- -- -- -- -- -- -- -- --                                 (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ 1<ℚz))))

-- -- -- -- -- -- -- -- --     ssw-lem2 : z^clmp-x ≤ᵣ fst (ℚ₊→ℝ₊ z ^ℚ [ pos (suc n) / 1+ 0 ])
-- -- -- -- -- -- -- -- --     ssw-lem2 = ((^ℚ-MonotoneR {ℚ₊→ℝ₊ z} 
-- -- -- -- -- -- -- -- --                                  (ℚ.clamp (ℚ.- [ pos (suc n) / 1+ 0 ]) [ pos (suc n) / 1+ 0 ] x)
-- -- -- -- -- -- -- -- --                                   (fromNat (suc n))
-- -- -- -- -- -- -- -- --                                   (ℚ.clamp≤ (ℚ.- [ pos (suc n) / 1+ 0 ]) _ x) 
-- -- -- -- -- -- -- -- --                                 (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ 1<ℚz))))

-- -- -- -- -- -- -- -- --     ssw : lim (λ x₁ →
-- -- -- -- -- -- -- -- --                   rat
-- -- -- -- -- -- -- -- --                   (ℚ.clamp (fst (invℚ₊ z) ℚ^ⁿ suc n)
-- -- -- -- -- -- -- -- --                     (fst z ℚ^ⁿ suc n) (fst ww x₁))) _ ≡ z^clmp-x
-- -- -- -- -- -- -- -- --     ssw = invEq (lim≡≃∼ _ _ _) λ ε →
-- -- -- -- -- -- -- -- --         let zz = isTrans≡≤ᵣ _ _ _
-- -- -- -- -- -- -- -- --                  (sym (cong absᵣ (cong₂ _-ᵣ_
-- -- -- -- -- -- -- -- --                    (clamp-lim _ _ _ (fst (snd (snd ww)))  ∙ congLim _ _ _ _
-- -- -- -- -- -- -- -- --                       (λ _ → refl) )
-- -- -- -- -- -- -- -- --                          (sym (∈ℚintervalℙ→clampᵣ≡ _ _ _
-- -- -- -- -- -- -- -- --                            ( (isTrans≡≤ᵣ _ _ _ (sym (z^n ((invℚ₊ z)) _) ∙
-- -- -- -- -- -- -- -- --                               cong fst (^ℚ-minus _ _ ∙
-- -- -- -- -- -- -- -- --                                 cong {y = ℚ₊→ℝ₊ z} (_^ℚ (fromNeg (suc n)))
-- -- -- -- -- -- -- -- --                                    (cong invℝ₊ (ℝ₊≡ (sym (invℝ₊-rat _))) ∙ invℝ₊Invol _)))
-- -- -- -- -- -- -- -- --                                ssw-lem1)
-- -- -- -- -- -- -- -- --                            , isTrans≤≡ᵣ _ _ _
-- -- -- -- -- -- -- -- --                                ssw-lem2 (z^n _ _)))))))
                 
-- -- -- -- -- -- -- -- --                  ((clampDistᵣ' ((fst (invℚ₊ z) ℚ^ⁿ (suc n))) ((fst z ℚ^ⁿ (suc n)))
-- -- -- -- -- -- -- -- --                     z^clmp-x (lim (λ x₁ → rat (fst ww x₁)) _)))
-- -- -- -- -- -- -- -- --         in isTrans≤<ᵣ _ _ _ zz (fst (lim≡≃∼ _ _ _) ssww' ε)




-- -- -- -- -- -- -- -- --   open Inv 
-- -- -- -- -- -- -- -- --          approx-^ℙ
-- -- -- -- -- -- -- -- --          (slUpBd n) (slUpBdInv n)
-- -- -- -- -- -- -- -- --          (lipFₙ n)
-- -- -- -- -- -- -- -- --          (slpBdIneq n)
-- -- -- -- -- -- -- -- --          (invLipFₙ n) public


-- -- -- -- -- -- -- -- --   Aℙ = ointervalℙ (rat (ℚ.- fromNat (suc n))) (fromNat (suc n))


-- -- -- -- -- -- -- -- --   A : Type
-- -- -- -- -- -- -- -- --   A = Σ ℝ (_∈ Aℙ)


-- -- -- -- -- -- -- -- --   Bℙ = ointervalℙ
-- -- -- -- -- -- -- -- --     (fst (fst (flₙ n)) (rat (ℚ.- fromNat (suc n))))
-- -- -- -- -- -- -- -- --     (fst (fst (flₙ n)) (rat (fromNat (suc n))))


-- -- -- -- -- -- -- -- --   B = Σ ℝ (_∈ Bℙ)

-- -- -- -- -- -- -- -- --   Bℙ' = ointervalℙ
-- -- -- -- -- -- -- -- --     (𝒇 (rat (ℚ.- fromNat (suc n))))
-- -- -- -- -- -- -- -- --     (𝒇 (rat (fromNat (suc n))))

-- -- -- -- -- -- -- -- --   B' = Σ ℝ (_∈ Bℙ')

-- -- -- -- -- -- -- -- --   isEquivₙ : isEquiv {A = A} {B = B} (λ (x , x∈) → fst (fst (flₙ n)) x , _) 
-- -- -- -- -- -- -- -- --   isEquivₙ = isEquivFo

-- -- -- -- -- -- -- -- --   𝒇-∈ₙ : ∀ x (x∈ : x ∈ Aℙ)  → 𝒇 x ∈ Bℙ'    
-- -- -- -- -- -- -- -- --   𝒇-∈ₙ x (<x , x<) =
-- -- -- -- -- -- -- -- --        𝒇-monotone-str _ _ <x
-- -- -- -- -- -- -- -- --      , 𝒇-monotone-str _ _ x<

-- -- -- -- -- -- -- -- --   fa≡ₙ : (fst (fst (flₙ n)) (rat (ℚ.- fromNat (suc n))))
-- -- -- -- -- -- -- -- --           ≡ (𝒇 (rat (ℚ.- fromNat (suc n))))
-- -- -- -- -- -- -- -- --   fa≡ₙ = cong (fst ∘ (ℚ₊→ℝ₊ z ^ℚ_))
-- -- -- -- -- -- -- -- --    (sym (∈ℚintervalℙ→clam≡ ((ℚ.- fromNat (suc n))) (fromNat (suc n)) _
-- -- -- -- -- -- -- -- --       (∈intervalℙ→∈ℚintervalℙ _ _ _ a∈)))
-- -- -- -- -- -- -- -- --      ∙ sym (𝒇-rat (ℚ.- fromNat (suc n)))


-- -- -- -- -- -- -- -- --   fb≡ₙ : (fst (fst (flₙ n)) (rat (fromNat (suc n))))
-- -- -- -- -- -- -- -- --           ≡ (𝒇 (rat (fromNat (suc n))))
-- -- -- -- -- -- -- -- --   fb≡ₙ = cong (fst ∘ (ℚ₊→ℝ₊ z ^ℚ_))
-- -- -- -- -- -- -- -- --    (sym (∈ℚintervalℙ→clam≡ ((ℚ.- fromNat (suc n))) (fromNat (suc n)) _
-- -- -- -- -- -- -- -- --       (∈intervalℙ→∈ℚintervalℙ _ _ _ b∈)))
-- -- -- -- -- -- -- -- --      ∙ sym (𝒇-rat (fromNat (suc n)))


-- -- -- -- -- -- -- -- --   isEquivₙ' : isEquiv {A = A} {B = B'} (λ (x , x∈) → 𝒇 x , 𝒇-∈ₙ x x∈) 
-- -- -- -- -- -- -- -- --   isEquivₙ' = subst {A = Σ (ℝ × ℝ)
-- -- -- -- -- -- -- -- --         (λ rr → A → Σ ℝ (_∈ ointervalℙ (fst rr) (snd rr)))}
-- -- -- -- -- -- -- -- --         (λ (_ , f) → isEquiv f)
-- -- -- -- -- -- -- -- --         (ΣPathP
-- -- -- -- -- -- -- -- --           (ΣPathP (fa≡ₙ , fb≡ₙ)
-- -- -- -- -- -- -- -- --            , funExt λ x → ΣPathPProp
-- -- -- -- -- -- -- -- --               (λ x → ∈-isProp (ointervalℙ _ _) x)
-- -- -- -- -- -- -- -- --                (sym (∩$-∈ₙ (fst x) _ n (snd x))) ))
-- -- -- -- -- -- -- -- --           isEquivₙ

-- -- -- -- -- -- -- -- --  module EFR = EquivFromRestr
-- -- -- -- -- -- -- -- --    𝒇
-- -- -- -- -- -- -- -- --    Invₙ.𝒇-∈ₙ
-- -- -- -- -- -- -- -- --    Invₙ.isEquivₙ'

-- -- -- -- -- -- -- -- --  𝒇₊ : ℝ → ℝ₊
-- -- -- -- -- -- -- -- --  𝒇₊ x = 𝒇 x , 0<powBL x


-- -- -- -- -- -- -- -- -- --  pre𝒇≃∈ : ∀ x → (x ∈ EFR.Bℙ) ≃ (0 <ᵣ x)
-- -- -- -- -- -- -- -- -- --  pre𝒇≃∈ x = propBiimpl→Equiv (∈-isProp EFR.Bℙ x) (isProp<ᵣ _ _)
-- -- -- -- -- -- -- -- -- --   (PT.rec (isProp<ᵣ _ _)
-- -- -- -- -- -- -- -- -- --     (λ (n , <x , _) →
-- -- -- -- -- -- -- -- -- --         isTrans<ᵣ _ _ _
-- -- -- -- -- -- -- -- -- --          (0<powBL (rat (ℚ.- fromNat (suc n)))) <x))
-- -- -- -- -- -- -- -- -- --   λ 0<x →
-- -- -- -- -- -- -- -- -- --     PT.map2
-- -- -- -- -- -- -- -- -- --       (λ (n , N) (m , M) →
-- -- -- -- -- -- -- -- -- --         (ℕ.max n m) , ({!!} ,
-- -- -- -- -- -- -- -- -- --            (isTrans<≤ᵣ _ _ _ N
-- -- -- -- -- -- -- -- -- --              (isTrans≤≡ᵣ _ _ _
-- -- -- -- -- -- -- -- -- --                {!N!}
-- -- -- -- -- -- -- -- -- --                (sym (𝒇-rat (fromNat (suc (ℕ.max n m)))))))))
-- -- -- -- -- -- -- -- -- --       (expBnd x) (expBnd (-ᵣ x))

-- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- --     expBnd : ∀ x → ∃[ n ∈ ℕ ] x <ᵣ fst ((ℚ₊→ℝ₊ z) ^ℚ {!!}) 
-- -- -- -- -- -- -- -- -- --     expBnd x =
-- -- -- -- -- -- -- -- -- --       PT.map {!!}
-- -- -- -- -- -- -- -- -- --        (EFR.clamp' x)
-- -- -- -- -- -- -- -- -- -- --  pre𝒇≃ : ℝ ≃ ℝ₊
-- -- -- -- -- -- -- -- -- -- --  pre𝒇≃ = (_ , EFR.equiv-fromRestr) ∙ₑ Σ-cong-equiv-snd pre𝒇≃∈
 
 
-- -- -- -- -- -- -- -- -- -- --  isEquiv-𝒇 : isEquiv 𝒇₊
-- -- -- -- -- -- -- -- -- -- --  isEquiv-𝒇 =
-- -- -- -- -- -- -- -- -- -- --    subst {A = ∀ x → 0 <ᵣ 𝒇 x}
-- -- -- -- -- -- -- -- -- -- --      {x = λ x → snd (fst pre𝒇≃ x)} {y = 0<powBL}
-- -- -- -- -- -- -- -- -- -- --      (λ f∈' → isEquiv {A = ℝ} {B = ℝ₊} (λ x → 𝒇 x , f∈' x))
-- -- -- -- -- -- -- -- -- -- --      (isPropΠ (λ _ → isProp<ᵣ 0 _) _ _) (snd pre𝒇≃ ) 

-- -- -- -- -- -- -- -- -- -- --  logℚ : ℝ₊ → ℝ
-- -- -- -- -- -- -- -- -- -- --  logℚ = invEq (_ , isEquiv-𝒇)
 
-- -- -- -- -- -- -- -- -- -- -- module Log (y : ℝ₊) where

-- -- -- -- -- -- -- -- -- -- -- -- PowBL⁻¹ (z : ℚ₊) Z
-- -- -- -- -- -- -- -- -- -- -- --           (z<Z : fst z ℚ.< fromNat (suc (suc Z)))
-- -- -- -- -- -- -- -- -- -- -- --           (1/Z<z : 1 ℚ.+ [ 1 / 1+ (suc Z) ] ℚ.< fst z )


-- -- -- -- -- -- -- -- -- -- --  pre-log : ∀ n (x : ℚ) →
-- -- -- -- -- -- -- -- -- -- --     (rat x ∈ ointervalℙ (rat (1 ℚ.+ [ 1 / 1+ (suc n) ]))
-- -- -- -- -- -- -- -- -- -- --             (fromNat (suc (suc n)))) → ℝ
-- -- -- -- -- -- -- -- -- -- --  pre-log n x (<x , x<) =
-- -- -- -- -- -- -- -- -- -- --   PowBL⁻¹.logℚ n (x , ℚ.<→0< _
-- -- -- -- -- -- -- -- -- -- --     (ℚ.isTrans< 0 ([ pos 1 / 1+ 0 ] ℚ.+ [ pos 1 / 2+ n ]) _
-- -- -- -- -- -- -- -- -- -- --      (ℚ.0<ℚ₊ (1 ℚ₊+ ([ pos 1 / 2+ n ] , _)))
-- -- -- -- -- -- -- -- -- -- --       (<ᵣ→<ℚ _ _ <x))) (<ᵣ→<ℚ _ _ x<) (<ᵣ→<ℚ _ _ <x) y
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fₙ+ : (n : ℕ) (x : ℝ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (x∈ : Σ (fromNeg (suc n) <ᵣ x) (λ _ → x <ᵣ fromNat (suc n))) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fst (fst (flₙ n)) x ∈
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ointervalℙ (𝒇 (fromNeg (suc n))) (𝒇 (fromNat (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fₙ+ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  equivₙ : (n : ℕ) → isEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {A = Σ ℝ (_∈ ointervalℙ (fromNeg (suc n)) (fromNat (suc n)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {B = Σ ℝ (_∈ ointervalℙ (𝒇 (fromNeg (suc n))) (𝒇 (fromNat (suc n))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ (x , x∈) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          fst (fst (flₙ n)) (x) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          fₙ+ n x x∈)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  equivₙ n = (subst {A = ( (Σ Type λ B →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (Σ ℝ (_∈ ointervalℙ (fromNeg (suc n)) (fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        → B))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ (B , f) → isEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         {A = (Σ ℝ (_∈ ointervalℙ (fromNeg (suc n)) (fromNat (suc n))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         {B = B} f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ( (ΣPathP ({!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            , {!?!}))))
       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (Invₙ.isEquivFo n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open Equiv𝒇₊ fₙ+
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       equivₙ {!!} {!!}  

  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (z : ℝ₊) (z≤1 : fst z ≤ᵣ 1)  where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  module _ (B B' : ℚ₊) (B<B' : fst B ℚ.< fst B') where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   boundMonInv : (z' : ℝ₊) → fst z ≤ᵣ fst z'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               → (fst (z' ^ℚ (fst B')) -ᵣ fst (z' ^ℚ (fst B)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               ≤ᵣ (fst (z ^ℚ (fst B')) -ᵣ fst (z ^ℚ (fst B)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   boundMonInv z' z≤z' =  {!!}





-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (z : ℝ₊) (1≤z : 1 ≤ᵣ fst z)  where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  module _ (B : ℚ₊) where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   boundMon : (z' : ℝ₊) → fst z ≤ᵣ fst z'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               → (fst (z ^ℚ (2 ℚ.· (fst B))) -ᵣ fst (z ^ℚ (fst B)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               ≤ᵣ (fst (z' ^ℚ (2 ℚ.· (fst B))) -ᵣ fst (z' ^ℚ (fst B)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   boundMon z' z≤z' =  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     subst2 _≤ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (sym (factor-xᵃ-xᵇ z (2 ℚ.· fst B) (fst B)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (sym (factor-xᵃ-xᵇ z' (2 ℚ.· fst B) (fst B)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (≤ᵣ₊Monotone·ᵣ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (<ᵣWeaken≤ᵣ _ _ (snd (z' ^ℚ fst B)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (x≤y→0≤y-x _ _ (1≤^ℚ _ h 1≤z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (^ℚ-Monotone B z≤z')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (≤ᵣ-+o _ _ _ (^ℚ-Monotone h  z≤z')))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     h = (ℚ.<→ℚ₊ (fst B) (2 ℚ.· fst B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (subst (ℚ._< 2 ℚ.· fst B) (ℚ.·IdL (fst B))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (ℚ.<-·o 1 _ _ (ℚ.0<ℚ₊ B) ℚ.decℚ<?)))




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  module _ Z (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z))) where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   bound<boundℚ : ∀ n →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (bound z (fromNat (suc n))) ≤ᵣ rat (fst (boundℚ Z n))  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   bound<boundℚ n =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       isTrans≤≡ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (≤ᵣ-·ᵣo _ _ _ (<ᵣWeaken≤ᵣ _ _ $ snd (ℚ₊→ℝ₊ (invℚ₊ (fromNat (suc n)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (boundMon _ _ z≤Z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (cong₂ _·ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (cong₂ _-ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ((cong (fst ∘ (fromNat (suc (suc Z)) ^ℚ_))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (ℚ.ℕ·→ℚ· _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ∙ ^ⁿ-ℚ^ⁿ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (^ⁿ-ℚ^ⁿ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 refl ∙ sym (rat·ᵣrat _ _))
 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ineq'' : ∀ (B : ℚ₊) x y → ℚ.abs x ℚ.≤ fst B → ℚ.abs y ℚ.≤ fst B → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∀ z → absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ≤ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             bound (maxᵣ₊ (invℝ₊ z) z) B ·ᵣ rat (ℚ.abs' (y ℚ.- x))   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ineq'' B x y absx≤B absy≤B =   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   uncurry $ <→≤ContPos'pred
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (IsContinuousWP∘' _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          IsContinuousAbsᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (contDiagNE₂WP sumR _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (IsContinuous^ℚ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (IsContinuousWP∘' _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              IsContinuous-ᵣ (IsContinuous^ℚ x ))))       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (IsContinuousWP∘' _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (IsContinuous·ᵣR (rat (ℚ.abs' (y ℚ.- x))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (IsContinuousWP∘ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (contBound B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (contDiagNE₂WP maxR _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (snd invℝ')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (AsContinuousWithPred _ _ IsContinuousId))))    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        λ u 0<u → w u 0<u (ℚ.≡⊎# u 1)
     
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  x≤B : x ℚ.≤ fst B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  x≤B = ℚ.isTrans≤ _ _ _ (ℚ.≤abs _) absx≤B 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  y≤B : y ℚ.≤ fst B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  y≤B = ℚ.isTrans≤ _ _ _ (ℚ.≤abs _) absy≤B 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w : ∀ u (0<u : 0 <ᵣ rat u) → ((u ≡ 1) ⊎ (u ℚ.# 1)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           absᵣ (fst ((rat u , 0<u) ^ℚ y) -ᵣ fst ((rat u , 0<u) ^ℚ x)) ≤ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        bound (maxᵣ₊ (invℝ₊ (rat u , 0<u)) (rat u , 0<u)) B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ·ᵣ rat (ℚ.abs' (y ℚ.- x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w u 0<u (inl u=1) = ≡ᵣWeaken≤ᵣ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (cong absᵣ (𝐑'.+InvR' _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (fst ∘ (_^ℚ y)) (ℝ₊≡ {_ , 0<u} {_ , decℚ<ᵣ? {0} {1}}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (cong rat u=1))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ∙∙ (cong fst (1^ℚ≡1 _) ∙ cong fst (sym (1^ℚ≡1 _))) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           cong (fst ∘ (_^ℚ x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (ℝ₊≡ {_ , decℚ<ᵣ? {0} {1}} {_ , 0<u} (cong rat (sym u=1)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ∙ sym (𝐑'.0LeftAnnihilates' _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (cong (flip bound B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (ℝ₊≡ (cong₂ maxᵣ (invℝ'-rat _ (ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<u)) _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∙ (cong (rat ∘ fst ∘ invℚ₊) (ℚ₊≡ u=1)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong rat u=1) ∙ maxᵣIdem _)) ∙ bound1≡0 B)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w u 0<u (inr (inl u<1)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    isTrans≤ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (isTrans≤≡ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (isTrans≡≤ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (cong absᵣ (cong₂ _-ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong fst (^ℚ-minus _ _) ∙ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           cong (fst ∘ (_^ℚ (ℚ.- y))) (ℝ₊≡ (invℝ'-rat _ _ _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong fst (^ℚ-minus _ _) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          cong (fst ∘ (_^ℚ (ℚ.- x))) (ℝ₊≡ (invℝ'-rat _ _ _))))) h)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (cong (bound 1/u₊ B ·ᵣ_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (cong rat (cong ℚ.abs' (sym (ℚ.-[x-y]≡y-x _ _)) ∙ sym (ℚ.-abs' _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ∙ cong ℚ.abs' (ℚ.+Comm _ _ ∙ cong (ℚ._- x) (ℚ.-Invol y))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (≤ᵣ-·o _ _ _ (subst (0 ℚ.≤_) (ℚ.abs'≡abs _) (ℚ.0≤abs (y ℚ.- x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ((≤ᵣ-·o _ _ ((fst (invℚ₊ B)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (ℚ.0≤ℚ₊ (invℚ₊ B))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (boundMon 1/u₊
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (<ᵣWeaken≤ᵣ _ _ 1<1/u₊)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (isTrans≡≤ᵣ _ _ _  (sym (invℝ'-rat _ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (≤maxᵣ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   1/u₊ : ℝ₊
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   1/u₊ = ℚ₊→ℝ₊ (invℚ₊ (u , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<u)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   1<1/u₊ : 1 <ᵣ (fst 1/u₊)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   1<1/u₊ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     let z = subst (1 ℚ.<_) (ℚ.·IdL _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             $ ℚ.y·x<z→x<z·invℚ₊y 1 1 ((u , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<u)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (subst (ℚ._< 1) (sym (ℚ.·IdR u)) u<1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     in <ℚ→<ᵣ _ _ z
    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   h : absᵣ (fst (1/u₊ ^ℚ (ℚ.- y)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- x))) ≤ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         bound 1/u₊ B ·ᵣ rat (ℚ.abs' ((ℚ.- y) ℚ.- (ℚ.- x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   h = ExpSlopeBound.ineq-abs 1/u₊ 1<1/u₊ B (ℚ.- x) (ℚ.- y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (ℚ.isTrans≤ _ _ _ (ℚ.≤abs _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (subst (ℚ._≤ fst B) (ℚ.-abs _) absx≤B))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (ℚ.isTrans≤ _ _ _ (ℚ.≤abs _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (subst (ℚ._≤ fst B) (ℚ.-abs _) absy≤B))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w u 0<u (inr (inr 1<u)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    isTrans≤ᵣ _ _ _ h
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (≤ᵣ-·o _ _ _ (subst (0 ℚ.≤_) (ℚ.abs'≡abs _) (ℚ.0≤abs _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (≤ᵣ-·o _ _ ((fst (invℚ₊ B)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (ℚ.0≤ℚ₊ (invℚ₊ B))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ((boundMon u₊  (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ 1<u))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        B  ((maxᵣ₊ (invℝ₊ (rat u , 0<u)) (rat u , 0<u)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (isTrans≤≡ᵣ _ _ _ (≤maxᵣ _ _) (maxᵣComm _ _)))) ))
       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   u₊ : ℝ₊
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   u₊ = rat u , 0<u

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   h : absᵣ (fst (u₊ ^ℚ y) -ᵣ fst (u₊ ^ℚ x)) ≤ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         bound u₊ B ·ᵣ rat (ℚ.abs' (y ℚ.- x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   h = ExpSlopeBound.ineq-abs u₊ (<ℚ→<ᵣ _ _ 1<u) B x y x≤B y≤B 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ineq''-inv : ∀ (B : ℚ₊) x y → ℚ.abs x ℚ.≤ fst B → ℚ.abs y ℚ.≤ fst B → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∀ z → absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ≤ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             bound (maxᵣ₊ (invℝ₊ z) z) B ·ᵣ rat (ℚ.abs' (y ℚ.- x))   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ineq''-inv B x y absx≤B absy≤B =   ?

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- monotone^ℚ' : ∀ q q' q'' 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  → q ℚ.≤ q'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  → q' ℚ.≤ q''
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  → ∀ u 0<u
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  → minᵣ (fst ((rat u , 0<u) ^ℚ q)) (fst ((rat u , 0<u) ^ℚ q'')) ≤ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    fst ((rat u , 0<u) ^ℚ q')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- monotone^ℚ' q q' q'' q≤q' q'≤q'' u 0<u =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ⊎.rec
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ 1≤u →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      isTrans≤ᵣ _ _ _ (min≤ᵣ (fst ((rat u , 0<u) ^ℚ q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst ((rat u , 0<u) ^ℚ q'')))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (^ℚ-MonotoneR {(rat u , 0<u)} q q'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            q≤q'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (≤ℚ→≤ᵣ _ _ 1≤u)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ u<1 → isTrans≤ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (min≤ᵣ' (fst ((rat u , 0<u) ^ℚ q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst ((rat u , 0<u) ^ℚ q'')))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        let xx = (^ℚ-MonotoneR {invℝ₊ (rat u , 0<u)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                _ _  (ℚ.minus-≤ _ _ q'≤q'')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (isTrans≤≡ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (invEq (z≤x/y₊≃y₊·z≤x 1 1 (rat u , 0<u))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       (isTrans≡≤ᵣ _ _ _ (·IdR _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ u<1))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (·IdL _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        in subst2 _≤ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (cong fst (sym (^ℚ-minus _ _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (cong fst (sym (^ℚ-minus _ _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             xx)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (ℚ.Dichotomyℚ 1 u)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- monotone^ℚ : ∀ q q' q'' 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  → q ℚ.≤ q'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  → q' ℚ.≤ q''
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  → ∀ z 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  → minᵣ (fst (z ^ℚ q)) (fst (z ^ℚ q'')) ≤ᵣ fst (z ^ℚ q')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- monotone^ℚ q q' q'' q≤q' q'≤q'' =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   uncurry (<→≤ContPos'pred {0}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (contDiagNE₂WP minR _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (IsContinuous^ℚ q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (IsContinuous^ℚ q''))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (IsContinuous^ℚ q')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ u 0<u → monotone^ℚ' q q' q'' q≤q' q'≤q'' u 0<u)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module PowBL (z : ℝ₊) Z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (z<Z : fst z <ᵣ fromNat (suc (suc Z)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (1/Z<z : rat [ 1 / 1+ (suc Z) ] <ᵣ fst z )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  z' = maxᵣ₊ (invℝ₊ z) z

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  hh : fst (invℝ₊ (ℚ₊→ℝ₊ ([ pos 1 / 2+ Z ] , tt))) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       rat [ pos (suc (suc Z)) / 1+ 0 ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  hh = invℝ'-rat [ pos 1 / 2+ Z ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      tt (snd (ℚ₊→ℝ₊ ([ 1 / 1+ (suc Z) ] , tt)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  1/z≤2+Z : fst (invℝ₊ z) ≤ᵣ fromNat (suc (suc Z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  1/z≤2+Z = isTrans≤≡ᵣ _ _ _ (isTrans≡≤ᵣ _ _ _ (sym (·IdL _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (invEq (z/y'≤x/y≃y₊·z≤y'₊·x 1 1 (ℚ₊→ℝ₊ ([ 1 / 1+ (suc Z) ] , _)) z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (subst2 _≤ᵣ_ (sym (·IdR _)) (sym (·IdR _)) (<ᵣWeaken≤ᵣ _ _  1/Z<z))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ((·IdL _) ∙ hh)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  bound≤boundℚ : ∀ n →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (bound z' (fromNat (suc n))) ≤ᵣ rat (fst (boundℚ Z n))  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  bound≤boundℚ n = bound<boundℚ z'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (subst (1 ≤ᵣ_) (maxᵣComm _ _) (1≤x⊔1/x z)) Z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (max≤-lem _ _ _ 1/z≤2+Z (<ᵣWeaken≤ᵣ _ _ z<Z)) n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  blPow : boundedLipschitz (λ x → fst (z ^ℚ x)) (boundℚ Z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  blPow n x y absx< absy< =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isTrans≤ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (ineq'' (fromNat (suc n)) x y absx< absy< z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (isTrans≤≡ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (≤ᵣ-·o _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (subst (0 ℚ.≤_) (ℚ.abs'≡abs _) (ℚ.0≤abs _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (bound≤boundℚ n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong (rat (fst (boundℚ Z n)) ·ᵣ_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (cong rat (sym (ℚ.abs'≡abs _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ sym (rat·ᵣrat _ _)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open BoundedLipsch
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (fst ∘ z ^ℚ_) (boundℚ Z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      blPow public


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  mid-𝒇 : ∀ q q' q'' → q ℚ.≤ q' → q' ℚ.≤ q'' →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     minᵣ (𝒇 (rat q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (𝒇 (rat q'')) ≤ᵣ 𝒇 (rat q')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  mid-𝒇 q q' q'' q≤q' q'≤q'' =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    subst2 _≤ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (cong₂ minᵣ (sym (𝒇-rat q)) (sym (𝒇-rat q'')))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (sym (𝒇-rat q'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (monotone^ℚ q q' q'' q≤q' q'≤q'' _)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  0<powBL : ∀ x → 0 <ᵣ 𝒇 x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  0<powBL x = PT.rec squash₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (λ ((q , q') , q'-q<1 , q<x , x<q') →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     let q⊓q' = (minᵣ₊ (z ^ℚ q) (z ^ℚ q')) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     in PT.rec squash₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ (ε , 0<ε , ε<q⊓q') →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          PT.rec squash₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ (δ , X) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           PT.rec squash₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ (r , r-x≤δ , x≤r) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                let r' = ℚ.clamp q q' r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    r'-x≤δ = isTrans≤ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              (≤ᵣ-+o _ _ (-ᵣ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                (≤ℚ→≤ᵣ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (ℚ.clamped≤ q q' r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                               (ℚ.<Weaken≤ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                 (<ᵣ→<ℚ _ _ (isTrans<≤ᵣ _ _ _ q<x x≤r))))) ) r-x≤δ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    x≤r' = ≤min-lem _ (rat (ℚ.max q r)) (rat q')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (isTrans≤ᵣ _ _ _ x≤r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              (≤ℚ→≤ᵣ _ _ (ℚ.≤max' q r)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (<ᵣWeaken≤ᵣ _ _ x<q')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    |fx-fr|<ε = fst (∼≃abs<ε _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        (sym∼ _ _ _ (X (rat r') (sym∼ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          ((invEq (∼≃abs<ε _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (isTrans≡<ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           (absᵣNonNeg _ (x≤y→0≤y-x _ _ x≤r'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            (isTrans≤<ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                r'-x≤δ (<ℚ→<ᵣ _ _ (x/2<x δ))))))) ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    zzz =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         mid-𝒇 q r' q'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           (<ᵣWeaken≤ᵣ _ _ q<x) x≤r'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          (ℚ.clamp≤ q q' r)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    zzz' = isTrans<≤ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (isTrans<≡ᵣ _ _ _ ε<q⊓q'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                               (cong₂ minᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                 (sym (𝒇-rat _)) (sym (𝒇-rat _))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              zzz
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                in isTrans≡<ᵣ _ _ _ (sym (CRℝ.+InvR _)) (a-b<c⇒a-c<b _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (isTrans<ᵣ _ _ _ |fx-fr|<ε zzz')))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               ) (∃rationalApprox≤ x (/2₊ δ)))
         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (𝒇-cont x (ε , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<ε)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (denseℚinℝ 0 _ (snd q⊓q')) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (∃rationalApprox x 1)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  module _ (1≤z : 1 ≤ᵣ fst z) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝒇-monotone : ∀ x y → x ≤ᵣ y → 𝒇 x ≤ᵣ 𝒇 y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝒇-monotone x y x≤y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (≡Cont₂ (cont₂∘ (contNE₂ maxR) 𝒇-cont 𝒇-cont)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (cont∘₂ 𝒇-cont (contNE₂ maxR) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (ℚ.elimBy≤
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ u u' X → maxᵣComm _ _ ∙∙ X ∙∙ cong 𝒇 (maxᵣComm _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         λ u u' u≤u' →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           cong₂ maxᵣ (𝒇-rat _) (𝒇-rat _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ∙∙ ^ℚ-MonotoneR u u' u≤u' 1≤z ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             cong (fst ∘ (z ^ℚ_)) (sym (ℚ.≤→max u u' u≤u')) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            sym (𝒇-rat _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ∙ cong 𝒇 x≤y

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  module _ (1<z : 1 <ᵣ fst z) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝒇-monotone-str : ∀ x y → x <ᵣ y → 𝒇 x <ᵣ 𝒇 y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝒇-monotone-str x y = PT.rec squash₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ ((q , q') , (≤q , q<q' , q'≤)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        isTrans≤<ᵣ _ _ _ (𝒇-monotone (<ᵣWeaken≤ᵣ _ _ 1<z) x (rat q) ≤q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (isTrans<≤ᵣ _ _ _ (
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             subst2 _<ᵣ_ (sym (𝒇-rat _)) (sym (𝒇-rat _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (^ℚ-StrictMonotoneR 1<z q q' q<q'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (𝒇-monotone (<ᵣWeaken≤ᵣ _ _ 1<z) (rat q') y q'≤))
           
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- x y x≤ y≤ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --  let zz : absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ≤ᵣ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      zz = isTrans≡≤ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --             (cong absᵣ (cong₂ _-ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --                 (cong fst (^ℚ-minus z y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --                 (cong fst (^ℚ-minus z x)) ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --            (ineq'' (fromNat (suc n)) (ℚ.- x) (ℚ.- y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --             (subst (ℚ._≤ fromNat (suc n)) (ℚ.-abs x) x≤)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --             (subst (ℚ._≤ fromNat (suc n)) (ℚ.-abs y) y≤) (invℝ₊ z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --  in {!zz!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  module _ (n : ℕ) (1<z : 1 <ᵣ fst z) where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   flₙ≡𝒇 : ∀ x n → (x ∈ intervalℙ (fromNeg (suc n)) (fromNat (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             →  fst (fst (flₙ n)) x ≡ 𝒇 x 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   flₙ≡𝒇 x n x∈ = ≡Continuous (fst (fst (flₙ n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (𝒇 ∘ clampᵣ (fromNeg (suc n)) (fromNat (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (snd (flₙ n)) (IsContinuous∘ _ _ 𝒇-cont
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ r → sym (𝒇-rat _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ∙ cong 𝒇 (sym (∈ℚintervalℙ→clampᵣ≡ _ _ x x∈))



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   incr^ : isIncrasingℙᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (intervalℙ (rat (ℚ.- fromNat (suc n))) (rat (fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ x _ → fst (fst (flₙ n)) x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   incr^ x x∈ y y∈ x<y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     subst2 _<ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (sym (flₙ≡𝒇 x n x∈))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (sym (flₙ≡𝒇 y n y∈))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (𝒇-monotone-str 1<z x y x<y)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   nondecr^ : isNondecrasingℙᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (intervalℙ (rat (ℚ.- [ pos (suc n) / 1+ 0 ]))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (rat [ pos (suc n) / 1+ 0 ]))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ x _ → fst (fst (flₙ n)) x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   nondecr^ x x∈ y y∈ x≤y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     subst2 _≤ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (sym (flₙ≡𝒇 x n x∈))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (sym (flₙ≡𝒇 y n y∈))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (𝒇-monotone (<ᵣWeaken≤ᵣ _ _ 1<z) x y x≤y)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module PowBL⁻¹ (z : ℚ₊) Z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (z<Z : fst z ℚ.< fromNat (suc (suc Z)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (1/Z<z : [ 1 / 1+ (suc Z) ] ℚ.< fst z )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (1<z : 1 ℚ.< fst z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open PowBL (ℚ₊→ℝ₊ z) Z (<ℚ→<ᵣ _ _ z<Z) (<ℚ→<ᵣ _ _ 1/Z<z)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- zzz : fst (ℚ₊→ℝ₊ (invℚ₊ z)) <ᵣ rat [ pos (suc (suc Z)) / 1+ 0 ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- zzz = isTrans<≡ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --    (<ℚ→<ᵣ (fst (invℚ₊ z)) _ (fst (ℚ.invℚ₊-<-invℚ₊ _ z) 1/Z<z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --    (cong rat (ℚ.invℚ₊-invol (fromNat (suc (suc Z)))))



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- pre-bil^ : ∀ n x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     → ( fromNeg (suc n) ) ℚ.≤ x 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     → ( fromNeg (suc n) ) ℚ.≤ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     → x ℚ.≤ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     → rat (y ℚ.- x) ≤ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      rat (fst (invℚ₊ (boundℚ Z n))) ·ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      (fst (ℚ₊→ℝ₊ z ^ℚ y) -ᵣ fst (ℚ₊→ℝ₊ z ^ℚ x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- pre-bil^ n x y x∈ y∈ x≤y = {!blPow n x y ? ?!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --  where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --  wzw : {!!} ≤ᵣ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --  wzw = subst2 _≤ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     (absᵣNonPos _ {!!} ∙ {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --    (PBL⁻¹.blPow n y x {!!} {!!})


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  z^n : ∀ z n → fst ((ℚ₊→ℝ₊ z) ^ℚ (fromNat (suc n))) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            rat (fst z ℚ^ⁿ (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  z^n z zero = sym (rat·ᵣrat _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  z^n z (suc n) = cong (_·ᵣ rat (fst z)) (z^n z n) ∙ sym (rat·ᵣrat _ _)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  bil^ : boundedInvLipschitz (invℚ₊ ∘ boundℚInv Z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  bil^ n x y x∈ y∈ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    isTrans≤ᵣ _ _ _ wzw (≤ᵣ-·ᵣo _ _ _ (0≤absᵣ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      zwz)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open ExpSlopeBound (ℚ₊→ℝ₊ z) (<ℚ→<ᵣ _ _ 1<z)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   0<-b : 0 <ᵣ (-ᵣ (bound (invℝ₊ (ℚ₊→ℝ₊ z)) (fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   0<-b = subst (0 <ᵣ_) (𝐑'.-DistL· _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (ℝ₊· (_ , subst (0 <ᵣ_) (
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          cong₂ (_-ᵣ_) (cong fst (sym (invℝ₊^ℤ' (ℚ₊→ℝ₊ z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fromNat (suc n)))) ∙ sym (-ᵣInvol _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong fst (cong ((ℚ₊→ℝ₊ z) ^ℤ_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (cong (ℤ.-_ ∘  ℤ.sucℤ) (ℤ.pos+ (suc n) n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∙ sym (invℝ₊^ℤ' _ _)))
         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∙ +ᵣComm _ _ ∙ 𝐑'.-Dist _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (x<y→0<y-x _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (invEq (invℝ₊-<-invℝ₊ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (^ⁿ-StrictMonotoneR (suc n) _ (<ℚ→<ᵣ _ _ 1<z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (subst2 (ℕ._<_) (ℕ.·-identityˡ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (ℕ.·-comm 2 (suc n) ∙ cong (2 ℕ.+_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (ℕ.·-comm n 2 ∙ cong (n ℕ.+_) (ℕ.+-zero _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (ℕ.<-·sk {1} {2} {n} ℕ.≤-refl))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (ℚ₊→ℝ₊ (invℚ₊ (fromNat (suc n)))))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   wzw : 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           rat (ℚ.abs (y ℚ.- x)) ≤ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              fst (invℝ₊ (_ , 0<-b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               ·ᵣ (absᵣ (fst (ℚ₊→ℝ₊ z ^ℚ y) -ᵣ fst (ℚ₊→ℝ₊ z ^ℚ x)))
            
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   wzw = isTrans≤≡ᵣ _ _ _ (invEq (z≤x/y₊≃y₊·z≤x _ _ (_ , 0<-b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (ineqInv-abs (fromNat (suc n)) x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst (ℚ.absTo≤×≤ _ _ x∈))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst (ℚ.absTo≤×≤ _ _ y∈))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (·ᵣComm _ _)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   zwz : fst (invℝ₊ (-ᵣ bound (invℝ₊ (ℚ₊→ℝ₊ z)) (fromNat (suc n)) , 0<-b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ≤ᵣ rat (fst (invℚ₊ (boundℚInv Z n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   zwz = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isTrans≤≡ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (invEq (invℝ₊-≤-invℝ₊
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (-ᵣ bound (invℝ₊ (ℚ₊→ℝ₊ z)) (fromNat (suc n)) , 0<-b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (ℚ₊→ℝ₊ (boundℚInv Z n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (isTrans≤≡ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (isTrans≡≤ᵣ _ _ _ (rat·ᵣrat _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         (≤ᵣ-·o _ _ _ (ℚ.0≤ℚ₊ (invℚ₊ (fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          (subst2 _≤ᵣ_ pp pp'

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               hIneq
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            -- (≤ᵣ₊Monotone·ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --    (fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --      (ℚ₊→ℝ₊ ([ 1 / fromNat (2 ℕ.+ Z) ] , tt) ^ℚ (2 ℚ.· fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --    (fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --      ((invℝ₊ (ℚ₊→ℝ₊ z) .fst , invℝ₊ (ℚ₊→ℝ₊ z) .snd) ^ℚ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --       (2 ℚ.· fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --    (fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --      (ℚ₊→ℝ₊ ([ 1 / fromNat (2 ℕ.+ Z) ] , tt) ^ℚ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --       (fromNat (suc n) ℚ.- (2 ℚ.· fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --      -ᵣ 1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --    (fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --      ((invℝ₊ (ℚ₊→ℝ₊ z) .fst , invℝ₊ (ℚ₊→ℝ₊ z) .snd) ^ℚ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --       (fromNat (suc n) ℚ.- (2 ℚ.· fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --      -ᵣ 1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --    -- (<ᵣWeaken≤ᵣ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --    --  (snd ((invℝ₊ (ℚ₊→ℝ₊ z) .fst , invℝ₊ (ℚ₊→ℝ₊ z) .snd) ^ℚ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --    --     (2 ℚ.· fromNat (suc n)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            --    {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (-ᵣ· _ _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (invℝ₊-rat _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     ppLHS : _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     ppLHS = fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              (ℚ₊→ℝ₊ ([ 1 / fromNat (2 ℕ.+ Z) ] , tt) ^ℚ (2 ℚ.· fromNat (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              ·ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              (fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (ℚ₊→ℝ₊ ([ 1 / fromNat (2 ℕ.+ Z) ] , tt) ^ℚ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (fromNat (suc n) ℚ.- (2 ℚ.· fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               -ᵣ 1)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     pp'LHS : _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     pp'LHS = fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              ((invℝ₊ (ℚ₊→ℝ₊ z)) ^ℚ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (2 ℚ.· fromNat (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              ·ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              (fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               ((invℝ₊ (ℚ₊→ℝ₊ z)) ^ℚ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (fromNat (suc n) ℚ.- (2 ℚ.· fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               -ᵣ 1)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     hIneq : ppLHS ≤ᵣ pp'LHS
               
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     hIneq = ≤ᵣ₊Monotone·ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (<ᵣWeaken≤ᵣ _ _ (snd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          (invℝ₊ (ℚ₊→ℝ₊ z) ^ℚ (2 ℚ.· [ pos (suc n) / 1+ 0 ]))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (x≤y→0≤y-x 1 (fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                     ((ℚ₊→ℝ₊ ([ 1 / fromNat (2 ℕ.+ Z) ] , tt))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                      ^ℚ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                      (fromNat (suc n) ℚ.- ((2 ℚ.· fromNat (suc n))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (subst2 _≤ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         (cong fst (sym (invℝ₊^ℚ (ℚ₊→ℝ₊ (fromNat (2 ℕ.+ Z))) (2 ℚ.· fromNat (suc n)))) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           cong (fst ∘ (_^ℚ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              (2 ℚ.· fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (ℝ₊≡ (invℝ₊-rat _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         (cong fst (sym (invℝ₊^ℚ _ _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         (invEq (invℝ₊-≤-invℝ₊ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           (^ℚ-Monotone ((2 ℚ· fromNat (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ z<Z)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (≤ᵣ-+o _ _ (-1) {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     pp : ppLHS ≡ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     pp = (sym (factor-xᵃ-xᵇ (ℚ₊→ℝ₊ ([ 1 / fromNat (2 ℕ.+ Z) ] , _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                    (fromNat (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                    (2 ℚ.· fromNat (suc n))) ∙ (cong₂ _-ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 (^ⁿ-ℚ^ⁿ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 (cong (λ q →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                       fst (ℚ₊→ℝ₊ ([ 1 / fromNat (2 ℕ.+ Z) ] , tt) ^ℚ q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                        (ℚ.ℕ·→ℚ· _ _) ∙ ^ⁿ-ℚ^ⁿ _ _)))
             

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     pp' : pp'LHS ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              -ᵣ (fst (invℝ₊ (ℚ₊→ℝ₊ z) ^ℚ (2 ℚ.· fst (fromNat (suc n)))) -ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                         fst (invℝ₊ (ℚ₊→ℝ₊ z) ^ℚ fst (fromNat (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     pp' = (sym (factor-xᵃ-xᵇ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (fromNat (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (2 ℚ.· fromNat (suc n))) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 {!!}) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     -- ineq1 : 0 ≤ᵣ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     --            fst ((invℝ₊ (ℚ₊→ℝ₊ z)) ^ℚ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     --             (2 ℚ.· fromNat (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     -- ineq1 = <ᵣWeaken≤ᵣ _ _ {!!}
      
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  approx-^ : ℚApproxℙ' ⊤Pred (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ x _ → 𝒇 x , 0<powBL x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  approx-^ y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       let ((p , q) , (_ , p/q≡y)) = ℚ.reduced y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       in subst (λ y → (q∈P : rat y ∈ ⊤Pred) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ℚApproxℙ'Num ⊤Pred (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (λ x _ → 𝒇 x , 0<powBL x) y q∈P)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            p/q≡y (w p q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w : ∀ p q → (q∈P : rat [ p / q ] ∈ ⊤Pred)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → ℚApproxℙ'Num ⊤Pred (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (λ x _ → 𝒇 x , 0<powBL x) [ p / q ] q∈P 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w p q q∈P =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        fst wwW
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , fst (snd wwW)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , fst (snd (snd wwW))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , snd (snd (snd wwW)) ∙∙ cong fst (sym (pow-root-comm (ℚ₊→ℝ₊ z) p q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ∙∙ sym (𝒇-rat [ p / q ])

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      www : ℚApproxℙ' (λ x → (0 <ᵣ x) , squash₁) (λ x → (0 <ᵣ x) , squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (curry
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (((λ p₁ → fst (root q (p₁ .fst , p₁ .snd)) , root q p₁ .snd))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ∘ uncurry (curry (_^ℤ p))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      www = ℚApproxℙ''→ℚApproxℙ' _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (ℚApproxℙ∘ (λ x → (0 <ᵣ x) , squash₁) _ (λ x → (0 <ᵣ x) , squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (curry (root q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (curry (_^ℤ p))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (uContRoot q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (ℚApproxℙ'→ℚApproxℙ'' _ _ _ (ℚApproxℙ-root q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (^ℤ-ℚApproxℙ'' p)) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      wwW = www (fst z) (snd (ℚ₊→ℝ₊ z))

            
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open BoundedInvLipsch (invℚ₊ ∘ boundℚInv Z) bil^


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  module _ (n : ℕ) where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open IsBilipschitz' (ℚ.- (fromNat (suc n))) (fromNat (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (ℚ.<ℤ→<ℚ _ _ ℤ.negsuc<pos)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ x _ → fst (fst (flₙ n)) x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (AsContinuousWithPred _ _ (snd (flₙ n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (incr^ n (<ℚ→<ᵣ _ _ 1<z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (nondecr^  n (<ℚ→<ᵣ _ _ 1<z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fa' = fst (invℚ₊ z) ℚ^ⁿ suc n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fa≡ : fa ≡ rat fa'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fa≡ =  flₙ≡𝒇 n (<ℚ→<ᵣ _ _ 1<z) (fromNeg (suc n)) n a∈
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∙ 𝒇-rat (fromNeg (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∙ cong fst (^ℚ-minus (ℚ₊→ℝ₊ z) (fromNeg (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ cong (_^ℚ fromNat (suc n)) (ℝ₊≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (invℝ₊≡invℝ (ℚ₊→ℝ₊ z) (inl (snd (ℚ₊→ℝ₊ z)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ∙ invℝ-rat _ _ (inl (ℚ.0<ℚ₊ z)) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              cong rat (ℚ.invℚ₊≡invℚ _ _))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∙ z^n (invℚ₊ z) n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fb' = (fst z ℚ^ⁿ suc n)
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fb≡ : fb ≡ rat fb'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fb≡ =  flₙ≡𝒇 n (<ℚ→<ᵣ _ _ 1<z) (fromNat (suc n)) n b∈
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ∙ 𝒇-rat _ ∙ z^n z n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fa'≤fb' : fa' ℚ.≤ fb'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fa'≤fb' = ℚ.isTrans≤ _ 1 _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (ℚ.x^ⁿ≤1 _ (suc n) (ℚ.0≤ℚ₊ (invℚ₊ z)) (fst (ℚ.invℚ₊-≤-invℚ₊ 1 z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (ℚ.<Weaken≤ 1 (fst z) 1<z)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (ℚ.1≤x^ⁿ _ (suc n) (ℚ.<Weaken≤ 1 (fst z) 1<z) ) 
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   approx-^ℙ : ℚApproxℙ'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ((intervalℙ (rat (ℚ.- fromNat (suc n))) (rat (fromNat (suc n)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (intervalℙ fa fb)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      f'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   approx-^ℙ x x∈ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ℚ.clamp (fst (invℚ₊ z) ℚ^ⁿ suc n) (fst z ℚ^ⁿ suc n) ∘ fst ww
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     , (λ ε → subst2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ fa fb →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (rat (ℚ.clamp (fst (invℚ₊ z) ℚ^ⁿ suc n) (fst z ℚ^ⁿ suc n) (fst ww ε)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∈ (intervalℙ fa fb))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (sym fa≡ ) (sym fb≡)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (∈ℚintervalℙ→∈intervalℙ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (clam∈ℚintervalℙ fa' fb' fa'≤fb' (fst ww ε)) ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     , (λ δ ε → invEq (∼≃abs<ε _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          let u = (<ᵣ→<ℚ _ _ (fst (∼≃abs<ε _ _ _) (fst (snd (snd ww)) δ ε)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          in <ℚ→<ᵣ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (ℚ.isTrans≤< _ _ _ (
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   subst2 ℚ._≤_ (ℚ.abs'≡abs _) (ℚ.abs'≡abs _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (ℚ.clampDist _ _ _ _) ) u))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     , ssw

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ww = approx-^ x _


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     z^clmp-x = fst (ℚ₊→ℝ₊ z ^ℚ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ℚ.clamp (ℚ.- [ pos (suc n) / 1+ 0 ]) [ pos (suc n) / 1+ 0 ] x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ssww' : lim (λ x₁ → rat (fst ww x₁)) _ ≡ z^clmp-x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ssww' = snd (snd (snd ww))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∙ 𝒇-rat _ ∙ cong (fst ∘ (ℚ₊→ℝ₊ z ^ℚ_))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (∈ℚintervalℙ→clam≡ _ _ x (∈intervalℙ→∈ℚintervalℙ _ _ _ x∈))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ssw-lem1 : fst (ℚ₊→ℝ₊ z ^ℚ [ ℤ.negsuc n / 1+ 0 ]) ≤ᵣ z^clmp-x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ssw-lem1 = ((^ℚ-MonotoneR {ℚ₊→ℝ₊ z} (fromNeg (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                  (ℚ.clamp (ℚ.- [ pos (suc n) / 1+ 0 ]) [ pos (suc n) / 1+ 0 ] x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                    (ℚ.≤clamp _ _ _ (ℚ.neg≤pos (suc n) (suc n))) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                 (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ 1<z))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ssw-lem2 : z^clmp-x ≤ᵣ fst (ℚ₊→ℝ₊ z ^ℚ [ pos (suc n) / 1+ 0 ])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ssw-lem2 = ((^ℚ-MonotoneR {ℚ₊→ℝ₊ z} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                  (ℚ.clamp (ℚ.- [ pos (suc n) / 1+ 0 ]) [ pos (suc n) / 1+ 0 ] x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                   (fromNat (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                   (ℚ.clamp≤ (ℚ.- [ pos (suc n) / 1+ 0 ]) _ x) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                 (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ 1<z))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ssw : lim (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   rat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (ℚ.clamp (fst (invℚ₊ z) ℚ^ⁿ suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (fst z ℚ^ⁿ suc n) (fst ww x₁))) _ ≡ z^clmp-x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ssw = invEq (lim≡≃∼ _ _ _) λ ε →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         let zz = isTrans≡≤ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (sym (cong absᵣ (cong₂ _-ᵣ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (clamp-lim _ _ _ (fst (snd (snd ww)))  ∙ congLim _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       (λ _ → refl) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          (sym (∈ℚintervalℙ→clampᵣ≡ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            ( (isTrans≡≤ᵣ _ _ _ (sym (z^n ((invℚ₊ z)) _) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                               cong fst (^ℚ-minus _ _ ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                 cong {y = ℚ₊→ℝ₊ z} (_^ℚ (fromNeg (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                    (cong invℝ₊ (ℝ₊≡ (sym (invℝ₊-rat _))) ∙ invℝ₊Invol _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                ssw-lem1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            , isTrans≤≡ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                ssw-lem2 (z^n _ _)))))))
                 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  ((clampDistᵣ' ((fst (invℚ₊ z) ℚ^ⁿ (suc n))) ((fst z ℚ^ⁿ (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     z^clmp-x (lim (λ x₁ → rat (fst ww x₁)) _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         in isTrans≤<ᵣ _ _ _ zz (fst (lim≡≃∼ _ _ _) ssww' ε)
    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   zzzz : fst (invℚ₊ (invℚ₊ (boundℚInv Z n))) ℚ.≤ fst (boundℚ Z n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   zzzz = subst (ℚ._≤ fst (boundℚ Z n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (sym (ℚ.invℚ₊-invol (boundℚInv Z n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (ℚ.<Weaken≤ _ _ (boundℚInv<boundℚ Z n))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   lipₙ : Lipschitz-ℝ→ℝℙ (boundℚ Z n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((intervalℙ (rat (ℚ.- fromNat (suc n))) (rat (fromNat (suc n)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ x _ → fst (fst (flₙ n)) x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   lipₙ u _ v _ = snd (fst (flₙ n)) u v
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Inv 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          approx-^ℙ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (boundℚ Z n) (invℚ₊ (boundℚInv Z n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          lipₙ zzzz
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (invLipFₙ n) public


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module Powᵣ (y : ℝ) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ff : (z : ℝ) (Z : ℕ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       z ∈ ointervalℙ (rat  [ 1 / 1+ (suc Z) ]) (fromNat (suc (suc Z)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        → ℝ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ff z Z (<z , z<) = PowBL.𝒇 (z , isTrans<ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) <z) Z  z< <z y



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  0<ff : ∀ x n x∈ → rat [ pos 0 / 1+ 0 ] <ᵣ ff x n x∈
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  0<ff z Z (<z , z<) = PowBL.0<powBL (z , isTrans<ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) <z) Z  z< <z y
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pow-seq⊆1< : Seq⊆
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pow-seq⊆1< .Seq⊆.𝕡 Z = ointervalℙ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (rat  [ 1 / 1+ (suc Z) ]) (fromNat (suc (suc Z)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pow-seq⊆1< .Seq⊆.𝕡⊆ Z _ (<z , z<) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      isTrans≤<ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (≤ℚ→≤ᵣ _ _ (ℚ.invℚ₊≤invℚ₊
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ([ pos (suc (suc (suc Z))) / 1 ] , _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ([ pos (suc (suc Z)) / 1 ] , _)  h))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        <z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    , isTrans<≤ᵣ _ _ _ z<
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (≤ℚ→≤ᵣ _ _ h)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   h = (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.≤-sucℕ))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pow-seq⊆→ : Seq⊆→ ℝ pow-seq⊆1<
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pow-seq⊆→ .Seq⊆→.fun = ff 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pow-seq⊆→ .Seq⊆→.fun⊆ x n m x∈ x∈' n<m =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong (λ 0<x → PowBL.𝒇 (x , 0<x) n _ _ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (squash₁ _ _) ∙ boundedLipsch-coh _ (boundℚ n) (boundℚ m)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ((PowBL.blPow _ n (x∈ .snd) (x∈ .fst)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pos⊆pow-seq⊆1< : pow-seq⊆1< Seq⊆.s⊇
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pos⊆pow-seq⊆1< x 0<x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    PT.map2 (λ (1+ N , x<N) (1+ N' , 1/x<N') →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ℕ.max (suc N) (suc N') ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        subst2 _<ᵣ_ (·IdR _) (·IdR _) (fst (z/y'<x/y≃y₊·z<y'₊·x 1 1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (ℚ₊→ℝ₊ ([ 1 / fromNat (3 ℕ.+ ℕ.max N N')] , _)) (x , 0<x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (subst2 _<ᵣ_ (sym (·IdL _)) (sym (·IdL _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (isTrans<ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ((isTrans≤<ᵣ _ _ _ (≤absᵣ _) 1/x<N'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (isTrans<≡ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ((<ℚ→<ᵣ (fromNat (1 ℕ.+ N'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (fromNat _) (ℚ.<ℤ→<ℚ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (ℤ.ℕ≤→pos-≤-pos (2 ℕ.+ N') _ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (ℕ.≤-trans ℕ.≤-sucℕ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (ℕ.right-≤-max {3 ℕ.+ N'} {3 ℕ.+ N} ))))) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (cong fst (sym (invℝ₊Invol _) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      cong (invℝ₊) (ℝ₊≡ (invℝ'-rat _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       ((<ℚ→<ᵣ 0 (fromNat (3 ℕ.+ (max N N')))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           (ℚ.0<pos _ _)))))))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        , (isTrans<ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (isTrans≤<ᵣ _ _ _ (≤absᵣ _) x<N)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (<ℚ→<ᵣ _ _ (ℚ.<ℤ→<ℚ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (ℤ.ℕ≤→pos-≤-pos _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (ℕ.≤-trans ℕ.≤-sucℕ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (ℕ.left-≤-max {3 ℕ.+ N} {3 ℕ.+ N'} )))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (getClamps x) (getClamps (fst (invℝ₊ (x , 0<x))))  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open Seq⊆→.FromIntersection pow-seq⊆→
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        isSetℝ (λ x → (0 <ᵣ x ) , squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         pos⊆pow-seq⊆1< public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pre^ : ℝ₊ → ℝ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pre^ = uncurry ∩$

 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pre^-rat : ∀ x q → y ≡ rat q → pre^ x ≡ fst (x ^ℚ q)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pre^-rat (x , 0<x) q p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PT.rec (isSetℝ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ (Z , (<z , z<) , v) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       v ∙ cong (PowBL.𝒇 (x , isTrans<ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) <z) Z  z< <z) p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∙ PowBL.𝒇-rat (x , isTrans<ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) <z) Z  z< <z q
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∙ (cong (fst ∘ (_^ℚ q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (ℝ₊≡ {(x ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              isTrans<ᵣ (rat [ pos 0 / 1+ 0 ]) (rat [ pos 1 / 2+ Z ]) x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (<ℚ→<ᵣ [ pos 0 / 1+ 0 ] [ pos 1 / 2+ Z ] (ℚ.0<pos 0 (2+ Z))) <z)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              {x , 0<x}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               refl)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (∩$-lem x 0<x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pre^-pos : ∀ x → 0 <ᵣ pre^ x 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  pre^-pos (x , 0<x) = ∩$-elimProp x 0<x  {0 <ᵣ_} (λ _ → squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (0<ff x)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _^ʳ_ : ℝ₊ → ℝ → ℝ₊
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- x ^ʳ y = _ , Powᵣ.pre^-pos y x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsContinuous^ʳ : ∀ x → IsContinuous (fst ∘ (x ^ʳ_))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsContinuous^ʳ (x , 0<x) y ε =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PT.rec squash₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ (Z , (<z , z<) , v) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        PT.map
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ (δ , X) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             δ , λ y' y∼y' →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               subst2 (_∼[ ε ]_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (sym v)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (sym (Powᵣ.∩$-∈ₙ y' x 0<x Z (<z , z<)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (X y' y∼y')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (PowBL.𝒇-cont (x , isTrans<ᵣ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) <z) Z  z< <z y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ε))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (Powᵣ.∩$-lem y x 0<x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ^ʳ-rat : ∀ x y → x ^ʳ (rat y) ≡ (x ^ℚ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ^ʳ-rat x y = ℝ₊≡ (Powᵣ.pre^-rat (rat y) x y refl)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- +IsGroup : IsGroup 0 _+ᵣ_ (-ᵣ_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- +IsGroup = CRℝ.+IsGroup

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ·IsGroup : IsGroup 1 _₊·ᵣ_ invℝ₊
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ·IsGroup = makeIsGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isSetℝ₊
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (λ _ _ _ → ℝ₊≡ (·ᵣAssoc _ _ _ ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (λ _ → ℝ₊≡ (·IdR _)) (λ _ → ℝ₊≡ (·IdL _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (λ (x , 0<x) → ℝ₊≡ (·invℝ' x 0<x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (λ (x , 0<x) → ℝ₊≡ (·ᵣComm _ _ ∙ ·invℝ' x 0<x))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ^ʳ-at1-split : ∀ (x : ℝ₊) y → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ^ʳ-at1-split = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (z : ℚ₊)  where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (1≤z : 1 ≤ᵣ rat (fst z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ( ^ʳ-MonotoneR : (q r : ℝ) → q ≤ᵣ r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               → fst ((ℚ₊→ℝ₊ z) ^ʳ q) ≤ᵣ fst ((ℚ₊→ℝ₊ z) ^ʳ r))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ^ʳ-MonotoneR  q r q≤r 1≤x = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ^ʳ-ℚApprox' : (a : ℚ₊) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ^ʳ-ℚApprox' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ^ʳ-ℚApprox : ℚApproxℙ' ⊤Pred
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (λ x → (0 <ᵣ x) , squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (λ x x∈ → (ℚ₊→ℝ₊ z) ^ʳ x )

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ^ʳ-ℚApprox y = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    let ((p , q) , (_ , p/q≡y)) = ℚ.reduced y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    in subst (λ y → (q∈P : rat y ∈ ⊤Pred) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ℚApproxℙ'Num _ _ (λ v _ → ℚ₊→ℝ₊ z ^ʳ v) y q∈P)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         p/q≡y (w p q)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w : ∀ p q → (q∈P : rat [ p / q ] ∈ ⊤Pred)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → ℚApproxℙ'Num _ _ (λ v _ → ℚ₊→ℝ₊ z ^ʳ v) [ p / q ] q∈P 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w p q q∈P =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        fst wwW
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , fst (snd wwW)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , fst (snd (snd wwW))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , snd (snd (snd wwW)) ∙ cong fst pp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     www : ℚApproxℙ' (λ x → (0 <ᵣ x) , squash₁) (λ x → (0 <ᵣ x) , squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (curry
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (((λ p₁ → fst (root q (p₁ .fst , p₁ .snd)) , root q p₁ .snd))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               ∘ uncurry (curry (_^ℤ p))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     www = ℚApproxℙ''→ℚApproxℙ' _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (ℚApproxℙ∘ (λ x → (0 <ᵣ x) , squash₁) _ (λ x → (0 <ᵣ x) , squash₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (curry (root q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (curry (_^ℤ p))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (uContRoot q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (ℚApproxℙ'→ℚApproxℙ'' _ _ _ (ℚApproxℙ-root q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (^ℤ-ℚApproxℙ'' p)) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     wwW = www (fst z) (snd (ℚ₊→ℝ₊ z))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     pp : (curry
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ((λ p₁ → fst (root q (p₁ .fst , p₁ .snd)) , root q p₁ .snd) ∘
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         uncurry (curry (_^ℤ p)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (rat (fst z)) (snd (ℚ₊→ℝ₊ z))) ≡ (ℚ₊→ℝ₊ z ^ʳ rat [ p / q ])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     pp = (sym (pow-root-comm (ℚ₊→ℝ₊ z) p q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ∙ sym (^ʳ-rat (ℚ₊→ℝ₊ z) [ p / q ]))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  module _ (z : ℚ₊) (1<z : 1 <ᵣ rat (fst z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (a₊ : ℚ₊) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   a = fst a₊

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Lipschitz-^ʳ : Lipschitz-ℝ→ℝℙ {!!} (intervalℙ (rat (ℚ.- a)) (rat a)) {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Lipschitz-^ʳ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ^-+ : ∀ x a b → fst ((x ^ʳ a) ₊·ᵣ (x ^ʳ b)) ≡ fst (x ^ʳ (a +ᵣ b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ^-+ x a =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ≡Continuous _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ^-· : ∀ x a b → fst ((x ^ʳ a) ^ʳ b) ≡ fst (x ^ʳ (a ·ᵣ b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ^-· x = {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ≡Continuous _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- x^-groupMorphism : ∀ x → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IsGroupHom (groupstr _ _ _ +IsGroup)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (x  ^ʳ_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (groupstr _ _ _ ·IsGroup)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- x^-groupMorphism x = makeIsGroupHom
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open BoundedLipsch {!!} {!!} {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso^ʳ : ∀ y → 0 ＃ y  → Iso ℝ₊ ℝ₊
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso^ʳ y 0＃y .Iso.fun = _^ʳ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso^ʳ y 0＃y .Iso.inv = _^ʳ (invℝ (y , 0＃y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso^ʳ y 0＃y .Iso.rightInv (x , 0<x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ℝ₊≡ (^-· _ _ _ ∙ ?)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso^ʳ y 0＃y .Iso.leftInv = {!!}
