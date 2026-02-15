module Cubical.HITs.CauchyReals.NthRoot where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Nat.Order.Inductive as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Fast.Int as ℤ using (pos; ℤ; sucℤ)
import Cubical.Data.Fast.Int.Order as ℤ

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding ([_])

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals.Fast as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Fast.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡ ; [_/_]₊)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base

open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Bisect


open import Cubical.Tactics.CommRingSolverFast.RationalsReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection
open import Cubical.Tactics.CommRingSolverFast.IntReflection
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.Tactics.CommRingSolverFast.RealsReflection

sqrRestr< : ∀ n → (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) ℚ.< (fromNat (2 ℕ.+ n))
sqrRestr< n =
  (ℚ.isTrans< (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) 1 (fromNat (2 ℕ.+ n))
               (fst (ℚ.invℚ₊-<-invℚ₊ 1 ([ (1+ (suc n)) / 1 ]₊))
                 (ℚ.inj (ℤ.Σℕ→< (_ , refl))))
               (ℚ.inj (ℤ.Σℕ→< (_ , refl))))

module NthRoot (m : ℕ) where


 module _ (n : ℕ) where


  open bⁿ-aⁿ m hiding (n)


  A B : ℝ
  A = rat (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
  B = (fromNat (2 ℕ.+ n))
  0<A = (snd (ℚ₊→ℝ₊ (invℚ₊ (fromNat (2 ℕ.+ n)))))
  0<B = (snd (ℚ₊→ℝ₊ (fromNat (2 ℕ.+ n))))
  A<B : A <ᵣ B
  A<B = <ℚ→<ᵣ _ _ (sqrRestr< n)



  L = (((fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m))
      ℚ₊· (fromNat (2 ℕ.+ m)))

  K = (fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m)

  incrF : isIncrasingℙ
   (ℚ.ℚintervalℙ (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
               (fromNat (2 ℕ.+ n))) (λ x _ → x ℚ^ⁿ (2 ℕ.+ m))
  incrF  x x∈ y y∈ =
    ℚ^ⁿ-StrictMonotone (2 ℕ.+ m)
     (ℕ.≤-suc (ℕ.suc-≤-suc (ℕ.zero-≤ {m})))
     (ℚ.isTrans≤ 0 (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
          x (ℚ.0≤ℚ₊ (invℚ₊ (fromNat (2 ℕ.+ n)))) (fst x∈))
     (ℚ.isTrans≤ 0 (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
          y (ℚ.0≤ℚ₊ (invℚ₊ (fromNat (2 ℕ.+ n)))) (fst y∈))

  1/K<L : fst (invℚ₊ K) ℚ.< fst L
  1/K<L = ℚ.isTrans≤< _ 1 _
    (subst (ℚ._≤ 1) (sym (ℚ.invℚ₊-ℚ^ⁿ ([ (1+ (suc n)) / 1 ]₊) (suc m)))
      (ℚ.x^ⁿ≤1 _ (suc m) (ℚ.0≤pos _ _)
       (fst (ℚ.invℚ₊-≤-invℚ₊ 1 (fromNat (2 ℕ.+ n)))
        (ℚ.≤ℤ→≤ℚ _ _ (ℤ.pos≤pos tt)))))
         (ℚ.isTrans≤< _ _ _
           (ℚ.1≤x^ⁿ (fromNat (2 ℕ.+ n))
            (fromNat (1 ℕ.+ m)) ((ℚ.≤ℤ→≤ℚ _ _ (ℤ.pos≤pos tt))))
            (subst (ℚ._< fst L)

               (ℚ.·IdR _)
                 (ℚ.<-o· 1 (fromNat (2 ℕ.+ m))
                   _ (ℚ.0<ℚ₊ ((fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m)))
            ((ℚ.<ℤ→<ℚ 1 (ℤ.pos (suc (suc m)))
             (ℤ.pos<pos tt)))))
            )


  rootRest : IsBilipschitz
               (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
               (fromNat (2 ℕ.+ n))
               (sqrRestr< n)
               λ x _ → x ℚ^ⁿ (2 ℕ.+ m)
  rootRest .IsBilipschitz.incrF = incrF
  rootRest .IsBilipschitz.L = L
  rootRest .IsBilipschitz.K = K
  rootRest .IsBilipschitz.1/K≤L = ℚ.<Weaken≤ _ _ 1/K<L

  rootRest .IsBilipschitz.lipF =
    Lipschitz-ℚ→ℝℙ<→Lipschitz-ℚ→ℝℙ ((ℚ.[ pos (suc (suc n)) , (1+ 0) ] ℚ^ⁿ m) ℚ.·
                                     ℚ.[ pos (suc (suc n)) , (1+ 0) ]
                                     ℚ.· ℚ.[ pos (suc (suc m)) , (1+ 0) ]
                                     ,
                                     ℚ.·0< (fst (([  (1+ (suc n)) / (1+ 0) ]₊) ℚ₊^ⁿ suc m))
                                     ℚ.[ pos (suc (suc m)) , (1+ 0) ]
                                     (snd (([ (1+ (suc n)) / (1+ 0) ]₊) ℚ₊^ⁿ suc m)) (ℚ.0<pos _ _))
                                  (λ z →
                                      (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) ≤ᵣ z) ×
                                      (z ≤ᵣ rat (fromNat (2 ℕ.+ n)))
                                      ,
                                      isProp× (isProp≤ᵣ (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n))))) z)
                                      (isProp≤ᵣ z (rat (fromNat (2 ℕ.+ n))))) _
      λ q q∈ r r∈ r<q  →
       let 0<r : 0 <ᵣ (rat r)
           0<r = isTrans<≤ᵣ 0 A (rat r) 0<A (fst r∈)
           0<q : 0 <ᵣ (rat q)
           0<q = isTrans<ᵣ 0 (rat r) (rat q) 0<r (<ℚ→<ᵣ _ _ r<q)

           ineqL : (rat q ^ⁿ suc (suc m)) -ᵣ (rat r ^ⁿ suc (suc m))
                      ≤ᵣ rat ((fst L) ℚ.· (q ℚ.- r))

           ineqL =
             isTrans≡≤ᵣ _ _ _ (sym $
                  [b-a]·S≡bⁿ-aⁿ (rat r) (rat q)
                     0<r 0<q)
               (isTrans≤≡ᵣ _ _ _ (≤ᵣ-o·ᵣ _ _ _
                      (isTrans≤≡ᵣ _ _ _  (≤ℚ→≤ᵣ _ _  $ ℚ.<Weaken≤ _ _ (ℚ.<→<minus _ _ r<q))
                       (sym (-ᵣ-rat₂ _ _))) --
                    (isTrans≤≡ᵣ _ _ _
               (S≤Bⁿ·n (rat r) (rat q) 0<r 0<q A B 0<A
                     (isTrans≤<ᵣ _ _ _
                       (fst r∈ ) (<ℚ→<ᵣ _ _ r<q)) 0<B A<B
                  (snd q∈)
                  (<ℚ→<ᵣ _ _ r<q))
                      (sym ((rat·ᵣrat ([ pos (2 ℕ.+ n) / 1 ] ℚ^ⁿ suc m) (fromNat (2 ℕ.+ m))
                        ∙ cong (_·ᵣ (rat ((fromNat (2 ℕ.+ m)))))
                          (sym (^ⁿ-ℚ^ⁿ (suc m) [ pos (2 ℕ.+ n) / 1 ])))))
                          ))
                           (cong₂ _·ᵣ_ (-ᵣ-rat₂ _ _) refl ∙ (sym (rat·ᵣrat _ _) ∙
                            (cong rat (ℚ.·Comm (q ℚ.- r)
                             (([ pos (2 ℕ.+ n) / 1 ] ℚ^ⁿ suc m) ℚ.· fromNat (2 ℕ.+ m)))))) --
                           )


       in isTrans≡≤ᵣ _ _ _ (cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣPos _
            (<ℚ→<ᵣ _ _  (ℚ.<→<minus _ _ (incrF r
                     (∈intervalℙ→∈ℚintervalℙ _ _ _ r∈)
                     q
                     (∈intervalℙ→∈ℚintervalℙ _ _ _ q∈)
                     r<q)))
                 ∙ sym (-ᵣ-rat₂ (q ℚ^ⁿ (2 ℕ.+ m)) (r ℚ^ⁿ (2 ℕ.+ m)))  ∙ cong₂ _-ᵣ_
                   (sym (^ⁿ-ℚ^ⁿ (2 ℕ.+ m) q))
                   (sym (^ⁿ-ℚ^ⁿ (2 ℕ.+ m) r ))) ineqL

  rootRest .IsBilipschitz.lip⁻¹F =
    Invlipschitz-ℚ→ℚℙ'<→Invlipschitz-ℚ→ℚℙ
     ((fromNat (2 ℕ.+ n) .fst ℚ^ⁿ m) ℚ.· fromNat (2 ℕ.+ n) .fst ,
         ℚ.0<ℚ^ⁿ (fromNat (2 ℕ.+ n) .fst) (fromNat (2 ℕ.+ n) .snd) (suc m))
         (λ z →
             Σ (fst (invℚ₊ (fromNat (2 ℕ.+ n))) ℚ.≤ z)
             (λ _ → z ℚ.≤ [ pos (2 ℕ.+ n) / 1 ])
             ,
             isProp× (ℚ.isProp≤ (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) z)
             (ℚ.isProp≤ z (fromNat (2 ℕ.+ n))))
         (λ x _ → x ℚ^ⁿ (2 ℕ.+ m))
       λ q q∈ r r∈ r<q →
          let r∈' = (∈ℚintervalℙ→∈intervalℙ _ _ _ r∈)
              q∈' = (∈ℚintervalℙ→∈intervalℙ
                      (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) _ _ q∈)
              0<r : 0 <ᵣ (rat r)
              0<r = isTrans<≤ᵣ 0 A (rat r) 0<A (fst r∈')
              0<q : 0 <ᵣ (rat q)
              0<q = isTrans<ᵣ 0 (rat r) (rat q) 0<r (<ℚ→<ᵣ _ _ r<q)

          in ℚ.x·invℚ₊y≤z→x≤y·z _ _ ((fromNat (2 ℕ.+ n) .fst ℚ^ⁿ m) ℚ.· fromNat (2 ℕ.+ n) .fst ,
                                      ℚ.0<ℚ^ⁿ (fromNat (2 ℕ.+ n) .fst) (fromNat (2 ℕ.+ n) .snd) (suc m)) (≤ᵣ→≤ℚ _ _
                $ isTrans≡≤ᵣ _ _ _ (cong rat
                  (cong ((q ℚ.+ ℚ.- r) ℚ.·_)
                    (ℚ.invℚ₊-ℚ^ⁿ (fromNat (2 ℕ.+ n)) (suc m)) )
                  ∙ rat·ᵣrat _ _) $
                isTrans≤≡ᵣ _ _ _
                  (≤ᵣ-o·ᵣ _ _ _
                        (≤ℚ→≤ᵣ _ _  $ ℚ.<Weaken≤ _ _ (ℚ.<→<minus _ _ r<q))
                  (isTrans≡≤ᵣ _ _ _
                     (sym (^ⁿ-ℚ^ⁿ (suc m) (fst (invℚ₊ (fromNat (2 ℕ.+ n))))))
                             (Aⁿ≤S (rat r) (rat q) 0<r 0<q
                              A B 0<A
                              (isTrans≤<ᵣ _ _ _
                                (fst r∈' ) (<ℚ→<ᵣ _ _ r<q))
                              0<B A<B
                             (snd q∈')
                             (<ℚ→<ᵣ _ _ r<q))
                             ))
                    (cong₂ _·ᵣ_ (sym (-ᵣ-rat₂ _ _)) refl ∙ [b-a]·S≡bⁿ-aⁿ (rat r) (rat q) 0<r 0<q
                       ∙
                      cong₂ _-ᵣ_ (^ⁿ-ℚ^ⁿ (2 ℕ.+ m) q)
                       (^ⁿ-ℚ^ⁿ (2 ℕ.+ m) r)
                      ∙ -ᵣ-rat₂ (q ℚ^ⁿ (2 ℕ.+ m)) (r ℚ^ⁿ (2 ℕ.+ m)) ∙ cong rat (sym (ℚ.absPos _
                      (ℚ.<→<minus _ _ (incrF r r∈ q q∈ r<q))) ∙
                       ℚ.abs'≡abs ((q ℚ^ⁿ (2 ℕ.+ m)) ℚ.- (r ℚ^ⁿ (2 ℕ.+ m)))))
                       )




 loB hiB : ∀ n → ℚ
 loB n = (((fst (invℚ₊ (fromNat (2 ℕ.+ n))))) ℚ^ⁿ (2 ℕ.+ m))
 hiB n = ((fromNat (2 ℕ.+ n)) ℚ^ⁿ (2 ℕ.+ m))

 loB-mon : ∀ n → loB (suc n) ℚ.< loB n
 loB-mon n = (
     (ℚ^ⁿ-StrictMonotone (2 ℕ.+ m) (ℕ.suc-≤-suc ℕ.zero-≤)
      (ℚ.0≤ℚ₊ [ 1 / (1+ (suc (suc n))) ]₊) (ℚ.0≤ℚ₊ [ 1 / (1+ (suc n)) ]₊)
      (fst (ℚ.invℚ₊-<-invℚ₊
    (fromNat (2 ℕ.+ n)) (fromNat (3 ℕ.+ n)))
      (ℚ.<ℤ→<ℚ _ _ (ℤ.pos<pos (ℕ.<ᵗsucm {n}))))))

 hiB-mon : ∀ n → hiB n ℚ.< hiB (suc n)
 hiB-mon n = ℚ^ⁿ-StrictMonotone (2 ℕ.+ m)
        (ℕ.suc-≤-suc ℕ.zero-≤) (ℚ.0≤ℚ₊ [ 1+ (suc n) / 1 ]₊) (ℚ.0≤ℚ₊ ([ (1+ (1 ℕ.+ suc n)) / 1 ]₊))
      (ℚ.<ℤ→<ℚ _ _ (ℤ.pos<pos (ℕ.<ᵗsucm {n})))

 rootSeq⊆ : Seq⊆
 rootSeq⊆ .Seq⊆.𝕡 n = intervalℙ
   (rat (loB n))
   (rat (hiB n))
 rootSeq⊆ .Seq⊆.𝕡⊆ n x (≤x , x≤) =
   isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (loB-mon n))) ≤x ,
   isTrans≤ᵣ _ _ _ x≤ (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (hiB-mon n)))




 f⊆ : (x : ℝ) (n n' : ℕ) →
      (ib : IsBilipschitz (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) (fromNat (2 ℕ.+ n))
        (sqrRestr< n) (λ x₁ _ → x₁ ℚ^ⁿ (2 ℕ.+ m)))
      (ib' : IsBilipschitz (fst (invℚ₊ (fromNat (2 ℕ.+ n'))))
         (fromNat (2 ℕ.+ n')) (sqrRestr< n') (λ x₁ _ → x₁ ℚ^ⁿ (2 ℕ.+ m))) →
      (x∈ : x ∈ intervalℙ (rat (loB n)) (rat (hiB n)))
      (x∈' : x ∈ intervalℙ (rat (loB n')) (rat (hiB n'))) →
      n ℕ.< n' →
      IsBilipschitz.𝒇⁻¹ ib x ≡
      IsBilipschitz.𝒇⁻¹ ib' x
 f⊆ x n n' ib ib' x∈ x∈' n<n' =
   sym (𝒇⁻¹∘𝒇 ib' (𝒇⁻¹ ib x) x⁻¹∈ )
    ∙ cong (𝒇⁻¹ ib') (𝒇'≡𝒇 (𝒇⁻¹ ib x) (𝒇⁻¹∈ ib x x∈)
       ∙ 𝒇∘𝒇⁻¹ ib _ x∈ )

  where
  open IsBilipschitz

  opaque
   𝒇'≡𝒇 : ∀ y → y ∈
       intervalℙ (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n)))))
             (rat (fromNat (2 ℕ.+ n)))
     → (𝒇 ib') y ≡ (𝒇 ib) y
   𝒇'≡𝒇 = elimInClampsᵣ _ _
     (≡Continuous _ _
        ((IsContinuous∘ _ _
              (Lipschitz→IsContinuous (IsBilipschitz.L ib') _ (snd (fl-ebl ib')))
              (IsContinuousClamp (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n))))) _)))
        (IsContinuous∘ _ _
              (Lipschitz→IsContinuous (IsBilipschitz.L ib) _ (snd (fl-ebl ib)))
               (IsContinuousClamp (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n))))) _))
       λ r → (cong (𝒇 ib') (clampᵣ-rat _ _ _) ∙ fromLipschitz-rat)
         ∙∙ cong rat
          (( ((ebl ib') .snd .snd .snd  _
              (inClmp' r))

          ∙ sym
           (((ebl ib) .snd .snd .snd  _
         (ℚ.clam∈ℚintervalℙ _ _ (ℚ.<Weaken≤ _ _ (sqrRestr< n)) r)))))
         ∙∙ (sym (fromLipschitz-rat) ∙ cong (𝒇 ib) (sym (clampᵣ-rat _ _ _)) )


         )
     where
     h : [ pos (suc (suc n)) / 1 ] ℚ.≤ [ pos (suc (suc n')) / 1 ]
     h = ℚ.≤ℤ→≤ℚ (pos (suc (suc n))) (pos (suc (suc n')))
           (( ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-k+ {k = 2} (ℕ.<-weaken n<n'))))


     inClmp' : ∀ r → ℚ.clamp (fst (invℚ₊ (ℚ.[  (1+ (suc n)) / 1 ]₊)))
       [ pos (suc (suc n)) / 1+ 0 ] r
       ∈
       ℚ.ℚintervalℙ (fst (invℚ₊ ([  (1+ (suc n')) / (1+ 0) ]₊)))
       [ pos (suc (suc n')) / 1+ 0 ]
     inClmp' r =
        ℚ.isTrans≤
          (fst (invℚ₊ ([ (1+ (suc n')) / 1 ]₊)))
          (fst (invℚ₊ ([  (1+ (suc n)) / 1 ]₊)))
          (ℚ.clamp (fst (invℚ₊ ([  (1+ (suc n)) / 1 ]₊)))
       [ pos (suc (suc n)) / 1+ 0 ] r)
          ((fst (ℚ.invℚ₊-≤-invℚ₊
            ([  (1+ (suc n)) / 1+ 0 ]₊)
            ([ (1+ (suc n')) / 1+ 0 ]₊)) h))
           (ℚ.≤clamp (fst (invℚ₊ ([  (1+ (suc n)) / (1+ 0) ]₊)))
       [ pos (suc (suc n)) / 1+ 0 ] r (
         (ℚ.<Weaken≤
           (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
           (fromNat (2 ℕ.+ n))

          (sqrRestr< n))))
        , ℚ.isTrans≤ _
             (ℚ.[ pos (suc (suc n)) , (1+ 0) ]) _
            (ℚ.clamp≤
              (fst (invℚ₊ ([  (1+ (suc n)) / 1 ]₊)))
              _ r)
            h


  2+n≤ℚ2+n' = ℚ.≤ℤ→≤ℚ _ _ ( ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-k+ {k = 2} (ℕ.<-weaken n<n')))

  x⁻¹∈ : 𝒇⁻¹ ib x ∈
            intervalℙ (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n')))))
            (rat (fromNat (2 ℕ.+ n')))
  x⁻¹∈ = (isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _
           (fst (ℚ.invℚ₊-≤-invℚ₊ (fromNat (2 ℕ.+ n)) (fromNat (2 ℕ.+ n')))
        2+n≤ℚ2+n'))
       (fst x∈*))
    , (isTrans≤ᵣ _ _ _ (snd x∈*) (≤ℚ→≤ᵣ _ _ 2+n≤ℚ2+n'))

   where
   x∈* : 𝒇⁻¹ ib x ∈
            intervalℙ (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n)))))
            (rat (fromNat (2 ℕ.+ n)))
   x∈* = 𝒇⁻¹∈ ib x x∈


 opaque

  rootSeq⊆→ : Seq⊆→ ℝ rootSeq⊆
  rootSeq⊆→ .Seq⊆→.fun x n _ = IsBilipschitz.𝒇⁻¹ (rootRest n) x
  rootSeq⊆→ .Seq⊆→.fun⊆ x n m = f⊆ x n m (rootRest n) (rootRest m)

  getBounds : ∀ x → 0 <ᵣ x → Σ ℚ (λ q → (0 <ᵣ rat q) × (rat q <ᵣ x)) →
       Σ[ M ∈ ℕ₊₁ ] (absᵣ x <ᵣ fromNat (ℕ₊₁→ℕ M)) →
       Σ[ N ∈ ℕ   ] (x ∈ intervalℙ (rat (loB N)) (rat (hiB N)))
  getBounds x 0<x (q , 0<q , q<x) ((1+ M) , x<1+M ) =
     𝑵 , loB≤x , x≤hiB
     -- 𝑵 ,
    -- (loB≤x , x≤hiB)
   where

   q₊ : ℚ₊
   q₊ = (q , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<q))

   flr-q : Σ (ℕ × ℚ) λ x₁ → (fromNat (fst x₁) ℚ.+ x₁ .snd ≡ fst (invℚ₊ q₊)) ×
                             (0 ℚ.≤ x₁ .snd) × (x₁ .snd ℚ.< 1)
   flr-q = ℚ.floor-fracℚ₊ (invℚ₊ q₊)

   lo𝑵 : ℕ
   lo𝑵 = suc (fst (fst flr-q))
   hi𝑵 : ℕ
   hi𝑵 = M

   𝑵 : ℕ
   𝑵 = ℕ.max lo𝑵 hi𝑵

   loB≤q : loB 𝑵 ℚ.≤ q
   loB≤q = subst2 (ℚ._≤_)
      (ℚ.invℚ₊-ℚ^ⁿ (fromNat (2 ℕ.+ 𝑵)) (suc (suc m)) ) (ℚ.invℚ₊-invol q₊)
      (fst (ℚ.invℚ₊-≤-invℚ₊ _ (fromNat (2 ℕ.+ 𝑵) ℚ₊^ⁿ suc (suc m)))
       (ℚ.isTrans≤ (fst (ℚ.invℚ₊ q₊)) _ _
         (ℚ.<Weaken≤ _ _ (ℚ.≤floor-fracℚ₊ (invℚ₊ q₊))) -- (ℚ.≤floor-fracℚ₊ (invℚ₊ q₊))
          (ℚ.isTrans≤ _ _ _
            (ℚ.isTrans≤ _ _ _ (ℚ.≤ℤ→≤ℚ _ _

              (ℤ.ℕ≤→pos-≤-pos
                  _ _ (subst (ℕ._≤ (lo𝑵 ^ suc (suc m)))
                    (ℕ.·-identityʳ lo𝑵)
                     ((ℕ.^-monotone lo𝑵 0 (suc m) ℕ.zero-≤))))
                     )
              (ℚ.≡Weaken≤ (fromNat (lo𝑵 ^ suc (suc m)))
                ((fromNat lo𝑵 ℚ^ⁿ (2 ℕ.+ m)))
                 (sym ((ℚ.fromNat-^ lo𝑵 (suc (suc m)))))))
            (ℚ^ⁿ-Monotone {fromNat lo𝑵} (suc (suc m))
              (ℚ.≤ℤ→≤ℚ _ _ ℤ.zero-≤pos)
              (ℚ.≤ℤ→≤ℚ _ _ ℤ.zero-≤pos)
              (((ℚ.≤ℤ→≤ℚ _ _

               (ℤ.ℕ≤→pos-≤-pos _ _ 
               (ℕ.≤-trans (ℕ.≤-suc (ℕ.≤-suc ℕ.≤-refl))
                (ℕ.≤-k+ {_} {_} {2} (ℕ.left-≤-max {lo𝑵} {hi𝑵}))
                ))
            )))))
           ))

   loB≤x : rat (loB 𝑵) ≤ᵣ x
   loB≤x = isTrans≤ᵣ _ _ _
     (≤ℚ→≤ᵣ _ _ loB≤q)
       (<ᵣWeaken≤ᵣ _ _ q<x)

   1+M≤hiB : fromNat (suc M) ℚ.≤ (hiB M)
   1+M≤hiB =
    subst (fromNat (suc M) ℚ.≤_) (sym (ℚ.fromNat-^ (2 ℕ.+ M) (suc (suc m))))
     ((ℚ.≤ℤ→≤ℚ (pos (suc M)) (pos ((2 ℕ.+ M) ^ suc (suc m))) (ℤ.ℕ≤→pos-≤-pos _ _
       (ℕ.≤-trans (ℕ.≤-suc ℕ.≤-refl) (subst (ℕ._≤ (suc (suc M) ^ suc (suc m)))
           (sym (cong (suc ∘ suc) (sym (·-identityʳ M))))
            (ℕ.^-monotone (suc (suc M)) 0 (suc m) ℕ.zero-≤ )))
       )))


   x≤hiB : x ≤ᵣ rat (hiB 𝑵)
   x≤hiB =
    isTrans≡≤ᵣ _ _ _  (sym (absᵣPos _ 0<x))
       (isTrans≤ᵣ _ _ _
        (<ᵣWeaken≤ᵣ _ _ x<1+M)
          ((≤ℚ→≤ᵣ _ _ (ℚ.isTrans≤ (fromNat (suc M)) _ _ 1+M≤hiB
            ((ℚ^ⁿ-Monotone (suc (suc m))
               (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.zero-≤)) (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.zero-≤))
             (ℚ.≤ℤ→≤ℚ _ _
              (ℤ.ℕ≤→pos-≤-pos _ _
              (ℕ.≤-k+ {_} {_} {2} ((ℕ.right-≤-max {(hi𝑵)} {(lo𝑵)})))))))))))

  ℝ₊⊆rootSeq : rootSeq⊆ Seq⊆.s⊇ (pred> 0)
  ℝ₊⊆rootSeq x 0<x =
    PT.map2
      (getBounds x 0<x)
       (denseℚinℝ _ _ 0<x)
       (getClamps x)


  0<root : (x : ℝ) (n : ℕ)
      (x∈ : x ∈ intervalℙ (rat (loB n)) (rat (hiB n))) →
      rat [ pos 0 / 1+ 0 ] <ᵣ IsBilipschitz.𝒇⁻¹ (rootRest n) x
  0<root x n x∈ =
    isTrans<≤ᵣ _ _ _
      (<ℚ→<ᵣ _ _ (ℚ.0<ℚ₊ (invℚ₊ ([  (1+ (suc n)) / 1 ]₊))))
      (fst (IsBilipschitz.𝒇⁻¹∈ (rootRest n) x x∈))

  rootSeq⊆→-fun : ∀ {n x y} → rootSeq⊆→ .Seq⊆→.fun x n y ≡ IsBilipschitz.𝒇⁻¹ (rootRest n) x
  rootSeq⊆→-fun = refl

 open Seq⊆→.FromIntersection rootSeq⊆→ isSetℝ (pred> 0) ℝ₊⊆rootSeq public

 opaque

  𝒇=f : ∀ n x → x ∈ intervalℙ
                      (rat (fst (invℚ₊ ([  (1+ (suc n)) / 1 ]₊))))
                      (rat (fromNat (2 ℕ.+ n)))  →
           (x ^ⁿ (suc (suc m))) ≡ fst (IsBilipschitz.fl-ebl (rootRest n)) x
  𝒇=f n = elimInClampsᵣ (rat (fst (invℚ₊ (ℚ.[  (1+ (suc n)) / 1 ]₊)))) (rat _)
   (≡Continuous _ _
        (IsContinuous∘ _ _ (IsContinuous^ⁿ (suc (suc m)) ) (IsContinuousClamp (rat _) (rat _)))
        (IsContinuous∘ _ _ (IsBilipschitz.isCont𝒇 (rootRest n)) (IsContinuousClamp (rat _) (rat _)))
       λ r →  cong (_^ⁿ suc (suc m)) ((clampᵣ-rat _ _ _))
          ∙ ^ⁿ-ℚ^ⁿ (suc (suc m)) _ ∙ cong rat (sym (IsBilipschitz.ebl (rootRest n) .snd .snd .snd
               (ℚ.clamp (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
                (fromNat (2 ℕ.+ n)) r) (ℚ.clam∈ℚintervalℙ _ _
                (ℚ.<Weaken≤ _ _ (sqrRestr< n)) r))) ∙
                 sym (fromLipschitz-rat) ∙ cong (fst (IsBilipschitz.fl-ebl (rootRest n))) (sym (clampᵣ-rat _ _ _)))



 bounds⊂ : (n : ℕ) (x : ℝ) →
      x ∈ (λ z → Seq⊆.𝕡 rootSeq⊆ n z) →
      ∃-syntax ℚ₊
      (λ δ →
         (y : ℝ) → x ∼[ δ ] y → y ∈ (λ z → Seq⊆.𝕡 rootSeq⊆ (suc n) z))
 bounds⊂ n x (lo<x , x<hi)  = ∣ δ
         , (λ y → (λ abs< →
             let u = isTrans≤ᵣ (x -ᵣ y) _
                        (rat (loB n ℚ.- loB (suc n) )) (≤absᵣ (x -ᵣ y))
                        (<ᵣWeaken≤ᵣ (absᵣ (x -ᵣ y)) _
                           (isTrans<≤ᵣ _ (rat (fst δ)) _ abs<
                       (≤ℚ→≤ᵣ _ _ (ℚ.min≤ _ _))))
                 v =
                   isTrans≤ᵣ (y -ᵣ x) _
                        (rat (hiB (suc n) ℚ.- hiB n )) (≤absᵣ (y -ᵣ x))
                      (isTrans≡≤ᵣ _ _ _ (minusComm-absᵣ _ _)
                        (<ᵣWeaken≤ᵣ (absᵣ (x -ᵣ y)) _ (isTrans<≤ᵣ _ _ _ abs<
                       (≤ℚ→≤ᵣ _ _ (ℚ.min≤' ((fst (invℚ₊ (fromNat (2 ℕ.+ n))) ℚ^ⁿ m) ℚ.·
                                             fst (invℚ₊ (fromNat (2 ℕ.+ n)))
                                             ℚ.· fst (invℚ₊ (fromNat (2 ℕ.+ n)))
                                             ℚ.+ ℚ.- loB (suc n)) _)))))
             in  subst2 _≤ᵣ_ ℝ! ℝ!
                    (≤ᵣMonotone+ᵣ _ _ _ _
                       lo<x (-ᵣ≤ᵣ _ _ (isTrans≤≡ᵣ _ _ _ u (sym (-ᵣ-rat₂  (loB n) (loB (suc n))) ))))
                    , subst2 _≤ᵣ_ ℝ! ℝ!
                          (isTrans≤≡ᵣ _ _ _ (≤ᵣMonotone+ᵣ _ _ _ _
                             v x<hi) (cong (_+ᵣ rat (hiB n)) (sym (-ᵣ-rat₂ (hiB (suc n)) (hiB n))))))
                              ∘ fst (∼≃abs<ε _ _ _)) ∣₁
  where
  δ = ℚ.min₊ (ℚ.<→ℚ₊ _ _ (loB-mon n))
                        (ℚ.<→ℚ₊ _ _ (hiB-mon n))
 opaque
  nth-root : ℝ₊ → ℝ₊
  nth-root (x , 0<x) =
      ∩$ x 0<x
    , ∩$-elimProp x 0<x {B = λ y → 0 <ᵣ y} (λ _ → isProp<ᵣ _ _)
       λ n x∈ → isTrans<≡ᵣ _ _ _ (0<root x n x∈) (sym rootSeq⊆→-fun)


  nth-root-impl-fst : ∀ x 0<x → fst (nth-root (x , 0<x)) ≡ ∩$ x 0<x
  nth-root-impl-fst _ _ = refl

  ^ⁿ∘ⁿ√ : ∀ x 0<x → (fst (nth-root (x , 0<x)) ^ⁿ (2 ℕ.+ m)) ≡ x
  ^ⁿ∘ⁿ√ x 0<x = ∩$-elimProp x 0<x
    {B = λ a → (a ^ⁿ (2 ℕ.+ m)) ≡ x}
    (λ _ → isSetℝ _ _)
      λ n x∈ →
           cong (_^ⁿ (2 ℕ.+ m)) rootSeq⊆→-fun ∙ 𝒇=f _ _ (IsBilipschitz.𝒇⁻¹∈ (rootRest n) x x∈)
        ∙ IsBilipschitz.𝒇∘𝒇⁻¹ (rootRest n) x x∈

  ⁿ√∘^ⁿ : ∀ x 0<x → fst (nth-root (x  ^ⁿ (2 ℕ.+ m) , 0<x^ⁿ x (2 ℕ.+ m) 0<x)) ≡ x
  ⁿ√∘^ⁿ  x 0<x = (∩$-elimProp _ (0<x^ⁿ x (suc (suc  m)) 0<x)
    {B = λ a → a ≡ x}
    (λ a → isSetℝ a x)
     λ n x∈' →
      let 0<n : 1 ℕ.≤ suc (suc m)
          0<n = ℕ.suc-≤-suc ℕ.zero-≤
          zzs : rat (fst (invℚ₊ ([ (1+ (suc n)) / 1 ]₊))) ≤ᵣ x
          zzs = (^ⁿMonotone⁻¹ (suc (suc m)) 0<n
                 (0<A n) 0<x (isTrans≡≤ᵣ _ _ _ (^ⁿ-ℚ^ⁿ (suc (suc m))
                  (fst (invℚ₊ ([ (1+ (suc n)) / 1 ]₊)))) (fst x∈')))

          zzss : x ≤ᵣ rat [ pos (suc (suc n)) / 1+ 0 ]
          zzss = (^ⁿMonotone⁻¹ (suc (suc m)) 0<n 0<x (0<B n)
                     (isTrans≤≡ᵣ _ _ _ (snd x∈') (sym (^ⁿ-ℚ^ⁿ (suc (suc m)) (fromNat (2 ℕ.+ n))))))
          x∈ : (rat (fst (invℚ₊ ([  (1+ (suc n)) / 1 ]₊))) ≤ᵣ x) ×
               (x ≤ᵣ rat (fromNat (2 ℕ.+ n)))
          x∈ =  zzs , zzss




      in rootSeq⊆→-fun ∙ cong (fst (IsBilipschitz.f⁻¹R-L (rootRest n)))
                 (𝒇=f n x x∈)
                ∙ IsBilipschitz.𝒇⁻¹∘𝒇 (rootRest n) x x∈)

  opaque
   unfolding rootSeq⊆→
   nth-root-cont : IsContinuousWithPred
           (pred> 0) (curry (fst ∘ nth-root))
   nth-root-cont = ∩$-cont' (pred> 0) rootSeq⊆
      bounds⊂ rootSeq⊆→ ℝ₊⊆rootSeq
       λ n → AsContinuousWithPred (Seq⊆.𝕡 rootSeq⊆ n) _
                (IsBilipschitz.isCont𝒇⁻¹ (rootRest n))

  ℚApproxℙ-nth-root : ℚApproxℙ'
                          (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                          (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                          (curry (nth-root))
  ℚApproxℙ-nth-root q q∈ =
   let q₊ = (q , ℚ.<→0< _ (<ᵣ→<ℚ _ _ q∈))
       (m , q<m) = ℚ.ceilℚ₊ q₊
       (n' , q∈') = getBounds (rat q) q∈
          (fst (/2₊ q₊) ,
            snd (ℚ₊→ℝ₊ (/2₊ q₊))
              , <ℚ→<ᵣ _ _ (x/2<x q₊))
               (1+ (ℕ₊₁→ℕ m) , isTrans<ᵣ _ _ _
                   (isTrans≡<ᵣ _ _ _
                     (absᵣPos _ (snd (ℚ₊→ℝ₊ q₊)))
                     (<ℚ→<ᵣ _ _ q<m))
                   (<ℚ→<ᵣ _ _ (ℚ.<ℤ→<ℚ _ _
                     (ℤ.pos<pos (ℕ.<ᵗsucm {ℕ₊₁→ℕ m})))))
       (a , b , c , d) =
          ( (IsBilipschitz.ℚApproxℙ-𝒇⁻¹ (rootRest n')))
   in a q q∈' , (λ ε →
      isTrans<≤ᵣ _ _ _ (snd (ℚ₊→ℝ₊ (invℚ₊ (fromNat (2 ℕ.+ _)))))
         (fst (b q q∈' ε))) , c q q∈' ,
      d q q∈'
      ∙ sym rootSeq⊆→-fun ∙ sym (∩$-∈ₙ (rat q) q∈ n' q∈')


 nth-pow-root-iso₊₂ : Iso ℝ₊ ℝ₊
 nth-pow-root-iso₊₂ .Iso.fun (x , 0<x) =
   (x ^ⁿ (2 ℕ.+ m)) , 0<x^ⁿ x (2 ℕ.+ m) 0<x
 nth-pow-root-iso₊₂ .Iso.inv = nth-root
 nth-pow-root-iso₊₂ .Iso.sec =
   ℝ₊≡ ∘ uncurry ^ⁿ∘ⁿ√
 nth-pow-root-iso₊₂ .Iso.ret =
   ℝ₊≡ ∘ uncurry ⁿ√∘^ⁿ


root : ℕ₊₁ → ℝ₊ →  ℝ₊
root one x = x
root (2+ n) x = NthRoot.nth-root n x

ℚApproxℙ-root : ∀ n → ℚApproxℙ'
                        (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                        (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                        (curry ((root n)))
ℚApproxℙ-root one q q∈ = (λ _ → q) , (λ _ → q∈) , (λ _ _ → refl∼ _ _) , limConstRat _ _

ℚApproxℙ-root (2+ n) = NthRoot.ℚApproxℙ-nth-root n

IsContinuousRoot : ∀ n → IsContinuousWithPred
         (λ x → _ , isProp<ᵣ _ _)
         λ x 0<x → fst (root n (x , 0<x))
IsContinuousRoot one =
  AsContinuousWithPred (pred> 0) _ IsContinuousId
IsContinuousRoot (2+ n) = NthRoot.nth-root-cont n


nth-pow-root-iso : ℕ₊₁ → Iso ℝ₊ ℝ₊
nth-pow-root-iso k .Iso.fun (x , 0<x) = (x ^ⁿ ℕ₊₁→ℕ k) , 0<x^ⁿ x (ℕ₊₁→ℕ k) 0<x
nth-pow-root-iso k .Iso.inv = root k
nth-pow-root-iso one .Iso.sec _ = ℝ₊≡ (·IdL _)
nth-pow-root-iso (2+ n) .Iso.sec = Iso.sec
  (NthRoot.nth-pow-root-iso₊₂ n)
nth-pow-root-iso one .Iso.ret _ = ℝ₊≡ (·IdL _)
nth-pow-root-iso (2+ n) .Iso.ret = Iso.ret
  (NthRoot.nth-pow-root-iso₊₂ n)


isEquiv-₊^ⁿ : ∀ n → isEquiv (_₊^ⁿ ℕ₊₁→ℕ n)
isEquiv-₊^ⁿ n = isoToIsEquiv (nth-pow-root-iso n)
