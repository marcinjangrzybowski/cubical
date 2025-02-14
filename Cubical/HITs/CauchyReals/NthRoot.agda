{-# OPTIONS --safe --lossy-unification #-}

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
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

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
open import Cubical.HITs.CauchyReals.Bisect


^ⁿ-ℚ^ⁿ : ∀ n q → ((rat q) ^ⁿ n) ≡ rat (q ℚ^ⁿ n)
^ⁿ-ℚ^ⁿ zero _ = refl
^ⁿ-ℚ^ⁿ (suc n) a =
  cong (_·ᵣ rat a) (^ⁿ-ℚ^ⁿ n a) ∙
          sym (rat·ᵣrat _ _)

ℚ^ⁿ-Monotone : ∀ {x y : ℚ} (n : ℕ) → 0 ℚ.≤ x → 0 ℚ.≤ y → x ℚ.≤ y
 → (x ℚ^ⁿ n) ℚ.≤ (y ℚ^ⁿ n)
ℚ^ⁿ-Monotone zero 0≤x 0≤y x≤y = ℚ.isRefl≤ 1
ℚ^ⁿ-Monotone {x} {y} (suc n) 0≤x 0≤y x≤y =
  ℚ.≤Monotone·-onNonNeg _ _ _ _
    (ℚ^ⁿ-Monotone n 0≤x 0≤y x≤y)
    x≤y
    (ℚ.0≤ℚ^ⁿ x 0≤x n)
    0≤x

ℚ^ⁿ-StrictMonotone : ∀ {x y : ℚ} (n : ℕ) → (0 ℕ.< n) → 0 ℚ.≤ x → 0 ℚ.≤ y → x ℚ.< y → (x ℚ.ℚ^ⁿ n) ℚ.< (y ℚ.ℚ^ⁿ n)
ℚ^ⁿ-StrictMonotone {x} {y} 0 0<n 0≤x 0≤y x<y = ⊥.rec (ℕ.¬-<-zero 0<n)
ℚ^ⁿ-StrictMonotone {x} {y} 1 0<n 0≤x 0≤y x<y = 
  subst2 ℚ._<_ (sym (ℚ.·IdL _)) (sym (ℚ.·IdL _)) x<y
ℚ^ⁿ-StrictMonotone {x} {y} (suc (suc n)) 0<n 0≤x 0≤y x<y =
  ℚ.<Monotone·-onPos _ _ _ _
    (ℚ^ⁿ-StrictMonotone (suc n) (ℕ.suc-≤-suc (ℕ.zero-≤ {n})) 0≤x 0≤y x<y)
    x<y
    (ℚ.0≤ℚ^ⁿ x 0≤x (suc n))
    0≤x


sqrRestr< : ∀ n → (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) ℚ.< (fromNat (2 ℕ.+ n))
sqrRestr< n =
  (ℚ.isTrans< (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) 1 (fromNat (2 ℕ.+ n))
               (fst (ℚ.invℚ₊-<-invℚ₊ 1 _)
                 (ℚ.<ℤ→<ℚ 1 _ (ℤ.suc-≤-suc (ℤ.suc-≤-suc (ℤ.zero-≤pos {n})))))
               (ℚ.<ℤ→<ℚ 1 _
               (ℤ.suc-≤-suc (ℤ.suc-≤-suc (ℤ.zero-≤pos {n}))))) 

module NthRoot (m : ℕ) where


 module _ (n : ℕ) where

  bounds = bⁿ-aⁿ' m
    (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n)))))
    (fromNat (2 ℕ.+ n))
      (snd (ℚ₊→ℝ₊ (invℚ₊ (fromNat (2 ℕ.+ n)))) )
      (snd (ℚ₊→ℝ₊ (fromNat (2 ℕ.+ n))))
      (<ℚ→<ᵣ _ _ (sqrRestr< n))

  L = (((fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m))
      ℚ₊· (fromNat (2 ℕ.+ m)))

  K = (fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m)

  incrF : isIncrasingℙ
   (ℚintervalℙ (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
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
    (subst (ℚ._≤ 1) (sym (ℚ.invℚ₊-ℚ^ⁿ _ _))
      (ℚ.x^ⁿ≤1 _ _ ℤ.zero-≤pos
       (fst (ℚ.invℚ₊-≤-invℚ₊ 1 (fromNat (2 ℕ.+ n)))
        (ℚ.≤ℤ→≤ℚ _ _ (ℤ.suc-≤-suc ℤ.zero-≤pos)))))
         (ℚ.isTrans≤< _ _ _
           (ℚ.1≤x^ⁿ (fromNat (2 ℕ.+ n))
            (fromNat (1 ℕ.+ m)) (ℚ.≤ℤ→≤ℚ 1 _ (ℤ.suc-≤-suc ℤ.zero-≤pos)))
            (subst (ℚ._< fst L)
             
               (ℚ.·IdR _)
                 (ℚ.<-o· 1 (fromNat (2 ℕ.+ m))
                   _ (ℚ.0<ℚ₊ ((fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m)))
            ((ℚ.<ℤ→<ℚ 1 (ℤ.pos (suc (suc m)))
             ( ℤ.suc-≤-suc (ℤ.suc-≤-suc (ℤ.zero-≤pos {m})))))))
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
    Lipschitz-ℚ→ℝℙ<→Lipschitz-ℚ→ℝℙ _ _ _
      λ q q∈ r r∈ r<q  →
       let bb = bounds (rat r) (rat q) (fst r∈) (snd q∈) (<ℚ→<ᵣ _ _ r<q)


           ineqL : (rat q ^ⁿ suc (suc m)) -ᵣ (rat r ^ⁿ suc (suc m))
                      ≤ᵣ rat ((fst L) ℚ.· (q ℚ.- r))
           ineqL =
             isTrans≡≤ᵣ _ _ _ (fst (snd bb))
               (isTrans≤≡ᵣ _ _ _ (≤ᵣ-o·ᵣ _ _ _
                      (≤ℚ→≤ᵣ _ _  $ ℚ.<Weaken≤ _ _ (ℚ.<→<minus _ _ r<q))
                    (isTrans≤≡ᵣ _ _ _ (fst (snd (snd bb)))
                      (sym ((rat·ᵣrat _ _
                        ∙ cong (_·ᵣ (rat ((fromNat (2 ℕ.+ m)))))
                          (sym (^ⁿ-ℚ^ⁿ _ _)))))
                          ))
                           (sym (rat·ᵣrat _ _) ∙ (cong rat (ℚ.·Comm _ _))))
           
           
       in isTrans≡≤ᵣ _ _ _ (absᵣPos _
            (<ℚ→<ᵣ _ _  (ℚ.<→<minus _ _ (incrF r
                     (∈intervalℙ→∈ℚintervalℙ _ _ _ r∈)
                     q
                     (∈intervalℙ→∈ℚintervalℙ _ _ _ q∈)
                     r<q)))
                 ∙ cong₂ _-ᵣ_
                   (sym (^ⁿ-ℚ^ⁿ _ _))
                   (sym (^ⁿ-ℚ^ⁿ _ _))) ineqL

  rootRest .IsBilipschitz.lip⁻¹F =
    Invlipschitz-ℚ→ℚℙ'<→Invlipschitz-ℚ→ℚℙ _ _ _
       λ q q∈ r r∈ r<q →
          let r∈' = (∈ℚintervalℙ→∈intervalℙ _ _ _ r∈)
              q∈' = (∈ℚintervalℙ→∈intervalℙ
                      (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) _ _ q∈)
              bb = bounds (rat r) (rat q) (fst r∈') (snd q∈')
                    (<ℚ→<ᵣ _ _ r<q)

          in ℚ.x·invℚ₊y≤z→x≤y·z _ _ _ (≤ᵣ→≤ℚ _ _
                $ isTrans≡≤ᵣ _ _ _ (cong rat
                  (cong ((q ℚ.+ ℚ.- r) ℚ.·_)
                    (ℚ.invℚ₊-ℚ^ⁿ _ (suc m)) )
                  ∙ rat·ᵣrat _ _) $
                isTrans≤≡ᵣ _ _ _
                  (≤ᵣ-o·ᵣ _ _ _
                        (≤ℚ→≤ᵣ _ _  $ ℚ.<Weaken≤ _ _ (ℚ.<→<minus _ _ r<q))
                  (isTrans≡≤ᵣ _ _ _
                     (sym (^ⁿ-ℚ^ⁿ _ _))
                             (snd (snd (snd bb)))))
                    (sym (fst (snd bb)) ∙
                      cong₂ _-ᵣ_ (^ⁿ-ℚ^ⁿ _ _) (^ⁿ-ℚ^ⁿ _ _)
                      ∙ cong rat (sym (ℚ.absPos _
                      (ℚ.<→<minus _ _ (incrF r r∈ q q∈ r<q))) ∙
                       ℚ.abs'≡abs _)))




 loB hiB : ∀ n → ℚ
 loB n = (((fst (invℚ₊ (fromNat (2 ℕ.+ n))))) ℚ^ⁿ (2 ℕ.+ m))
 hiB n = ((fromNat (2 ℕ.+ n)) ℚ^ⁿ (2 ℕ.+ m))
 
 rootSeq⊆ : Seq⊆
 rootSeq⊆ .Seq⊆.𝕡 n = intervalℙ
   (rat (loB n))
   (rat (hiB n))
 rootSeq⊆ .Seq⊆.𝕡⊆ n x (≤x , x≤) =
  
   isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _
     (ℚ^ⁿ-Monotone (2 ℕ.+ m) (ℚ.0≤ℚ₊ _) (ℚ.0≤ℚ₊ _)         
      (fst (ℚ.invℚ₊-≤-invℚ₊
    (fromNat (2 ℕ.+ n)) (fromNat (3 ℕ.+ n)))
      (ℚ.≤ℤ→≤ℚ _ _ (ℤ.≤-suc ℤ.isRefl≤)))
      )) ≤x ,
   isTrans≤ᵣ _ _ _ x≤ (≤ℚ→≤ᵣ _ _
     (ℚ^ⁿ-Monotone (2 ℕ.+ m) (ℚ.0≤ℚ₊ _) (ℚ.0≤ℚ₊ _)         
      ((ℚ.≤ℤ→≤ℚ _ _ (ℤ.≤-suc ℤ.isRefl≤)))
      ))




 f⊆ : (x : ℝ) (n n' : ℕ)
      (x∈ : x ∈ intervalℙ (rat (loB n)) (rat (hiB n)))
      (x∈' : x ∈ intervalℙ (rat (loB n')) (rat (hiB n'))) →
      n ℕ.< n' →
      IsBilipschitz.𝒇⁻¹ (rootRest n) x ≡
      IsBilipschitz.𝒇⁻¹ (rootRest n') x
 f⊆ x n n' x∈ x∈' n<n' =
   h 

  where
  open IsBilipschitz
  ib = rootRest n
  ib' = rootRest n'

  -- zz' : {!!}
  -- zz' = 

  𝒇'≡𝒇 : ∀ y → y ∈
      intervalℙ (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n)))))
            (rat (fromNat (2 ℕ.+ n)))
    → (𝒇 ib') y ≡ (𝒇 ib) y
  𝒇'≡𝒇 = elimInClampsᵣ _ _
    (≡Continuous _ _
       ((IsContinuous∘ _ _
             (Lipschitz→IsContinuous _ _ (snd (fl-ebl ib')))
             (IsContinuousClamp (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n))))) _)))
       (IsContinuous∘ _ _
             (Lipschitz→IsContinuous _ _ (snd (fl-ebl ib)))
              (IsContinuousClamp (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n))))) _))
      λ r → cong rat
           ( ((ebl ib') .snd .snd .snd  _
             (inClmp' r))
            
         ∙ sym
          (((ebl ib) .snd .snd .snd  _
        (clam∈ℚintervalℙ _ _ (ℚ.<Weaken≤ _ _ (sqrRestr< n)) r))))
        )
    where
    h = ℚ.≤ℤ→≤ℚ _ _ (ℤ.suc-≤-suc (ℤ.≤-suc (ℤ.ℕ≤→pos-≤-pos _ _ n<n')))
    inClmp' : ∀ r → ℚ.clamp (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt)))
      [ pos (suc (suc n)) / 1+ 0 ] r
      ∈
      ℚintervalℙ (fst (invℚ₊ (ℚ.[ pos (suc (suc n')) , (1+ 0) ] , tt)))
      [ pos (suc (suc n')) / 1+ 0 ]
    inClmp' r =
       ℚ.isTrans≤
         (fst (invℚ₊ (ℚ.[ pos (suc (suc n')) , (1+ 0) ] , tt)))
         (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt)))
         (ℚ.clamp (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ]
        , tt)))
      [ pos (suc (suc n)) / 1+ 0 ] r)
         ((fst (ℚ.invℚ₊-≤-invℚ₊
           ([ pos (suc (suc n)) / 1+ 0 ] , _)
           ([ pos (suc (suc n')) / 1+ 0 ] , _)) h))
          (ℚ.≤clamp (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt)))
      [ pos (suc (suc n)) / 1+ 0 ] r (
        (ℚ.<Weaken≤
          (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
          (fromNat (2 ℕ.+ n))

         (sqrRestr< n))))
       , ℚ.isTrans≤ _
            (ℚ.[ pos (suc (suc n)) , (1+ 0) ]) _
           (ℚ.clamp≤
             (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt)))
             _ r)
           h
           
  2+n≤ℚ2+n' = (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.<-weaken (ℕ.<-k+ n<n'))))

  x⁻¹∈ : 𝒇⁻¹ ib x ∈
            intervalℙ (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n')))))
            (rat (fromNat (2 ℕ.+ n')))
  x⁻¹∈ = (isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _
           (fst (ℚ.invℚ₊-≤-invℚ₊ _ (fromNat (2 ℕ.+ n')))
        2+n≤ℚ2+n'))
       (fst x∈*))
    , (isTrans≤ᵣ _ _ _ (snd x∈*) (≤ℚ→≤ᵣ _ _ 2+n≤ℚ2+n'))

   where
   x∈* : 𝒇⁻¹ ib x ∈
            intervalℙ (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n)))))
            (rat (fromNat (2 ℕ.+ n)))
   x∈* = 𝒇⁻¹∈ ib x x∈

  h : 𝒇⁻¹ ib x ≡ 𝒇⁻¹ ib' x
  h = sym (𝒇⁻¹∘𝒇 ib' (𝒇⁻¹ ib x) x⁻¹∈ )
    ∙ cong (𝒇⁻¹ ib') (𝒇'≡𝒇 (𝒇⁻¹ ib x) (𝒇⁻¹∈ ib x x∈)
       ∙ 𝒇∘𝒇⁻¹ ib _ x∈ )



 rootSeq⊆→ : Seq⊆→ ℝ rootSeq⊆
 rootSeq⊆→ .Seq⊆→.fun x n _ = IsBilipschitz.𝒇⁻¹ (rootRest n) x
 rootSeq⊆→ .Seq⊆→.fun⊆ = f⊆

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

  flr-q = ℚ.floor-fracℚ₊ (invℚ₊ q₊)

  lo𝑵 = suc (fst (fst flr-q))
  hi𝑵 = M

  𝑵 = ℕ.max lo𝑵 hi𝑵  
    
  loB≤q : loB 𝑵 ℚ.≤ q
  loB≤q = subst2 (ℚ._≤_)
     (ℚ.invℚ₊-ℚ^ⁿ _ _) (ℚ.invℚ₊-invol q₊)
     (fst (ℚ.invℚ₊-≤-invℚ₊ _ _)
      (ℚ.isTrans≤ (fst (ℚ.invℚ₊ q₊)) _ _
        (ℚ.<Weaken≤ _ _ (ℚ.≤floor-fracℚ₊ (invℚ₊ q₊))) -- (ℚ.≤floor-fracℚ₊ (invℚ₊ q₊))
         (ℚ.isTrans≤ _ _ _
           (ℚ.isTrans≤ _ _ _ (ℚ.≤ℤ→≤ℚ _ _
             (ℤ.ℕ≤→pos-≤-pos _ _
                 (subst (ℕ._≤ (lo𝑵 ^ suc (suc m)))
                   (ℕ.·-identityʳ lo𝑵)
                    ((ℕ.^-monotone lo𝑵 0 (suc m) ℕ.zero-≤)))))
             (ℚ.≡Weaken≤ (fromNat (lo𝑵 ^ suc (suc m)))
               ((fromNat lo𝑵 ℚ^ⁿ (2 ℕ.+ m)))
                (sym ((ℚ.fromNat-^ lo𝑵 (suc (suc m)))))))
           (ℚ^ⁿ-Monotone {fromNat lo𝑵} (suc (suc m))
             (ℚ.≤ℤ→≤ℚ _ _ ℤ.zero-≤pos)
             (ℚ.≤ℤ→≤ℚ _ _ ℤ.zero-≤pos)
             (((ℚ.≤ℤ→≤ℚ _ _
          (ℤ.ℕ≤→pos-≤-pos _ _ 
          (ℕ.≤-trans (ℕ.≤-suc (ℕ.≤-suc ℕ.≤-refl))
           (ℕ.left-≤-max {suc (suc lo𝑵)} {suc (suc hi𝑵)}))))))))
          ))
  
  loB≤x : rat (loB 𝑵) ≤ᵣ x
  loB≤x = isTrans≤ᵣ _ _ _
    (≤ℚ→≤ᵣ _ _ loB≤q)
      (<ᵣWeaken≤ᵣ _ _ q<x)

  1+M≤hiB : fromNat (suc M) ℚ.≤ (hiB M)
  1+M≤hiB = 
   subst (fromNat (suc M) ℚ.≤_) (sym (ℚ.fromNat-^ _ _))
    ((ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
      (ℕ.≤-trans (ℕ.≤-suc ℕ.≤-refl) (subst (ℕ._≤ (suc (suc M) ^ suc (suc m)))
          (sym (cong (suc ∘ suc) (sym (·-identityʳ M))))
           (ℕ.^-monotone (suc (suc M)) 0 (suc m) ℕ.zero-≤ )))
      )))


  x≤hiB : x ≤ᵣ rat (hiB 𝑵)
  x≤hiB = 
   isTrans≡≤ᵣ _ _ _  (sym (absᵣPos _ 0<x))
      (isTrans≤ᵣ _ _ _    
       (<ᵣWeaken≤ᵣ _ _ x<1+M)
         (≤ℚ→≤ᵣ _ _ (ℚ.isTrans≤ _ _ _ 1+M≤hiB
           ((ℚ^ⁿ-Monotone (suc (suc m))
              (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.zero-≤))
              (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.zero-≤))
            (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
             ((ℕ.right-≤-max {suc (suc hi𝑵)} {suc (suc lo𝑵)})) ))
             )))))

 ℝ₊⊆rootSeq : rootSeq⊆ Seq⊆.s⊇ (λ x → (0 <ᵣ x ) , squash₁)
 ℝ₊⊆rootSeq x 0<x = 
   PT.map2
     (getBounds x 0<x)
      (denseℚinℝ _ _ 0<x)
      (getClamps x)
 
 nth-root : ℝ₊ → ℝ₊
 nth-root (x , 0<x) =
   seq⊆→$ _ isSetℝ _ rootSeq⊆→ (λ x → (0 <ᵣ x ) , squash₁)
      ℝ₊⊆rootSeq x 0<x
     , {!!}

-- -- sqrt2 : {!!}
-- -- sqrt2 = {!!}

-- --  -- x n n' x∈ x∈' _ =
-- --  --    {!!}
     
-- --  --   -- elimInClampsᵣ {P = λ x → 𝒇⁻¹ (rootRest n m) x ≡ 𝒇⁻¹ (rootRest n' m) x}
-- --  --   --    (rat (loB n))
-- --  --   --    (rat (hiB n))
-- --  --   --   {!h!}
-- --  --   --   x x∈

      
-- --  --   where
-- --  --   open IsBilipschitz
-- --  --   ib = rootRest n m
-- --  --   ib' = rootRest n' m

-- --  --   h : {!!}
-- --  --   h = {!   cong fst (isoFunInjective (isoF ib)
-- --  --     (_ , x⁻¹∈)
-- --  --     (_ , {!!}) {!!})         !}

-- --  --   w : {!!}
-- --    -- w =  ≡Continuous _ _
-- --    --        (IsContinuous∘ _ _
-- --    --           (Lipschitz→IsContinuous _ _ (snd (fl-ebl ib)))
-- --    --           ((Lipschitz→IsContinuous _ _ (snd (f⁻¹R-L ib)))))
-- --  --          (IsContinuous∘ _ _
-- --  --             (Lipschitz→IsContinuous _ _ (snd (fl-ebl ib')))
-- --  --             ((Lipschitz→IsContinuous _ _ (snd (f⁻¹R-L ib')))))
-- --  --             {!λ r → ?!} {!!}
             

-- --    -- IsBilipschitz.inj𝒇 (rootRest n m)
-- --    -- ((Lipschitz→IsContinuous _
-- --    --  {!!} {!
-- --    --   IsContinuous∘ _ _
-- --    --    ?
-- --    --    ?!}))
-- --       -- {!!} {!!} x
-- --   --  z ∙ {!!} 
-- --   -- where
-- --   --  z : {!!}
-- --   --  z = IsBilipschitz.inj𝒇 (rootRest n m) _ _
-- --   --   {!!}
-- --  -- bisect
-- --  --   (2 ℚ₊· fromNat (2 ℕ.+ n))
-- --  --   (2 ℚ₊· fromNat (2 ℕ.+ n))
-- --  --   {!!}
-- --  --   (fst (invℚ₊ (fromNat (suc n))))
-- --  --   ((fromNat (suc n)))
-- --  --   {!!}
-- --  --   (λ x _ → x ℚ.· x)
-- --  --   (λ x x∈ y y∈ x₁ → {!!})
-- --  --   (λ q q∈ r r∈ ε x → 
-- --  --     let z = {!!}
-- --  --           -- restrSq (suc n) q r --(≤ᵣ→≤ℚ _ _ (snd r∈))
-- --  --           --      {!snd q∈!}
-- --  --           --      {!!}
-- --  --           --     -- (ℚ.isTrans≤< _ _ _ {!snd q∈!} {!!} )
-- --  --           --     -- (ℚ.isTrans≤< _ _ _ {!!} {!!})
-- --  --           --     -- (ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ _ _ (snd q∈))
-- --  --           --     --  {!!})
-- --  --           --     -- ((ℚ.isTrans<≤ _ _ _ {!!} (≤ᵣ→≤ℚ _ _ (fst q∈))
-- --  --           --     --  {!!}))
-- --  --           --     ε x
-- --  --     in {!z!}
-- --  --     )
-- --  --   λ q q∈ r r∈ ε x →
-- --  --     let x' = subst (λ x → ℚ.abs' x ℚ.< fst ε)
-- --  --                 (sym lem--040) x
-- --  --         uu = (((ℚ.[ pos 2 , (1+ 0) ] , tt) ℚ₊·
-- --  --            (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt)))
-- --  --     in ℚ.isTrans≤< (ℚ.abs' (q ℚ.- r))
-- --  --         (fst uu ℚ.·  ℚ.abs' ((q ℚ.+ r) ℚ.· (q ℚ.- r))) _
-- --  --           {!!} (ℚ.<-o· _ _ (fst uu) (ℚ.0<ℚ₊ uu) x')

