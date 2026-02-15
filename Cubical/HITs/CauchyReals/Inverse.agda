module Cubical.HITs.CauchyReals.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit
open import Cubical.Data.Fast.Int as ℤ using (pos)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.NatPlusOne


import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.Ring as RP


open import Cubical.Relation.Binary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals.Fast as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Fast.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡ ; [_/_]₊)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication


open import Cubical.Tactics.CommRingSolverFast.RationalsReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection
open import Cubical.Tactics.CommRingSolverFast.IntReflection
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.Tactics.CommRingSolverFast.RealsReflection



Rℝ = (CR.CommRing→Ring ℝring)

module 𝐑' = RP.RingTheory Rℝ


Invᵣ-restrℚ : (η : ℚ₊) →
  Σ (ℚ → ℚ) (Lipschitz-ℚ→ℚ (invℚ₊ (η ℚ₊· η)))

Invᵣ-restrℚ η = f ,
  Lipschitz-ℚ→ℚ'→Lipschitz-ℚ→ℚ ((invℚ₊ (η ℚ₊· η))) f w
 where

 f = fst ∘ invℚ₊ ∘ ℚ.maxWithPos η

 w : ∀ q r → ℚ.abs (f q ℚ.- f r) ℚ.≤
      fst (invℚ₊ (η ℚ₊· η)) ℚ.· ℚ.abs (q ℚ.- r)
 w q r =
  let z = cong ℚ.abs (ℚ.1/p+1/q (ℚ.maxWithPos η q) (ℚ.maxWithPos η r))
           ∙ ℚ.pos·abs _ _ (ℚ.0≤ℚ₊ (invℚ₊ (ℚ.maxWithPos η q ℚ₊· ℚ.maxWithPos η r)))
           ∙ cong (fst (invℚ₊ (ℚ.maxWithPos η q ℚ₊· ℚ.maxWithPos η r)) ℚ.·_)
       ((ℚ.absComm- (ℚ.max (fst η) r) (ℚ.max (fst η) q)))
  in subst (ℚ._≤ fst (invℚ₊ (η ℚ₊· η)) ℚ.· ℚ.abs (q ℚ.- r))
       (sym z)
         (ℚ.≤Monotone·-onNonNeg
           (fst (invℚ₊ (ℚ.maxWithPos η q ℚ₊· ℚ.maxWithPos η r))) _ _ _
            (ℚ.invℚ₊≤invℚ₊ _ _
              (ℚ.≤Monotone·-onNonNeg _ _ _ _
                (ℚ.≤max _ _)
                (ℚ.≤max _ _)
                (ℚ.0≤ℚ₊ η)
                (ℚ.0≤ℚ₊ η)))
            (ℚ.maxDist (fst η) r q)
            (ℚ.0≤ℚ₊ (invℚ₊ (ℚ.maxWithPos η q ℚ₊· ℚ.maxWithPos η r)))
            (ℚ.0≤abs (fst (ℚ.maxWithPos η q) ℚ.- fst (ℚ.maxWithPos η r))))

Invᵣ-restr : (η : ℚ₊) → Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ (invℚ₊ (η ℚ₊· η)))
Invᵣ-restr η = (fromLipschitzGo (invℚ₊ (η ℚ₊· η)))
                   (_ , Lipschitz-rat∘ ((invℚ₊ (η ℚ₊· η))) (fst (Invᵣ-restrℚ η)) (snd (Invᵣ-restrℚ η)))






ℚmax-min-minus : ∀ x y → ℚ.max (ℚ.- x) (ℚ.- y) ≡ ℚ.- (ℚ.min x y)
ℚmax-min-minus = ℚ.elimBy≤
 (λ x y p → ℚ.maxComm (ℚ.- y) (ℚ.- x) ∙∙ p ∙∙ cong ℚ.-_ (ℚ.minComm x y))
  λ x y x≤y →
    ℚ.maxComm (ℚ.- x) (ℚ.- y) ∙∙ ℚ.≤→max (ℚ.- y) (ℚ.- x) (ℚ.minus-≤ x y x≤y)
      ∙∙ cong ℚ.-_ (sym (ℚ.≤→min _ _ x≤y))



absᵣNonPos : ∀ x → x ≤ᵣ 0 → absᵣ x ≡ -ᵣ x
absᵣNonPos x p = abs-max x ∙ ≤ᵣ→≡ z
 where
   z : x ≤ᵣ (-ᵣ x)
   z = isTrans≤ᵣ _ _ _ p (isTrans≡≤ᵣ _ _ _  (sym (-ᵣ-rat _)) (-ᵣ≤ᵣ _ _ p))


-- TODO: this is overcomplciated! it follows simply form density...

<ᵣMonotone+ᵣ : ∀ m n o s → m <ᵣ n → o <ᵣ s → (m +ᵣ o) <ᵣ (n +ᵣ s)
<ᵣMonotone+ᵣ m n o s m<n o<s =
  isTrans<ᵣ _ _ _ (<ᵣ-+o m n o m<n) (<ᵣ-o+ o s n o<s)

≤<ᵣMonotone+ᵣ : ∀ m n o s → m ≤ᵣ n → o <ᵣ s → (m +ᵣ o) <ᵣ (n +ᵣ s)
≤<ᵣMonotone+ᵣ m n o s m≤n o<s =
  isTrans≤<ᵣ _ _ _ (≤ᵣ-+o m n o m≤n) (<ᵣ-o+ o s n o<s)

<≤ᵣMonotone+ᵣ : ∀ m n o s → m <ᵣ n → o ≤ᵣ s → (m +ᵣ o) <ᵣ (n +ᵣ s)
<≤ᵣMonotone+ᵣ m n o s m<n o≤s =
  isTrans<≤ᵣ _ _ _ (<ᵣ-+o m n o m<n) (≤ᵣ-o+ o s n o≤s)



ℝ₊+ : (m : ℝ₊) (n : ℝ₊) → 0 <ᵣ (fst m) +ᵣ (fst n)
ℝ₊+ (m , <m) (n , <n) = isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat  _ _)) (<ᵣMonotone+ᵣ 0 m 0 n <m <n)


opaque
 unfolding _<ᵣ_
 isIrrefl<ᵣ : BinaryRelation.isIrrefl _<ᵣ_
 isIrrefl<ᵣ a = PT.rec isProp⊥
   λ ((q , q') , (a≤q , q<q' , q'≤a)) →
     ℚ.≤→≯ _ _ (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ (rat q') _ _ q'≤a a≤q)) q<q'

_＃_ : ℝ → ℝ → Type
x ＃ y = (x <ᵣ y) ⊎ (y <ᵣ x)

isProp＃ : ∀ x y → isProp (x ＃ y)
isProp＃ x y (inl x₁) (inl x₂) = cong inl (isProp<ᵣ _ _ x₁ x₂)
isProp＃ x y (inl x₁) (inr x₂) = ⊥.rec (isAsym<ᵣ _ _ x₁ x₂)
isProp＃ x y (inr x₁) (inl x₂) = ⊥.rec (isAsym<ᵣ _ _ x₁ x₂)
isProp＃ x y (inr x₁) (inr x₂) = cong inr (isProp<ᵣ _ _ x₁ x₂)


rat＃ : ∀ q q' → (rat q ＃ rat q') ≃ (q ℚ.# q' )
rat＃ q q' = propBiimpl→Equiv (isProp＃ _ _) (ℚ.isProp# _ _)
  (⊎.map (<ᵣ→<ℚ _ _) (<ᵣ→<ℚ _ _))
  (⊎.map (<ℚ→<ᵣ _ _) (<ℚ→<ᵣ _ _))


decCut : ∀ x → 0 <ᵣ (absᵣ x) → (0 ＃ x)
decCut x 0<absX =
  PT.rec (isProp＃ 0 x)
    (λ (Δ , Δ<absX) →
      PT.rec (isProp＃ 0 x)
         (λ (q , q-x<Δ/2 , x<q) →
          let z→ : 0 ℚ.< q → 0 <ᵣ x
              z→ 0<q =
                let zzz : rat q <ᵣ rat (fst (/2₊ Δ)) →
                            0 <ᵣ x
                    zzz q<Δ/2 =
                      let zzz' =
                           subst2 _≤ᵣ_
                             (cong absᵣ ℝ!)
                               (cong₂ _+ᵣ_
                                 (absᵣNonNeg _
                                      (≤ℚ→≤ᵣ _ _
                                         (ℚ.<Weaken≤ 0 q 0<q )))
                                  (minusComm-absᵣ _ _ ∙
                                       absᵣNonNeg _
                                         (subst (_≤ᵣ (rat q +ᵣ (-ᵣ x)))
                                           (+-ᵣ x) (≤ᵣ-+o _ _ (-ᵣ x)
                                          (<ᵣWeaken≤ᵣ _ _ x<q)))))
                              (absᵣ-triangle (rat q) (x +ᵣ (-ᵣ (rat q))))
                          zzzz' = subst (absᵣ x <ᵣ_) (+ᵣ-rat _ _ ∙ cong rat
                               (ℚ.ε/2+ε/2≡ε (fst Δ)))
                             (isTrans≤<ᵣ _ _ _ zzz'
                                     ((<ᵣMonotone+ᵣ
                                       _ _ _ _ q<Δ/2 q-x<Δ/2)))
                      in ⊥.rec (isAsym<ᵣ _ _ Δ<absX zzzz')
                in ⊎.rec
                    (λ Δ≤q →
                       subst2 _<ᵣ_
                          (+-ᵣ (rat (fst (/2₊ Δ))))
                          ((cong (rat q +ᵣ_) (-ᵣDistr (rat q) (-ᵣ x))
                             ∙ (λ i → +ᵣAssoc (rat q) (-ᵣ (rat q))
                                (-ᵣInvol x i) i) ∙
                              cong (_+ᵣ x) (+-ᵣ (rat q)) ∙ +IdL x)) --
                          (≤<ᵣMonotone+ᵣ (rat (fst (/2₊ Δ))) (rat q) _ _
                            (≤ℚ→≤ᵣ _ _ Δ≤q) (-ᵣ<ᵣ _ _ q-x<Δ/2)))
                   (zzz ∘S <ℚ→<ᵣ _ _ )
                    (ℚ.Dichotomyℚ (fst (/2₊ Δ)) q)
              z← : q ℚ.≤ 0 → x <ᵣ 0
              z← q≤0 = isTrans<≤ᵣ _ _ _ x<q (≤ℚ→≤ᵣ q 0 q≤0)
          in ⊎.rec (inr ∘ z←) (inl ∘ z→) (ℚ.Dichotomyℚ q 0))
         (∃rationalApprox< x (/2₊ Δ)))
     (lowerℚBound _ 0<absX)


opaque

 ＃≃0<dist : ∀ x y → x ＃ y ≃ (0 <ᵣ (absᵣ (x +ᵣ (-ᵣ y))))
 ＃≃0<dist x y = propBiimpl→Equiv (isProp＃ _ _) (isProp<ᵣ _ _)
   (⊎.rec ((λ x<y → subst (0 <ᵣ_) (minusComm-absᵣ y x)
                 (isTrans<≤ᵣ _ _ _ (subst (_<ᵣ (y +ᵣ (-ᵣ x)))
              (+-ᵣ x) (<ᵣ-+o _ _ (-ᵣ x) x<y)) (≤absᵣ _ ))))
          (λ y<x → isTrans<≤ᵣ _ _ _ (subst (_<ᵣ (x +ᵣ (-ᵣ y)))
              (+-ᵣ y) (<ᵣ-+o _ _ (-ᵣ y) y<x)) (≤absᵣ _ )))
   (⊎.rec (inr ∘S subst2 _<ᵣ_ (+IdL _) ℝ! ∘S <ᵣ-+o _ _ y)
          (inl ∘S subst2 _<ᵣ_ ℝ! (+IdR y) ∘S <ᵣ-o+ _ _ y)
           ∘S decCut (x +ᵣ (-ᵣ y)))

-- ＃≃abs< : ∀ x y → absᵣ x <ᵣ y ≃
-- ＃≃abs< : ?

isSym＃ : BinaryRelation.isSym _＃_
isSym＃ _ _ = fst ⊎-swap-≃

opaque
 unfolding _<ᵣ_
 0＃→0<abs : ∀ r → 0 ＃ r → 0 <ᵣ absᵣ r
 0＃→0<abs r 0＃r =
   subst (rat 0 <ᵣ_) (cong absᵣ (+IdR r))
     (fst (＃≃0<dist r 0) (isSym＃ 0 r 0＃r))

opaque

 ≤ᵣ-·o : ∀ m n o → 0 ℚ.≤ o  →  m ≤ᵣ n → (m ·ᵣ rat o ) ≤ᵣ (n ·ᵣ rat o)
 ≤ᵣ-·o m n o 0≤o p = ≡→≤ᵣ (sym (·ᵣMaxDistrPos m n o 0≤o) ∙
   cong (_·ᵣ rat o) (≤ᵣ→≡ p))


 ≤ᵣ-o· : ∀ m n o → 0 ℚ.≤ o →  m ≤ᵣ n → (rat o ·ᵣ m ) ≤ᵣ (rat o ·ᵣ n)
 ≤ᵣ-o· m n o q p = ≡→≤ᵣ $
     cong₂ maxᵣ ℝ! ℝ! ∙ ≤ᵣ→≡ (≤ᵣ-·o m n o q p) ∙ ℝ!

 <ᵣ→Δ : ∀ x y → x <ᵣ y → ∃[ δ ∈ ℚ₊ ] rat (fst δ) <ᵣ y +ᵣ (-ᵣ x)
 <ᵣ→Δ x y =  (PT.map λ ((q , q') , (a , a' , a'')) →
               /2₊ (ℚ.<→ℚ₊ q q' a') ,
                 let zz = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ a') a''
                     zz' = -ᵣ≤ᵣ _ _ a
                     zz'' = ≤ᵣMonotone+ᵣ _ _ _ _ a'' zz'
                 in isTrans<≤ᵣ _ _ _
                        (<ℚ→<ᵣ _ _ (x/2<x (ℚ.<→ℚ₊ q q' a')))
                        ( isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat₂ _ _)) zz'')) ∘S fst (<ᵣ-impl _ _)









 a-b≤c⇒a-c≤b : ∀ a b c → a +ᵣ (-ᵣ b) ≤ᵣ c  → a +ᵣ (-ᵣ c) ≤ᵣ b
 a-b≤c⇒a-c≤b a b c p =
   subst2 _≤ᵣ_
     ℝ! ℝ!
      (≤ᵣ-+o _ _ (b +ᵣ (-ᵣ c)) p)




 a-b≤c⇒a≤c+b : ∀ a b c → a +ᵣ (-ᵣ b) ≤ᵣ c  → a ≤ᵣ c +ᵣ b
 a-b≤c⇒a≤c+b a b c p =
   subst (_≤ᵣ (c +ᵣ b))
     ℝ!
      (≤ᵣ-+o _ _ b p)

 a<c+b⇒a-c<b : ∀ a b c → a <ᵣ c +ᵣ b  → a -ᵣ c <ᵣ b
 a<c+b⇒a-c<b a b c p =
   subst ((a -ᵣ c) <ᵣ_) ℝ! (<ᵣ-+o _ _ (-ᵣ c) p)

 a<c+b⇒a-b<c : ∀ a b c → a <ᵣ c +ᵣ b  → a -ᵣ b <ᵣ c
 a<c+b⇒a-b<c a b c p =
   a<c+b⇒a-c<b a c b (isTrans<≡ᵣ _ _ _ p ℝ!)


 a≤c+b⇒a-c≤b : ∀ a b c → a ≤ᵣ c +ᵣ b  → a -ᵣ c ≤ᵣ b
 a≤c+b⇒a-c≤b a b c p =
   subst ((a -ᵣ c) ≤ᵣ_) ℝ! (≤ᵣ-+o _ _ (-ᵣ c) p)


 a+b≤c⇒b≤c-b : ∀ a b c → a +ᵣ b ≤ᵣ c   → b  ≤ᵣ c -ᵣ a
 a+b≤c⇒b≤c-b a b c p = subst2 _≤ᵣ_
   ℝ! ℝ!
   (≤ᵣ-o+ _ _ (-ᵣ a) p)

 b≤c-b⇒a+b≤c : ∀ a b c → b  ≤ᵣ c -ᵣ a → a +ᵣ b ≤ᵣ c
 b≤c-b⇒a+b≤c a b c p = subst (_ ≤ᵣ_)
   ℝ!
   (≤ᵣ-o+ _ _ a p)

 a-b≤c-d⇒a+d≤c+b : ∀ a b c d → a -ᵣ b ≤ᵣ c -ᵣ d → a +ᵣ d ≤ᵣ c +ᵣ b
 a-b≤c-d⇒a+d≤c+b a b c d x =
   isTrans≡≤ᵣ _ (d +ᵣ a) _ ℝ! (a-b≤c⇒a≤c+b _ _ _
    (isTrans≡≤ᵣ _ _ _ ℝ!
    (b≤c-b⇒a+b≤c _ _ _ x)))

 a+d≤c+b⇒a-b≤c-d : ∀ a b c d → a +ᵣ d ≤ᵣ c +ᵣ b → a -ᵣ b ≤ᵣ c -ᵣ d
 a+d≤c+b⇒a-b≤c-d a b c d x =
   a-b≤c-d⇒a+d≤c+b a (-ᵣ d) c (-ᵣ b)
    (subst2 (λ d b → a +ᵣ d ≤ᵣ c +ᵣ b)
     ℝ! ℝ! x)

 b<c-b⇒a+b<c : ∀ a b c → b  <ᵣ c -ᵣ a → a +ᵣ b <ᵣ c
 b<c-b⇒a+b<c a b c p = subst (_ <ᵣ_)
   ℝ!
   (<ᵣ-o+ _ _ a p)


 ≤-o+-cancel : ∀ m n o →  o +ᵣ m ≤ᵣ o +ᵣ n → m ≤ᵣ n
 ≤-o+-cancel m n o p =
      subst2 (_≤ᵣ_) ℝ! ℝ!
      (≤ᵣ-o+ _ _ (-ᵣ o) p)

 <-o+-cancel : ∀ m n o →  o +ᵣ m <ᵣ o +ᵣ n → m <ᵣ n
 <-o+-cancel m n o p =
      subst2 (_<ᵣ_) ℝ! ℝ!
      (<ᵣ-o+ _ _ (-ᵣ o) p)


 ≤-+o-cancel : ∀ m n o →  m +ᵣ o ≤ᵣ n +ᵣ o → m ≤ᵣ n
 ≤-+o-cancel m n o p =
      subst2 (_≤ᵣ_) ℝ! ℝ!
      (≤ᵣ-+o _ _ (-ᵣ o) p)

 <-+o-cancel : ∀ m n o →  m +ᵣ o <ᵣ n +ᵣ o → m <ᵣ n
 <-+o-cancel m n o p =
      subst2 (_<ᵣ_) ℝ! ℝ!
      (<ᵣ-+o _ _ (-ᵣ o) p)




 x≤y→0≤y-x : ∀ x y →  x ≤ᵣ y  → 0 ≤ᵣ y +ᵣ (-ᵣ x)
 x≤y→0≤y-x x y p =
   subst (_≤ᵣ y +ᵣ (-ᵣ x)) (+-ᵣ x) (≤ᵣ-+o x y (-ᵣ x) p)



 0<y-x→x<y : ∀ x y → 0 <ᵣ y +ᵣ (-ᵣ x) → x <ᵣ y
 0<y-x→x<y x y p =
   subst2 (_<ᵣ_)
    (+IdL x) ℝ!
     (<ᵣ-+o 0 (y +ᵣ (-ᵣ x)) x p)

 x≤y≃0≤y-x : ∀ x y → (x ≤ᵣ y) ≃ (0 ≤ᵣ y -ᵣ x)
 x≤y≃0≤y-x x y =   propBiimpl→Equiv (isProp≤ᵣ _ _) (isProp≤ᵣ _ _)
    (x≤y→0≤y-x x y)
     λ p →  subst2 (_≤ᵣ_)
    (+IdL x) ℝ!
     (≤ᵣ-+o 0 (y +ᵣ (-ᵣ x)) x p)


 x<y≃0<y-x : ∀ x y → (x <ᵣ y) ≃ (0 <ᵣ y -ᵣ x)
 x<y≃0<y-x x y =   propBiimpl→Equiv (isProp<ᵣ _ _) (isProp<ᵣ _ _)
    (x<y→0<y-x x y) (0<y-x→x<y x y)

 x<y≃-y<-x : ∀ x y → (x <ᵣ y) ≃ (-ᵣ y <ᵣ -ᵣ x)
 x<y≃-y<-x x y =   propBiimpl→Equiv (isProp<ᵣ _ _) (isProp<ᵣ _ _)
    (-ᵣ<ᵣ x y) (<ᵣ-ᵣ x y)



 x<y→x-y<0 : ∀ x y →  x <ᵣ y  → x -ᵣ y <ᵣ 0
 x<y→x-y<0 x y p =
   subst (x -ᵣ y <ᵣ_) (+-ᵣ y) (<ᵣ-+o x y (-ᵣ y) p)

 x-y<0→x<y : ∀ x y → x -ᵣ y <ᵣ 0 →  x <ᵣ y
 x-y<0→x<y x y p =

    (0<y-x→x<y _  _ (subst2 (_<ᵣ_) ℝ! ℝ! (-ᵣ<ᵣ (x -ᵣ y) 0 p)))


 x<y≃x-y<0 : ∀ x y → (x <ᵣ y) ≃ (x -ᵣ y <ᵣ 0)
 x<y≃x-y<0 x y =   propBiimpl→Equiv (isProp<ᵣ _ _) (isProp<ᵣ _ _)
    (x<y→x-y<0 x y) (x-y<0→x<y x y)


 x≤y→x-y≤0 : ∀ x y →  x ≤ᵣ y  → x -ᵣ y ≤ᵣ 0
 x≤y→x-y≤0 x y p =
   subst (x -ᵣ y ≤ᵣ_) (+-ᵣ y) (≤ᵣ-+o x y (-ᵣ y) p)

 x-y≤0→x≤y : ∀ x y → x -ᵣ y ≤ᵣ 0 →  x ≤ᵣ y
 x-y≤0→x≤y x y p =

    (invEq (x≤y≃0≤y-x _  _) (subst2 (_≤ᵣ_) ℝ! ℝ! (-ᵣ≤ᵣ (x -ᵣ y) 0 p)))

 x≤y≃x-y≤0 : ∀ x y → (x ≤ᵣ y) ≃ (x -ᵣ y ≤ᵣ 0)
 x≤y≃x-y≤0 x y =   propBiimpl→Equiv (isProp≤ᵣ _ _) (isProp≤ᵣ _ _)
    (x≤y→x-y≤0 x y) (x-y≤0→x≤y x y)



 <ᵣ-o+-cancel : ∀ m n o →  o +ᵣ m <ᵣ o +ᵣ n → m <ᵣ n
 <ᵣ-o+-cancel m n o p =
      subst2 (_<ᵣ_) ℝ! ℝ!
      (<ᵣ-o+ _ _ (-ᵣ o) p)


invℝ'' : Σ (∀ r → ∃[ σ ∈ ℚ₊ ] (rat (fst σ) <ᵣ r) → ℝ)
      λ _ → Σ (∀ r → 0 <ᵣ r → ℝ) (IsContinuousWithPred (λ r → _ , isProp<ᵣ _ _))
invℝ'' = f , (λ r 0<r → f r (lowerℚBound r 0<r)) ,
   ctnF

 where

 2co : ∀ σ σ' r
    → (rat (fst σ ) <ᵣ r)
    → (rat (fst σ') <ᵣ r)
    → fst (Invᵣ-restr σ) r ≡ fst (Invᵣ-restr σ') r

 2co σ σ' = Elimℝ-Prop.go w
  where
  w : Elimℝ-Prop _
  w .Elimℝ-Prop.ratA x σ<x σ'<x =
    cong (rat ∘ fst ∘ invℚ₊)
      (ℚ₊≡ (ℚ.≤→max _ _ (≤ᵣ→≤ℚ _  _ (<ᵣWeaken≤ᵣ _ _ σ<x))
           ∙ sym (ℚ.≤→max _ _ (≤ᵣ→≤ℚ _  _ (<ᵣWeaken≤ᵣ _ _ σ'<x))) ))
  w .Elimℝ-Prop.limA x y R σ<limX σ'<limX = eqℝ _ _ λ ε →
    PT.rec (isProp∼ _ _ _)
      (λ (q , σ⊔<q , q<limX) →
       let φ*ε : ℚ₊
           φ*ε = (((invℚ₊ ((invℚ₊ (σ ℚ₊· σ))
                                   ℚ₊+ (invℚ₊ (σ' ℚ₊· σ'))))
                                   ℚ₊· ε))


           φ*σ : ℚ₊
           φ*σ = (/2₊ (ℚ.<→ℚ₊ (fst σ⊔) q (<ᵣ→<ℚ _ _ σ⊔<q)))

           φ* : ℚ₊
           φ* = ℚ.min₊ (/2₊ φ*ε) φ*σ



           limRestr'' : rat (fst φ*)
               ≤ᵣ (rat q +ᵣ (-ᵣ rat (fst σ⊔))) ·ᵣ rat [ 1 / 2 ]
           limRestr'' =
             let zz = ((ℚ.min≤'
                    ((fst (/2₊ ((invℚ₊ ((invℚ₊ (σ ℚ₊· σ))
                                   ℚ₊+ (invℚ₊ (σ' ℚ₊· σ'))))
                                   ℚ₊· ε))))
                                    (fst (/2₊
                             (ℚ.<→ℚ₊ (fst σ⊔) q (<ᵣ→<ℚ _ _ σ⊔<q))
                          ))))
             in subst (rat (fst φ*) ≤ᵣ_)
                (rat·ᵣrat _ _ ∙ cong (_·ᵣ rat [ 1 / 2 ]) (sym (-ᵣ-rat₂ _ _)))
                  (≤ℚ→≤ᵣ (fst φ*)
                    (fst (/2₊
                             (ℚ.<→ℚ₊ (fst σ⊔) q (<ᵣ→<ℚ _ _ σ⊔<q))
                          )) zz)


           limRestr' : rat (fst φ* ℚ.+ fst φ*)
               ≤ᵣ (lim x y +ᵣ (-ᵣ rat (fst σ⊔)))
           limRestr' =
             let zz : ((rat q +ᵣ (-ᵣ rat (fst σ⊔)))) ≤ᵣ
                        ((lim x y +ᵣ (-ᵣ rat (fst σ⊔))) )
                 zz = ≤ᵣ-+o (rat q) (lim x y) (-ᵣ rat (fst σ⊔))
                          (<ᵣWeaken≤ᵣ _ _ q<limX)
                 zzz' : ∀ φ* → φ* ℚ.· [ pos 2 / 1 ] ≡ φ* ℚ.+ φ*
                 zzz' _ = ℚ!!

             in  subst2 _≤ᵣ_
                    (sym (rat·ᵣrat _ _) ∙
                      cong rat (zzz' (fst φ*)))
                    ℝ!
                   (≤ᵣ-·o _ _ 2 (ℚ.decℚ≤? {0} {2}) (isTrans≤ᵣ _ _ _
                   limRestr'' (≤ᵣ-·o _ _ [ 1 / 2 ] (ℚ.decℚ≤? {0} {[ 1 / 2 ]})
                         zz)))

           zzzz' : ∀ (φ* : ℚ₊) → rat (fst σ⊔) +ᵣ -ᵣ rat (fst φ* ℚ.+ fst φ*) +ᵣ
                          (lim x y +ᵣ -ᵣ rat (fst σ⊔))
                          ≡ lim x y +ᵣ -ᵣ rat (fst φ* ℚ.+ fst φ*)
           zzzz' _ = ℝ!
           zzzz'' : ∀ (φ* : ℚ₊) → rat (fst σ⊔) +ᵣ -ᵣ rat (fst φ* ℚ.+ fst φ*) +ᵣ
                        rat (fst φ* ℚ.+ fst φ*)
                        ≡ rat (fst σ⊔)
           zzzz'' _ = ℝ!
           limRestr : rat (fst σ⊔)
               ≤ᵣ ((lim x y +ᵣ (-ᵣ rat (fst φ* ℚ.+ fst φ*))))
           limRestr = subst2 _≤ᵣ_ (zzzz'' φ*) (zzzz' φ*)
             (≤ᵣ-o+ _ _
               (rat (fst σ⊔) +ᵣ (-ᵣ (rat (fst φ* ℚ.+ fst φ*))))
                 limRestr')

           zzz''' : ∀ (φ* : ℚ₊) → lim x y +ᵣ -ᵣ x φ* +ᵣ (x φ* +ᵣ -ᵣ rat (fst φ* ℚ.+ fst φ*)) ≡
                    lim x y +ᵣ -ᵣ rat (fst φ* ℚ.+ fst φ*)
           zzz''' _ = ℝ!
           zzz'''' : ∀ (φ* : ℚ₊) →  rat (fst φ* ℚ.+ fst φ*) +ᵣ (x φ* +ᵣ -ᵣ rat (fst φ* ℚ.+ fst φ*)) ≡
                      x φ*
           zzz'''' _ = ℝ!

           ∣x-limX∣ : (lim x y +ᵣ (-ᵣ rat (fst φ* ℚ.+ fst φ*))) <ᵣ x φ*

           ∣x-limX∣ =
             let zz = isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                  (subst (_<ᵣ rat (fst φ* ℚ.+ fst φ*))
                   (minusComm-absᵣ _ _)
                   (fst (∼≃abs<ε _ _ (φ* ℚ₊+ φ*))
                   $ 𝕣-lim-self x y φ* φ*))
             in subst2 _<ᵣ_ (zzz''' φ* )
                  (zzz'''' φ* )
                   (<ᵣ-+o _ _ (x φ* +ᵣ (-ᵣ rat (fst φ* ℚ.+ fst φ*))) zz)



           φ : ℚ₊
           φ = (invℚ₊ (σ ℚ₊· σ)) ℚ₊·  φ*
           φ' : ℚ₊
           φ' = (invℚ₊ (σ' ℚ₊· σ')) ℚ₊·  φ*
           σ⊔<Xφ* : rat (fst σ⊔) <ᵣ x φ*
           σ⊔<Xφ* = isTrans≤<ᵣ _ _ _ limRestr ∣x-limX∣
           σ<Xφ* : rat (fst σ) <ᵣ x φ*
           σ<Xφ* = isTrans≤<ᵣ _ _ _
              (≤ℚ→≤ᵣ _ _ (ℚ.≤max (fst σ) (fst σ'))) σ⊔<Xφ*
           σ'<Xφ* : rat (fst σ') <ᵣ x φ*
           σ'<Xφ* = isTrans≤<ᵣ _ _ _
              (≤ℚ→≤ᵣ _ _ (ℚ.≤max' (fst σ) (fst σ'))) σ⊔<Xφ*

           preε'< :  (fst ((invℚ₊ (σ ℚ₊· σ)) ℚ₊·  φ*)
                                   ℚ.+ fst ((invℚ₊ (σ' ℚ₊· σ')) ℚ₊·  φ*))
                                    ℚ.≤ fst (/2₊ ε)
           preε'< = subst2 ℚ._≤_
               ((ℚ.·DistR+ (fst (invℚ₊ (σ ℚ₊· σ))) (fst (invℚ₊ (σ' ℚ₊· σ'))) (fst φ*)))
               ((
                cong (fst (invℚ₊ (σ ℚ₊· σ) ℚ₊+ invℚ₊ (σ' ℚ₊· σ')) ℚ.·_)
                   ((sym ((ℚ.·Assoc (fst (invℚ₊ (invℚ₊ (σ ℚ₊· σ) ℚ₊+ invℚ₊ (σ' ℚ₊· σ'))))
                      (fst ε) (([ 1 / 2 ]))))))
                 ∙ ℚ.y·[x/y] ((invℚ₊ (σ ℚ₊· σ))
                                   ℚ₊+ (invℚ₊ (σ' ℚ₊· σ'))) (fst (/2₊ ε)) ))
               (ℚ.≤-o· _ _ (fst ((invℚ₊ (σ ℚ₊· σ))
                                   ℚ₊+ (invℚ₊ (σ' ℚ₊· σ'))))
                              (ℚ.0≤ℚ₊ ((invℚ₊ (σ ℚ₊· σ))
                                   ℚ₊+ (invℚ₊ (σ' ℚ₊· σ'))))
                             (
                               (ℚ.min≤ (fst (/2₊ φ*ε)) (fst φ*σ))))

           ε'< : 0< (fst ε ℚ.- (fst ((invℚ₊ (σ ℚ₊· σ)) ℚ₊·  φ*)
                                   ℚ.+ fst ((invℚ₊ (σ' ℚ₊· σ')) ℚ₊·  φ*)))
           ε'< = snd (ℚ.<→ℚ₊ (fst ((invℚ₊ (σ ℚ₊· σ)) ℚ₊·  φ*)
                                   ℚ.+ fst ((invℚ₊ (σ' ℚ₊· σ')) ℚ₊·  φ*))
                                    (fst ε)
              (ℚ.isTrans≤< _ _ _ preε'< (x/2<x ε)))


           φ= = ℚ₊≡ {φ*} $ sym (ℚ.[y·x]/y (invℚ₊ (σ ℚ₊· σ)) (fst φ*))

           φ'= = ℚ₊≡ {φ*} $ sym (ℚ.[y·x]/y (invℚ₊ (σ' ℚ₊· σ')) (fst φ*))


           R' : _
           R' = invEq (∼≃≡ _ _) (R φ* σ<Xφ* σ'<Xφ* )
             ((fst ε ℚ.- (fst φ ℚ.+ fst φ')) , ε'<)


       in (lim-lim _ _ ε φ φ' _ _ ε'<
                (((cong ((fst (Invᵣ-restr σ)) ∘ x) (φ=))
                   subst∼[ refl ] (cong ((fst (Invᵣ-restr σ')) ∘ x)
                     (φ'=))) R')))
      (denseℚinℝ (rat (fst σ⊔)) (lim x y) σ⊔<limX)
   where
   σ⊔ = ℚ.max₊ σ σ'

   opaque
    unfolding maxᵣ
    σ⊔<limX : rat (fst σ⊔) <ᵣ lim x y
    σ⊔<limX = max<-lem (rat (fst σ)) (rat (fst σ'))
       (lim x y) σ<limX σ'<limX


  w .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → isSetℝ _ _

 f' : ∀ r → Σ ℚ₊ (λ σ → rat (fst σ) <ᵣ r) → ℝ
 f' r (σ , σ<) = fst (Invᵣ-restr σ) r

 f : ∀ r → ∃[ σ ∈ ℚ₊ ] (rat (fst σ) <ᵣ r) → ℝ
 f r = PT.rec→Set {B = ℝ} isSetℝ (f' r)
          λ (σ , σ<r) (σ' , σ'<r) → 2co σ σ' r σ<r σ'<r


 ctnF : ∀ u ε u∈ → ∃[ δ ∈ ℚ₊ ]
                 (∀ v v∈P → u ∼[ δ ] v →
                  f u (lowerℚBound u u∈) ∼[ ε ] f v (lowerℚBound v v∈P))
 ctnF u ε u∈ = ctnF' (lowerℚBound u u∈)

  where
  ctnF' : ∀ uu → ∃[ δ ∈ ℚ₊ ]
                 (∀ v v∈P → u ∼[ δ ] v →
                  f u uu ∼[ ε ] f v (lowerℚBound v v∈P))
  ctnF' = PT.elim (λ _ → squash₁)
    λ (σ , σ<u) →
     let zz : ∃[ δ ∈ ℚ₊ ] ((v₁ : ℝ) →  u ∼[ δ ] v₁
                      → f u ∣ σ , σ<u ∣₁ ∼[ ε ] Invᵣ-restr σ .fst v₁)
         zz = Lipschitz→IsContinuous (invℚ₊ (σ ℚ₊· σ))
                 (λ z → Invᵣ-restr σ .fst z)
                 (snd (Invᵣ-restr σ) ) u ε

         zz' : ∃[ δ ∈ ℚ₊ ] (∀ v v∈ →
                    u ∼[ δ ] v →
                  f u ∣ σ , σ<u ∣₁ ∼[ ε ] f v (lowerℚBound v v∈))
         zz' = PT.rec2 squash₁
             (uncurry (λ δ R (η , η<u-σ)  →
               let δ' = ℚ.min₊ δ η
               in ∣ δ' ,
                   (λ v v∈ →
                      PT.elim {P = λ vv → u ∼[ δ' ] v →
                               f u ∣ σ , σ<u ∣₁ ∼[ ε ] f v vv}
                          (λ _ → isPropΠ λ _ → isProp∼ _ _ _)
                          (λ (σ' , σ'<v) u∼v →
                             let zuz :  (u +ᵣ (-ᵣ v)) <ᵣ rat (fst η)
                                 zuz = isTrans≤<ᵣ _ _ _ (≤absᵣ (u +ᵣ (-ᵣ v)))
                                    (isTrans<≤ᵣ _ _ _ (fst (∼≃abs<ε _ _ _) u∼v)
                                       (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) (fst η))))

                                 u-η≤v : u +ᵣ (-ᵣ rat (fst η)) ≤ᵣ v
                                 u-η≤v = a-b≤c⇒a-c≤b _ _ _
                                          (<ᵣWeaken≤ᵣ _ _ zuz)
                                 σ<u-η : rat (fst σ) <ᵣ u +ᵣ (-ᵣ rat (fst η))
                                 σ<u-η = a<b-c⇒c<b-a _ _ _ η<u-σ
                                 σ<v : rat (fst σ) <ᵣ v
                                 σ<v = isTrans<≤ᵣ _ _ _ σ<u-η u-η≤v
                             in subst (f u ∣ σ , σ<u ∣₁ ∼[ ε ]_)
                                        (2co σ σ' v σ<v σ'<v)
                                        (R v
                                         (∼-monotone≤ (ℚ.min≤ _ _) u∼v)))
                          ((lowerℚBound v v∈))) ∣₁
                          ))
           zz (<ᵣ→Δ _ _ σ<u)
     in zz'

opaque
 invℝ' : Σ (∀ r → 0 <ᵣ r → ℝ) (IsContinuousWithPred (λ r → _ , isProp<ᵣ _ _))
 invℝ' = snd invℝ''

 invℝ'-rat : ∀ q p' p →
              fst invℝ' (rat q) p ≡
               rat (fst (invℚ₊ (q , p')))
 invℝ'-rat q p' p = PT.elim (λ xx →
                        isSetℝ ((fst invℝ'') (rat q) xx) _)
                         (λ x → cong (rat ∘ fst ∘ invℚ₊)
                         (ww x)) (lowerℚBound (rat q) p)

  where
  ww : ∀ (x : Σ ℚ₊ (λ v → rat (fst v) <ᵣ rat q)) → (ℚ.maxWithPos (fst x) q) ≡ (q , p')
  ww x = ℚ₊≡ (ℚ.≤→max (fst (fst x)) q (ℚ.<Weaken≤ _ _ (<ᵣ→<ℚ _ _ (snd x))))


opaque

 invℝ'-pos : ∀ u p →
              0 <ᵣ fst invℝ' u p
 invℝ'-pos u p = PT.rec (isProp<ᵣ _ _)
   (λ (n , u<n) →
     PT.rec (isProp<ᵣ _ _)
        (λ (σ , X) →
          PT.rec (isProp<ᵣ _ _)
            (λ ((q , q'*) , x* , x' , x''*) →
              let q' : ℚ
                  q' = ℚ.min q'* [ pos (ℕ₊₁→ℕ n) / 1 ]
                  x : q' ℚ.- q ℚ.< fst σ
                  x = ℚ.isTrans≤< _ _ _ (
                     ℚ.≤-+o q' q'* (ℚ.- q)
                       (ℚ.min≤ q'* [ pos (ℕ₊₁→ℕ n) / 1 ])) x*
                  x'' : u <ᵣ rat q'
                  x'' =  isTrans<≡ᵣ _ _ _ (<min-lem _ _ _ x''* (isTrans≤<ᵣ _ _ _ (≤absᵣ u) u<n))
                          (minᵣ-rat _ _)


                  0<q' : 0 <ᵣ rat q'
                  0<q' = isTrans<ᵣ _ _ _ p x''
                  z' : rat [ 1 / n ] ≤ᵣ invℝ' .fst (rat q') 0<q'
                  z' = subst (rat [ 1 / n ] ≤ᵣ_) (sym (invℝ'-rat q'
                                (ℚ.<→0< q' (<ᵣ→<ℚ _ _ 0<q')) 0<q'))
                             (≤ℚ→≤ᵣ _ _ (
                              ℚ.invℚ≤invℚ ([ n / 1 ]₊)
                                (q' , ℚ.<→0< q' (<ᵣ→<ℚ [ pos 0 / 1 ] q' 0<q'))
                                 ((ℚ.min≤' q'* [ pos (ℕ₊₁→ℕ n) / 1 ]))))
                  z : ((invℝ' .fst (rat q') 0<q') +ᵣ (-ᵣ rat [ 1 / n ]))
                        <ᵣ
                        (invℝ' .fst u p)
                  z = a-b<c⇒a-c<b _ (invℝ' .fst u p) _
                        (isTrans≤<ᵣ _ _ _ (≤absᵣ _) (fst (∼≃abs<ε _ _ _)
                       (sym∼ _ _ _  (X (rat q') 0<q'
                        (sym∼ _ _ _ (invEq (∼≃abs<ε (rat q') u σ) (
                           isTrans≤<ᵣ _ _ _
                             (subst (_≤ᵣ ((rat q') +ᵣ (-ᵣ (rat q))))
                               (sym (absᵣNonNeg (rat q' +ᵣ (-ᵣ u))
                                 (x≤y→0≤y-x _ _ (<ᵣWeaken≤ᵣ _ _ x''))))
                               (≤ᵣ-o+ _ _ _ (-ᵣ≤ᵣ _ _ (<ᵣWeaken≤ᵣ _ _ x'))))
                            (isTrans≡<ᵣ _ _ _ ((-ᵣ-rat₂ _ _)) (<ℚ→<ᵣ _ _ x)))))))))


              in isTrans≤<ᵣ _ _ _ (x≤y→0≤y-x _ _ z') z
              )
            (∃rationalApprox u σ))
       (snd invℝ' u ([ 1 / n ]₊) p))
   (getClamps u)


opaque
 invℝ₊ : ℝ₊ → ℝ₊
 invℝ₊ (y , 0<y) = fst invℝ' y 0<y , invℝ'-pos y 0<y

 invℝ₊-impl : ∀ y  → invℝ₊ y ≡ (fst invℝ' (fst y) (snd y) , invℝ'-pos (fst y) (snd y))
 invℝ₊-impl _ = refl

signᵣ : ∀ r → 0 ＃ r → ℝ
signᵣ _ = ⊎.rec (λ _ → rat 1) (λ _ → rat -1)

0<signᵣ : ∀ r 0＃r → 0 <ᵣ r → 0 <ᵣ signᵣ r 0＃r
0<signᵣ r (inl x) _ = <ℚ→<ᵣ _ _ ((𝟚.toWitness {Q = ℚ.<Dec 0 1} _))
0<signᵣ r (inr x) y = ⊥.rec (isAsym<ᵣ _ _ x y)

signᵣ-rat : ∀ r p  → signᵣ (rat r) p ≡ rat (ℚ.sign r)
signᵣ-rat r (inl x) = cong rat (sym (fst (ℚ.<→sign r) (<ᵣ→<ℚ _ _ x)))
signᵣ-rat r (inr x) = cong rat (sym (snd (snd (ℚ.<→sign r)) (<ᵣ→<ℚ _ _ x)))

0＃ₚ : ℝ → hProp ℓ-zero
0＃ₚ r = 0 ＃ r , isProp＃ _ _


-- HoTT Theorem (11.3.47)

opaque
 -- unfolding _<ᵣ_
 IsContinuousWithPredSignᵣ : IsContinuousWithPred 0＃ₚ signᵣ
 IsContinuousWithPredSignᵣ u ε =
  ⊎.elim
   (λ 0<u → PT.map (λ (q , 0<q , q<u) →
              ((q , ℚ.<→0< q (<ᵣ→<ℚ _ _ 0<q))) ,
               λ v v∈P v∼u →
                 ⊎.elim {C = λ v∈P → signᵣ u (inl 0<u) ∼[ ε ] signᵣ v v∈P}
                   (λ _ → refl∼ _ _)
                   (⊥.rec ∘ (isAsym<ᵣ 0 v
                     (subst2 _<ᵣ_ ℝ! ℝ!
                          (<ᵣMonotone+ᵣ _ _ _ _ (-ᵣ<ᵣ (rat q) _ q<u)
                        (a-b<c⇒a<c+b u v _ ((isTrans≤<ᵣ (u +ᵣ -ᵣ v) (absᵣ (u +ᵣ -ᵣ v)) _
                          (≤absᵣ (u -ᵣ v))
                           ((fst (∼≃abs<ε u v (q , ℚ.<→0< q (<ᵣ→<ℚ 0 q 0<q))) v∼u))))
                           ))))) v∈P)
          (denseℚinℝ 0 u 0<u))
   (λ u<0 → PT.map (λ (q , u<q , q<0) →
              (ℚ.- q , ℚ.<→0< (ℚ.- q) (ℚ.minus-< q _ (<ᵣ→<ℚ _ _ q<0))) ,
               λ v v∈P v∼u →
                 ⊎.elim {C = λ v∈P → signᵣ u (inr u<0) ∼[ ε ] signᵣ v v∈P}
                   ((⊥.rec ∘ (isAsym<ᵣ v 0
                     (subst2 _<ᵣ_  ℝ!
                      (+-ᵣ (rat q)) (<ᵣMonotone+ᵣ u _ _ _
                        u<q (isTrans<≡ᵣ _ _ _ (isTrans≤<ᵣ (v -ᵣ u) _ _ (≤absᵣ (v -ᵣ u))
                           (fst (∼≃abs<ε _ _ _) (sym∼ _ _ _ v∼u))) (sym (-ᵣ-rat q))))))))
                   (λ _ → refl∼ _ _) v∈P)
              (denseℚinℝ u 0 u<0))



-ᵣ≡[-1·ᵣ] : ∀ x → -ᵣ x ≡ (-1) ·ᵣ x
-ᵣ≡[-1·ᵣ] = ≡Continuous _ _
   IsContinuous-ᵣ
   (IsContinuous·ᵣL -1)
   λ r → -ᵣ-rat _ ∙ rat·ᵣrat _ _




isOpenPred0＃ : ⟨ openPred 0＃ₚ ⟩
isOpenPred0＃ x =
 ⊎.rec
   (PT.map (map-snd ((inl ∘_) ∘_)) ∘ openPred< 0 x)
   (PT.map (map-snd ((inr ∘_) ∘_)) ∘ openPred> 0 x)



·invℝ' : ∀ r 0<r → (r ·ᵣ fst invℝ' (r) 0<r) ≡ 1
·invℝ' r =  ∘diag $
  ≡ContinuousWithPred (pred> 0) (pred> 0) (openPred< 0) (openPred< 0)
   _ _ (cont₂·ᵣWP (pred> 0) _ _
          (AsContinuousWithPred (pred> 0) _ IsContinuousId)
          (snd invℝ'))
        (AsContinuousWithPred (pred> 0) _ (IsContinuousConst 1))
        (λ r r∈ r∈' → cong (rat r ·ᵣ_) (invℝ'-rat r _ r∈)
          ∙∙ sym (rat·ᵣrat _ _) ∙∙ cong rat (ℚ.x·invℚ₊[x]
            (r , ℚ.<→0< _ (<ᵣ→<ℚ _ _ r∈)))) r

opaque
 unfolding _≤ᵣ_
 ≤ContWP : ∀ {P f₀ f₁} → ⟨ openPred P ⟩
          → IsContinuousWithPred P f₀
          → IsContinuousWithPred P f₁
          → (∀ u u∈ → f₀ (rat u) u∈ ≤ᵣ f₁ (rat u) u∈)
              → ∀ x x∈ → f₀ x x∈  ≤ᵣ f₁ x x∈
 ≤ContWP {P} {f₀} {f₁} oP f₀C f₁C X x x∈ =
     ≡ContinuousWithPred P P  oP oP
     _ _
     (contDiagNE₂WP maxR P _ _ f₀C f₁C)
     f₁C (λ r r∈ r∈' →
        X _ _
         ∙ cong (f₁ (rat r)) (∈-isProp P _ r∈ r∈')) x x∈ x∈

 ≤ContWP＃≤ : ∀ {f₀ f₁} q → 0 ℚ.< q
          → IsContinuousWithPred 0＃ₚ f₀
          → IsContinuousWithPred 0＃ₚ f₁
          → (∀ u u∈ → u ℚ.≤ q → f₀ (rat u) u∈ ≤ᵣ f₁ (rat u) u∈)
              → ∀ x x∈ → x ≤ᵣ rat q →  f₀ x x∈  ≤ᵣ f₁ x x∈
 ≤ContWP＃≤ {f₀} {f₁} q 0<q f₀C f₁C X x x∈ x≤q =
   let ＃min : ∀ r → 0 ＃ r → 0 ＃ minᵣ r (rat q)
       ＃min r = ⊎.map
         (λ 0<r → <min-lem _ _ 0 0<r (<ℚ→<ᵣ _ _ 0<q))
         λ r<0 → isTrans≤<ᵣ (minᵣ r (rat q)) r _ ((min≤ᵣ r (rat q))) r<0
       z = ≤ContWP {0＃ₚ} {λ r z → f₀ (minᵣ r (rat q)) (＃min r z)}
                       {λ r z → f₁ (minᵣ r (rat q)) (＃min r z)}
              isOpenPred0＃
                (IsContinuousWP∘ 0＃ₚ 0＃ₚ _ _ _
                 f₀C (AsContinuousWithPred 0＃ₚ _ (IsContinuousMinR _)))
                (IsContinuousWP∘ 0＃ₚ 0＃ₚ _ _ _
                 f₁C (AsContinuousWithPred 0＃ₚ _ (IsContinuousMinR _)))
                (λ u u∈ →
                  X (ℚ.min u q) (＃min (rat u) u∈) (ℚ.min≤' u _))
                 x x∈
   in subst {A = Σ _ (_∈ 0＃ₚ) } (λ (x , x∈) → f₀ x x∈ ≤ᵣ f₁ x x∈)
        (Σ≡Prop (∈-isProp 0＃ₚ) (≤→minᵣ _ _ x≤q))
          z

 ≤ContWP＃≤' : ∀ {f₀ f₁} q → q ℚ.< 0
          → IsContinuousWithPred 0＃ₚ f₀
          → IsContinuousWithPred 0＃ₚ f₁
          → (∀ u u∈ → q ℚ.≤ u → f₀ (rat u) u∈ ≤ᵣ f₁ (rat u) u∈)
              → ∀ x x∈ → rat q ≤ᵣ x →  f₀ x x∈  ≤ᵣ f₁ x x∈
 ≤ContWP＃≤' {f₀} {f₁} q q<0 f₀C f₁C X x x∈ q≤x =
   let ＃max : ∀ r → 0 ＃ r → 0 ＃ maxᵣ r (rat q)
       ＃max r =  ⊎.map
         (λ 0<r → isTrans<≤ᵣ 0 _ _ 0<r (≤maxᵣ r (rat q)) )
         λ r<0 → max<-lem r (rat q) _ r<0 (<ℚ→<ᵣ _ _ q<0) --isTrans≤<ᵣ _ _ _ (min≤ᵣ _ _) r<0

       z = ≤ContWP {0＃ₚ} {λ r z → f₀ (maxᵣ r (rat q)) (＃max r z)}
                       {λ r z → f₁ (maxᵣ r (rat q)) (＃max r z)}
              isOpenPred0＃
                (IsContinuousWP∘ 0＃ₚ 0＃ₚ _ _ _
                 f₀C (AsContinuousWithPred 0＃ₚ _ (IsContinuousMaxR _)))
                (IsContinuousWP∘ 0＃ₚ 0＃ₚ _ _ _
                 f₁C (AsContinuousWithPred 0＃ₚ _ (IsContinuousMaxR _)))
                (λ u u∈ →
                  X (ℚ.max u q) (＃max (rat u) u∈) (ℚ.≤max' u q))
                 x x∈
   in subst {A = Σ _ (_∈ 0＃ₚ) } (λ (x , x∈) → f₀ x x∈ ≤ᵣ f₁ x x∈)
        (Σ≡Prop (∈-isProp 0＃ₚ) (maxᵣComm x (rat q) ∙ ≤→maxᵣ (rat q) _ q≤x))
          z


sign²=1 :  ∀ r 0＃r → (signᵣ r 0＃r) ·ᵣ (signᵣ r 0＃r) ≡ 1
sign²=1 r = ⊎.elim
    (λ _ → sym (rat·ᵣrat _ _))
    (λ _ → sym (rat·ᵣrat _ _))

opaque
 unfolding absᵣ
 sign·absᵣ : ∀ r 0＃r → absᵣ r ·ᵣ (signᵣ r 0＃r) ≡ r
 sign·absᵣ r = ∘diag $
   ≡ContinuousWithPred 0＃ₚ 0＃ₚ isOpenPred0＃ isOpenPred0＃
       (λ r 0＃r → absᵣ r ·ᵣ (signᵣ r 0＃r))
        (λ r _ → r)
         (cont₂·ᵣWP 0＃ₚ _ _
           (AsContinuousWithPred 0＃ₚ _ IsContinuousAbsᵣ)
           IsContinuousWithPredSignᵣ)
         (AsContinuousWithPred 0＃ₚ _ IsContinuousId)
         (λ r 0＃r 0＃r' → (cong₂ _·ᵣ_ refl (signᵣ-rat r 0＃r)
           ∙ sym (rat·ᵣrat _ _))
           ∙ cong rat (cong (ℚ._· ℚ.sign r) (sym (ℚ.abs'≡abs r))
            ∙ ℚ.sign·abs r) ) r


 ·sign-flip≡ : ∀ r 0＃r → absᵣ r ≡ r ·ᵣ (signᵣ r 0＃r)
 ·sign-flip≡ r 0＃r =
  (sym (𝐑'.·IdR' _ _ (sign²=1 r 0＃r)) ∙ ·ᵣAssoc _ _ _)
  ∙ cong (_·ᵣ (signᵣ r 0＃r)) (sign·absᵣ r 0＃r)

-- HoTT Theorem (11.3.47)

opaque
 unfolding absᵣ -ᵣ_
 absᵣNeg : ∀ x → x <ᵣ 0 → absᵣ x ≡ -ᵣ x
 absᵣNeg x x<0 = -absᵣ x ∙ absᵣPos _ (-ᵣ<ᵣ x _ x<0)


opaque
 unfolding -ᵣ_  absᵣ
 invℝ : ∀ r → 0 ＃ r → ℝ
 invℝ r 0＃r = signᵣ r 0＃r ·ᵣ fst invℝ' (absᵣ r) (0＃→0<abs r 0＃r)


 invℝimpl : ∀ r 0＃r → invℝ r 0＃r ≡
             signᵣ r 0＃r ·ᵣ fst invℝ' (absᵣ r) (0＃→0<abs r 0＃r)

 invℝimpl r 0＃r = refl

 invℝ≡ : ∀ r 0＃r 0＃r' →
            invℝ r 0＃r ≡ invℝ r 0＃r'
 invℝ≡ r 0＃r 0＃r' = cong (invℝ r) (isProp＃ _ _ _ _)

 IsContinuousWithPredInvℝ : IsContinuousWithPred (λ _ → _ , isProp＃ _ _) invℝ
 IsContinuousWithPredInvℝ =
    IsContinuousWP∘ 0＃ₚ 0＃ₚ _ _ (λ r x → x)
    (cont₂·ᵣWP 0＃ₚ _ _
        IsContinuousWithPredSignᵣ (IsContinuousWP∘ (pred> 0) 0＃ₚ
            _ _ 0＃→0<abs (snd invℝ')
          (AsContinuousWithPred 0＃ₚ _ IsContinuousAbsᵣ)))
      (AsContinuousWithPred 0＃ₚ
        _ IsContinuousId)


 invℝ-rat : ∀ q p p' → invℝ (rat q) p ≡ rat (ℚ.invℚ q p')
 invℝ-rat q p p' =
   cong₂ _·ᵣ_ (signᵣ-rat q p) (invℝ'-rat _ _ _) ∙ sym (rat·ᵣrat _ _)


 invℝ-pos : ∀ x → (p : 0 <ᵣ x) → 0 <ᵣ invℝ x (inl p)
 invℝ-pos x p = subst (0 <ᵣ_) (sym (·IdL _))
     (invℝ'-pos (absᵣ x) (0＃→0<abs x (inl p)))


 invℝ-neg : ∀ x → (p : x <ᵣ 0) → invℝ x (inr p) <ᵣ 0
 invℝ-neg x p =
      subst (_<ᵣ 0)
        (-ᵣ≡[-1·ᵣ] _)
        (-ᵣ<ᵣ 0 _ (invℝ'-pos (absᵣ x) (0＃→0<abs x (inr p))))

 invℝ0＃ : ∀ r 0＃r → 0 ＃ (invℝ r 0＃r)
 invℝ0＃ r = ⊎.elim (inl ∘ invℝ-pos r)
                    (inr ∘ invℝ-neg r)



 invℝInvol : ∀ r 0＃r → invℝ (invℝ r 0＃r) (invℝ0＃ r 0＃r) ≡ r
 invℝInvol r 0＃r = ≡ContinuousWithPred
   0＃ₚ 0＃ₚ isOpenPred0＃ isOpenPred0＃
    (λ r 0＃r → invℝ (invℝ r 0＃r) (invℝ0＃ r 0＃r)) (λ x _ → x)
     (IsContinuousWP∘ 0＃ₚ 0＃ₚ _ _ invℝ0＃
       IsContinuousWithPredInvℝ IsContinuousWithPredInvℝ)
     (AsContinuousWithPred 0＃ₚ
        _ IsContinuousId)
         (λ r 0＃r 0＃r' →
           let 0#r = (fst (rat＃ 0 r) 0＃r)
               0#InvR = ℚ.0#invℚ r 0#r
           in  cong₂ invℝ (invℝ-rat _ _ 0#r)
                  (isProp→PathP (λ i → isProp＃ _ _) _ _)

              ∙∙ invℝ-rat ((invℚ r (fst (rat＃ [ pos 0 / 1+ 0 ] r) 0＃r)))
                    (invEq (rat＃ 0 _) 0#InvR)
                     (ℚ.0#invℚ r (fst (rat＃ [ pos 0 / 1+ 0 ] r) 0＃r))
                ∙∙ cong rat (ℚ.invℚInvol r 0#r 0#InvR)
             )
    r 0＃r 0＃r

 x·invℝ[x] : ∀ r 0＃r → r ·ᵣ (invℝ r 0＃r) ≡ 1
 x·invℝ[x] r 0＃r =
   cong (_·ᵣ (invℝ r 0＃r)) (sym (sign·absᵣ r 0＃r))
    ∙∙ sym (·ᵣAssoc _ _ _)
    ∙∙ (cong (absᵣ r ·ᵣ_) (·ᵣAssoc _ _ _
      ∙ cong (_·ᵣ (fst invℝ' (absᵣ r) (0＃→0<abs r 0＃r)))
         (sign²=1 r 0＃r) ∙ ·IdL (fst invℝ' (absᵣ r) (0＃→0<abs r 0＃r)))
    ∙ ·invℝ' (absᵣ r) (0＃→0<abs r 0＃r))

 invℝ₊≡invℝ : ∀ x 0＃x → fst (invℝ₊ x) ≡ invℝ (fst x) 0＃x
 invℝ₊≡invℝ x (inl x₁) =
  cong fst (invℝ₊-impl x) ∙ (cong (uncurry (fst invℝ'))
   (ℝ₊≡ (sym (absᵣPos _ x₁)))
  ∙ sym (·IdL _)) ∙ sym (invℝimpl _ _)
 invℝ₊≡invℝ x (inr x₁) = ⊥.rec (isAsym<ᵣ _ _ x₁ (snd x))


 x·invℝ₊[x] : ∀ x → (fst x) ·ᵣ fst (invℝ₊ x) ≡ 1
 x·invℝ₊[x] x = cong ((fst x) ·ᵣ_) (invℝ₊≡invℝ x _)
   ∙ x·invℝ[x] (fst x) (inl (snd x))

_／ᵣ[_,_] : ℝ → ∀ r → 0 ＃ r  → ℝ
q ／ᵣ[ r , 0＃r ] = q ·ᵣ (invℝ r 0＃r)

_／ᵣ₊_ : ℝ → ℝ₊  → ℝ
q ／ᵣ₊ r = q ·ᵣ fst (invℝ₊ r)


[x·y]/yᵣ : ∀ q r → (0＃r : 0 ＃ r) →
               ((q ·ᵣ r) ／ᵣ[ r , 0＃r ]) ≡ q
[x·y]/yᵣ q r 0＃r = ℝ! ∙∙ cong (q ·ᵣ_) (x·invℝ[x] r 0＃r) ∙∙ ℝ!




[x/₊y]·yᵣ : ∀ q r →
               (q ／ᵣ₊ r ) ·ᵣ (fst r) ≡ q
[x/₊y]·yᵣ q r = ℝ! ∙∙ cong (q ·ᵣ_) (x·invℝ₊[x] r) ∙∙ ℝ!


[x·yᵣ]/₊y : ∀ q r →
               ((q ·ᵣ (fst r)) ／ᵣ₊ r )  ≡ q
[x·yᵣ]/₊y q r =
      ℝ! ∙∙ cong (q ·ᵣ_) (x·invℝ₊[x] r) ∙∙ ℝ!



[x/y]·yᵣ : ∀ q r → (0＃r : 0 ＃ r) →
               (q ／ᵣ[ r , 0＃r ]) ·ᵣ r ≡ q
[x/y]·yᵣ q r 0＃r =
      ℝ! ∙∙ cong (q ·ᵣ_) (x·invℝ[x] r 0＃r) ∙∙ ℝ!

x/y≡z→x≡z·y : ∀ x q r → (0＃r : 0 ＃ r)
               → (x ／ᵣ[ r , 0＃r ]) ≡ q
               → x ≡ q ·ᵣ r
x/y≡z→x≡z·y x q r 0＃r p =
    sym ([x/y]·yᵣ _ _ _) ∙ cong (_·ᵣ r) p

x/₊y≡z→x≡z·y : ∀ x q r
               → (x ／ᵣ₊ r) ≡ q
               → x ≡ q ·ᵣ (fst r)
x/₊y≡z→x≡z·y x q r p =
    sym ([x/₊y]·yᵣ _ _) ∙ cong (_·ᵣ fst r) p


x·y≡z→x≡z/y : ∀ x q r → (0＃r : 0 ＃ r)
               → (x ·ᵣ r) ≡ q
               → x ≡ q ／ᵣ[ r , 0＃r ]
x·y≡z→x≡z/y x q r 0＃r p =
    sym ([x·y]/yᵣ _ _ _) ∙ cong (_／ᵣ[ r , 0＃r ]) p



x·y≡z→x≡z/₊y : ∀ x q r
               → (x ·ᵣ fst r) ≡ q
               → x ≡ q ／ᵣ₊ r
x·y≡z→x≡z/₊y x q r  p =
    sym ([x·yᵣ]/₊y _ _) ∙ cong (_／ᵣ₊ r) p


x·rat[α]+x·rat[β]=x : ∀ x →
    ∀ {α β : ℚ} → {𝟚.True (ℚ.discreteℚ (α ℚ.+ β) 1)} →
                   (x ·ᵣ rat α) +ᵣ (x ·ᵣ rat β) ≡ x
x·rat[α]+x·rat[β]=x x {α} {β} {p} =
       ℝ! ∙∙ cong (x ·ᵣ_) (+ᵣ-rat α β ∙ decℚ≡ᵣ? {_} {_} {p}) ∙∙ ℝ!

x/y=x/z·z/y : ∀ x q r → (0＃q : 0 ＃ q) → (0＃r : 0 ＃ r)
              → x ／ᵣ[ q , 0＃q ] ≡
                  (x ／ᵣ[ r , 0＃r ]) ·ᵣ (r ／ᵣ[ q , 0＃q ])
x/y=x/z·z/y x q r 0＃q 0＃r =
  cong (_／ᵣ[ q , 0＃q ]) (sym ([x/y]·yᵣ x r 0＃r)) ∙ ℝ!

invℝ1 : (0＃1 : 0 ＃ 1) → invℝ 1 0＃1 ≡ 1
invℝ1 0＃1 =
   ℝ! ∙ x·invℝ[x] (rat 1) 0＃1


invℝ· : ∀ x y 0＃x 0＃y 0＃x·y →
          invℝ (x ·ᵣ y) 0＃x·y ≡
            (invℝ x 0＃x) ·ᵣ (invℝ y 0＃y)
invℝ· x y 0＃x 0＃y 0＃x·y = sym (·IdL _) ∙
  sym (x·y≡z→x≡z/y _ _ _ _
    (·ᵣComm _ _
     ∙∙    sym (·ᵣAssoc _ _ _)
        ∙∙ cong (x ·ᵣ_) (·ᵣAssoc _ _ _ ∙ ·ᵣComm _ _)
        ∙∙ (·ᵣAssoc _ _ _)
     ∙∙ cong₂ _·ᵣ_ (x·invℝ[x] x 0＃x) (x·invℝ[x] y 0＃y) ∙ ·IdL _ ))
   ∙ ·ᵣComm _ _

-＃ : ∀ x y → x ＃ y → (-ᵣ x) ＃ (-ᵣ y)
-＃ x y p = ⊎.map (-ᵣ<ᵣ _ _) (-ᵣ<ᵣ _ _) (isSym＃ _ _ p)


opaque
 unfolding -ᵣ_

 -invℝ : ∀ x y → -ᵣ (invℝ x y) ≡ invℝ (-ᵣ x) (subst (_＃ (-ᵣ x)) (-ᵣ-rat 0) (-＃ _ _ y)) -- -＃ _ _ y
 -invℝ x y =
   (cong -ᵣ_ (sym (·IdL _)) ∙ sym (-ᵣ· _ _) ∙
      cong (_·ᵣ invℝ x y) (sym (invℝ-rat _ (inr (decℚ<ᵣ? { -1} {0})) (inr ℚ.decℚ<?))))
       ∙ sym (invℝ· _ _ _ _
         (subst (0 ＃_) ((cong -ᵣ_ (sym (·IdL _))) ∙ sym (-ᵣ· _ _)) (-＃ 0 x y)))
    ∙ cong₂ invℝ (-ᵣ· _ _ ∙ cong -ᵣ_ (𝐑'.·IdL' _ _ refl ))
     (toPathP (isProp＃ _ _ _ _))

 absᵣ-invℝ : ∀ x y → absᵣ (invℝ x y) ≡ fst (invℝ₊ (absᵣ x , 0＃→0<abs _ y))
 absᵣ-invℝ x (inl x₁) = cong absᵣ (sym (invℝ₊≡invℝ (x , x₁) (inl x₁))) ∙∙
    absᵣPos _ (snd (invℝ₊ (x , x₁))) ∙∙
     cong (fst ∘ invℝ₊) (ℝ₊≡ (sym (absᵣPos x x₁)))
 absᵣ-invℝ x (inr x₁) = absᵣNeg _ (invℝ-neg _ x₁)
   ∙ -invℝ _ _  ∙ sym (invℝ₊≡invℝ (-ᵣ x , -ᵣ<ᵣ x _ x₁) _)
    ∙ cong (fst ∘ invℝ₊) (ℝ₊≡ (sym (absᵣNeg _ x₁)))



opaque
 unfolding _≤ᵣ_


 ≤ᵣ-·ᵣo : ∀ m n o → 0 ≤ᵣ o  →  m ≤ᵣ n → (m ·ᵣ o ) ≤ᵣ (n ·ᵣ o)
 ≤ᵣ-·ᵣo m n o 0≤o m≤n = subst (λ o →
    (m ·ᵣ o ) ≤ᵣ (n ·ᵣ o)) 0≤o (w ∙
       cong (_·ᵣ maxᵣ (rat [ pos 0 / 1+ 0 ]) o) m≤n)
  where
  w : maxᵣ (m ·ᵣ maxᵣ 0 o ) (n ·ᵣ maxᵣ 0 o) ≡  (maxᵣ m n ·ᵣ maxᵣ 0 o)
  w = ≡Continuous _ _
      (cont₂maxᵣ _ _
        ((IsContinuous∘ _ _
          (IsContinuous·ᵣL m) (IsContinuousMaxL 0)  ))
        ((IsContinuous∘ _ _
          (IsContinuous·ᵣL n) (IsContinuousMaxL 0)  )))
      (IsContinuous∘ _ _
          (IsContinuous·ᵣL _) (IsContinuousMaxL 0)  )
       (λ o' →
         ≡Continuous _ _
           (IsContinuous∘ _ _ (IsContinuousMaxR ((n ·ᵣ maxᵣ 0 (rat o'))))
                 (IsContinuous·ᵣR (maxᵣ 0 (rat o'))) )
           (IsContinuous∘ _ _  (IsContinuous·ᵣR (maxᵣ 0 (rat o')))
                                 (IsContinuousMaxR n))
           (λ m' →
             ≡Continuous
               (λ n → maxᵣ (rat m' ·ᵣ maxᵣ 0 (rat o') ) (n ·ᵣ maxᵣ 0 (rat o')))
               (λ n →  maxᵣ (rat m') n ·ᵣ maxᵣ 0 (rat o'))
               ((IsContinuous∘ _ _
                 (IsContinuousMaxL (((rat m') ·ᵣ maxᵣ 0 (rat o'))))
                 (IsContinuous·ᵣR (maxᵣ 0 (rat o'))) ))
               (IsContinuous∘ _ _ ((IsContinuous·ᵣR (maxᵣ 0 (rat o'))))
                   (IsContinuousMaxL (rat m')))
               (λ n' →
                  (cong₂ maxᵣ (sym (rat·ᵣrat _ _)) (sym (rat·ᵣrat _ _)))
                   ∙∙ cong rat (sym (ℚ.·MaxDistrℚ' m' n' (ℚ.max 0 o')
                       (ℚ.≤max 0 o'))) ∙∙
                   rat·ᵣrat _ _
                  ) n) m) o

 ≤ᵣ-o·ᵣ : ∀ m n o → 0 ≤ᵣ o →  m ≤ᵣ n → (o ·ᵣ m   ) ≤ᵣ (o ·ᵣ n)
 ≤ᵣ-o·ᵣ m n o 0≤o p = subst2 _≤ᵣ_
   (·ᵣComm _ _)
   (·ᵣComm _ _)
   (≤ᵣ-·ᵣo m n o 0≤o p)

≤ᵣ₊Monotone·ᵣ : ∀ m n o s → 0 ≤ᵣ n → 0 ≤ᵣ o
       → m ≤ᵣ n → o ≤ᵣ s
       → (m ·ᵣ o) ≤ᵣ (n ·ᵣ s)
≤ᵣ₊Monotone·ᵣ m n o s 0≤n 0≤o m≤n o≤s =
  isTrans≤ᵣ _ _ _ (≤ᵣ-·ᵣo m n o 0≤o m≤n)
    (≤ᵣ-o·ᵣ o s n 0≤n o≤s)

NonNeg·ᵣ : ∀ x y → 0 ≤ᵣ x → 0 ≤ᵣ y → 0 ≤ᵣ x ·ᵣ y
NonNeg·ᵣ x y 0≤x 0≤y = isTrans≡≤ᵣ _ _ _ (rat·ᵣrat 0 0)
 (≤ᵣ₊Monotone·ᵣ _ _ _ _ 0≤x (≤ᵣ-refl _) 0≤x 0≤y)



opaque
 unfolding _<ᵣ_

 ℝ₊· : (m : ℝ₊) (n : ℝ₊) → 0 <ᵣ (fst m) ·ᵣ (fst n)
 ℝ₊· (m , 0<m) (n , 0<n) = PT.map2
   (λ ((q , q') , 0≤q , q<q' , q'≤m) →
    λ ((r , r') , 0≤r , r<r' , r'≤n) →
     let 0<r' = ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ 0 r 0≤r) r<r'
         qr₊ = (q' , ℚ.<→0< _ (ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ 0 q 0≤q) q<q'))
                ℚ₊· (r' , ℚ.<→0< _ 0<r')
     in (fst (/2₊ qr₊) , fst qr₊) ,
          ≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ (/2₊ qr₊)) ,
            x/2<x qr₊ ,
            subst (_≤ᵣ (m ·ᵣ n))
              (sym (rat·ᵣrat q' r'))
               (≤ᵣ₊Monotone·ᵣ (rat q')
                 (m) (rat r') n (<ᵣWeaken≤ᵣ 0 _ 0<m)
                                (<ᵣWeaken≤ᵣ 0 _ (<ℚ→<ᵣ _ _ 0<r'))
                              q'≤m r'≤n) ) 0<m 0<n



_₊+ᵣ_ : ℝ₊ → ℝ₊ → ℝ₊
(m , 0<m) ₊+ᵣ (n , 0<n) = m +ᵣ n ,
 isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) (<ᵣMonotone+ᵣ 0 m 0 n 0<m 0<n)

_₊·ᵣ_ : ℝ₊ → ℝ₊  → ℝ₊
(m , 0<m) ₊·ᵣ (n , 0<n) = _ , ℝ₊· (m , 0<m) (n , 0<n)

_₊／ᵣ₊_ : ℝ₊ → ℝ₊  → ℝ₊
(q , 0<q) ₊／ᵣ₊ (r , 0<r) = (q ／ᵣ[ r , inl (0<r) ] ,
  ℝ₊· (q , 0<q) (_ , invℝ-pos r 0<r) )



0<x^ⁿ : ∀ x n → 0 <ᵣ x → 0 <ᵣ (x ^ⁿ n)
0<x^ⁿ x zero x₁ = decℚ<ᵣ?
0<x^ⁿ x (suc n) x₁ = ℝ₊· (_ , 0<x^ⁿ x n x₁) (_ , x₁)

0≤x^ⁿ : ∀ x n → 0 ≤ᵣ x → 0 ≤ᵣ (x ^ⁿ n)
0≤x^ⁿ x zero _ = decℚ≤ᵣ?
0≤x^ⁿ x (suc n) 0≤x =
 isTrans≡≤ᵣ _ _ _ (sym (𝐑'.0RightAnnihilates _))
   (≤ᵣ-o·ᵣ 0 _ _ (0≤x^ⁿ x n 0≤x) 0≤x)


_₊^ⁿ_ : ℝ₊ → ℕ → ℝ₊
(x , 0<x) ₊^ⁿ n  = (x ^ⁿ n) , 0<x^ⁿ x n 0<x




0<1/x : ∀ x 0＃x → 0 <ᵣ x → 0 <ᵣ invℝ x 0＃x
0<1/x x 0＃x 0<x = subst (0 <ᵣ_)  (sym (invℝimpl x 0＃x)) (ℝ₊·
  (_ , 0<signᵣ x 0＃x 0<x)
  (_ , invℝ'-pos (absᵣ x) (0＃→0<abs x 0＃x)))

<ᵣ-·ᵣo : ∀ m n (o : ℝ₊) →  m <ᵣ n → (m ·ᵣ (fst o)) <ᵣ (n ·ᵣ (fst o))
<ᵣ-·ᵣo m n (o , 0<o) p =
  let z = subst (0 <ᵣ_) (·DistR+ n (-ᵣ m) o ∙
                   cong ((n ·ᵣ o) +ᵣ_) (-ᵣ· m o))
           (ℝ₊· (_ , x<y→0<y-x _ _ p) (o , 0<o))
  in 0<y-x→x<y _ _ z

<ᵣ-o·ᵣ : ∀ m n (o : ℝ₊) →  m <ᵣ n → ((fst o) ·ᵣ m) <ᵣ ((fst o) ·ᵣ n )
<ᵣ-o·ᵣ m n (o , 0<o) p =
  subst2 (_<ᵣ_)
    (·ᵣComm _ _) (·ᵣComm _ _) (<ᵣ-·ᵣo m n (o , 0<o) p)


absᵣ-triangle-minus : (x y : ℝ) → absᵣ x -ᵣ absᵣ y ≤ᵣ absᵣ (x -ᵣ y)
absᵣ-triangle-minus x y =
  isTrans≡≤ᵣ _ _ _ (cong (_-ᵣ _) (cong absᵣ ℝ!))
   (a≤c+b⇒a-c≤b _ _ _ (absᵣ-triangle y (x -ᵣ y)))

absᵣ-triangle' : (x y : ℝ) → absᵣ x  ≤ᵣ absᵣ (x -ᵣ y) +ᵣ absᵣ y
absᵣ-triangle' x y =
   isTrans≡≤ᵣ _ _ _ (cong absᵣ ℝ!) (absᵣ-triangle (x -ᵣ y) y)


opaque
 unfolding _<ᵣ_

 <ᵣ₊Monotone·ᵣ : ∀ m n o s → (0 ≤ᵣ m) → (0 ≤ᵣ o)
        → m <ᵣ n → o <ᵣ s
        → (m ·ᵣ o) <ᵣ (n ·ᵣ s)
 <ᵣ₊Monotone·ᵣ m n o s 0≤m 0≤o = PT.map2
    (λ m<n@((q , q') , m≤q , q<q' , q'≤n) →
         λ ((r , r') , o≤r , r<r' , r'≤s) →
     let 0≤q = isTrans≤ᵣ 0 _ _ 0≤m m≤q
         0≤r = isTrans≤ᵣ 0 _ _ 0≤o o≤r
         0≤r' = isTrans≤ᵣ 0 _ _ 0≤r (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ r<r'))
         0≤n = isTrans≤ᵣ 0 _ _ 0≤m (<ᵣWeaken≤ᵣ m _ ∣ m<n ∣₁)
      in (q ℚ.· r , q' ℚ.· r') ,
            subst (m ·ᵣ o ≤ᵣ_) (sym (rat·ᵣrat _ _))
               (≤ᵣ₊Monotone·ᵣ m (rat q) o (rat r)
                (0≤q) 0≤o m≤q o≤r) ,
                 ℚ.<Monotone·-onPos _ _ _ _
                   q<q' r<r' (≤ᵣ→≤ℚ _ _ 0≤q)
                             (≤ᵣ→≤ℚ _ _ 0≤r) ,
                 (subst (_≤ᵣ n ·ᵣ s ) (sym (rat·ᵣrat _ _))
                   (≤ᵣ₊Monotone·ᵣ (rat q') n (rat r') s
                     0≤n 0≤r'
                     q'≤n r'≤s)))


<≤ᵣ₊Monotone·ᵣ : ∀ (m : ℝ₀₊) n (o : ℝ₊) s
       → fst m <ᵣ n → fst o ≤ᵣ s
       → (fst m ·ᵣ fst o) <ᵣ (n ·ᵣ s)
<≤ᵣ₊Monotone·ᵣ m n o s m<n o≤s =
   isTrans<≤ᵣ _ _ _ (<ᵣ-·ᵣo _ _ o m<n)
           (≤ᵣ-o·ᵣ _ _ n (isTrans≤ᵣ _ _ _ (snd m)
              (<ᵣWeaken≤ᵣ _ _ m<n) ) o≤s)


≤<ᵣ₊Monotone·ᵣ : ∀ (m : ℝ₊) n (o : ℝ₀₊) s
       → fst m ≤ᵣ n → fst o <ᵣ s
       → (fst m ·ᵣ fst o) <ᵣ (n ·ᵣ s)
≤<ᵣ₊Monotone·ᵣ m n o s m≤n o<s =
   isTrans≤<ᵣ _ _ _
     (≤ᵣ-·ᵣo _ _ _ (snd o) m≤n)
     (<ᵣ-o·ᵣ _ _ (n , isTrans<≤ᵣ _ _ _ (snd m) m≤n) o<s )



opaque


 z<x≃y₊·z<y₊·x : ∀ x z (y : ℝ₊) → (z <ᵣ x) ≃ ((fst y) ·ᵣ z <ᵣ (fst y) ·ᵣ x)
 z<x≃y₊·z<y₊·x x z y =  propBiimpl→Equiv (isProp<ᵣ _ _) (isProp<ᵣ _ _)
  (<ᵣ-o·ᵣ _ _ y) (subst2 _<ᵣ_
   (·ᵣAssoc _ _ _ ∙ cong (_·ᵣ z) (·ᵣComm _ _ ∙ x·invℝ₊[x] y) ∙ ·IdL z)
   (·ᵣAssoc _ _ _ ∙ cong (_·ᵣ x) (·ᵣComm _ _ ∙ x·invℝ₊[x] y) ∙ ·IdL x)
   ∘S (<ᵣ-o·ᵣ _ _ (invℝ₊ y)))


 z<x/y₊≃y₊·z<x : ∀ x z (y : ℝ₊) → (z <ᵣ x ·ᵣ (fst (invℝ₊ y))) ≃ ((fst y) ·ᵣ z <ᵣ x)
 z<x/y₊≃y₊·z<x x z y =
     z<x≃y₊·z<y₊·x (x ·ᵣ (fst (invℝ₊ y))) z y
     ∙ₑ  substEquiv ((fst y ·ᵣ z) <ᵣ_) (·ᵣComm _ _ ∙ [x/₊y]·yᵣ x y )

 z/y<x₊≃z<y₊·x : ∀ x z (y : ℝ₊) → (z  ·ᵣ (fst (invℝ₊ y)) <ᵣ x)
                          ≃ (z <ᵣ (fst y) ·ᵣ  x)
 z/y<x₊≃z<y₊·x x z y =
       z<x≃y₊·z<y₊·x _ _ y ∙ₑ
        substEquiv (_<ᵣ (fst y) ·ᵣ x) (·ᵣComm _ _ ∙ [x/₊y]·yᵣ z y )


 z≤x≃y₊·z≤y₊·x : ∀ x z (y : ℝ₊) → (z ≤ᵣ x) ≃ ((fst y) ·ᵣ z ≤ᵣ (fst y) ·ᵣ x)
 z≤x≃y₊·z≤y₊·x x z y =  propBiimpl→Equiv (isProp≤ᵣ _ _) (isProp≤ᵣ _ _)
  (≤ᵣ-o·ᵣ _ _ (fst y) (<ᵣWeaken≤ᵣ 0 _ (snd y)))
  (subst2 _≤ᵣ_
   (·ᵣAssoc _ _ _ ∙ cong (_·ᵣ z) (·ᵣComm _ _ ∙ x·invℝ₊[x] y) ∙ ·IdL z)
   (·ᵣAssoc _ _ _ ∙ cong (_·ᵣ x) (·ᵣComm _ _ ∙ x·invℝ₊[x] y) ∙ ·IdL x)
   ∘S (≤ᵣ-o·ᵣ _ _ (fst (invℝ₊ y)) (<ᵣWeaken≤ᵣ 0 _ (snd (invℝ₊ y)))))

 z/y≤x₊≃z≤y₊·x : ∀ x z (y : ℝ₊) → (z  ·ᵣ (fst (invℝ₊ y)) ≤ᵣ x)
                          ≃ (z ≤ᵣ (fst y) ·ᵣ  x)
 z/y≤x₊≃z≤y₊·x x z y =
       z≤x≃y₊·z≤y₊·x _ _ y ∙ₑ
        substEquiv (_≤ᵣ (fst y) ·ᵣ x) (·ᵣComm _ _ ∙ [x/₊y]·yᵣ z y )

 z≤x/y₊≃y₊·z≤x : ∀ x z (y : ℝ₊) → (z  ≤ᵣ x ·ᵣ (fst (invℝ₊ y)))
                          ≃ ((fst y) ·ᵣ  z ≤ᵣ x)
 z≤x/y₊≃y₊·z≤x x z y =
       z≤x≃y₊·z≤y₊·x _ _ y ∙ₑ
         substEquiv ((fst y) ·ᵣ z ≤ᵣ_)
            (·ᵣComm _ _ ∙ [x/₊y]·yᵣ x y )


 z/y'≤x/y≃y₊·z≤y'₊·x : ∀ x z (y y' : ℝ₊) → (z ·ᵣ (fst (invℝ₊ y'))
                                      ≤ᵣ x ·ᵣ (fst (invℝ₊ y))) ≃
                       ((fst y) ·ᵣ z ≤ᵣ (fst y') ·ᵣ x)
 z/y'≤x/y≃y₊·z≤y'₊·x x z y y' =
      z≤x/y₊≃y₊·z≤x _ _ _
   ∙ₑ substEquiv (_≤ᵣ x) (·ᵣAssoc _ _ _)
   ∙ₑ z/y≤x₊≃z≤y₊·x _ _ _

 -- x/x'≤y/y'≃x/y≤x'/y' : ∀ x (x' y y' : ℝ₊) → (z ·ᵣ (fst (invℝ₊ y'))
 --                                      ≤ᵣ x ·ᵣ (fst (invℝ₊ y))) ≃
 --                       ((fst y) ·ᵣ z ≤ᵣ (fst y') ·ᵣ x)
 -- x/x'≤y/y'≃x/y≤x'/y' x z y y' = ?
 --   --    z≤x/y₊≃y₊·z≤x _ _ _
 --   -- ∙ₑ substEquiv (_≤ᵣ x) (·ᵣAssoc _ _ _)
 --   -- ∙ₑ z/y≤x₊≃z≤y₊·x _ _ _


 z/y'<x/y≃y₊·z<y'₊·x : ∀ x z (y y' : ℝ₊) → (z ·ᵣ (fst (invℝ₊ y'))
                                      <ᵣ x ·ᵣ (fst (invℝ₊ y))) ≃
                       ((fst y) ·ᵣ z <ᵣ (fst y') ·ᵣ x)
 z/y'<x/y≃y₊·z<y'₊·x x z y y' =
      z<x/y₊≃y₊·z<x _ _ _
   ∙ₑ substEquiv (_<ᵣ x) (·ᵣAssoc _ _ _)
   ∙ₑ z/y<x₊≃z<y₊·x _ _ _


 x/y≤x'/y'≃y'/x'≤y/x : ∀ (x x' y y' : ℝ₊) → (fst x ·ᵣ (fst (invℝ₊ y))
                                      ≤ᵣ fst x' ·ᵣ (fst (invℝ₊ y'))) ≃
                       (fst y' ·ᵣ (fst (invℝ₊ x'))
                                      ≤ᵣ fst y ·ᵣ (fst (invℝ₊ x)))
 x/y≤x'/y'≃y'/x'≤y/x x x' y y' =
   z/y'≤x/y≃y₊·z≤y'₊·x _ _ _ _
   ∙ₑ subst2Equiv (_≤ᵣ_) (·ᵣComm _ _) (·ᵣComm _ _)
   ∙ₑ invEquiv (z/y'≤x/y≃y₊·z≤y'₊·x _ _ _ _)

 0<x≃0<y₊·x : ∀ x (y : ℝ₊) → (0 <ᵣ x) ≃ (0 <ᵣ (fst y) ·ᵣ x)
 0<x≃0<y₊·x x y =   propBiimpl→Equiv (isProp<ᵣ _ _) (isProp<ᵣ _ _)
    (λ 0<x → isTrans≡<ᵣ _ _ _ (sym (𝐑'.0RightAnnihilates  (fst y)))
       (<ᵣ-o·ᵣ 0 x y 0<x))
    λ 0<y·x →
      isTrans<≡ᵣ 0 _ x (isTrans≡<ᵣ _ _ _ (sym (𝐑'.0RightAnnihilates
        (fst (invℝ₊ y))))
       (<ᵣ-o·ᵣ 0 ((fst y) ·ᵣ x) (invℝ₊ y) 0<y·x))
         (·ᵣAssoc _ _ _ ∙ cong (_·ᵣ x) (·ᵣComm _ _ ∙ x·invℝ₊[x] _) ∙ ·IdL x)



 invℝ₊-<-invℝ₊ : ∀ x y → (fst (invℝ₊ x) <ᵣ fst (invℝ₊ y))
                       ≃ (fst y <ᵣ fst x)
 invℝ₊-<-invℝ₊ x y =
      subst2Equiv _<ᵣ_ (sym (·IdL _)) (sym (·IdL _))
   ∙ₑ z/y'<x/y≃y₊·z<y'₊·x 1 1 y x
   ∙ₑ subst2Equiv _<ᵣ_ (·IdR _) (·IdR _)

invℝ₊-≤-invℝ₊ : ∀ x y → (fst (invℝ₊ x) ≤ᵣ fst (invℝ₊ y))
                      ≃ (fst y ≤ᵣ fst x)
invℝ₊-≤-invℝ₊ x y =
     subst2Equiv _≤ᵣ_ (sym (·IdL _)) (sym (·IdL _))
  ∙ₑ z/y'≤x/y≃y₊·z≤y'₊·x 1 1 y x
  ∙ₑ subst2Equiv _≤ᵣ_ (·IdR _) (·IdR _)


invℝ₊-rat : ∀ q → fst (invℝ₊ (ℚ₊→ℝ₊ q)) ≡ fst (ℚ₊→ℝ₊ (invℚ₊ q))
invℝ₊-rat q = invℝ₊≡invℝ _ (inl (snd (ℚ₊→ℝ₊ q))) ∙∙
    invℝ-rat _ _ (inl (ℚ.0<ℚ₊ q)) ∙∙
     cong rat (ℚ.invℚ₊≡invℚ q (inl (ℚ.0<ℚ₊ q)))



invℝ₊· : ∀ x y →
          invℝ₊ (x ₊·ᵣ y) ≡
            (invℝ₊ x) ₊·ᵣ (invℝ₊ y)
invℝ₊· x y =
  ℝ₊≡ (invℝ₊≡invℝ (x ₊·ᵣ y) (inl (ℝ₊· x y)) ∙∙
       invℝ· _ _ _ _ _
       ∙∙ cong₂ _·ᵣ_
        (sym (invℝ₊≡invℝ x (inl (snd x)))) (sym (invℝ₊≡invℝ y (inl (snd y)))) )


invℝ₊Invol : ∀ x → invℝ₊ (invℝ₊ x) ≡ x
invℝ₊Invol x = ℝ₊≡ $
   fst (invℝ₊ (invℝ₊ x))
       ≡⟨ (cong (fst ∘ invℝ₊) (ℝ₊≡ (invℝ₊≡invℝ _ _))) ⟩ _
       ≡⟨ invℝ₊≡invℝ (_ , invℝ-pos _ _) _  ⟩ _
       ≡⟨ invℝInvol (fst x) (inl (snd x)) ⟩ _ ∎


invℝ₊1 : invℝ₊ 1 ≡ 1
invℝ₊1 = ℝ₊≡ (invℝ₊≡invℝ 1 (inl decℚ<ᵣ?)  ∙ (invℝ1 _))


1/x<1≃1<x : ∀ x → (fst (invℝ₊ x) <ᵣ 1) ≃ (1 <ᵣ fst x)
1/x<1≃1<x x =
  substEquiv (fst (invℝ₊ x) <ᵣ_) (sym (cong fst invℝ₊1))
    ∙ₑ invℝ₊-<-invℝ₊ x 1

1<x/y≃y<x : ∀ x y → (1 <ᵣ x ／ᵣ₊ y) ≃ (fst y <ᵣ x)
1<x/y≃y<x x y =
      substEquiv (_<ᵣ x ／ᵣ₊ y) (sym (x·invℝ₊[x] 1))
   ∙ₑ z/y'<x/y≃y₊·z<y'₊·x x 1 y 1
   ∙ₑ subst2Equiv _<ᵣ_ (·IdR _) (·IdL _)



x+y≤z+y≃x≤z : ∀ x z y → (x +ᵣ y ≤ᵣ z +ᵣ y)
                      ≃ (x ≤ᵣ z)
x+y≤z+y≃x≤z x z y = propBiimpl→Equiv (isProp≤ᵣ _ _) (isProp≤ᵣ _ _)
  (subst2 _≤ᵣ_ (𝐑'.plusMinus _ _) (𝐑'.plusMinus _ _)
    ∘ ≤ᵣ-+o _ _ (-ᵣ y))
 (≤ᵣ-+o _ _ _)


x+y<z+y≃x<z : ∀ x z y → (x +ᵣ y <ᵣ z +ᵣ y)
                      ≃ (x <ᵣ z)
x+y<z+y≃x<z x z y = propBiimpl→Equiv (isProp<ᵣ _ _) (isProp<ᵣ _ _)
  (subst2 _<ᵣ_ (𝐑'.plusMinus _ _) (𝐑'.plusMinus _ _)
    ∘ <ᵣ-+o _ _ (-ᵣ y))
 (<ᵣ-+o _ _ _)


x+y<x+z≃y<z : ∀ x z y → (x +ᵣ y <ᵣ x +ᵣ z)
                      ≃ (y <ᵣ z)
x+y<x+z≃y<z x z y = propBiimpl→Equiv (isProp<ᵣ _ _) (isProp<ᵣ _ _)
  (subst2 _<ᵣ_
     ((λ i → +ᵣComm (-ᵣ x) (+ᵣComm x y i) i) ∙ 𝐑'.plusMinus y x)
     ((λ i → +ᵣComm (-ᵣ x) (+ᵣComm x z i) i) ∙ 𝐑'.plusMinus z x)
    ∘ <ᵣ-o+ _ _ (-ᵣ x))
 (<ᵣ-o+ _ _ _)


x'/x<[x'+y']/[x+y]≃[x'+y']/[x+y]<y'/y :
  ∀ x x' y y' →
     ((x' ／ᵣ₊ x) <ᵣ ((x' +ᵣ y') ／ᵣ₊ (x ₊+ᵣ y))) ≃
       (((x' +ᵣ y') ／ᵣ₊ (x ₊+ᵣ y)) <ᵣ (y' ／ᵣ₊ y))
x'/x<[x'+y']/[x+y]≃[x'+y']/[x+y]<y'/y x x' y y' =
  z/y'<x/y≃y₊·z<y'₊·x _ _ _ _
  ∙ₑ subst2Equiv _<ᵣ_ (·DistR+ _ _ _) (·DistL+ _ _ _)
  ∙ₑ x+y<x+z≃y<z _ _ _ ∙ₑ invEquiv (x+y<z+y≃x<z _ _ _)
  ∙ₑ subst2Equiv _<ᵣ_
       ((sym (·DistL+ _ _ _))) (sym (·DistR+ _ _ _))
  ∙ₑ invEquiv (z/y'<x/y≃y₊·z<y'₊·x _ _ _ _)


opaque


 IsUContinuousℚℙ→IsUContinuousℙ : ∀ f →
   (∀ x 0<x y 0<y → x ≤ᵣ y → f x 0<x ≤ᵣ f y 0<y)
   → IsUContinuousℚℙ (λ x → (0 <ᵣ x) , isProp<ᵣ _ _ ) (f ∘ rat)
   → IsUContinuousℙ (λ x → (0 <ᵣ x) , isProp<ᵣ _ _ ) f
 IsUContinuousℚℙ→IsUContinuousℙ f incr uc ε =
   let (δ , Δ) = uc ε
   in δ , λ u v u∈ v∈ →
     ((λ u-v<δ →
        PT.rec2
          (isProp∼ _ _ _)
          (λ (η , 0<η , η<)
             (τ , 0<τ , τ<) →
            let η' = ℚ.min₊ (η , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<η))
                            (τ , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<τ))

            in PT.rec2 (isProp∼ _ _ _)
                   (λ ((u⊓v , uu) , (<η' , u⊓v< , <uu))
                      ((vv , u⊔v) , (<η'' , vv< , <u⊔v)) →
                     let xx = isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (≤maxᵣ _ _)

                         η<* = a<b-c⇒a+c<b _
                            (rat (fst δ)) _
                           $ fst (z<x/y₊≃y₊·z<x _ _ (ℚ₊→ℝ₊ 2))
                            (isTrans<≡ᵣ _ _ _ η<
                               ((cong ((rat (fst δ) -ᵣ absᵣ (u -ᵣ v)) ·ᵣ_)
                                (sym (invℝ'-rat 2 (ℚ.0<pos _ _) (snd (ℚ₊→ℝ₊ 2))) ∙
                                 cong fst (sym (invℝ₊-impl _)))))

                                )
                         u⊓v<u⊔v = isTrans<ᵣ _ _ _
                                   (isTrans<≤ᵣ _ _ _
                                    (u⊓v<) xx) (<u⊔v)
                         0<u⊓v : 0 <ᵣ rat u⊓v
                         0<u⊓v = isTrans<ᵣ _ _ _
                              (x<y→0<y-x _ _
                                (isTrans<ᵣ _ _ _
                                  (isTrans≤<ᵣ _ _ _
                                    (isTrans≡≤ᵣ _ _ _
                                     (minᵣComm (rat η) (rat τ))
                                      (min≤ᵣ _ (rat η))) τ<)
                                  <uu)
                                )
                             (a-b<c⇒a-c<b (rat uu) _ _
                                    (subst2 _<ᵣ_ ℚℝ! ℚℝ!
                                       (<ℚ→<ᵣ (uu ℚ.- u⊓v) _ <η'))
                                    )

                         <η* : -ᵣ (rat u⊓v) <ᵣ -ᵣ rat uu +ᵣ rat (fst η')
                         <η* = isTrans≡<ᵣ _ _ _
                                  (ℝ! ∙ cong₂ _+ᵣ_ refl  ((-ᵣ-rat₂ uu u⊓v)))
                                     (<ᵣ-o+ _ _ (-ᵣ (rat uu))
                                   (<ℚ→<ᵣ (uu ℚ.- u⊓v) _ <η'))

                         <η** : (rat u⊔v) <ᵣ rat (fst η') +ᵣ rat vv
                         <η** = a-b<c⇒a<c+b (rat u⊔v) (rat vv) _
                               (isTrans≡<ᵣ _ _ _ ℚℝ! (<ℚ→<ᵣ _ _ <η''))
                         zzz''' : ∀ mmm → mmm +ᵣ rat vv +ᵣ (-ᵣ rat uu +ᵣ mmm) ≡
                                     mmm +ᵣ mmm +ᵣ (rat vv -ᵣ rat uu)
                         zzz''' _  = ℝ!
                         z = Δ u⊓v u⊔v 0<u⊓v
                             (isTrans<ᵣ _ _ _
                              ((snd (maxᵣ₊ (u , u∈) (v , v∈)))) <u⊔v)
                               (<ᵣ→<ℚ (ℚ.abs (u⊓v ℚ.- u⊔v))
                                (fst δ)
                                 (isTrans≡<ᵣ _ _ _
                                  (cong rat (ℚ.absComm- u⊓v u⊔v ∙ ℚ.absPos _
                                   (<ᵣ→<ℚ _ _
                                      (isTrans<≡ᵣ _ _ _
                                       (x<y→0<y-x _ _ u⊓v<u⊔v)
                                       ℚℝ!)
                                      )))
                                     (isTrans≤<ᵣ _ _ _
                                        (isTrans≤≡ᵣ _ _ _
                                          (isTrans≤ᵣ _ _ _
                                            (<ᵣWeaken≤ᵣ _ _
                                           (isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat₂ _ _))
                                            (<ᵣMonotone+ᵣ _ _ _ _
                                              <η** <η*))

                                            )
                                            (isTrans≡≤ᵣ _ _ _
                                              (ℚℝ! ∙ zzz''' (minᵣ (rat η) (rat τ)))
                                            (≤ᵣMonotone+ᵣ _ _
                                             (rat vv -ᵣ rat uu) _
                                             (≤ᵣMonotone+ᵣ _ _ _ _
                                               (min≤ᵣ _ (rat τ))
                                               (min≤ᵣ _ (rat τ)))
                                             (isTrans≤≡ᵣ _ _ _
                                               (≤ᵣMonotone+ᵣ _ _ _ _
                                             (<ᵣWeaken≤ᵣ _ _ vv<)
                                              (<ᵣWeaken≤ᵣ _ _
                                                (-ᵣ<ᵣ _ _ <uu)))
                                               ((sym (absᵣNonNeg _
                                                   (x≤y→0≤y-x _ _
                                                     (isTrans≤ᵣ _ _ _
                                                    (min≤ᵣ _ _) (≤maxᵣ _ _)))))
                                                      ∙
                                                      absᵣ-min-max _ _)))
                                              ))
                                           (cong (_+ᵣ _)
                                              (x+x≡2x _))) η<*)))

                     in invEq (∼≃abs<ε _ _ _)
                          (isTrans≡<ᵣ _ _ _
                           (sym (absᵣ-min-max _ _))
                           (isTrans≤<ᵣ _ _ _
                             ((absᵣ-monotoneOnNonNeg
                                 (_ , fst (x≤y≃0≤y-x _ _)
                                    (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (≤maxᵣ _ _)))

                                (_ , fst (x≤y≃0≤y-x _ _)
                                (incr _ _ _ _ (<ᵣWeaken≤ᵣ _ _ u⊓v<u⊔v)))
                              (≤ᵣMonotone+ᵣ _ _ _ _
                                (isTrans≤ᵣ _ _ _
                                    (incr→max≤ f incr _ _ _ _)
                                     (incr _ _ _ _
                                  (<ᵣWeaken≤ᵣ _ _ <u⊔v)))
                                (-ᵣ≤ᵣ _ _
                                  (isTrans≤ᵣ _ _ _ (incr _ _ _ _
                                    (<ᵣWeaken≤ᵣ _ _ u⊓v<
                                      )) (incr→≤min f incr _ _ _ _))))))
                              (fst (∼≃abs<ε _ _ _) (sym∼ _ _ _ z)))))
                 (∃rationalApprox (minᵣ u v) η')
                 (∃rationalApprox (maxᵣ u v) η'))
         (denseℚinℝ 0 (((rat (fst δ)) -ᵣ absᵣ (u -ᵣ v)) ·ᵣ  rat [ 1 / 2 ])
                (isTrans≡<ᵣ _ _ _
                  (sym (𝐑'.0LeftAnnihilates _))
                  ((<ᵣ-·ᵣo 0 ((rat (fst δ)) -ᵣ absᵣ (u -ᵣ v))
                    (ℚ₊→ℝ₊ ([ 1 / 2 ]₊))
                    (x<y→0<y-x _ _ u-v<δ)))))
                    (denseℚinℝ 0 (minᵣ u v)
                       (snd (minᵣ₊ (u , u∈) (v , v∈))))

        )
      ∘ fst (∼≃abs<ε _ _ _))


≤Weaken<+ᵣ : ∀ x y (z : ℝ₊) →
       x ≤ᵣ y → x <ᵣ y +ᵣ fst z
≤Weaken<+ᵣ x y z x≤y =
  isTrans≡<ᵣ _ _ _ (sym (+IdR _))
   (≤<ᵣMonotone+ᵣ x y 0 (fst z) x≤y (snd z))




clampᵣ∈ℚintervalℙ : ∀ a b → (a ≤ᵣ b) → ∀ x →
  clampᵣ a b x ∈ intervalℙ a b
clampᵣ∈ℚintervalℙ a b a≤b x =
        ≤clampᵣ _ _ _ a≤b , min≤ᵣ' (maxᵣ a x) b

≡clampᵣ→∈intervalℙ : ∀ a b → (a ≤ᵣ b) → ∀ x →
  x ≡ clampᵣ a b x → x ∈ intervalℙ a b
≡clampᵣ→∈intervalℙ a b a≤b x p =
        subst-∈ (intervalℙ a b ) (sym p) (clampᵣ∈ℚintervalℙ a b a≤b x)



opaque

 x≤→clampᵣ≡ : ∀ a b x → a ≤ᵣ b  → x ≤ᵣ a →  clampᵣ a b x ≡ a
 x≤→clampᵣ≡ a b x a≤b x≤a = (≤→minᵣ _ _
  (isTrans≡≤ᵣ _ _ _ ((maxᵣComm _ _) ∙ (≤→maxᵣ _ _ x≤a)) a≤b) ∙ maxᵣComm _ _)
  ∙ ≤→maxᵣ _ _ x≤a

 ≤x→clampᵣ≡ : ∀ a b x → a ≤ᵣ b → b ≤ᵣ x →  clampᵣ a b x ≡ b
 ≤x→clampᵣ≡ a b x a≤b b≤x =
   cong (flip minᵣ b)
     (≤→maxᵣ _ _ (isTrans≤ᵣ _ _ _ a≤b b≤x))
    ∙ minᵣComm _ _ ∙ ≤→minᵣ _ _ b≤x


 min-monotone-≤ᵣ : ∀ a → ∀ x y  → x ≤ᵣ y →
                        minᵣ x a ≤ᵣ minᵣ y a
 min-monotone-≤ᵣ a x y x≤y =
  ≤min-lem _ _ _ (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) x≤y)
   (isTrans≡≤ᵣ _ _ _ (minᵣComm _ _) (min≤ᵣ _ _) )

 max-monotone-≤ᵣ : ∀ a → ∀ x y  → x ≤ᵣ y →
                        maxᵣ a x ≤ᵣ maxᵣ a y
 max-monotone-≤ᵣ a x y x≤y =
  max≤-lem _ _ _
    (≤maxᵣ _ _)
    (isTrans≤ᵣ _ _ _ x≤y
     (isTrans≤≡ᵣ _ _ _
       (≤maxᵣ _ _)
       (maxᵣComm _ _)))

clamp-monotone-≤ᵣ : ∀ a b x y  → x ≤ᵣ y →
                       clampᵣ a b x ≤ᵣ clampᵣ a b y
clamp-monotone-≤ᵣ a b x y x≤y =
  min-monotone-≤ᵣ b _ _ (max-monotone-≤ᵣ a _ _ x≤y)

opaque

 clampDistᵣ' : ∀ L L' x y →
     absᵣ (clampᵣ (rat L) (rat L') y -ᵣ clampᵣ (rat L) (rat L') x) ≤ᵣ absᵣ (y -ᵣ x)
 clampDistᵣ' L L' = ≤Cont₂


           (cont∘₂ IsContinuousAbsᵣ
              (IsContinuous-₂∘ (asIsContinuous₂-snd _ (IsContinuousClamp (rat L) (rat L')))
                ((asIsContinuous₂-fst _ (IsContinuousClamp (rat L) (rat L'))))))
           (cont∘₂ IsContinuousAbsᵣ (snd IsContinuous-₂ , fst IsContinuous-₂))
           λ u u' →
              subst2 _≤ᵣ_ (sym (cong rat (sym
                   (ℚ.abs'≡abs (ℚ.clamp L L' u' ℚ.- ℚ.clamp L L' u)))) ∙
                    ℚℝ!)
                ( sym (absᵣ-rat _) ∙ cong absᵣ (sym (-ᵣ-rat₂ _ _)))
                (≤ℚ→≤ᵣ _ _ (ℚ.clampDist L L' u u'))

