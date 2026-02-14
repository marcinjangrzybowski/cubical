module Cubical.Data.Rationals.Fast.Order.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Involution

open import Cubical.Functions.Logic using (_⊔′_; ⇔toPath)

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fast.Int.Base as ℤ using (ℤ;pos;negsuc)
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Fast.Int.Properties as ℤ using ()
open import Cubical.Data.Fast.Int.Order as ℤ using ()
open import Cubical.Data.Fast.Int.Divisibility as ℤ
open import Cubical.Data.Rationals.Fast.Base as ℚ
open import Cubical.Data.Rationals.Fast.Properties
open import Cubical.Data.Nat as ℕ using (ℕ; suc; zero;znots)
open import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr; isProp⊎)

open import Cubical.HITs.PropositionalTruncation as ∥₁ using (isPropPropTrunc; ∣_∣₁)
open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.Data.Rationals.Fast.Order

open import Cubical.Algebra.CommRing.Instances.Rationals.Fast
open import Cubical.Tactics.CommRingSolverFast.IntPlusReflection
open import Cubical.Tactics.CommRingSolverFast.RationalsReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflectionPre

open import Cubical.Foundations.Powerset


<- : ∀ q r  → 0 < r - q → q < r
<- q r x = subst2 _<_ (+IdL _) ℚ!!
    (<-+o 0 (r - q) q x)

≤- : ∀ q r  → 0 ≤ r - q → q ≤ r
≤- q r x = subst2 _≤_ (+IdL _) ℚ!!
    (≤-+o 0 (r - q) q x)


decℚ? : ∀ {x y} → {𝟚.True (discreteℚ x y)} →  (x ≡ y)
decℚ? {_} {_} {p} = 𝟚.toWitness p

decℚ<? : ∀ {x y} → {𝟚.True (<Dec x y)} →  (x < y)
decℚ<? {_} {_} {p} = 𝟚.toWitness p

decℚ≤? : ∀ {x y} → {𝟚.True (≤Dec x y)} →  (x ≤ y)
decℚ≤? {_} {_} {p} = 𝟚.toWitness p

0<sucN : ∀ n → 0 < fromNat (suc n)
0<sucN n = <ℤ→<ℚ _ _ (ℤ.pos<pos tt)

0<pos : ∀ n m → 0 < [ pos (suc n) / m ]
0<pos n m = 0<→< [ pos (suc n) / m ] (inj (ℤ.pos<pos _))

0≤pos : ∀ n m → 0 ≤ [ pos n / m ]
0≤pos n m = inj (subst (0 ℤ.≤_)
   (sym (ℤ.·IdR _))
  (ℤ.zero-≤pos {n}))


-fromNat : ∀ n → fromNeg n ≡ - fromNat n
-fromNat zero = refl
-fromNat (suc n) = cong [_/ 1 ] (sym (ℤ.-1·x≡-x _))

neg≤pos : ∀ n m → fromNeg n ≤ fromNat m
neg≤pos n m =
 subst (_≤ fromNat m) (sym (-fromNat n))
  (isTrans≤ _ 0 (fromNat m) ((minus-≤ 0 (fromNat n) (0≤pos n 1))) (0≤pos m 1))

floor-lemma : ∀ p q → fromNat (ℕ.quotient p / (suc q))
                   + [ ℤ.pos (ℕ.remainder p / (suc q)) / 1+ q ]
                   ≡ [ ℤ.pos p / 1+ q ]
floor-lemma p q = eq/ _ _
     (cong (ℤ._· q') w ∙ cong (ℤ.pos p ℤ.·_)
     (cong ℚ.ℕ₊₁→ℤ (sym (·₊₁-identityˡ (1+ q)))))

 where
  q' = ℚ.ℕ₊₁→ℤ (1+ q)
  w : (ℤ.pos (ℕ.quotient p / (suc q)) ℤ.· q'
        ℤ.+ ℤ.pos (ℕ.remainder p / (suc q)) ℤ.· ℤ.pos 1)
           ≡ ℤ.pos p
  w = cong₂ (ℤ._+_) (ℤ.·Comm (pos (quotient p / suc q)) (pos (suc q))
     ∙ sym (ℤ.pos·pos (suc q) (quotient p / suc q))) (ℤ.·IdR (pos (remainder p / suc q)))
       ∙ sym (ℤ.pos+ (suc q ℕ.· (quotient p / suc q)) (remainder p / suc q)) ∙ cong ℤ.pos
          (ℕ.+-comm (suc q ℕ.· (quotient p / suc q)) (remainder p / suc q)
           ∙ ℕ.≡remainder+quotient (suc q) p)





floor-fracℚ₊ : ∀ (x : ℚ₊) → Σ (ℕ × ℚ) λ (k , q) →
                       (fromNat k + q ≡ fst x ) × ((0 ≤ q)  × (q < 1))
floor-fracℚ₊ = uncurry (SQ.Elim.go w)
 where


 ww : ∀ p p' q q' → p ℕ.· (suc q') ≡ p' ℕ.· (suc q) →
         ℤ.pos (ℕ.remainder p / (suc q)) ℤ.·
           (ℤ.pos (2 ℕ.· ((suc q) ℕ.· (suc q')) ))
           ≡ ℤ.pos (ℕ.remainder (p ℕ.· (suc q') ℕ.+ p' ℕ.· (suc q))
                / ℕ₊₁→ℕ (2 ·₊₁ ((1+ q) ·₊₁ (1+ q')))) ℤ.· ℤ.pos (suc q)
 ww p p' q q' e =
    sym (ℤ.pos·pos (p mod suc q) (2 ℕ.· (suc q ℕ.· suc q')))
   ∙ (cong ℤ.pos ((cong ((p ℕ.mod suc q) ℕ.·_)
         (cong (2 ℕ.·_) (ℕ.·-comm (suc q) (suc q')) ∙  ℕ.·-assoc 2 (suc q') (suc q))
     ∙ ℕ.·-assoc (p mod suc q) (2 ℕ.· suc q') (suc q) ) ∙
     cong (ℕ._· (suc q))
       ((ℕ.·-comm (p mod suc q) (2 ℕ.· suc q'))
         ∙ sym (ℕ.·mod (2 ℕ.· (suc q')) p _) ∙ cong₂ ℕ.remainder_/_
                 ((sym (ℕ.·-assoc 2 (suc q') p)
                   ∙ cong (2 ℕ.·_) (ℕ.·-comm (suc q') p))
                     ∙ (cong (p ℕ.· (suc q') ℕ.+_) (ℕ.+-zero _ ∙ e)))
              (sym (ℕ.·-assoc 2 (suc q') (suc q)) ∙
                cong (2 ℕ.·_) (ℕ.·-comm (suc q') (suc q))))))
     ∙ ℤ.pos·pos (remainder p ℕ.· suc q' ℕ.+ p' ℕ.· suc q /
                   (2 ℕ.· (suc q ℕ.· suc q'))) (suc q)

 w : Elim _
 w .Elim.isSetB _ = isSetΠ λ _ →
   isSetΣ (isSet× ℕ.isSetℕ isSetℚ)
    (isProp→isSet ∘ λ _ → isProp× (isSetℚ _ _)
      (isProp× (isProp≤ _ _) (isProp< _ _)))
 w .Elim.f∼ (ℤ.negsuc n , (1+ n₁)) (ℤ.pos n₂ , (1+ n₃)) r =
   funExtDep λ {x₀} → ⊥.rec (ℤ.¬pos<negsuc (_<_.prf x₀))
 w .Elim.f∼ (_ , (1+ n)) (ℤ.negsuc n₁ , (1+ n₂)) r =
   funExtDep λ {_} {x₁} → ⊥.rec (ℤ.¬pos<negsuc (_<_.prf x₁))
 w .Elim.f (ℤ.pos p , 1+ q) _ =
   ((ℕ.quotient p / (suc q)) ,
     [ ℤ.pos (ℕ.remainder p / (suc q)) / 1+ q ]) ,
      floor-lemma p q , (
        inj (subst (0 ℤ.≤_) (sym (ℤ.·IdR _)) (ℤ.zero-≤pos {remainder p / suc q})) , inj f<1)
  where

  f<1 : ℤ.pos (ℕ.remainder p / suc q) ℤ.· 1 ℤ.< ℤ.pos 1 ℤ.· ℕ₊₁→ℤ (1+ q)
  f<1 = subst2 ℤ._<_
     (sym (ℤ.·IdR (pos (remainder p / suc q)))) (sym (ℤ.·IdL (pos (suc q))))
     (ℤ.suc≤→< (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.mod< q p)))
     

 w .Elim.f∼ (ℤ.pos p , 1+ q) (ℤ.pos p' , 1+ q') e₀ =
  toPathP (funExt λ x → Σ≡Prop
    (λ _ → isProp× (isSetℚ _ _)
      (isProp× (isProp≤ _ _) (isProp< _ _)))
    (cong₂ _,_ z z'))
  where

  e : p ℕ.· (suc q') ≡ p' ℕ.· (suc q)
  e = ℤ.injPos (ℤ.pos·pos p (ℕ₊₁→ℕ (1+ q')) ∙∙ e₀ ∙∙ sym (ℤ.pos·pos p' (ℕ₊₁→ℕ (1+ q))))


  z' : [ ℤ.pos (ℕ.remainder p / (suc q)) / 1+ q ]
        ≡ [ ℤ.pos (ℕ.remainder p' / (suc q')) / 1+ q' ]
  z' = eq/ _ ((ℤ.pos (ℕ.remainder (p ℕ.· (suc q') ℕ.+ p' ℕ.· (suc q))
                / (2 ℕ.· ((suc q) ℕ.· (suc q'))))) ,
                 (2 ·₊₁ ((1+ q) ·₊₁ (1+ q'))))
     (ww p p' q q' e) ∙∙
      cong₂ [_/_] (cong ℤ.pos
          (cong₂ ℕ.remainder_/_
             (ℕ.+-comm (p ℕ.· suc q') (p' ℕ.· suc q)) (cong (2 ℕ.·_) (ℕ.·-comm (suc q) (suc q')))))
        (cong (2 ·₊₁_) (·₊₁-comm (1+ q) (1+ q')))
      ∙∙ sym (eq/ _
        ((ℤ.pos (ℕ.remainder (p' ℕ.· (suc q) ℕ.+ p ℕ.· (suc q'))
                / (2 ℕ.· ((suc q') ℕ.· (suc q))))) ,
                 (2 ·₊₁ ((1+ q') ·₊₁ (1+ q))))
                 (ww p' p q' q (sym e)))


  z'' : (ℕ.remainder p / suc q) ℕ.· (suc q') ≡
          (ℕ.remainder p' / suc q') ℕ.· (suc q)
  z'' = ℤ.injPos (ℤ.pos·pos (remainder p / suc q) (ℕ₊₁→ℕ (1+ q')) ∙∙ eq/⁻¹ (pos (remainder p / suc q) , (1+ q)) (pos (remainder p' / suc q') , (1+ q')) z' ∙∙ sym (ℤ.pos·pos (remainder p' / suc q') (ℕ₊₁→ℕ (1+ q))))

  z : (ℕ.quotient p / suc q)
        ≡
        (ℕ.quotient p' / suc q')
  z = ℕ.inj-·sm (ℕ.inj-sm· {m = q} (ℕ.·-assoc (suc q) (quotient p / suc q) (suc q')
     ∙∙ ℕ.inj-m+ ((cong (ℕ._+ (suc q ℕ.· (ℕ.quotient p / suc q) ℕ.· suc q'))
      (sym z''))
     ∙ (ℕ.·-distribʳ (remainder p / suc q) (suc q ℕ.· (quotient p / suc q)) (suc q')) ∙∙ cong (ℕ._· (suc q'))
         (ℕ.≡remainder+quotient (suc q) p) ∙∙ e ∙∙
       sym (cong (ℕ._· (suc q)) (ℕ.≡remainder+quotient (suc q') p'))
         ∙∙ sym (ℕ.·-distribʳ (remainder p' / suc q') (suc q' ℕ.· (quotient p' / suc q')) (suc q)))
        ∙∙ (λ i → ℕ.·-comm (ℕ.·-comm (suc q') (ℕ.quotient p' / suc q') i) (suc q) i)))

floor-fracℚ₊≤ : (x : ℚ₊) → fromNat (fst (fst (floor-fracℚ₊ x))) ≤ fst x
floor-fracℚ₊≤ x =
  let ((N , q) , (e , (0≤q , _))) = floor-fracℚ₊ x
      zz = ≡Weaken≤ _ _ e
      uu = subst (_≤ (fst x + q))
                (+IdR _) $ ≤Monotone+ _ _ 0 _ zz 0≤q
  in ≤-+o-cancel (fromNat N) _ _ uu

≤floor-fracℚ₊ : (x : ℚ₊) → fst x < fromNat (suc (fst (fst (floor-fracℚ₊ x))))
≤floor-fracℚ₊ x =
  let ((N , q) , (e , (_ , q<1))) = floor-fracℚ₊ x
  in subst (fst x <_) (ℕ+→ℚ+ N 1 ∙ cong (λ x → [ pos x / 1 ])
             (ℕ.+-comm N 1))
           $ isTrans≤< (fst x) (fromNat (fst (fst (floor-fracℚ₊ x))) + q) ((fromNat N) + 1)
              (≡Weaken≤ (fst x) (fromNat (fst (fst (floor-fracℚ₊ x))) + q) (sym e))
                 (<-o+ q 1 (fromNat N) q<1)


ceil-[1-frac]ℚ₊ : ∀ (x : ℚ₊) → Σ (ℕ × ℚ) λ (k , q) →
                       (fst x + q ≡ fromNat k) × ((0 ≤ q)  × (q < 1))
ceil-[1-frac]ℚ₊ x =
 let ((fl , fr) , e , (e' , e'')) = floor-fracℚ₊ x

 in decRec
      (λ p → (fl , 0) ,
        (+IdR _ ∙ sym e ∙ cong  ((fromNat fl) +_) (sym p) ∙ (+IdR _)) ,
          (isRefl≤ 0 , decℚ<?))
      (λ p → (suc fl , (1 - fr)) ,
          (cong₂ (_+_) (sym e) (+Comm [ ℤ.pos 1 / 1+ 0 ] (- fr)) ∙
            sym (+Assoc (fromNat (fst (fst (floor-fracℚ₊ x)))) fr (- fr + 1)) ∙
              cong  ((fromNat fl) +_)
                (+Assoc fr (- fr) 1
                  ∙∙ cong (_+ 1) (+InvR fr) ∙∙ +IdL 1)
               ∙ +Comm ([ pos fl / 1 ]) 1 ∙ ℕ+→ℚ+ 1 fl) ,
               <Weaken≤ 0 _ (-< fr 1 e'') ,
                 (<-o+ _ _ 1 (
                   (⊎.rec (⊥.rec ∘ p) (minus-< 0 fr) (≤→≡⊎< 0 fr e')))))
     (discreteℚ 0 fr)


{-
floor-frac : ∀ (x : ℚ) → Σ (ℤ × ℚ) λ (k , q) →
                       ([ k , 1 ] + q ≡ x) × ((0 ≤ q)  × (q < 1))
floor-frac x with 0 ≟ x
... | lt x₁ =
  let ((c , fr') , e ) = floor-fracℚ₊ (x , <→0< _ x₁)
  in (ℤ.pos c , fr') , e

... | eq x₁ = (0 , 0) , (x₁ , isRefl≤ 0 , decℚ<? )
... | gt x₁ =
  let ((c , fr') , e , e') = ceil-[1-frac]ℚ₊
          (- x , <→0< (- x) (minus-< x 0 x₁))
      fl = (ℤ.- ℤ.pos c)
      p : [ fl , 1 ] + fr' ≡ x
      p = (sym (-Invol _)
             ∙ cong (-_) (-Distr _ _
                 ∙ cong (_- fr')
                    (cong [_/ 1 ] (ℤ.-Involutive _) )))
              ∙ sym (cong -_ (+CancelL- _ _ _ e)) ∙ -Invol _
  in (fl , fr') ,
        p , e'
-}

ceilℚ₊ : (q : ℚ₊) → Σ[ k ∈ ℕ₊₁ ] (fst q) < fromNat (ℕ₊₁→ℕ k)
ceilℚ₊ q = 1+ (fst (fst (floor-fracℚ₊ q))) ,
   subst2 (_<_) --  (fromNat (suc (fst (fst (floor-fracℚ₊ q)))))
      (+Comm (floor-fracℚ₊ q .fst .snd) (fromNat (fst (fst (floor-fracℚ₊ q)))) ∙
       fst (snd (floor-fracℚ₊ q)))
      (ℕ+→ℚ+ 1 (fst (fst (floor-fracℚ₊ q))))
       (<-+o (floor-fracℚ₊ q .fst .snd) (1) (fromNat (fst (fst (floor-fracℚ₊ q))))
         (snd (snd (snd (floor-fracℚ₊ q)))))





sign : ℚ → ℚ
sign = Rec.go w
 where
 w : Rec _
 w .Rec.isSetB = isSetℚ
 w .Rec.f (ℤ.pos zero , snd₁) = 0
 w .Rec.f (ℤ.pos (suc n) , snd₁) = 1
 w .Rec.f (ℤ.negsuc n , snd₁) = [ ℤ.ℤ.negsuc 0 , 1 ]
 w .Rec.f∼ (ℤ.pos zero , (1+ nn)) (ℤ.pos zero , snd₂) x = refl
 w .Rec.f∼ (ℤ.pos zero , (1+ nn)) (ℤ.pos (suc n₁) , snd₂) x =
    ⊥.rec $ znots $
     ℤ.injPos (x ∙ sym (ℤ.pos·pos (suc n₁) (suc nn)))
 w .Rec.f∼ (ℤ.pos (suc n₁) , snd₁) (ℤ.pos zero , (1+ nn)) x =
   ⊥.rec $ znots $
     ℤ.injPos (sym x ∙ sym (ℤ.pos·pos (suc n₁) (suc nn)))
 w .Rec.f∼ (ℤ.pos (suc n) , snd₁) (ℤ.pos (suc n₁) , snd₂) x = refl
 w .Rec.f∼ (ℤ.pos n₁ , snd₂) (ℤ.negsuc n , snd₁) x =
    ⊥.rec (
     𝟚.toWitnessFalse
      {Q = (ℤ.discreteℤ _ _)}
       tt ((cong (ℤ.-_) (ℤ.pos·pos (suc n) (ℕ₊₁→ℕ snd₂))
        ∙ sym (ℤ.negsuc·pos n _)) ∙∙ (sym x) ∙∙ sym (ℤ.pos·pos n₁ _) ))
 w .Rec.f∼ (ℤ.negsuc n , snd₁) (ℤ.pos n₁ , snd₂) x =
   ⊥.rec (
     𝟚.toWitnessFalse
      {Q = (ℤ.discreteℤ _ _)}
       tt ((cong (ℤ.-_) (ℤ.pos·pos (suc n) (ℕ₊₁→ℕ snd₂))
        ∙ sym (ℤ.negsuc·pos n (ℕ₊₁→ℕ snd₂))) ∙∙ x ∙∙ sym (ℤ.pos·pos n₁ _) ))
 w .Rec.f∼ (ℤ.negsuc n , snd₁) (ℤ.negsuc n₁ , snd₂) x = refl

<≃sign : ∀ x → ((0 < x) ≃ (sign x ≡ 1))
               × ((0 ≡ x) ≃ (sign x ≡ 0))
                 × ((x < 0) ≃ (sign x ≡ -1))
<≃sign = ElimProp.go w
 where
 w : ElimProp _
 w .ElimProp.isPropB _ =
  isProp× (isOfHLevel≃ 1 (isProp< _ _) (isSetℚ _ _))
     (isProp× (isOfHLevel≃ 1 (isSetℚ _ _) (isSetℚ _ _))
         (isOfHLevel≃ 1 (isProp< _ _) (isSetℚ _ _))
       )
 w .ElimProp.f (ℤ.pos zero , (1+ n)) =
  propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
    ((λ (inj x₁) → ⊥.rec $ ℤ.isIrrefl< x₁))
      (λ x → ⊥.rec $ ℕ.znots (ℤ.injPos (eq/⁻¹ _ _ x))) ,
   (propBiimpl→Equiv (isSetℚ _ _) (isSetℚ _ _)
     (λ _ → refl) (λ _ → eq/ _ _ refl) ,
      propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
        (λ (inj x) → ⊥.rec (ℤ.¬-pos<-zero x))
          (λ x → ⊥.rec $ ℤ.posNotnegsuc _ _ ((eq/⁻¹ _ _ x))))

 w .ElimProp.f (ℤ.pos (suc n) , snd₁) =
   propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
    (λ _ → refl) (λ _ → 0<→< [ ℤ.pos (suc n) , snd₁ ] (inj (ℤ.pos<pos tt))) ,
   (propBiimpl→Equiv (isSetℚ _ _) (isSetℚ _ _)
     ((λ b → ⊥.rec
      (znots $ ℤ.injPos (b ∙ ℤ.·IdR (ℤ.pos (suc n))))) ∘S eq/⁻¹ _ _)
     (λ x → ⊥.rec (ℕ.snotz $ ℤ.injPos (eq/⁻¹ _ _ x)))  ,
      propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
        (λ (inj x) → ⊥.rec (ℤ.¬-pos<-zero (subst (ℤ._< 0)
         (sym (ℤ.pos·pos (suc n) 1)) x)))
          λ x → ⊥.rec (ℤ.posNotnegsuc _ _ (eq/⁻¹ _ _ x)))

 w .ElimProp.f (ℤ.negsuc n , snd₁) =
   propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
    ((λ (inj x₁) → ⊥.rec $
   ℤ.¬pos≤negsuc (subst ((ℤ.pos 1) ℤ.≤_) (ℤ.negsuc·pos n 1 ∙
    cong ℤ.-_ (sym (ℤ.pos·pos (suc n) 1)) ) (ℤ.<→suc≤ x₁))))
     ((λ x → ⊥.rec (ℤ.posNotnegsuc 1 0 (sym x))) ∘S eq/⁻¹ _ _) ,
   (propBiimpl→Equiv (isSetℚ _ _) (isSetℚ _ _)
     ((λ x → ⊥.rec (ℤ.posNotnegsuc _ _
     (eq/⁻¹ _ _ x ∙ ℤ.·IdR (ℤ.negsuc n)))))
     ((⊥.rec ∘ ℤ.posNotnegsuc _ _ ∘ sym ) ∘S eq/⁻¹ _ _ )  ,
      propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
        (λ _ → refl)
         λ _ → minus-<' _ _ (0<→< (- [ ℤ.negsuc n , snd₁ ]) (inj (ℤ.pos<pos tt))))


<→sign : ∀ x → (0 < x → sign x ≡ 1)
               × (0 ≡ x → sign x ≡ 0)
                 × (x < 0 → sign x ≡ -1)
<→sign x =
 let ((y , _) , (y' , _) , (y'' , _)) = <≃sign x
 in (y , y' , y'')

abs≡sign· : ∀ x → abs x ≡ x · (sign x)
abs≡sign· x = abs'≡abs x ∙ ElimProp.go w x
 where
 w : ElimProp (λ z → abs' z ≡ z · sign z)
 w .ElimProp.isPropB _ = isSetℚ _ _
 w .ElimProp.f x@(ℤ.pos zero , snd₁)    = decℚ?
 w .ElimProp.f x@(ℤ.pos (suc n) , snd₁) = sym (·CancelR 1)
 w .ElimProp.f x@(ℤ.negsuc n , snd₁)    = sym (·CancelR 1)

absPos : ∀ x → 0 < x → abs x ≡ x
absPos x 0<x = abs≡sign· x ∙∙ cong (x ·_) (fst (<→sign x) 0<x)  ∙∙ (·IdR x)

absNonNeg : ∀ x → 0 ≤ x → abs x ≡ x
absNonNeg x 0<x with x ≟ 0
... | lt x₁ = ⊥.rec $ ≤→≯ 0 x 0<x x₁
... | eq x₁ = cong abs x₁ ∙ sym x₁
... | gt x₁ = absPos x x₁



absNeg : ∀ x → x < 0 → abs x ≡ - x
absNeg x x<0 = abs≡sign· x ∙∙ cong (x ·_) (snd (snd (<→sign x)) x<0)
                 ∙∙ ·Comm x -1



0≤abs : ∀ x → 0 ≤ abs x
0≤abs x with x ≟ 0
... | lt x₁ = subst (0 ≤_) (sym (absNeg x x₁)) ((<Weaken≤ 0 (- x) (minus-< x 0 x₁) ))
... | eq x₁ = subst ((0 ≤_) ∘ abs) (sym x₁) (isRefl≤ 0)
... | gt x₁ = subst (0 ≤_) (sym (absPos x x₁)) (<Weaken≤ 0 x x₁)


abs+pos : ∀ x y → 0 < x → abs (x + y) ≤ x + abs y
abs+pos x y x₁ with y ≟ 0
... | lt x₂ =
 let xx = (≤-o+ y (- y) x
            (<Weaken≤ y (- y) $ isTrans< y 0 (- y) x₂ ((minus-< y 0 x₂))))
 in subst (λ yy → abs (x + y) ≤ x + yy)
        (sym (absNeg y x₂)) (absFrom≤×≤ (x - y) _
          (subst (_≤ x + y)
            (sym (-Distr' x y)) (≤-+o (- x) x y
             (<Weaken≤ (- x) x $ isTrans< (- x) 0 x (minus-< 0 x x₁) x₁))) xx)
... | eq x₂ = subst2 _≤_ (sym (absPos x x₁)
        ∙ cong abs (sym (+IdR x) ∙ cong (x +_) ( (sym x₂))))
   (sym (+IdR x) ∙ cong (x +_) (cong abs (sym x₂))  ) (isRefl≤ x)
... | gt x₂ = subst2 _≤_ (sym (absPos _ (<Monotone+ 0 x 0 y x₁ x₂)))
    (cong (x +_) (sym (absPos y x₂)))
   $ isRefl≤ (x + y)

abs+≤abs+abs : ∀ x y → abs (x + y) ≤ abs x + abs y
abs+≤abs+abs x y with (x ≟ 0) | (y ≟ 0)
... | _ | gt x₁ = subst2 (_≤_)
                   (cong abs (+Comm y x))
            ((+Comm y (abs x)) ∙ cong ((abs x) +_ ) (sym (absPos y x₁)))
             (abs+pos y x x₁)
... | eq x₁ | _ = subst2 _≤_ (cong abs (sym (+IdL y) ∙
    cong (_+ y) (sym x₁) ))
                    (sym (+IdL (abs y)) ∙
                     cong (_+ (abs y)) (cong abs (sym x₁)))
                      (isRefl≤ (abs y))
... | gt x₁ | _ = subst (abs (x + y) ≤_)
            (cong (_+ (abs y)) (sym (absPos x x₁)))
              (abs+pos x y x₁)
... | lt x₁ | lt x₂ =
  subst2 _≤_ (sym (-Distr x y) ∙ sym (absNeg (x + y)
    (<Monotone+ x 0 y 0 x₁ x₂)))
     (cong₂ _+_ (sym (absNeg x x₁)) (sym (absNeg y x₂))) (isRefl≤ ((- x) - y) )
... | lt x₁ | eq x₂ =
  subst2 _≤_ ((cong abs (sym (+IdR x) ∙
    cong (x +_) (sym x₂))))
     (sym (+IdR (abs x)) ∙
                     cong ((abs x) +_ ) (cong abs (sym x₂)))
    ((isRefl≤ (abs x)))

data Trichotomy0· (m n : ℚ) : Type₀ where
  eqₘ₌₀ : m ≡ 0 → m · n ≡ 0  → Trichotomy0· m n
  eqₙ₌₀ : n ≡ 0 → m · n ≡ 0 → Trichotomy0· m n
  lt-lt : m < 0 → n < 0 → 0 < m · n  → Trichotomy0· m n
  lt-gt : m < 0 → 0 < n → m · n < 0  → Trichotomy0· m n
  gt-lt : 0 < m → n < 0 → m · n < 0  → Trichotomy0· m n
  gt-gt : 0 < m → 0 < n → 0 < m · n  → Trichotomy0· m n

trichotomy0· : ∀ m n → Trichotomy0· m n
trichotomy0· m n with m ≟ 0 | n ≟ 0
... | eq p | _    = eqₘ₌₀ p (cong (_· n) p ∙ ·AnnihilL n)
... | _    | eq p = eqₙ₌₀ p (cong (m ·_) p ∙ ·AnnihilR m)
... | lt x₁ | lt x₂ = lt-lt x₁ x₂
  (subst (0 <_) (-·- m n)
    (0<-m·n (- m) (- n) (minus-< m 0 x₁) (minus-< n 0 x₂)))
... | lt x₁ | gt x₂ = lt-gt x₁ x₂
 ((subst (m · n <_) (·AnnihilL n) $ <-·o m 0 n x₂ x₁ ))
... | gt x₁ | lt x₂ = gt-lt x₁ x₂
 (subst (m · n <_) (·AnnihilR m) $ <-o· n 0 m x₁ x₂ )
... | gt x₁ | gt x₂ = gt-gt x₁ x₂ (0<-m·n m n x₁ x₂)

sign·sign : ∀ x y → sign x · sign y ≡ sign (x · y)
sign·sign x y = h $ trichotomy0· x y

 where

 x' = <→sign x
 y' = <→sign y
 x·y' = <→sign (x · y)

 h : Trichotomy0· x y → _ -- ·AnnihilL
 h (eqₘ₌₀ p p₁) =
  cong (_· sign y) (fst (snd x') (sym p))
   ∙∙ ℚ!! ∙∙ sym (fst (snd x·y') (sym p₁))
 h (eqₙ₌₀ p p₁) =   cong (sign x ·_) (fst (snd y') (sym p))
   ∙∙ ℚ!! ∙∙ sym (fst (snd x·y') (sym p₁))
 h (lt-lt p p₁ p₂) = cong₂ _·_ (snd (snd x') p) (snd (snd y') p₁)
  ∙ (sym $ fst x·y' p₂)
 h (lt-gt p p₁ p₂) = cong₂ _·_  (snd (snd x') p) (fst y' p₁)
          ∙ sym (snd (snd x·y') p₂)
 h (gt-lt p p₁ p₂) = cong₂ _·_ (fst x' p) (snd (snd y') p₁)
          ∙ sym (snd (snd x·y') p₂)
 h (gt-gt p p₁ p₂) = cong₂ _·_ (fst x' p) (fst y' p₁)
  ∙ (sym $ fst x·y' p₂)

0≤x² : ∀ x → 0 ≤ x · x
0≤x² = ElimProp.go w
 where
 w : ElimProp (λ z → 0 ≤ z · z)
 w .ElimProp.isPropB _ = isProp≤ _ _
 w .ElimProp.f (p , q) = inj (subst (0 ℤ.≤_) (sym (ℤ.·IdR _)) (ℤ.0≤x² p))

signX·signX : ∀ x → 0 # x → sign x · sign x ≡ 1
signX·signX x y = sign·sign x x ∙
   fst (fst (<≃sign (x · x)))
    (⊎.rec (λ z → 0<-m·n _ _ z z)
      ((λ z → subst (0 <_) (-·- x x) (0<-m·n (- x) (- x) z z)) ∘S minus-< x 0) y)

abs·abs : ∀ x y → abs x · abs y ≡ abs (x · y)
abs·abs x y = cong₂ _·_ (abs≡sign· x) (abs≡sign· y)
 ∙∙ (sym (·Assoc x (sign x) (y · sign y))) ∙∙
  cong (x ·_) (( (·Assoc (sign x) y (sign y))) ∙∙
  congS (_· sign y) (·Comm (sign x) y) ∙∙ (sym (·Assoc y (sign x) (sign y))))
   ∙∙ (·Assoc x y (sign·sign x y i0))
 ∙∙ (λ i → x · y · sign·sign x y i) ∙ sym (abs≡sign· (x · y))

abs'·abs' : ∀ x y → abs' x · abs' y ≡ abs' (x · y)
abs'·abs' x y = cong₂ _·_ (sym (abs'≡abs x)) (sym (abs'≡abs y))
  ∙∙ abs·abs x y ∙∙ abs'≡abs (x · y)

pos·abs : ∀ x y → 0 ≤ x →  abs (x · y) ≡ x · (abs y)
pos·abs x y 0≤x = sym (abs·abs x y) ∙ cong (_· (abs y))
  (absNonNeg x 0≤x)

clamp≤ : ∀ L L' x → clamp L L' x ≤ L'
clamp≤ L L' x = min≤' (max L x) L'


≤cases : ∀ x y → (x ≤ y) ⊎ (y ≤ x)
≤cases x y with x ≟ y
... | lt x₁ = inl (<Weaken≤ _ _ x₁)
... | eq x₁ = inl (≡Weaken≤ _ _ x₁)
... | gt x₁ = inr (<Weaken≤ _ _ x₁)

elimBy≤ : ∀ {ℓ} {A : ℚ → ℚ → Type ℓ}
  → (∀ x y → A x y → A y x)
  → (∀ x y → x ≤ y → A x y)
  → ∀ x y → A x y
elimBy≤ s f x y = ⊎.rec
  (f _ _ ) (s _ _ ∘ f _ _ ) (≤cases x y)

elim≤By≡⊎< : ∀ {ℓ} (a : ℚ) {A : ∀ x → a ≤ x → Type ℓ}
  → (A a (isRefl≤ a))
  → (∀ x a<x → A x (<Weaken≤ _ _ a<x)  )
  → ∀ x a<x → A x a<x
elim≤By≡⊎< a {A = A} r f x =
  ⊎.rec
    (λ a=x → subst (uncurry A) (Σ≡Prop (isProp≤ a) a=x) r)
    (subst (A x) (isProp≤ a x _ _) ∘ f x)
    ∘ (≤→≡⊎< a x)

elimBy≡⊎< : ∀ {ℓ} {A : ℚ → ℚ → Type ℓ}
  → (∀ x y → A x y → A y x)
  → (∀ x → A x x)
  → (∀ x y → x < y → A x y)
  → ∀ x y → A x y
elimBy≡⊎< {A = A} s r f =
 elimBy≤ s (λ x y → ⊎.rec (λ p → subst (A x) p (r x)) (f x y) ∘ ≤→≡⊎< x y)


max< : ∀ x y z → x < z → y < z → max x y < z
max< = elimBy≤
  (λ x y X z y<z x<z → subst (_< z) (maxComm x y) (X z x<z y<z) )
  λ x y x≤y z x<z y<z →
    subst (_< z) (sym (≤→max x y x≤y)) y<z

maxDistMin : ∀ x y z → min (max x y) z ≡ max (min x z) (min y z)
maxDistMin = elimBy≤
 (λ x y p z → cong (flip min z) (maxComm y x)  ∙∙ p z ∙∙
                maxComm (min x z) (min y z) )
 λ x y p z → cong (flip min z) (≤→max x y p) ∙
   sym (≤→max (min x z) (min y z) (≤MonotoneMin x y z z p (isRefl≤ z) ))



minDistMax : ∀ x y y' → max x (min y y') ≡ min (max x y) (max x y')
minDistMax x = elimBy≤
  (λ y y' X → cong (max x) (minComm y' y) ∙∙ X ∙∙ minComm (max x y) (max x y'))
  λ y y' y≤y' → cong (max x) (≤→min _ _ y≤y') ∙
    sym (≤→min (max x y) (max x y')
      (≤MonotoneMax x x y y' (isRefl≤ x) y≤y'))

≤clamp : ∀ L L' x → L ≤ L' →  L ≤ clamp L L' x
≤clamp L L' x y =
 subst (L ≤_) (cong (λ y → max y _) (sym $ ≤→min L L' y)
      ∙ sym (maxDistMin L x L')) (≤max L (min x L'))

clamped≤ : ∀ L L' x → L ≤ x → clamp L L' x ≤ x
clamped≤ L L' x L≤x = subst (_≤ x)
  (cong (flip min L') (sym (≤→max L x L≤x))) (min≤ x L')

absComm- : ∀ x y → abs (x - y) ≡ abs (y - x)
absComm- x y i = maxComm (-[x-y]≡y-x y x (~ i)) (-[x-y]≡y-x x y i) i

abs'Comm- : ∀ x y → abs' (x - y) ≡ abs' (y - x)
abs'Comm- x y = sym (abs'≡abs (x - y)) ∙∙ absComm- x y ∙∙ abs'≡abs (y - x)

≤MonotoneClamp : ∀ L L' x y → x ≤ y → clamp L L' x ≤ clamp L L' y
≤MonotoneClamp L L' x y p =
 ≤MonotoneMin
  (max L x) (max L y) L'
   L' (≤MonotoneMax L L x y (isRefl≤ L) p) (isRefl≤ L')



inClamps : ∀ L L' x → L ≤ x → x ≤ L' → clamp L L' x ≡ x
inClamps L L' x u v =
  cong (λ y → min y L') (≤→max L x u)
    ∙ ≤→min x L' v

≤abs : ∀ x → x ≤ abs x
≤abs x = ≤max x (- x)

≤abs' : ∀ x → x ≤ abs' x
≤abs' x = subst (x ≤_) (abs'≡abs x) (≤abs x)


-abs : ∀ x → abs x ≡ abs (- x)
-abs x = maxComm x (- x)
  ∙ cong (max (- x)) (sym (-Invol x))

-abs' : ∀ x → abs' x ≡ abs' (- x)
-abs' x = sym (abs'≡abs x) ∙∙ -abs x ∙∙ abs'≡abs (- x)

-≤abs' : ∀ x → - x ≤ abs' x
-≤abs' x = subst (- x ≤_) (sym (-abs' x)) (≤abs' (- x))

-≤abs : ∀ x → - x ≤ abs x
-≤abs x = subst (- x ≤_) (sym (-abs x)) (≤abs (- x))


absTo≤×≤ : ∀ ε q
                → abs q ≤ ε
                → (- ε ≤ q) × (q ≤ ε)

absTo≤×≤ ε q abs[q]≤ε .fst =
 subst (- ε ≤_) (-Invol q) (minus-≤ _ _ (isTrans≤ _ _ _ (-≤abs q) abs[q]≤ε))
absTo≤×≤ ε q abs[q]≤ε .snd = isTrans≤ _ _ _ (≤abs q) abs[q]≤ε


Dichotomyℚ : ∀ (n m : ℚ) → (n ≤ m) ⊎ (m < n)
Dichotomyℚ n m = decRec inr (inl ∘ ≮→≥ _ _) (<Dec m n)

sign·abs : ∀ x → abs x · (sign x) ≡ x
sign·abs x with 0 ≟ x
... | lt x₁ =
 cong₂ _·_ (absPos x x₁) (fst (<→sign x) x₁)
    ∙ ·IdR x
... | eq x₁ = cong (abs x ·_) ( (fst (snd (<→sign x)) x₁))
 ∙ ·AnnihilR (abs x) ∙ x₁
... | gt x₁ =
  cong₂ _·_ (absNeg x x₁) (snd (snd (<→sign x)) x₁)
    ∙ -·- x 1 ∙ ·IdR x


0#→0<abs' : ∀ q → 0 # q → 0 < abs' q
0#→0<abs' q (inl x) =
  subst (0 <_) (sym (absPos q x) ∙ (abs'≡abs q)) x
0#→0<abs' q (inr y) =
  subst (0 <_) (sym (absNeg q y) ∙ (abs'≡abs q)) (minus-< q 0 y)

0#→ℚ₊ : ∀ q → 0 # q → ℚ₊
0#→ℚ₊ q x = abs' q , <→0< _ (0#→0<abs' q x)

·Monotone0# : ∀ q q' → 0 # q → 0 # q' → 0 # (q · q')
·Monotone0# q q' (inl x) (inl x₁) =
 inl (0<→< _ (·0< q q' (<→0< q x) (<→0< q' x₁)))
·Monotone0# q q' (inl x) (inr x₁) =
  inr (minus-<' 0 (q · q')
        (subst {x = q · - q'} {y = - (q · q')} (0 <_) ℚ!!
         (0<→< _ (·0< q (- q') (<→0< q x) (<→0< _ (minus-< q' 0 x₁)))) ))
·Monotone0# q q' (inr x) (inl x₁) =
  inr (minus-<' 0 (q · q')
     (subst (0 <_) (sym (·Assoc -1 q q'))
       ((0<→< _ (·0< (- q) q' (<→0< _ (minus-< q 0 x)) (<→0< q' x₁))))))
·Monotone0# q q' (inr x) (inr x₁) =
 inl (subst (0 <_) (-·- q q') (0<→< _
     (·0< (- q) (- q') (<→0< _ (minus-< q 0 x)) (<→0< _ (minus-< q' 0 x₁)))) )



0#sign : ∀ q → 0 # q ≃ 0 # (sign q)
0#sign q =
 propBiimpl→Equiv (isProp# _ _) (isProp# _ _)
   (⊎.map (((flip (subst (0 <_))
     (𝟚.toWitness {Q = <Dec 0 1} _)) ∘ sym) ∘S fst (<→sign q))
     ((((flip (subst (_< 0))
     (𝟚.toWitness {Q = <Dec -1 0} _)) ∘ sym) ∘S snd (snd (<→sign q)))))
     (⊎.rec (⊎.rec ((λ y z → ⊥.rec (isIrrefl# (sign q) (subst (_# (sign q))
        (sym y) z))) ∘S fst (snd (<→sign q))) (const ∘ inl) ∘ ≤→≡⊎< _ _ ) (λ x _ → inr x)
      (Dichotomyℚ 0 q))


-- ceil-fracℚ₊ : ∀ (x : ℚ₊) → Σ (ℕ × ℚ) λ (k , q) →
--                        (fromNat k + q ≡ fst x ) × (q < 1)
-- ceil-fracℚ₊ = {!!}

boundℕ : ∀ q → Σ[ k ∈ ℕ₊₁ ] (abs q < ([ ℕ₊₁→ℤ k , 1 ]))
boundℕ q with ≤→≡⊎< 0 (abs q) (0≤abs q)
... | inl x = 1 , subst (_< 1) x (decℚ<? {0} {1})
... | inr x =
 let ((k , f) , e , e' , e'') = floor-fracℚ₊ (abs q , <→0< _ x)
 in (1+ k , subst2 (_<_)
          (+Comm f _ ∙ e)
           (ℕ+→ℚ+ 1 k) ((<-+o f 1 [ pos k / 1+ 0 ] e'')))

isSetℚ₊ : isSet ℚ₊
isSetℚ₊ = isSetΣ isSetℚ λ q → isProp→isSet (snd (0<ₚ q))

invℚ₊ : ℚ₊ → ℚ₊
invℚ₊ = uncurry (Elim.go w)
 where

 w : Elim (λ z → (y : 0< z) → ℚ₊)
 w .Elim.isSetB _ = isSetΠ λ _ → isSetℚ₊
 w .Elim.f ( x , y ) (z) = [ (ℕ₊₁→ℤ y) , (ℤ.0<→ℕ₊₁-fst x) ] , inj (ℤ.pos<pos tt)
 w .Elim.f∼ r@( x , y ) r'@( x' , y' ) p = funExtDep h
  where
  h : {x₀ : 0< eq/ r r' p i0}
      {x₁ : 0< eq/ r r' p i1}
      (p₁ : PathP (λ z → 0< eq/ r r' p z) x₀ x₁) → _
  h {inj z} {inj z'} pp =  
    ℚ₊≡ (eq/ _ _ ((λ i → ℤ.·Comm (ℕ₊₁→ℤ y) ( (snd (ℤ.0<→ℕ₊₁ x' (subst (0 ℤ.<_) ℤ! z'))) (~ i)) i)
      ∙∙ sym p ∙∙
      λ i → ℤ.·Comm  ( (snd (ℤ.0<→ℕ₊₁ x (subst (0 ℤ.<_) ℤ! z))) i) (ℕ₊₁→ℤ y') i))
     


/2₊ : ℚ₊ → ℚ₊
/2₊ = _ℚ₊· ([ 1 / 2 ] , inj (ℤ.pos<pos tt))

/3₊ : ℚ₊ → ℚ₊
/3₊ = _ℚ₊· ([ 1 / 3 ] , inj (ℤ.pos<pos tt))


/4 : ℚ → ℚ
/4 = _· [ 1 / 4 ]

/4₊ : ℚ₊ → ℚ₊
/4₊ = _ℚ₊· ([ 1 / 4 ] , inj (ℤ.pos<pos tt))



invℚ₊-invol : ∀ x → fst (invℚ₊ (invℚ₊ x)) ≡ fst  x
invℚ₊-invol x = ℚ!



x·invℚ₊[x] : ∀ x → fst x · fst (invℚ₊ x) ≡ 1
x·invℚ₊[x] x = ℚ!

invℚ₊[x]·x : ∀ x →  fst (invℚ₊ x) · fst x ≡ 1
invℚ₊[x]·x x = ℚ!

[y·x]/y : ∀ y x → fst (invℚ₊ y) · (fst y · x) ≡ x
[y·x]/y y x = ℚ!

y·[x/y] : ∀ y x →  fst y · (fst (invℚ₊ y) · x) ≡ x
y·[x/y] y x = ℚ!


invℚ₊Dist· : ∀ x y →  ((invℚ₊ x) ℚ₊· (invℚ₊ y)) ≡
       (invℚ₊ (x ℚ₊· y))
invℚ₊Dist· x y = ℚ₊≡ ℚ!

/4₊+/4₊≡/2₊ : ∀ ε → (/4₊ ε) ℚ₊+ (/4₊ ε) ≡ /2₊ ε
/4₊+/4₊≡/2₊ ε = ℚ₊≡ ℚ!!

/4₊≡/2₊/2₊ : ∀ ε → fst (/4₊ ε) ≡ fst (/2₊ (/2₊ ε))
/4₊≡/2₊/2₊ ε = ℚ!!


n/k+m/k : ∀ n m k → [ n / k ] + [ m / k ] ≡ [ n ℤ.+ m / k ]
n/k+m/k n m k = ℚ!

n/k-m/k : ∀ n m k → [ n / k ] - [ m / k ] ≡ [ n ℤ.- m / k ]
n/k-m/k n m k = ℚ!

k/k : ∀ k → [ ℕ₊₁→ℤ k / k ] ≡ 1
k/k _ = ℚ!

1/[k+1]+k/[k+1] : (k : ℕ₊₁) → [ 1 / suc₊₁ k ] + [ pos (ℕ₊₁→ℕ k) / suc₊₁ k ] ≡ 1
1/[k+1]+k/[k+1] k = ℚ!


ε/2+ε/2≡ε : ∀ ε → (ε · [ 1 / 2 ]) + (ε · [ 1 / 2 ]) ≡ ε
ε/2+ε/2≡ε ε = ℚ!

ε/3+ε/3+ε/3≡ε : ∀ ε → (ε · [ 1 / 3 ]) +
                ((ε · [ 1 / 3 ]) + (ε · [ 1 / 3 ])) ≡ ε
ε/3+ε/3+ε/3≡ε ε = ℚ!

ε/6+ε/6≡ε/3 : ∀ ε → (ε · [ 1 / 6 ]) + (ε · [ 1 / 6 ]) ≡
               (ε · [ 1 / 3 ])
ε/6+ε/6≡ε/3 ε = ℚ!


equivInvℚ₊ : ℚ₊ ≃ ℚ₊
equivInvℚ₊ = involEquiv {f = invℚ₊} λ x → ℚ₊≡ (invℚ₊-invol x)


weak0< : ∀ q (ε δ : ℚ₊)
             →  q < (fst ε - fst δ)
             → q < fst ε
weak0< q ε δ x =
  let z = <Monotone+ q (fst ε - fst δ) 0 (fst δ) x (0<→< (fst δ) (snd δ))
   in subst2 _<_
       (+IdR q) ℚ!! z



weak0<' : ∀ q (ε δ : ℚ₊)
             → - (fst ε - fst δ) < q
             → - (fst ε) < q
weak0<' q ε δ x =
  let z = <Monotone+ (- (fst ε - fst δ)) q (- fst δ) 0 x
           (minus-< 0 (fst δ) ((0<→< (fst δ) (snd δ))))
  in (subst2 {x = (- (fst ε - fst δ)) + (- fst δ)}
         {y = - (fst ε)} _<_ ℚ!! ℚ!! z)



0</k : ∀ (q q' : ℚ₊) (k : ℕ₊₁) →
          0< ((fst q - fst q') )
           → 0< ((fst q - fst (q' ℚ₊· ([ 1 / (suc₊₁ k) ] , inj (ℤ.pos<pos tt)))) )
0</k q q' (1+ k) x =
   subst {x = (fst q - fst q') +
     (fst (([ pos (suc k)  / (1+ (suc k)) ] , inj (ℤ.pos<pos tt)) ℚ₊· q'))}
       {y = ((fst q - fst (q' ℚ₊· ([ 1 / 1+ (suc k) ] , inj (ℤ.pos<pos tt)))) )}  0<_
     ( sym (+Assoc (fst q) (- fst q') (fst (([ pos (suc k) / 2+ k ] , inj (ℤ.pos<pos tt)) ℚ₊· q'))) ∙ cong (fst q +_)
     (sym (·DistR+ (-1) [ pos (suc k) / 1+ (suc k) ] (fst q')) ∙
        (cong (_· (fst q'))
           (sym (-Distr' 1 ([ pos (ℕ₊₁→ℕ (1+ k)) / suc₊₁ (1+ k) ]))
              ∙ sym (cong (-_) $ +CancelL- [ 1 / suc₊₁ (1+ k) ] [ pos (ℕ₊₁→ℕ (1+ k)) / suc₊₁ (1+ k) ] _ (1/[k+1]+k/[k+1] (1+ k))))
          ∙∙ sym (·Assoc -1 [ pos 1 / 2+ k ] (fst q') )
         ∙∙ (cong (-_) (·Comm  [ pos 1 / 2+ k ]  (fst q')) ) ))
       ) (+0< (fst q - fst q')
    (fst (([ pos (suc k)  / (1+ (suc k)) ] , inj (ℤ.pos<pos tt)) ℚ₊· q')) x
     ((snd (([ pos (suc k)  / (1+ (suc k)) ] , inj (ℤ.pos<pos tt)) ℚ₊· q'))) )


-- x/k<x : ∀ x k → fst (x ℚ₊· ([ 1 / (1+ (suc k)) ] , tt)) < fst x
-- x/k<x x k =
--   let z = {!0</k k !}
--   in {!!}


x/2<x : (ε : ℚ₊)
           → (fst ε) · [ pos 1 / 1+ 1 ] < fst ε
x/2<x ε =
 let ε/2 = /2₊ ε
     z = <-+o 0 (fst ε/2) ((fst ε/2)) $ 0<→< (fst ε/2) (snd ε/2)
 in subst2 (_<_) (+IdL (fst ε/2))
      (ε/2+ε/2≡ε (fst ε)) z


getθ : ∀ (ε : ℚ₊) q → (((- fst ε) < q) × (q < fst ε)) →
   Σ ℚ₊ λ θ → (0< (fst ε - fst θ))
     × ((- (fst ε - fst θ) < q) × (q < (fst ε - fst θ)))
getθ ε q (x , x') =
 let m1< = <→0< (fst ε + q)
            (subst (_< fst ε + q) (+InvR (fst ε))
                   (<-o+  (- fst ε) q  (fst ε) x)
                    )
     m1 = (/2₊ (fst ε + q ,
                   m1<))
     m2< = <→0< (fst ε - q) $ subst (_< fst ε + (- q))
              ((+InvR q)) (<-+o q (fst ε) (- q) x')
     m2 = (/2₊ (fst ε - q , m2<))
     mm = (min₊ m1 m2)
     z'1 : fst mm < (fst ε + q)

     z'1 = isTrans≤<
            (fst mm)
            ((fst ε + q) · [ 1 / 2 ])
            (fst ε + q)
             (min≤ ((fst ε + q) · [ 1 / 2 ])
                  ((fst ε - q) · [ 1 / 2 ]))
                  (x/2<x ((fst ε + q) , m1<))
     z'2 : fst mm < (fst ε - q)

     z'2 =
        isTrans≤< (fst mm)
            _
            (fst ε - q)
            (isTrans≤ (fst mm)
                        _
                        _
               (≡Weaken≤ _ _
                 (minComm (((fst ε + q) · [ 1 / 2 ]))
                    (((fst ε - q) · [ 1 / 2 ]))))
               (min≤ ((fst ε - q) · [ 1 / 2 ])
                 ((fst ε + q) · [ 1 / 2 ])))
            (x/2<x ((fst ε - q) , m2<))
 in  mm ,
             <→0< (fst ε - fst mm)
               ( let zz = (<-·o ((fst mm) + (fst mm))
                                 ((fst ε + q) + (fst ε - q))
                               [ pos 1 / 1+ 1 ]
                                 (0<→< [ pos 1 / 1+ 1 ] (inj (ℤ.pos<pos tt)) )
                          (<Monotone+ (fst mm) (fst ε + q)
                             (fst mm) (fst ε - q)
                             z'1 z'2))
                     zz' = subst2 _<_
                             (·DistR+ (fst mm) (fst mm) [ pos 1 / 1+ 1 ]
                                ∙ ε/2+ε/2≡ε (fst mm))
                              (cong
                                {x = ((fst ε + q) + (fst ε - q))}
                                {y = (fst ε + fst ε)}
                                (_· [ pos 1 / 1+ 1 ])
                                (ℚ!!)
                                ∙∙ ·DistR+ (fst ε) (fst ε) [ pos 1 / 1+ 1 ]
                                ∙∙ ε/2+ε/2≡ε (fst ε))
                              zz
                 in -< (fst mm) (fst ε)  zz')
           , (subst2 _<_ ℚ!! ℚ!!
                      (<-o+ (fst mm)
                              (fst ε + q) (- fst ε) z'1)
           , subst2 _<_ ℚ!! ℚ!!
                       (<-+o (fst mm)
                              (fst ε - q)
                               (q - fst mm)
                               z'2))


strength-lem-01 : (ε q' a'' : ℚ₊) →
                    0< (fst ε + (- fst q') + (- fst a''))
                    → 0< (fst ε - fst a'')
strength-lem-01 ε q' a'' x =
   let z = +0< ((fst ε + (- fst q') + (- fst a'')))
                (fst q') x (snd q')
    in subst  {x = ((fst ε + (- fst q') + (- fst a''))) +
                fst q' }
        {y = (fst ε - fst a'')} 0<_ ℚ!! z


x/2+[y-x]=y-x/2 : ∀ (x y : ℚ₊) →
   fst (/2₊ x) + (fst y - fst x) ≡
     fst y - fst (/2₊ x)
x/2+[y-x]=y-x/2 x y = ℚ!!


elimBy≡⊎<' : ∀ {ℓ} {A : ℚ → ℚ → Type ℓ}
  → (∀ x y → A x y → A y x)
  → (∀ x → A x x)
  → (∀ x (ε : ℚ₊) → A x (x + fst ε))
  → ∀ x y → A x y
elimBy≡⊎<' {A = A} s r f' =
 elimBy≤ s (λ x y → ⊎.rec (λ p → subst (A x) p (r x)) (f x y) ∘ ≤→≡⊎< x y)

 where
 f : ∀ x y → x < y → A x y
 f x y v = subst (A x) ℚ!! $ f' x (<→ℚ₊ x y v)

elim≤By+ : ∀ {ℓ} {A : ∀ x y → x < y →  Type ℓ}
  → (∀ x (ε : ℚ₊) x< → A x (x + fst ε) x<)
  → ∀ x y x<y → A x y x<y
elim≤By+ {A = A} X x y v =
  subst (uncurry (A x)) (Σ≡Prop (isProp< x) {x + (y - x) , _} {y , _} ℚ!!) $
   X x (<→ℚ₊ x y v) (<+ℚ₊' x x ((<→ℚ₊ x y v)) (isRefl≤ x))


module HLP where



 data GExpr : Type where
  ge[_] : ℚ → GExpr
  neg-ge_ : GExpr → GExpr
  _+ge_ : GExpr → GExpr → GExpr
  _·ge_ : GExpr → GExpr → GExpr
  ge1 : GExpr

 infixl 6 _+ge_
 infixl 7 _·ge_


 ·GE : ℚ → GExpr → GExpr
 ·GE ε ge[ x ] = ge[ ε · x ]
 ·GE ε (neg-ge x) = (neg-ge (·GE ε x))
 ·GE ε (x +ge x₁) = ·GE ε x +ge ·GE ε x₁
 ·GE ε (x ·ge x₁) = (·GE ε x) ·ge x₁
 ·GE ε ge1 = ge[ ε ]

 evGE : GExpr → ℚ
 evGE ge[ x ] = x
 evGE (neg-ge x) = - evGE x
 evGE (x +ge x₁) = evGE x + evGE x₁
 evGE (x ·ge x₁) = evGE x · evGE x₁
 evGE ge1 = 1

 ·mapGE : ∀ ε e → ε · evGE e ≡ evGE (·GE ε e)
 ·mapGE ε ge[ x ] = refl
 ·mapGE ε (neg-ge e) = ·Assoc ε -1 (evGE e) ∙∙
   cong (_· evGE e) (·Comm ε -1) ∙
    sym (·Assoc -1 ε (evGE e)) ∙∙ cong (-_) (·mapGE ε e)
 ·mapGE ε (e +ge e₁) =
   ·DistL+ ε _ _ ∙ λ i → (·mapGE ε e i) + (·mapGE ε e₁ i)
 ·mapGE ε (e ·ge e₁) = ·Assoc ε (evGE e) (evGE e₁) ∙ cong (_· evGE e₁) (·mapGE ε e)
 ·mapGE ε (ge1) = ·IdR ε


 infixl 20 distℚ!!_·[_≡_]


 distℚ!!_·[_≡_] : (ε : ℚ) → (lhs rhs : GExpr)
    → {𝟚.True (discreteℚ (evGE lhs) (evGE rhs))}
     → (evGE (·GE ε lhs)) ≡ (evGE (·GE ε rhs))
 distℚ!! ε ·[ lhs ≡ rhs ] {p} =
   sym (·mapGE ε lhs) ∙∙ cong (ε ·_) (𝟚.toWitness p)  ∙∙
    ·mapGE ε rhs

 infixl 20 distℚ<!_[_<_]

 distℚ<!_[_<_] : (ε : ℚ₊) → (lhs rhs : GExpr)
    → {𝟚.True (<Dec (evGE lhs) (evGE rhs))}
     → (evGE (·GE (fst ε) lhs)) < (evGE (·GE (fst ε) rhs))
 distℚ<! ε [ lhs < rhs ] {p} =
   subst2 _<_ (·mapGE (fst ε) lhs) (·mapGE (fst ε) rhs)
     (<-o· _ _ (fst ε) (0<ℚ₊ ε) (𝟚.toWitness p))


 distℚ≤!_[_≤_] : (ε : ℚ₊) → (lhs rhs : GExpr)
    → {𝟚.True (≤Dec (evGE lhs) (evGE rhs))}
     → (evGE (·GE (fst ε) lhs)) ≤ (evGE (·GE (fst ε) rhs))
 distℚ≤! ε [ lhs ≤ rhs ] {p} =
   subst2 _≤_ (·mapGE (fst ε) lhs) (·mapGE (fst ε) rhs)
     (≤-o· _ _ (fst ε) (0≤ℚ₊ ε) (𝟚.toWitness p))

 distℚ0<! : (ε : ℚ₊) → (rhs : GExpr)
    → {𝟚.True (<Dec 0 (evGE rhs))}
     →  0< (evGE (·GE (fst ε) rhs))
 distℚ0<! ε rhs {p} =
  <→0< _
   (subst2 _<_ (·mapGE (fst ε) ge[ 0 ] ∙ ·AnnihilR (fst ε))
    (·mapGE (fst ε) rhs)
     (<-o· _ _ (fst ε) (0<ℚ₊ ε) (𝟚.toWitness p)))


open HLP public


-<⁻¹ : ∀ q r → 0 < r - q → q < r
-<⁻¹ q r x = subst2 (_<_)
 (+IdL q) ((sym (ℚ!!))) (<-+o 0 (r - q) q x)


riseQandD : ∀ p q r → Path ℚ ([ p / q ]) ([ p ℤ.· ℕ₊₁→ℤ r / (q ·₊₁ r) ])
riseQandD p q r =
 let z = _
 in sym (·IdR z) ∙ cong (z ·_) (eq/ _ ( ℕ₊₁→ℤ r , r ) (ℤ.·Comm (pos (ℕ₊₁→ℕ one)) (ℕ₊₁→ℤ r)))


+MaxDistrℚ : ∀ x y z → (max x y) + z ≡ max (x + z) (y + z)
+MaxDistrℚ = SQ.elimProp3 (λ _ _ _ → isSetℚ _ _)
  $ uncurry λ a a' → uncurry λ b b' → uncurry λ c c' →
   let zzz' : ∀ a' b' c' →
            (ℤ.max (a ℤ.· b') (b ℤ.· a') ℤ.· (pos c') ℤ.+ c ℤ.· (a' ℤ.· b'))
                 ≡
            (ℤ.max ((a ℤ.· (pos c') ℤ.+ c ℤ.· a') ℤ.· b')
                   ((b ℤ.· (pos c') ℤ.+ c ℤ.· b') ℤ.· a'))
       zzz' a' b' c' =
            cong (ℤ._+ _) (ℤ.·DistPosLMax (a ℤ.· b') (b ℤ.· a') c' ∙
              cong₂
               {x = a ℤ.· b' ℤ.· pos c'}
               {a ℤ.· pos c' ℤ.· b'}
               ℤ.max ℤ!
                {u = b ℤ.· a' ℤ.· pos c'}
                {v = b ℤ.· pos c' ℤ.· a'} ℤ!)
          ∙∙ ℤ.+DistLMax (a ℤ.· pos c' ℤ.· b') (b ℤ.· pos c' ℤ.· a') (c ℤ.· (a' ℤ.· b'))
          ∙∙ cong₂ ℤ.max ℤ! ℤ!
       z* = _

   in congS (SQ.[_] ∘S (_, a' ·₊₁ b' ·₊₁ c'))
        (  congS ((λ ab → ℤ.max (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a')
             ℤ.· pos (suc (ℕ₊₁.n c')) ℤ.+
             ab) ∘ (c ℤ.·_)) (ℤ.pos·pos (ℕ₊₁→ℕ a') (ℕ₊₁→ℕ b'))
              ∙ zzz' (ℕ₊₁→ℤ a') (ℕ₊₁→ℤ b') (suc (ℕ₊₁.n c')))
        ∙∙ (sym (·IdR z*) ∙ cong (z* ·_)
            (eq/ _ ( ℕ₊₁→ℤ c' , c' )
          (ℤ.·Comm (pos (ℕ₊₁→ℕ one)) (ℕ₊₁→ℤ c'))) ) ∙∙
         congS (SQ.[_])
          (cong₂ _,_
          ((ℤ.·DistPosLMax
                 ((a ℤ.· pos (suc (ℕ₊₁.n c')) ℤ.+ c ℤ.· ℕ₊₁→ℤ a') ℤ.· ℕ₊₁→ℤ b')
                 ((b ℤ.· pos (suc (ℕ₊₁.n c')) ℤ.+ c ℤ.· ℕ₊₁→ℤ b') ℤ.· ℕ₊₁→ℤ a')
             (suc (ℕ₊₁.n c'))) ∙ cong₂
            ℤ.max ℤ! ℤ!)
            (ℕ₊₁→ℕ-inj (ℤ.injPos ℤ!)))



+MinDistrℚ : ∀ x y z → (min x y) + z ≡ min (x + z) (y + z)
+MinDistrℚ = SQ.elimProp3 (λ _ _ _ → isSetℚ _ _)
  $ uncurry λ a a' → uncurry λ b b' → uncurry λ c c' →
   let z : ∀ a' b' c' →
              (ℤ.min (a ℤ.· pos b') (b ℤ.· pos a') ℤ.· pos c'
                 ℤ.+ c ℤ.· (pos a' ℤ.· pos b')) ℤ.· pos c'
               ≡
               ℤ.min
                ((a ℤ.· pos c' ℤ.+ c ℤ.· pos a') ℤ.· (pos b' ℤ.· pos c'))
                ((b ℤ.· pos c' ℤ.+ c ℤ.· pos b') ℤ.· (pos a' ℤ.· pos c'))

       z a' b' c' =
            _ ≡⟨ ℤ! ∙  ((λ i → (ℤ.·DistPosLMin (a ℤ.· pos b') (b ℤ.· pos a') (c' ℕ.· c') i
                 ℤ.+ c ℤ.· (pos a' ℤ.· pos b') ℤ.· pos c')  )) ⟩
            _ ≡⟨ ℤ.+DistLMin (a ℤ.· pos b' ℤ.· pos (c' ℕ.· c'))
                             (b ℤ.· pos a' ℤ.· pos (c' ℕ.· c'))
                             (c ℤ.· (pos a' ℤ.· pos b') ℤ.· pos c') ⟩
            _ ≡⟨ cong₂ ℤ.min ℤ! ℤ! ⟩
             _ ∎
   in riseQandD
         (ℤ.min (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') ℤ.· ℕ₊₁→ℤ c' ℤ.+
               c ℤ.· ℕ₊₁→ℤ (a' ·₊₁ b')) ( a' ·₊₁ b' ·₊₁ c') c'
            ∙ congS (SQ.[_])
              (cong₂ _,_
                 ((λ i →
                      (ℤ.min (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') ℤ.· ℕ₊₁→ℤ c' ℤ.+
                         c ℤ.· ℤ.pos·pos (ℕ₊₁→ℕ a') (ℕ₊₁→ℕ b') (i))
                        ℤ.· ℕ₊₁→ℤ c' )
                   ∙∙ z (suc (ℕ₊₁.n a')) (suc (ℕ₊₁.n b')) (suc (ℕ₊₁.n c'))
                   ∙∙ cong₂ ℤ.min ℤ! ℤ!)
                 (ℕ₊₁→ℕ-inj (ℤ.injPos ℤ!)))
                    --


<MonotoneMax : ∀ m o n s → m < n → o < s → max m o < max n s
<MonotoneMax =
  elimBy≤ (λ x y X o s u v → subst2 _<_ (maxComm x y) (maxComm s o)
                 ((X s o) v u))
   λ x y x≤y n s _ y<s →
     subst (_< max n s) (sym (≤→max x y x≤y))
      (isTrans<≤ _ _ _ y<s (≤max' n s))

<MonotoneMin : ∀ n s m o  → m < n → o < s → min m o < min n s
<MonotoneMin =
  elimBy≤ (λ x y X o s u v → subst2 _<_ (minComm s o) (minComm x y)
                 ((X s o) v u))
   λ x y x≤y n s n<x _ →
     subst (min n s <_) (sym (≤→min x y x≤y))
       (isTrans≤< _ _ _ (min≤ n s) n<x)


clampDelta : ∀ L L' x → clamp L L' x ≡
               (x + clamp (L - x) (L' - x) 0)
clampDelta L L' x =
     cong₂ min
       (cong₂ {x = L} {y = (L - x) + x} max (ℚ!!) {x} {0 + x}
         (sym $ +IdL x) ∙ sym (+MaxDistrℚ (L - x) 0 x))
       (ℚ!!)
  ∙∙ sym (+MinDistrℚ (max (L - x) 0) (L' - x) x)
  ∙∙ +Comm (min (max (L - x) 0) (L' - x)) x



clampDiff : ∀ L L' x y → x ≤ y →
    clamp L L' y - clamp L L' x ≤ y - x
clampDiff L L' x y z =
  (subst2 _≤_
     ((sym ℚ!!) ∙
       cong₂ _-_ (sym $ clampDelta L L' y)
                   (sym $ clampDelta L L' x))
     (+IdR (y - x))
     (≤-o+ ((a' - a)) 0 (y - x)
      (subst (_≤ 0) (-[x-y]≡y-x a a')
       $ minus-≤ 0 (a - a') (-≤ a' a zz'))  ))

 where

 a = clamp (L - x) (L' - x) 0
 a' = clamp (L - y) (L' - y) 0
 zz' : a' ≤ a
 zz' = ≤MonotoneMin _ _ _ _
          (≤MonotoneMax _ _ _ _
           (≤-o+ (- y) (- x) L (minus-≤ x y z)) (isRefl≤ 0)
            ) (≤-o+ (- y) (- x) L' $ minus-≤ x y z)


minDiff : ∀ L' x y → x ≤ y →
    min y L' - min x L' ≤ y - x
minDiff L' x y x≤y =
 subst (_≤ (y - x))
    (cong₂ _-_
     (cong (flip min L') (≤→max x y x≤y ))
     (cong (flip min L') (maxIdem x)))
     (clampDiff x L' x y x≤y)


clampDist' : ∀ L L' x y → x ≤ y →
    abs (clamp L L' y - clamp L L' x) ≤ abs (y - x)
clampDist' L L' x y z =
 subst2 _≤_
  (sym (absNonNeg (clamp L L' y - clamp L L' x)
          (-≤ (clamp L L' x) (clamp L L' y)  (≤MonotoneClamp L L' x y z))))
  (sym (absNonNeg (y - x) (-≤ x y z)))
  (clampDiff L L' x y z)

clampDist : ∀ L L' x y →
    abs (clamp L L' y - clamp L L' x) ≤ abs (y - x)
clampDist L L' =
 elimBy≤ (λ x y → subst2 _≤_ (absComm- (clamp L L' y) (clamp L L' x))
    (absComm- y x)) (clampDist' L L')

maxDist : ∀ M x y →
    abs (max M y - max M x) ≤ abs (y - x)
maxDist M x y =
  subst2 {x = min (max M y) (max M (max x y))}
          {(max M y)}
    {z = min (max M x) (max M (max x y))} {(max M x)}
    (λ a b → abs (a - b) ≤ abs (y - x))
    (≤→min _ _ (subst (max M y ≤_)
      (sym (maxAssoc M y x) ∙ cong (max M) (maxComm y x))
      (≤max _ x)))
    (≤→min _ _
      ((subst (max M x ≤_)
      (sym (maxAssoc M x y))
      (≤max _ y))))
    (clampDist M (max M (max x y)) x y)


≤→<⊎≡ : ∀ p q → p ≤ q → (p ≡ q) ⊎ (p < q)
≤→<⊎≡ p q x with p ≟ q
... | lt x₁ = inr x₁
... | eq x₁ = inl x₁
... | gt x₁ = ⊥.rec $ ≤→≯ p q x x₁


getPosRatio : (L₁ L₂ : ℚ₊) → (fst ((invℚ₊ L₁) ℚ₊·  L₂) ≤ 1)
                           ⊎ (fst ((invℚ₊ L₂) ℚ₊·  L₁) ≤ 1)
getPosRatio L₁ L₂ =
  elimBy≤ {A = λ (L₁ L₂ : ℚ) → (<L₁ : 0< L₁) → (<L₂ : 0< L₂)
                      →  (((fst (invℚ₊ (L₁ , <L₁) ℚ₊·  (L₂ , <L₂))) ≤ 1)
                           ⊎ ((fst ((invℚ₊ (L₂ , <L₂)) ℚ₊·
                            (L₁ , <L₁))) ≤ 1))}
    (λ x y x₁ <L₁ <L₂ →
      Iso.fun (⊎.⊎-swap-Iso) (x₁ <L₂ <L₁) )
     (λ L₁ L₂ x₁ <L₁ <L₂ →
             inr (
               subst (fst (invℚ₊ (L₂ , <L₂)) · L₁ ≤_)
                  (invℚ₊[x]·x (L₂ , <L₂))
                  (≤-o· L₁ L₂ (fst (invℚ₊ (L₂ , <L₂)))
                    (0≤ℚ₊ (invℚ₊ (L₂ , <L₂))) x₁)))
     (fst L₁) (fst L₂) (snd L₁) (snd L₂)


·MaxDistrℚ : ∀ x y z → 0< z → (max x y) · z ≡ max (x · z) (y · z)
·MaxDistrℚ = SQ.elimProp3 (λ _ _ _ → isPropΠ λ _ → isSetℚ _ _)
  www

 where
 www : (a b c : ℤ.ℤ × ℕ₊₁) →
         0< _//_.[ c ] →
         max _//_.[ a ] _//_.[ b ] · _//_.[ c ] ≡
         max (_//_.[ a ] · _//_.[ c ]) (_//_.[ b ] · _//_.[ c ])
 www (a , a') (b , b') (c@(pos (suc n)) , c') (inj (ℤ.pos<pos x)) = eq/ _ _ wwww
  where


   wwww : ℤ.max (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') ℤ.· c
            ℤ.· ℕ₊₁→ℤ (a' ·₊₁ c' ·₊₁ (b' ·₊₁ c'))
          ≡ ℤ.max ((a ℤ.· c) ℤ.· ℕ₊₁→ℤ (b' ·₊₁ c'))
                    ((b ℤ.· c) ℤ.· ℕ₊₁→ℤ (a' ·₊₁ c'))  ℤ.·
              ℕ₊₁→ℤ (a' ·₊₁ b' ·₊₁ c')
   wwww =
    cong (ℤ.max (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') ℤ.· pos (suc n) ℤ.·_)
      (cong (λ ac → ℕ₊₁→ℤ (ac ·₊₁ (b' ·₊₁ c'))) (·₊₁-comm a'  c')
       ∙∙ cong ℕ₊₁→ℤ (sym (·₊₁-assoc c' a' (b' ·₊₁ c'))) ∙∙
         ℤ.pos·pos (suc (c' .ℕ₊₁.n)) (ℕ₊₁→ℕ (a' ·₊₁ (b' ·₊₁ c'))))
      ∙∙ ℤ.·Assoc (ℤ.max (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') ℤ.· pos (suc n)) (pos (suc (c' .ℕ₊₁.n))) (pos (ℕ₊₁→ℕ (a' ·₊₁ (b' ·₊₁ c')))) ∙∙
    cong₂ (ℤ._·_)
       (cong (ℤ._· (pos (ℕ₊₁→ℕ c')))
         (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') (suc n))
         ∙ ℤ.·DistPosLMax
              ((a ℤ.· ℕ₊₁→ℤ b') ℤ.· pos (suc n))
              ((b ℤ.· ℕ₊₁→ℤ a') ℤ.· pos (suc n)) (ℕ₊₁→ℕ c')
          ∙ cong₂ ℤ.max ℤ! ℤ!)
           (cong ℕ₊₁→ℤ (·₊₁-assoc a' b' c'))


·MaxDistrℚ' : ∀ x y z → 0 ≤ z → (max x y) · z ≡ max (x · z) (y · z)
·MaxDistrℚ' x y z =
  ⊎.rec (λ p → cong ((max x y) ·_) (sym p) ∙
        ·AnnihilR (max x y)  ∙ cong₂ max (sym (·AnnihilR x) ∙ cong (x ·_) p)
            (sym (·AnnihilR y) ∙ cong (y ·_) p))
    (·MaxDistrℚ x y z ∘ <→0< z) ∘ (≤→≡⊎< 0 z)

≤Monotone·-onNonNeg : ∀ x x' y y' →
  x ≤ x' →
  y ≤ y' →
  0 ≤ x →
  0 ≤ y →
   x · y ≤ x' · y'
≤Monotone·-onNonNeg x x' y y' x≤x' y≤y' 0≤x 0≤y =
  isTrans≤ _ _ _ (≤-·o x x' y 0≤y x≤x')
   (≤-o· y y' x' (isTrans≤ 0 _ _ 0≤x x≤x') y≤y')

<Monotone·-onPos : ∀ x x' y y' →
  x < x' →
  y < y' →
  0 ≤ x →
  0 ≤ y →
   x · y < x' · y'
<Monotone·-onPos x x' y y' x₁ x₂ x₃ x₄ =
   let zz = 0<-m·n (x' - x) (y' - y) (-< x x' x₁) (-< y y' x₂)
   in subst2 _<_ (+IdL _ ∙ +IdR _)
          (ℚ!!)
        (<≤Monotone+ 0 ((x' - x) · (y' - y)) (x · y + 0)
             (x' · y + ((x · (y' - y)))) zz
               (≤Monotone+ (x · y) (x' · y) 0  (x · (y' - y))
                (≤-·o x x' y x₄ (<Weaken≤ x x' x₁))
                (subst (_≤ x · (y' - y))
                  (·AnnihilL (y' - y)) $ ≤-·o 0 x (y' - y)
                  (<Weaken≤ 0 (y' - y) (-< y y' x₂) ) x₃)))


≤<Monotone·-onPos : ∀ x x' y y' →
  x ≤ x' →
  y < y' →
  0 < x →
  0 ≤ y →
   x · y < x' · y'
≤<Monotone·-onPos x x' y y' x≤x' y<y' 0<x 0≤y =
  isTrans≤< _ _ _
    (≤-·o x x' y 0≤y x≤x')
    (<-o· y y' x' (isTrans<≤ 0 _ _ 0<x x≤x') y<y')

invℚ : ∀ q → 0 # q → ℚ
invℚ q p = sign q · fst (invℚ₊ (0#→ℚ₊ q p))

invℚ₊≡invℚ : ∀ q p → invℚ (fst q) p ≡ fst (invℚ₊ q)
invℚ₊≡invℚ q p = cong₂ _·_ (fst (<→sign (fst q)) (0<ℚ₊ q)
    ) (cong (fst ∘ invℚ₊) (ℚ₊≡ (sym (abs'≡abs (fst q)) ∙
     absPos (fst q) ((0<ℚ₊ q))))) ∙ ·IdL (fst (invℚ₊ q))

fromNat-invℚ' : ∀ n p → invℚ [ ℕ₊₁→ℤ n / (1+ zero) ] p ≡ [ (pos 1) / n ]
fromNat-invℚ' n p = eq/ _ _ ℤ!


fromNat-invℚ : ∀ n p → invℚ [ pos (suc n) / (1+ zero) ] p ≡ [ (pos 1) / 1+ n ]
fromNat-invℚ n p = fromNat-invℚ' _ p


invℚ-pos : ∀ x y → 0 < x → 0 < invℚ x y
invℚ-pos x y z =
  subst (0 <_)
    (sym (invℚ₊≡invℚ (x , <→0< _ z) y))
      (0<ℚ₊ (invℚ₊ (x , <→0< _ z)))


0#invℚ : ∀ q 0#q → 0 # (invℚ q 0#q)
0#invℚ q 0#q = ·Monotone0# _ _  (fst (0#sign q) 0#q)
  (inl (0<ℚ₊ (invℚ₊ (0#→ℚ₊ q 0#q))))




·DistInvℚ : ∀ x y 0#x 0#y 0#xy →
  (invℚ x 0#x) · (invℚ y 0#y) ≡ invℚ (x · y) 0#xy
·DistInvℚ x y 0#x 0#y 0#xy =
   (sym (·Assoc (sign x) (fst (invℚ₊ (0#→ℚ₊ x 0#x))) (sign y · fst (invℚ₊ (0#→ℚ₊ y 0#y)))) ∙
    cong ((sign x) ·_)
      (·Assoc (fst (invℚ₊ (0#→ℚ₊ x 0#x))) (sign y) (fst (invℚ₊ (0#→ℚ₊ y 0#y)))
       ∙∙ cong (_· fst (invℚ₊ (0#→ℚ₊ y 0#y)))
         (·Comm (fst (invℚ₊ (0#→ℚ₊ x 0#x))) (sign y)) ∙∙
       sym (·Assoc (sign y) (fst (invℚ₊ (0#→ℚ₊ x 0#x))) (fst (invℚ₊ (0#→ℚ₊ y 0#y)))))
   ∙ (·Assoc (sign x) (sign y) (fst (invℚ₊ (0#→ℚ₊ x 0#x)) · fst (invℚ₊ (0#→ℚ₊ y 0#y)))))
   ∙
   cong₂ _·_
     (sign·sign x y)
     (cong fst (invℚ₊Dist· (0#→ℚ₊ x 0#x) (0#→ℚ₊ y 0#y))
       ∙ cong (fst ∘ invℚ₊) (ℚ₊≡ (abs'·abs' x y)) )

invℚ-sign : ∀ q 0#q → sign q ≡ (invℚ (sign q) 0#q)
invℚ-sign q =
  (λ {a} → ⊎.rec (λ p → p ∙ cong  (uncurry invℚ)
     (Σ≡Prop  (λ x → isProp# 0 x )
       {u = 1 , inl (𝟚.toWitness {Q = <Dec 0 1} tt)} {v = sign q , a} (sym p) )
     )
     ((λ p → p ∙ cong (uncurry invℚ)
    (Σ≡Prop  (λ x → isProp# 0 x)
     {u = -1 , inr (𝟚.toWitness {Q = <Dec -1 0} tt)} {v = sign q , a} (sym p) ))))
 ∘ ⊎.map (fst (fst (<≃sign q)))
   (fst (snd (snd (<≃sign q)))) ∘ invEq (0#sign q)


invℚInvol : ∀ q 0#q 0#invQ → invℚ (invℚ q 0#q) 0#invQ ≡ q
invℚInvol q 0#q 0#invQ =
  sym (·DistInvℚ (sign q) _ (fst (0#sign q) 0#q)
    (inl (0<ℚ₊ (invℚ₊ ((0#→ℚ₊ q 0#q)) )))
    0#invQ )
    ∙∙ cong₂ _·_ (sym (invℚ-sign q (fst (0#sign q) 0#q)))
     ((invℚ₊≡invℚ (invℚ₊ (0#→ℚ₊ q 0#q)) (inl (0<ℚ₊ (invℚ₊ (0#→ℚ₊ q 0#q)))) ∙ invℚ₊-invol (0#→ℚ₊ q 0#q)) ∙  sym (abs'≡abs q))  ∙∙
     (·Comm (sign q) (abs q) ∙ (sign·abs q))


_／ℚ[_,_] : ℚ → ∀ r → 0 # r  → ℚ
q ／ℚ[ r , 0＃r ] = q · (invℚ r 0＃r)


ℚ-y/y : ∀ r → (0＃r : 0 # r) → (r ／ℚ[ r , 0＃r ]) ≡ 1
ℚ-y/y r y = cong (_· (invℚ r y)) (sym (sign·abs r))
  ∙ sym (·Assoc (abs r) (sign r) (sign r · fst (invℚ₊ (0#→ℚ₊ r y))))
  ∙ cong {x = sign r · (sign r · fst (invℚ₊ (0#→ℚ₊ r y)))} {y = fst (invℚ₊ (0#→ℚ₊ r y))} (abs r ·_) (·Assoc (sign r) (sign r) (fst (invℚ₊ (0#→ℚ₊ r y))) ∙∙
    cong (_· fst (invℚ₊ (0#→ℚ₊ r y))) (signX·signX r y) ∙∙
      ·IdL (fst (invℚ₊ (0#→ℚ₊ r y))))
  ∙ cong (_· fst (invℚ₊ (0#→ℚ₊ r y))) (abs'≡abs r)
   ∙ x·invℚ₊[x] (0#→ℚ₊ r y)

ℚ-[x·y]/y : ∀ x r → (0＃r : 0 # r) → ((x · r) ／ℚ[ r , 0＃r ]) ≡ x
ℚ-[x·y]/y x r 0#r = sym (·Assoc x r (invℚ r 0#r)) ∙∙
  cong (x ·_) (ℚ-y/y r 0#r) ∙∙ ·IdR x

ℚ-[x/y]·y : ∀ x r → (0＃r : 0 # r) → ((x ／ℚ[ r , 0＃r ]) · r) ≡ x
ℚ-[x/y]·y x r 0#r = sym (·Assoc x (invℚ r 0#r) r) ∙∙
  cong (x ·_) (·Comm (invℚ r 0#r) r ∙ ℚ-y/y r 0#r) ∙∙ ·IdR x


ℚ-x·y≡z→x≡z/y : ∀ x q r → (0＃r : 0 # r)
               → (x · r) ≡ q
               → x ≡ q ／ℚ[ r , 0＃r ]
ℚ-x·y≡z→x≡z/y x q r 0＃r p =
    sym (ℚ-[x·y]/y x r 0＃r ) ∙ cong (_／ℚ[ r , 0＃r ]) p

x≤z/y→x·y≤z : ∀ x q r 0#r → (0<r : 0 < r)
               → x ≤ q ／ℚ[ r , 0#r  ]
               → (x · r) ≤ q
x≤z/y→x·y≤z x q r 0＃r 0<r  p =
   subst ((x · r) ≤_) (ℚ-[x/y]·y q r 0＃r) (≤-·o _ _ r (<Weaken≤ 0 r 0<r ) p)


x/y≤z→x≤z·y : ∀ x q r 0#r → (0<r : 0 < r)
               → x ／ℚ[ r , 0#r  ] ≤ q
               → x ≤ q · r
x/y≤z→x≤z·y x q r 0＃r 0<r  p =
   subst (_≤ (q · r)) (ℚ-[x/y]·y x r 0＃r) (≤-·o _ _ r (<Weaken≤ 0 r 0<r ) p)

x·invℚ₊y≤z→x≤y·z : ∀ x q r
               → x · fst (invℚ₊ r) ≤ q
               → x ≤ (fst r) · q
x·invℚ₊y≤z→x≤y·z x q r  p =
   subst (_≤ ((fst r) · q)) (cong ((fst r) ·_) (·Comm x (fst (invℚ₊ r))) ∙ y·[x/y] r x)
      (≤-o· _ _ (fst r) (0≤ℚ₊ r ) p)


x·invℚ₊y<z→x<y·z : ∀ x q r
               → x · fst (invℚ₊ r) < q
               → x < (fst r) · q
x·invℚ₊y<z→x<y·z x q r  p =
   subst (_< ((fst r) · q)) (cong ((fst r) ·_) (·Comm x (fst (invℚ₊ r))) ∙ y·[x/y] r x)
      (<-o· _ _ (fst r) (0<ℚ₊ r ) p)


y·x<z→x<z·invℚ₊y : ∀ x z r
               → (fst r) · x < z
               → x < z · fst (invℚ₊ r)
y·x<z→x<z·invℚ₊y x z r p =
   subst (_< z · fst (invℚ₊ r))
    (·Comm (fst r · x) (fst (invℚ₊ r)) ∙ [y·x]/y r _)
    (<-·o _ _ (fst (invℚ₊ r)) (0<ℚ₊ (invℚ₊ r) ) p)

x≤y·z→x·invℚ₊y≤z : ∀ x q r
               → x ≤ (fst r) · q
               → x · fst (invℚ₊ r) ≤ q

x≤y·z→x·invℚ₊y≤z x q r  p =
  subst (x · fst (invℚ₊ r) ≤_)
   (·Comm (fst r · q) (fst (invℚ₊ r)) ∙ [y·x]/y r _)
   (≤-·o x _ (fst (invℚ₊ r)) ((0≤ℚ₊ ( invℚ₊ r) )) p)


x<y·z→x·invℚ₊y<z : ∀ x q r
               → x < (fst r) · q
               → x · fst (invℚ₊ r) < q

x<y·z→x·invℚ₊y<z x q r  p =
  subst (x · fst (invℚ₊ r) <_)
   (·Comm (fst r · q) (fst (invℚ₊ r)) ∙ [y·x]/y r _)
   (<-·o x _ (fst (invℚ₊ r)) ((0<ℚ₊ ( invℚ₊ r) )) p)




ℚ-x/y<z→x/z<y : ∀ x q r  → (0<x : 0 < x) → (0<q : 0 < q) → (0<r : 0 < r)
               → (x ／ℚ[ r , inl 0<r ]) < q
               → (x ／ℚ[ q , inl 0<q ]) < r
ℚ-x/y<z→x/z<y x q r 0<x 0<q 0<r p =
 subst2 _<_ (sym (·Assoc x (invℚ r (inl 0<r)) (r · invℚ q (inl 0<q)))
   ∙  cong (x ·_) ((·Comm (invℚ r (inl 0<r)) (r · invℚ q (inl 0<q))) ∙
     cong (_· invℚ r (inl 0<r)) (·Comm r (invℚ q (inl 0<q))) ∙
      ℚ-[x·y]/y _ r (inl 0<r) ) )
   ((·Comm q (r ／ℚ[ q , inl 0<q ])) ∙ ℚ-[x/y]·y _ q (inl 0<q))
   (<-·o (x ／ℚ[ r , (inl 0<r) ]) q (r ／ℚ[ q , (inl 0<q) ])
     (0<-m·n _ _ 0<r (invℚ-pos q (inl 0<q)  0<q)) p)

invℚ≤invℚ : ∀ (p q : ℚ₊) → fst q ≤ fst p → fst (invℚ₊ p) ≤ fst (invℚ₊ q)
invℚ≤invℚ p q x =
 subst2 _≤_
   (cong ((fst q) ·_) (·Comm (fst (invℚ₊ p)) (fst (invℚ₊ q)) ) ∙
    (y·[x/y] q (fst (invℚ₊ p)))) (y·[x/y] p (fst (invℚ₊ q)))
    (≤-·o _ _ (fst ((invℚ₊ p) ℚ₊· (invℚ₊ q)))
     (0≤ℚ₊ ((invℚ₊ p) ℚ₊· (invℚ₊ q))) x)

maxWithPos : ℚ₊ → ℚ → ℚ₊
maxWithPos ε q .fst = max (fst ε) q
maxWithPos ε q .snd = <→0< (max (fst ε) q)
 (isTrans<≤ 0 (fst ε) _ (0<ℚ₊ ε) (≤max (fst ε) q))


1/p+1/q : (p q : ℚ₊) → fst (invℚ₊ p) - fst (invℚ₊ q) ≡
                       fst (invℚ₊ (p ℚ₊· q))
                        · (fst q - fst p)
1/p+1/q _ _ = ℚ!

invℚ₊≤invℚ₊ : ∀ x y
      → fst y ≤ fst x
      → fst (invℚ₊ x) ≤ fst (invℚ₊ y)
invℚ₊≤invℚ₊ x y p =
  subst2 _≤_
    ℚ! ℚ!
     (≤Monotone·-onNonNeg (fst (invℚ₊ x) · fst (invℚ₊ y)) (fst (invℚ₊ y) · fst (invℚ₊ x)) (fst y) (fst x)
        (≡Weaken≤ _ _ (·Comm (fst (invℚ₊ x)) (fst (invℚ₊ y)) ))
        p
        ((0≤ℚ₊ ((invℚ₊ x) ℚ₊· (invℚ₊ y))))
        ((0≤ℚ₊ y)))




_ℚ^ⁿ_ : ℚ → ℕ → ℚ
x ℚ^ⁿ zero = 1
x ℚ^ⁿ suc n = (x ℚ^ⁿ n) · x

0<ℚ^ⁿ : ∀ q (0<q : 0< q) n → 0< (q ℚ^ⁿ n)
0<ℚ^ⁿ q 0<q zero = inj (ℤ.pos<pos tt)
0<ℚ^ⁿ q 0<q (suc n) = snd (((q ℚ^ⁿ n) , 0<ℚ^ⁿ q 0<q n) ℚ₊· (q , 0<q))

0≤ℚ^ⁿ : ∀ q (0≤q : 0 ≤ q) n → 0 ≤ (q ℚ^ⁿ n)
0≤ℚ^ⁿ q 0≤q zero = 𝟚.toWitness {Q = ≤Dec 0 1} tt
0≤ℚ^ⁿ q 0≤q (suc n) = ≤Monotone·-onNonNeg
 0 _ 0 _
  (0≤ℚ^ⁿ q 0≤q n)
   0≤q (isRefl≤ 0) (isRefl≤ 0)


x^ⁿ≤1 : ∀ x n → 0 ≤ x → x ≤ 1 →  (x ℚ^ⁿ n) ≤ 1
x^ⁿ≤1 x zero 0≤x x≤1 = isRefl≤ 1
x^ⁿ≤1 x (suc n) 0≤x x≤1 =
 ≤Monotone·-onNonNeg _ 1 _ 1
   (x^ⁿ≤1 x n 0≤x x≤1) x≤1 (0≤ℚ^ⁿ x 0≤x n) 0≤x

1≤x^ⁿ : ∀ x n → 1 ≤ x →  1 ≤ (x ℚ^ⁿ n)
1≤x^ⁿ x zero 1≤x = isRefl≤ 1
1≤x^ⁿ x (suc n) 1≤x =
 ≤Monotone·-onNonNeg 1 _ 1 _
   (1≤x^ⁿ x n 1≤x) 1≤x (decℚ≤? {0} {1})
     (decℚ≤? {0} {1})

1<x^ⁿ : ∀ x n → 1 < x →  1 < (x ℚ^ⁿ (suc n))
1<x^ⁿ x zero 1<x = subst (1 <_) (sym (·IdL _)) 1<x
1<x^ⁿ x (suc n) 1<x =
 <Monotone·-onPos 1 _ 1 _
   (1<x^ⁿ x n 1<x) 1<x (decℚ≤? {0} {1})
     (decℚ≤? {0} {1})


·-ℚ^ⁿ : ∀ n m x → (x ℚ^ⁿ n) · (x ℚ^ⁿ m) ≡ (x ℚ^ⁿ (n ℕ.+ m))
·-ℚ^ⁿ zero m x = ·IdL _
·-ℚ^ⁿ (suc n) m x = (sym (·Assoc (x ℚ^ⁿ n) x (x ℚ^ⁿ m))
   ∙ cong ((x ℚ^ⁿ n) ·_) (·Comm x (x ℚ^ⁿ m)))
  ∙∙ ·Assoc (x ℚ^ⁿ n) (x ℚ^ⁿ m) x
  ∙∙ cong (_· x) (·-ℚ^ⁿ n m x)

_ℚ₊^ⁿ_ : ℚ₊ → ℕ → ℚ₊
(q , 0<q) ℚ₊^ⁿ n = (q ℚ^ⁿ n) , 0<ℚ^ⁿ q 0<q n


fromNat-^ : ∀ m n → ((fromNat m) ℚ^ⁿ n ) ≡ fromNat (m ℕ.^ n)
fromNat-^ m zero = refl
fromNat-^ m (suc n) =
 cong (_· (fromNat m)) (fromNat-^ m n) ∙
   (ℕ·→ℚ· (m ℕ.^ n) m) ∙ cong [_/ 1 ] (cong ℤ.pos (ℕ.·-comm (m ℕ.^ n) m))

invℚ₊-ℚ^ⁿ : ∀ q n → fst (invℚ₊ (q ℚ₊^ⁿ n)) ≡ (fst (invℚ₊ q)) ℚ^ⁿ n
invℚ₊-ℚ^ⁿ q zero = refl
invℚ₊-ℚ^ⁿ q (suc n) =
  cong fst (sym (invℚ₊Dist· ((q .fst ℚ^ⁿ n) , 0<ℚ^ⁿ (q .fst) (q .snd) n) q))
    ∙ cong (fst ∘ (_ℚ₊· (invℚ₊ q)))
     (ℚ₊≡ {x = (invℚ₊ (q ℚ₊^ⁿ n))}
      {y = (fst (invℚ₊ q) ℚ^ⁿ n) , snd ((invℚ₊ q) ℚ₊^ⁿ n)} (invℚ₊-ℚ^ⁿ q n))


invℚ₊-<-invℚ₊ : ∀ q r → ((fst q) < (fst r))
             ≃ (fst (invℚ₊ r) < fst (invℚ₊ q))
invℚ₊-<-invℚ₊ (q , 0<q) (r , 0<r) = ElimProp2.go w q r 0<q 0<r
 where
 w : ElimProp2 λ q r → ∀ 0<q 0<r → (q < r) ≃
         (fst (invℚ₊ (r , 0<r)) < fst (invℚ₊ (q , 0<q)))
 w .ElimProp2.isPropB _ _ =
   isPropΠ2 λ _ _ → isOfHLevel≃ 1 (isProp< _ _) (isProp< _ _)
 w .ElimProp2.f (ℤ.pos (suc n) , 1+ m) (ℤ.pos (suc n') , 1+ m') (inj (ℤ.pos<pos _)) (inj (ℤ.pos<pos _)) =
  let w : ∀ (n n' : ℕ₊₁) →
                     ([ ℕ₊₁→ℤ n , (1+ m) ] < [ ℕ₊₁→ℤ n' , (1+ m') ]) ≃
            (fst (invℚ₊ ([ ℕ₊₁→ℤ n' , (1+ m') ] , inj (ℤ.pos<pos tt))) <
             fst (invℚ₊ ([ ℕ₊₁→ℤ n , (1+ m) ] , inj (ℤ.pos<pos tt))))
      w n n' = propBiimpl→Equiv (isProp< _ _)  (isProp< _ _)
                      (inj ∘S subst2 {x = (ℕ₊₁→ℤ n) ℤ.· ℕ₊₁→ℤ (1+ m')} {y = ℕ₊₁→ℤ (1+ m') ℤ.·
                       ℕ₊₁→ℤ (fst (ℤ.0<→ℕ₊₁ (ℕ₊₁→ℤ n) (ℤ.pos<pos tt)))} {z = ℕ₊₁→ℤ n' ℤ.· ℕ₊₁→ℤ (1+ m)}
                        {w = ℕ₊₁→ℤ (1+ m) ℤ.· ℕ₊₁→ℤ (fst (ℤ.0<→ℕ₊₁ (ℕ₊₁→ℤ n') (ℤ.pos<pos tt)))} ℤ._<_ ℤ! ℤ! ∘S _<_.prf)
                      (inj ∘S subst2 {x = ℕ₊₁→ℤ (1+ m') ℤ.· ℕ₊₁→ℤ (fst (ℤ.0<→ℕ₊₁ (ℕ₊₁→ℤ n) (ℤ.pos<pos tt)))}
                       {y = (ℕ₊₁→ℤ n) ℤ.· ℕ₊₁→ℤ (1+ m')} {z = ℕ₊₁→ℤ (1+ m) ℤ.·
                        ℕ₊₁→ℤ (fst (ℤ.0<→ℕ₊₁ (ℕ₊₁→ℤ n') (ℤ.pos<pos tt)))}
                         {w = (ℕ₊₁→ℤ n') ℤ.· ℕ₊₁→ℤ (1+ m)} ℤ._<_ ℤ! ℤ! ∘S _<_.prf)
  in w _ _
  
invℚ₊-≤-invℚ₊ : ∀ q r → ((fst q) ≤ (fst r))
             ≃ (fst (invℚ₊ r) ≤ fst (invℚ₊ q))
invℚ₊-≤-invℚ₊ q r =
    (≤≃≡⊎< _ _)
   ∙ₑ ⊎.⊎-equiv (Σ≡PropEquiv (snd ∘ 0<ₚ_) {u = q} {v = r}
    ∙ₑ congEquiv equivInvℚ₊ ∙ₑ
     invEquiv (Σ≡PropEquiv (snd ∘ 0<ₚ_) {u = invℚ₊ r} {v = invℚ₊ q}
        ∙ₑ isoToEquiv symIso )) (invℚ₊-<-invℚ₊ q r)
   ∙ₑ (invEquiv (≤≃≡⊎< _ _))


lowerBoundℕ⁻¹ : ∀ (q : ℚ₊) → Σ[ k ∈ ℕ₊₁ ] ([ 1 , k ] < fst q)
lowerBoundℕ⁻¹ q =
 map-snd (subst ([ 1 , _ ] <_) (cong (fst ∘ invℚ₊)
   (ℚ₊≡ {abs (fst (invℚ₊ q)) ,
     (subst (0<_) (sym (absPos _ (0<ℚ₊ (invℚ₊ q))))
      (snd (invℚ₊ q)))}
    (absPos _ (0<ℚ₊ (invℚ₊ q)))) ∙ invℚ₊-invol q)  ∘S fst (invℚ₊-<-invℚ₊ _
      ([ ℕ₊₁→ℤ _ , 1 ] , inj (ℤ.pos<pos tt)))) (boundℕ (fst (invℚ₊ q)))

1/n<sucK : ∀ m n → ℚ.[ 1 / (suc₊₁ m) ] < ([ ℚ.ℕ₊₁→ℤ n / 1 ])
1/n<sucK m n = inj (ℤ.pos<pos tt)


0<ℕ₊₁ : ∀ n m → 0 < ([ ℚ.ℕ₊₁→ℤ n / m ])
0<ℕ₊₁ n m = 0<→< ([ ℚ.ℕ₊₁→ℤ n / m ]) (inj (ℤ.pos<pos tt))


<Δ : ∀ n → [ 1 / 4 ] < ([ pos (suc n) / 1 ])
<Δ n = 1/n<sucK 3 (1+ n)


clam∈ℚintervalℙ : ∀ a b → (a ≤ b) → ∀ x → clamp a b x ∈ ℚintervalℙ a b
clam∈ℚintervalℙ a b a≤b x = ≤clamp _ _ _ a≤b , (clamp≤ a _ x)

∈ℚintervalℙ→clam≡ : ∀ a b → ∀ x →
    x ∈ ℚintervalℙ a b → x ≡ clamp a b x
∈ℚintervalℙ→clam≡ a b x = sym ∘ uncurry (inClamps a b x)


clamp-contained-agree : ∀ (a b a' b' x : ℚ)
  → a ≤ a'
  → b' ≤ b
  → x ∈ ℚintervalℙ a' b'
  → clamp a b x ≡ clamp a' b' x
clamp-contained-agree a b a' b' x a≤a' b'≤b x∈ =
  sym (∈ℚintervalℙ→clam≡ a b x
   ((isTrans≤ _ _ _ a≤a' (fst x∈)) ,
    (isTrans≤ _ _ _ (snd x∈) b'≤b))) ∙ ∈ℚintervalℙ→clam≡ a' b' x x∈
