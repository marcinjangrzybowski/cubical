{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --safe #-}
module Cubical.Data.Rationals.MoreOrder where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Logic using (_⊔′_; ⇔toPath)

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Int.Base as ℤ using (ℤ)
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Int.Properties as ℤ using ()
open import Cubical.Data.Int.Order as ℤ using ()
open import Cubical.Data.Int.Divisibility as ℤ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr; isProp⊎)

open import Cubical.HITs.PropositionalTruncation as ∥₁ using (isPropPropTrunc; ∣_∣₁)
open import Cubical.HITs.SetQuotients

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.Data.Rationals.Order

decℚ? : ∀ {x y} → {𝟚.True (discreteℚ x y)} →  (x ≡ y) 
decℚ? {_} {_} {p} = 𝟚.toWitness p

decℚ<? : ∀ {x y} → {𝟚.True (<Dec x y)} →  (x < y) 
decℚ<? {_} {_} {p} = 𝟚.toWitness p

decℚ≤? : ∀ {x y} → {𝟚.True (≤Dec x y)} →  (x ≤ y) 
decℚ≤? {_} {_} {p} = 𝟚.toWitness p


bound∃ : ∀ q → ∃[ k ∈ ℕ₊₁ ] (abs q < ([ ℕ₊₁→ℤ k , 1 ]))  
bound∃ = ElimProp.go w
 where
 w : ElimProp _
 w .ElimProp.isPropB q = ∥₁.squash₁
 w .ElimProp.f q@(p , (1+ n)) =
  let z' : ℤ.max p (ℤ.- p) ℤ.< (1 ℤ.+ ℤ.pos (ℤ.abs p)) ℤ.· ℤ.pos (suc n)
      z' = subst2 ℤ._<_ (sym (ℤ.pos0+ (ℤ.pos (ℤ.abs p))) ∙ ℤ.abs-max p)
               (sym (ℤ.·DistL+ 1 (ℤ.pos (ℤ.abs p)) (ℤ.pos (suc n))))
              (ℤ.<-+-≤ {0} {(ℤ.pos (suc n))} {ℤ.pos (ℤ.abs p)}
                  {ℤ.pos (ℤ.abs p) ℤ.· ℤ.pos (suc n)}
                   (ℤ.suc-≤-suc (ℤ.zero-≤pos {n}))
                    ((subst ((ℤ.pos (ℤ.abs p)) ℤ.≤_) (ℤ.·Comm (ℤ.pos (suc n))
                        (ℤ.pos (ℤ.abs p))) $
                      ℤ.≤-·o {1} {(ℤ.pos (suc n))} {( (ℤ.abs p))}
                        (ℤ.suc-≤-suc $ ℤ.zero-≤pos {n}))))
      z : ℤ.max (p ℤ.· (ℕ₊₁→ℤ (1 ·₊₁ (1+ n)))) (ℤ.- p ℤ.· ℤ.pos (suc n))
            ℤ.· 1 ℤ.<
           (1 ℤ.+ (ℤ.pos (ℤ.abs p))) ℤ.· (ℕ₊₁→ℤ ((1+ n) ·₊₁ (1 ·₊₁ (1+ n)))) 
      z = subst2 ℤ._<_
              ((ℤ.·DistPosLMax (p) (ℤ.- p) (suc n)
                ∙ congS (λ xx →
                      ℤ.max (p ℤ.· ℤ.pos (suc xx) )
                         (ℤ.- p ℤ.· ℤ.pos (suc n)))
                           (sym (ℕ.+-zero n))
                           ) ∙
                 sym (ℤ.·IdR (ℤ.max (p ℤ.· (ℕ₊₁→ℤ (1 ·₊₁ (1+ n))))
                    (ℤ.- p ℤ.· ℤ.pos (suc n)))))
              (sym (ℤ.·Assoc (1 ℤ.+ (ℤ.pos (ℤ.abs p)))
                (ℤ.pos (suc n)) (ℤ.pos (suc n)))
               ∙ cong ((1 ℤ.+ (ℤ.pos (ℤ.abs p))) ℤ.·_)
                  (sym (ℤ.pos·pos ((suc n)) ((suc n)))
                    ∙ cong ℤ.pos
                      (sym (ℕ₊₁→ℕ-·₊₁-comm (1+ n) (1+ n)) ∙
                       cong ℕ₊₁→ℕ
                        (cong ((1+ n) ·₊₁_)
                          (sym (·₊₁-identityˡ (1+ n))))))
                 ) (ℤ.<-·o {(ℤ.max (p) (ℤ.- p))}
                   {(((1 ℤ.+ (ℤ.pos (ℤ.abs p))))) ℤ.· ℤ.pos (suc n)}
                     {n} z')
      pp : 1 ℤ.+ (ℤ.pos (ℤ.abs p)) ≡ ℕ₊₁→ℤ (1+ ℤ.abs p)               
      pp = sym (ℤ.pos+ 1 (ℤ.abs p))    
  in ∣ 1+ (ℤ.abs p) , subst (λ k → abs [ q ] < ([ k , 1 ])) pp z ∣₁ 

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
       _ ((cong (ℤ.-_) (ℤ.pos·pos (suc n) _)
        ∙ sym (ℤ.negsuc·pos n _)) ∙∙ (sym x) ∙∙ sym (ℤ.pos·pos n₁ _) ))
 w .Rec.f∼ (ℤ.negsuc n , snd₁) (ℤ.pos n₁ , snd₂) x =
   ⊥.rec (
     𝟚.toWitnessFalse
      {Q = (ℤ.discreteℤ _ _)}
       _ ((cong (ℤ.-_) (ℤ.pos·pos (suc n) _)
        ∙ sym (ℤ.negsuc·pos n _)) ∙∙ x ∙∙ sym (ℤ.pos·pos n₁ _) ))
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
    ((λ x₁ → ⊥.rec $ ℤ.isIrrefl< x₁)) 
      (λ x → ⊥.rec $ ℕ.znots (ℤ.injPos (eq/⁻¹ _ _ x))) ,
   (propBiimpl→Equiv (isSetℚ _ _) (isSetℚ _ _)
     (λ _ → refl) (λ _ → eq/ _ _ refl) ,
      propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
        (λ x → ⊥.rec (ℤ.¬-pos<-zero x))
          (λ x → ⊥.rec $ ℤ.posNotnegsuc _ _ ((eq/⁻¹ _ _ x))))
       
 w .ElimProp.f (ℤ.pos (suc n) , snd₁) =
   propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
    (λ _ → refl) (λ _ → 0<→< [ ℤ.pos (suc n) , snd₁ ] _) ,
   (propBiimpl→Equiv (isSetℚ _ _) (isSetℚ _ _)
     ((λ b → ⊥.rec
      (znots $ ℤ.injPos (b ∙ ℤ.·IdR (ℤ.pos (suc n))))) ∘S eq/⁻¹ _ _)
     (λ x → ⊥.rec (ℕ.snotz $ ℤ.injPos (eq/⁻¹ _ _ x)))  ,
      propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
        (λ x → ⊥.rec (ℤ.¬-pos<-zero (subst (ℤ._< 0)
         (sym (ℤ.pos·pos (suc n) 1)) x)))
          λ x → ⊥.rec (ℤ.posNotnegsuc _ _ (eq/⁻¹ _ _ x)))

 w .ElimProp.f (ℤ.negsuc n , snd₁) =
   propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
    ((λ x₁ → ⊥.rec $
   ℤ.¬pos≤negsuc (subst ((ℤ.pos _) ℤ.≤_) (ℤ.negsuc·pos n 1 ∙
    cong ℤ.-_ (sym (ℤ.pos·pos (suc n) 1)) ) x₁)))
     ((λ x → ⊥.rec (ℤ.posNotnegsuc 1 0 (sym x))) ∘S eq/⁻¹ _ _) ,
   (propBiimpl→Equiv (isSetℚ _ _) (isSetℚ _ _)
     ((λ x → ⊥.rec (ℤ.posNotnegsuc _ _
     (eq/⁻¹ _ _ x ∙ ℤ.·IdR (ℤ.negsuc n)))))
     ((⊥.rec ∘ ℤ.posNotnegsuc _ _ ∘ sym ) ∘S eq/⁻¹ _ _ )  ,
      propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
        (λ _ → refl)
         λ _ → minus-<' _ _ (0<→< (- [ ℤ.negsuc n , snd₁ ]) _))


<→sign : ∀ x → (0 < x → sign x ≡ 1)
               × (0 ≡ x → sign x ≡ 0)
                 × (x < 0 → sign x ≡ -1)
<→sign x =
 let ((y , _) , (y' , _) , (y'' , _)) = <≃sign x
 in (y , y' , y'')
 
abs≡sign· : ∀ x → ℚ.abs x ≡ x ℚ.· (sign x)
abs≡sign· x = abs'≡abs x ∙ ElimProp.go w x
 where
 w : ElimProp (λ z → abs' z ≡ z ℚ.· sign z)
 w .ElimProp.isPropB _ = isSetℚ _ _
 w .ElimProp.f x@(ℤ.pos zero , snd₁) = decℚ?
 w .ElimProp.f x@(ℤ.pos (suc n) , snd₁) =
  eq/ _ _ $
    cong₂ ℤ._·_ (sym (ℤ.·IdR _)) (cong ℕ₊₁→ℤ (·₊₁-identityʳ (snd₁)))

 w .ElimProp.f x@(ℤ.negsuc n , snd₁) = eq/ _ _
   $ cong₂ ℤ._·_ (ℤ.·Comm (ℤ.negsuc 0) (ℤ.negsuc n) )
      (cong ℕ₊₁→ℤ (·₊₁-identityʳ (snd₁)))

absPos : ∀ x → 0 < x → abs x ≡ x
absPos x 0<x = abs≡sign· x ∙∙ cong (x ℚ.·_) (fst (<→sign x) 0<x)  ∙∙ (ℚ.·IdR x)

absNonNeg : ∀ x → 0 ≤ x → abs x ≡ x
absNonNeg x 0<x with x ≟ 0
... | lt x₁ = ⊥.rec $ ≤→≯ 0 x 0<x x₁ 
... | eq x₁ = cong abs x₁ ∙ sym x₁
... | gt x₁ = absPos x x₁



absNeg : ∀ x → x < 0 → abs x ≡ - x
absNeg x x<0 = abs≡sign· x ∙∙ cong (x ℚ.·_) (snd (snd (<→sign x)) x<0)
                 ∙∙ ℚ.·Comm x -1



0≤abs : ∀ x → 0 ≤ abs x
0≤abs x with x ≟ 0
... | lt x₁ = subst (0 ≤_) (sym (absNeg x x₁)) ((<Weaken≤ 0 (- x) (minus-< x 0 x₁) ))
... | eq x₁ = subst ((0 ≤_) ∘ abs) (sym x₁) (isRefl≤ 0)
... | gt x₁ = subst (0 ≤_) (sym (absPos x x₁)) (<Weaken≤ 0 x x₁)


abs+pos : ∀ x y → 0 < x → abs (x ℚ.+ y) ≤ x ℚ.+ abs y
abs+pos x y x₁ with y ≟ 0
... | lt x₂ =
 let xx = (≤-o+ y (- y) x
            (<Weaken≤ y (- y) $ isTrans< y 0 (- y) x₂ ((minus-< y 0 x₂))))
 in subst (λ yy → abs (x ℚ.+ y) ≤ x ℚ.+ yy)
        (sym (absNeg y x₂)) (absFrom≤×≤ (x ℚ.- y) _
          (subst (_≤ x ℚ.+ y)
            (sym (-Distr' x y)) (≤-+o (- x) x y
             (<Weaken≤ (- x) x $ isTrans< (- x) 0 x (minus-< 0 x x₁) x₁))) xx)
... | eq x₂ = subst2 _≤_ (sym (absPos x x₁)
        ∙ cong abs (sym (ℚ.+IdR x) ∙ cong (x ℚ.+_) ( (sym x₂))))
   (sym (ℚ.+IdR x) ∙ cong (x ℚ.+_) (cong abs (sym x₂))  ) (isRefl≤ x) 
... | gt x₂ = subst2 _≤_ (sym (absPos _ (<Monotone+ 0 x 0 y x₁ x₂)))
    (cong (x ℚ.+_) (sym (absPos y x₂)))
   $ isRefl≤ (x ℚ.+ y)

abs+≤abs+abs : ∀ x y → ℚ.abs (x ℚ.+ y) ≤ ℚ.abs x ℚ.+ ℚ.abs y
abs+≤abs+abs x y with (x ≟ 0) | (y ≟ 0)
... | _ | gt x₁ = subst2 (_≤_)
                   (cong ℚ.abs (ℚ.+Comm y x))
            ((ℚ.+Comm y (ℚ.abs x)) ∙ cong ((ℚ.abs x) ℚ.+_ ) (sym (absPos y x₁)))
             (abs+pos y x x₁)
... | eq x₁ | _ = subst2 _≤_ (cong ℚ.abs (sym (ℚ.+IdL y) ∙
    cong (ℚ._+ y) (sym x₁) ))
                    (sym (ℚ.+IdL (ℚ.abs y)) ∙
                     cong (ℚ._+ (ℚ.abs y)) (cong ℚ.abs (sym x₁)))
                      (isRefl≤ (ℚ.abs y))
... | gt x₁ | _ = subst (ℚ.abs (x ℚ.+ y) ≤_)
            (cong (ℚ._+ (ℚ.abs y)) (sym (absPos x x₁)))
              (abs+pos x y x₁)
... | lt x₁ | lt x₂ =
  subst2 _≤_ (sym (-Distr x y) ∙ sym (absNeg (x ℚ.+ y)
    (<Monotone+ x 0 y 0 x₁ x₂)))
     (cong₂ ℚ._+_ (sym (absNeg x x₁)) (sym (absNeg y x₂))) (isRefl≤ ((- x) - y) )
... | lt x₁ | eq x₂ =
  subst2 _≤_ ((cong ℚ.abs (sym (ℚ.+IdR x) ∙
    cong (x ℚ.+_) (sym x₂))))
     (sym (ℚ.+IdR (ℚ.abs x)) ∙
                     cong ((ℚ.abs x) ℚ.+_ ) (cong ℚ.abs (sym x₂)))
    ((isRefl≤ (ℚ.abs x)))

data Trichotomy0· (m n : ℚ) : Type₀ where
  eqₘ₌₀ : m ≡ 0 → m ℚ.· n ≡ 0  → Trichotomy0· m n
  eqₙ₌₀ : n ≡ 0 → m ℚ.· n ≡ 0 → Trichotomy0· m n
  lt-lt : m < 0 → n < 0 → 0 < m ℚ.· n  → Trichotomy0· m n
  lt-gt : m < 0 → 0 < n → m ℚ.· n < 0  → Trichotomy0· m n
  gt-lt : 0 < m → n < 0 → m ℚ.· n < 0  → Trichotomy0· m n  
  gt-gt : 0 < m → 0 < n → 0 < m ℚ.· n  → Trichotomy0· m n

trichotomy0· : ∀ m n → Trichotomy0· m n
trichotomy0· m n with m ≟ 0 | n ≟ 0
... | eq p | _    = eqₘ₌₀ p (cong (ℚ._· n) p ∙ ℚ.·AnnihilL n)
... | _    | eq p = eqₙ₌₀ p (cong (m ℚ.·_) p ∙ ℚ.·AnnihilR m)
... | lt x₁ | lt x₂ = lt-lt x₁ x₂
  (subst (0 <_) (-·- m n)
    (0<-m·n (- m) (- n) (minus-< m 0 x₁) (minus-< n 0 x₂)))
... | lt x₁ | gt x₂ = lt-gt x₁ x₂
 ((subst (m ℚ.· n <_) (ℚ.·AnnihilL n) $ <-·o m 0 n x₂ x₁ ))
... | gt x₁ | lt x₂ = gt-lt x₁ x₂
 (subst (m ℚ.· n <_) (ℚ.·AnnihilR m) $ <-o· n 0 m x₁ x₂ )
... | gt x₁ | gt x₂ = gt-gt x₁ x₂ (0<-m·n m n x₁ x₂)

sign·sign : ∀ x y → sign x ℚ.· sign y ≡ sign (x ℚ.· y) 
sign·sign x y = h $ trichotomy0· x y

 where

 x' = <→sign x
 y' = <→sign y
 x·y' = <→sign (x ℚ.· y)
 
 h : Trichotomy0· x y → _ -- ℚ.·AnnihilL
 h (eqₘ₌₀ p p₁) =
  cong (ℚ._· sign y) (fst (snd x') (sym p))
   ∙∙ ℚ.·AnnihilL _ ∙∙ sym (fst (snd x·y') (sym p₁))
 h (eqₙ₌₀ p p₁) =   cong (sign x ℚ.·_) (fst (snd y') (sym p))
   ∙∙ ℚ.·AnnihilR _ ∙∙ sym (fst (snd x·y') (sym p₁))
 h (lt-lt p p₁ p₂) = cong₂ ℚ._·_ (snd (snd x') p) (snd (snd y') p₁)
  ∙ (sym $ fst x·y' p₂)
 h (lt-gt p p₁ p₂) = cong₂ ℚ._·_  (snd (snd x') p) (fst y' p₁)
          ∙ sym (snd (snd x·y') p₂)
 h (gt-lt p p₁ p₂) = cong₂ ℚ._·_ (fst x' p) (snd (snd y') p₁)
          ∙ sym (snd (snd x·y') p₂)
 h (gt-gt p p₁ p₂) = cong₂ ℚ._·_ (fst x' p) (fst y' p₁)
  ∙ (sym $ fst x·y' p₂)

0≤x² : ∀ x → 0 ≤ x ℚ.· x
0≤x² = ElimProp.go w
 where
 w : ElimProp (λ z → 0 ≤ z ℚ.· z)
 w .ElimProp.isPropB _ = isProp≤ _ _
 w .ElimProp.f (p , q) = subst (0 ℤ.≤_) (sym (ℤ.·IdR _)) (ℤ.0≤x² p)

signX·signX : ∀ x → 0 # x → sign x ℚ.· sign x ≡ 1
signX·signX x y = sign·sign x x ∙
   fst (fst (<≃sign (x ℚ.· x)))
    (⊎.rec (λ z → 0<-m·n _ _ z z)
      ((λ z → subst (0 <_) (-·- _ _) (0<-m·n _ _ z z)) ∘S minus-< x 0) y) 

abs·abs : ∀ x y → abs x ℚ.· abs y ≡ abs (x ℚ.· y) 
abs·abs x y = cong₂ ℚ._·_ (abs≡sign· x) (abs≡sign· y)
 ∙∙ (sym (ℚ.·Assoc _ _ _)) ∙∙
  cong (x ℚ.·_) (( (ℚ.·Assoc _ _ _)) ∙∙
  cong (ℚ._· sign y) (ℚ.·Comm (sign x) y) ∙∙ (sym (ℚ.·Assoc _ _ _))) ∙∙ (ℚ.·Assoc _ _ _)
 ∙∙ (λ i → x ℚ.· y ℚ.· sign·sign x y i) ∙ sym (abs≡sign· (x ℚ.· y))

abs'·abs' : ∀ x y → abs' x ℚ.· abs' y ≡ abs' (x ℚ.· y)
abs'·abs' x y = cong₂ ℚ._·_ (sym (abs'≡abs _)) (sym (abs'≡abs _))
  ∙∙ abs·abs x y ∙∙ abs'≡abs _

pos·abs : ∀ x y → 0 ≤ x →  abs (x ℚ.· y) ≡ x ℚ.· (abs y) 
pos·abs x y 0≤x = sym (abs·abs x y) ∙ cong (ℚ._· (abs y))
  (absNonNeg x 0≤x)

clamp≤ : ∀ L L' x → clamp L L' x ≤ L'
clamp≤ L L' x = min≤' _ L'


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

elimBy≡⊎< : ∀ {ℓ} {A : ℚ → ℚ → Type ℓ}
  → (∀ x y → A x y → A y x)
  → (∀ x → A x x)
  → (∀ x y → x < y → A x y)
  → ∀ x y → A x y
elimBy≡⊎< {A = A} s r f =
 elimBy≤ s (λ x y → ⊎.rec (λ p → subst (A x) p (r x)) (f x y) ∘ ≤→≡⊎< x y)


maxDistMin : ∀ x y z → ℚ.min (ℚ.max x y) z ≡ ℚ.max (ℚ.min x z) (ℚ.min y z)    
maxDistMin = elimBy≤
 (λ x y p z → cong (flip ℚ.min z) (ℚ.maxComm y x)  ∙∙ p z ∙∙
                ℚ.maxComm _ _ )
 λ x y p z → cong (flip ℚ.min z) (≤→max x y p) ∙
   sym (≤→max (ℚ.min x z) (ℚ.min y z) (≤MonotoneMin x y z z p (isRefl≤ z) ))



minDistMax : ∀ x y y' → ℚ.max x (ℚ.min y y') ≡ ℚ.min (ℚ.max x y) (ℚ.max x y')
minDistMax x = elimBy≤
  (λ y y' X → cong (ℚ.max x) (ℚ.minComm _ _) ∙∙ X ∙∙ ℚ.minComm _ _)
  λ y y' y≤y' → cong (ℚ.max x) (≤→min _ _ y≤y') ∙
    sym (≤→min (ℚ.max x y) (ℚ.max x y')
      (≤MonotoneMax x x y y' (isRefl≤ x) y≤y')) 

≤clamp : ∀ L L' x → L ≤ L' →  L ≤ clamp L L' x
≤clamp L L' x y =
 subst (L ≤_) (cong (λ y → ℚ.max y _) (sym $ ≤→min L L' y)
      ∙ sym (maxDistMin L x L')) (≤max L (ℚ.min x L')) 

absComm- : ∀ x y → ℚ.abs (x ℚ.- y) ≡ ℚ.abs (y ℚ.- x)
absComm- x y i = ℚ.maxComm (-[x-y]≡y-x y x (~ i)) (-[x-y]≡y-x x y i) i

≤MonotoneClamp : ∀ L L' x y → x ≤ y → clamp L L' x ≤ clamp L L' y 
≤MonotoneClamp L L' x y p = 
 ≤MonotoneMin
  (ℚ.max L x) (ℚ.max L y) L'
   L' (≤MonotoneMax L L x y (isRefl≤ L) p) (isRefl≤ L')



inClamps : ∀ L L' x → L ≤ x → x ≤ L' → clamp L L' x ≡ x
inClamps L L' x u v =
  cong (λ y → ℚ.min y L') (≤→max L x u)
    ∙ ≤→min x L' v

≤abs : ∀ x → x ≤ abs x
≤abs x = ≤max x (ℚ.- x) 

≤abs' : ∀ x → x ≤ abs' x
≤abs' x = subst (x ≤_) (abs'≡abs x) (≤abs x)


-abs : ∀ x → ℚ.abs x ≡ ℚ.abs (ℚ.- x)
-abs x = ℚ.maxComm _ _
  ∙ cong (ℚ.max (ℚ.- x)) (sym (ℚ.-Invol x))

-abs' : ∀ x → ℚ.abs' x ≡ ℚ.abs' (ℚ.- x)
-abs' x = sym (ℚ.abs'≡abs x) ∙∙ -abs x ∙∙ ℚ.abs'≡abs (ℚ.- x)


-≤abs' : ∀ x → ℚ.- x ≤ abs' x
-≤abs' x = subst (- x ≤_) (sym (-abs' x)) (≤abs' (ℚ.- x))

Dichotomyℚ : ∀ (n m : ℚ) → (n ≤ m) ⊎ (m < n)
Dichotomyℚ n m = decRec inr (inl ∘ ≮→≥ _ _) (<Dec m n)

sign·abs : ∀ x → abs x ℚ.· (sign x) ≡ x
sign·abs x with 0 ≟ x
... | lt x₁ =
 cong₂ ℚ._·_ (absPos x x₁) (fst (<→sign x) x₁)
    ∙ ℚ.·IdR x
... | eq x₁ = cong (abs x ℚ.·_) ( (fst (snd (<→sign x)) x₁))
 ∙ ·AnnihilR (abs x) ∙ x₁
... | gt x₁ =
  cong₂ ℚ._·_ (absNeg x x₁) (snd (snd (<→sign x)) x₁)
    ∙ -·- _ _ ∙ ℚ.·IdR x
   

0#→0<abs' : ∀ q → 0 # q → 0 < abs' q 
0#→0<abs' q (inl x) =
  subst (0 <_) (sym (absPos q x) ∙ (abs'≡abs q)) x
0#→0<abs' q (inr y) =
  subst (0 <_) (sym (absNeg q y) ∙ (abs'≡abs q)) (minus-< q 0 y)

0#→ℚ₊ : ∀ q → 0 # q → ℚ₊ 
0#→ℚ₊ q x = abs' q , <→0< _ (0#→0<abs' q x)

·Monotone0# : ∀ q q' → 0 # q → 0 # q' → 0 # (q ℚ.· q')  
·Monotone0# q q' (inl x) (inl x₁) =
 inl (0<→< _ (·0< q q' (<→0< q x) (<→0< q' x₁)))
·Monotone0# q q' (inl x) (inr x₁) =
  inr (minus-<' 0 (q ℚ.· q')
        (subst (0 <_) (((ℚ.·Comm  q (- q')) ∙ sym (ℚ.·Assoc -1 q' q))
         ∙ cong (-_) (ℚ.·Comm _ _))
         (0<→< _ (·0< q (- q') (<→0< q x) (<→0< _ (minus-< q' 0 x₁)))) ))
·Monotone0# q q' (inr x) (inl x₁) =
  inr (minus-<' 0 (q ℚ.· q')
     (subst (0 <_) (sym (ℚ.·Assoc -1 q q'))
       ((0<→< _ (·0< (- q) q' (<→0< _ (minus-< q 0 x)) (<→0< q' x₁)))))) 
·Monotone0# q q' (inr x) (inr x₁) =
 inl (subst (0 <_) (-·- _ _) (0<→< _
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
