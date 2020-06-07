{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Record.Base where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

-- open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)



corner0 : ∀ {n} →  Vec Interval n
corner0 {zero} = []
corner0 {suc n} =  zero ∷ corner0

corner1 : ∀ {n} →  Vec Interval n
corner1 {zero} = []
corner1 {suc n} =  one ∷ corner1



one= : ∀ i' → one ≡ i'
one= (zero) = sym seg
one= (one) = refl
one= (seg i) i₁ = seg (i ∨ ~ i₁)

=zero : ∀ (i' : Interval) → i' ≡ zero 
=zero zero = refl
=zero one = sym seg
=zero (seg i) i₁ = seg (i ∧ ~ i₁)

=one : ∀ i' → i' ≡ one
=one (zero) = seg
=one (one) = refl
=one (seg i) i₁ = seg (i ∨ i₁)

zero= : ∀ (i' : Interval) → zero ≡ i' 
zero= zero = refl
zero= one = seg
zero= (seg i) i₁ = seg (i ∧ i₁)


isPropCube : ∀ {n} → isProp (Vec Interval n)
isPropCube {zero} [] [] i = []
isPropCube {suc n} (x ∷ x₁) (x₂ ∷ x₃) i =
    (isContr→isProp isContrInterval) x x₂ i ∷ (isPropCube x₁ x₃ i)


RecordImplementation : ∀ ℓ → Type (ℓ-suc (ℓ-suc ℓ))
RecordImplementation ℓ = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ 

from-RecordImplementation-to-Σ-Sig-Rec : ∀ {ℓ} → RecordImplementation ℓ → Type (ℓ-suc ℓ)
from-RecordImplementation-to-Σ-Sig-Rec = uncurry Σ

RI↑-L : ∀ {ℓ} → RecordImplementation ℓ → RecordImplementation ℓ
RI↑-L {ℓ} (Sig , Rec) =
    (Σ[ Ty ∈ Type ℓ ]  (Ty → Sig)) , λ x → Σ (fst x) (Rec ∘ snd x)

RI↑-R : ∀ {ℓ} → RecordImplementation ℓ → RecordImplementation ℓ
RI↑-R {ℓ} (Sig , Rec) =
    (Σ Sig (λ x → Rec x → Type ℓ)) , λ x → Σ (Rec (fst x)) (snd x)



RI-LR-0 : ∀ {ℓ} → (RI↑-L (Type ℓ , λ  Ty → Ty)) ≡ (RI↑-R (Type ℓ , λ  Ty → Ty))
RI-LR-0 = refl

RI-LR : ∀ {ℓ} → ∀ ri → (RI↑-L {ℓ} ∘ RI↑-R) ri ≡ (RI↑-R {ℓ} ∘ RI↑-L) ri
RI-LR {ℓ} ri = sigmaPath→pathSigma _ _
                   ((isoToPath signatureIso) ,
                       funExt λ x → transportsRefls x ∙ isoToPath (recordIso x))
  where

    Sig = fst
    Rec = snd

    signatureIso =  (iso (λ x → (fst x , fst ∘ snd x) , λ x₂ → snd (snd x (fst x₂)) (snd x₂))
                       (λ x → (fst (fst x)) , λ x₂ → (snd (fst x) x₂) , snd x ∘ (x₂ ,_))
                       (λ _ → refl) (λ _ → refl)) 

    recordIso : (a : Sig (RI↑-R (RI↑-L ri))) → Iso _ _
    recordIso a = iso (λ x → ((fst x) , fst (snd x)) , snd (snd x))
                       (λ x → fst (fst x) , (snd (fst x) , snd x))
                         (λ b → refl) λ a → refl

    transportsRefls : (a : Sig (RI↑-R (RI↑-L ri))) →  _ ≡ _
    transportsRefls a = cong (Σ (fst (fst a)))
              λ i x →
               Σ (snd ri (transportRefl (snd (fst a)
                      (transportRefl x i)) i))
                  λ x₁ → snd a ((transportRefl x i) ,
                         transp ((λ i₁ → snd ri (transp (λ i₂ → fst ri) (i₁ ∨ i)
                          (snd (fst a) (transp (λ j → fst (fst a)) (i₁ ∨ i)
                                        (transp (λ i₂ → fst (fst a)) ((~ i₁) ∨ i) x))))))
                            i x₁)


RI : ∀ {ℓ} → ∀ {n} → Vec Interval n → RecordImplementation ℓ
RI {n = zero} _ = Lift Unit , λ _ → Lift Unit
RI (_ ∷ []) = Type _ , λ  Ty → Ty
RI (zero ∷ v) = RI↑-L (RI v)
RI (one ∷ v) =  RI↑-R (RI v)
RI {n = 2} (seg i ∷ i' ∷ []) = RI-LR-0 i
RI {n = suc (suc n)} (j' ∷ i' ∷ v ∷ vs) =
       I-elim _ 
      ((λ i → RI↑-L (RI (=one i' i ∷ v ∷ vs)))
              ∙∙  RI-LR (RI (v ∷ vs))  ∙∙
        λ i → RI↑-R (RI (zero= i' i ∷ v ∷ vs)))
      j' 




Sig* : ∀ ℓ → ∀ {n} → Vec Interval n →  Type (ℓ-suc ℓ)
Sig* ℓ v = fst (RI {ℓ} v)

Rec* : ∀ {ℓ} → ∀ {n} → {v : Vec Interval n} → Sig* ℓ v → Type ℓ
Rec* {v = v} = snd (RI {_} v)

Sigₗ : ∀ ℓ → ∀ n →  Type (ℓ-suc ℓ)
Sigₗ ℓ n = Sig* ℓ {n} corner0

Recₗ : ∀ {ℓ} → ∀ {n} → Sigₗ ℓ n → Type ℓ
Recₗ {ℓ} {n} = snd (RI {ℓ} {n} corner0)


Sigᵣ : ∀ ℓ → ∀ n →  Type (ℓ-suc ℓ)
Sigᵣ ℓ n = Sig* ℓ {n} corner1

Recᵣ : ∀ {ℓ} → ∀ {n} → Sigᵣ ℓ n → Type ℓ
Recᵣ {ℓ} {n} = snd (RI {ℓ} {n} corner1)

Sig*-subst : ∀ {ℓ} → ∀ {n} → {v₁ : Vec Interval n}
                   → (v₂ : Vec Interval n)
                   → Sig* ℓ v₁ → Sig* ℓ v₂  
Sig*-subst {v₁ = v₁} v₂ = subst (Sig* _) (isPropCube v₁ v₂)


Rec*-subst : ∀ {ℓ} → ∀ {n} → (v₁ v₂ : Vec Interval n)
                   → {s : Sig* ℓ v₁}
                   → Rec* {v = v₁} s
                   → Rec* {v = v₂} (Sig*-subst v₂ s)
Rec*-subst v₁ v₂ {s = s} =
     transport (λ i → snd (RI (isPropCube v₁ v₂ i))
       (coe0→i (λ i → Sig* _ ((isPropCube v₁ v₂ i))) i s)) 

Rec*-subst⁻ : ∀ {ℓ} → ∀ {n} → (v₁ v₂ : Vec Interval n)
                   → {s : Sig* ℓ v₁}
                   → Rec* {v = v₂} (Sig*-subst v₂ s)
                   → Rec* {v = v₁} s 
Rec*-subst⁻ v₁ v₂ {s = s} =
     transport⁻ (λ i → snd (RI (isPropCube v₁ v₂ i))
       (coe0→i (λ i → Sig* _ ((isPropCube v₁ v₂ i))) i s)) 


toₗ : ∀ {ℓ} → ∀ {n} → (v : Vec Interval n) → Sig* ℓ v → Sigₗ ℓ n 
toₗ v = Sig*-subst {v₁ = v} corner0

fromₗ : ∀ {ℓ} → ∀ {n} → (v : Vec Interval n) → Sigₗ ℓ n → Sig* ℓ v 
fromₗ = Sig*-subst {v₁ = corner0} 

toᵣ : ∀ {ℓ} → ∀ {n} → (v : Vec Interval n) → Sig* ℓ v → Sigᵣ ℓ n 
toᵣ v = Sig*-subst {v₁ = v} corner1

fromᵣ : ∀ {ℓ} → ∀ {n} → (v : Vec Interval n) → Sigᵣ ℓ n → Sig* ℓ v 
fromᵣ = Sig*-subst {v₁ = corner1} 

prependTyₗ : ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → (A → Sigₗ ℓ n) → Sigₗ ℓ (suc n)
prependTyₗ {n = zero} {A} _ = A
prependTyₗ {n = suc n} = _ ,_ 

prependValₗ : ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
                → (s : A → Sigₗ ℓ n)
                → (x : A)
                → Recₗ {n = n} (s x)
                → Recₗ {n = suc n} (prependTyₗ {n = n} s)
prependValₗ {n = zero} s x _ = x
prependValₗ {n = suc n} s = _,_

appendTyᵣ : ∀ {ℓ} → ∀ {n} → (s : Sigᵣ ℓ n) → (Recᵣ {n = n} s → Type ℓ) → Sigᵣ ℓ (suc n)
appendTyᵣ {n = zero}  s r = r _
appendTyᵣ {n = suc n} = _,_

appendValᵣ :  ∀ {ℓ} → ∀ {n} → (s : Sigᵣ ℓ n)
             → (A : Recᵣ {n = n} s → Type ℓ)
             → (r : Recᵣ {n = n} s)
             → A r
             → Recᵣ {n = (suc n)} (appendTyᵣ {n = n} s A)
appendValᵣ {n = zero} s A r x = x
appendValᵣ {n = suc n} s A = _,_

Sig : ∀ ℓ → ∀ n →  Type (ℓ-suc ℓ)
Sig ℓ n = Σ _ (fst ∘ RI {ℓ} {n})


Rec : ∀ {ℓ} → ∀ {n} → Sig ℓ n → Type ℓ
Rec s = snd (RI (fst s)) (snd s)


prependTy : ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
                → (A → Sig ℓ n)
                → Sig ℓ (suc n)
prependTy {n = n} =
   (corner0  ,_) ∘ prependTyₗ {n = n} ∘
     (λ a x → (Sig*-subst {v₁ = fst (a x) } corner0 (snd (a x))))

prependVal : ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
                → (s : A → Sig ℓ n)
                → (x : A)
                → Rec (s x)
                → Rec (prependTy s)
prependVal {n = n} s x r =
  prependValₗ {n = n}
          (λ a → (Sig*-subst {v₁ = fst (s a) } corner0 (snd (s a)))) x
            (Rec*-subst (fst (s x)) corner0 r)
  
appendTy : ∀ {ℓ} → ∀ {n}
                → (s : Sig ℓ n)
                → (Rec {n = n} s → Type ℓ)
                → Sig ℓ (suc n)
appendTy {n = n} s x = corner1 ,
              (appendTyᵣ {n = n} (Sig*-subst {v₁ = fst s } corner1 (snd s))
                    ( x ∘ (Rec*-subst⁻ (fst s) (corner1))))



KindSig : ∀ ℓ → ∀ n → Sigᵣ (ℓ-suc ℓ) n

fromKindRec : ∀ {ℓ} → ∀ {n} → Recᵣ {n = n} (KindSig ℓ n) → Sigᵣ ℓ n

toKindRec : ∀ {ℓ} → ∀ {n} → Sigᵣ ℓ n → Recᵣ {n = n} (KindSig ℓ n)

KindSig _ zero =  _
KindSig _ (suc n) =
  appendTyᵣ {n = n} (KindSig _ n)
  (λ r → Recᵣ {n = n} (fromKindRec {n = n} r) → Type _)

fromKindRec {n = zero} x = _
fromKindRec {n = suc zero} x = x _
fromKindRec {n = suc (suc n)} x =
    appendTyᵣ {n = suc n} (fromKindRec {n = suc n} (fst x)) (snd x)

tofromKindRec : ∀ {ℓ} → ∀ {n} → ∀ (s : Sigᵣ ℓ n) →
                      Recᵣ {ℓ} {n = n} (fromKindRec {n = n} (toKindRec {ℓ} {n} s))
                    → Recᵣ {ℓ} {n = n} s

toKindRec {ℓ} {zero} x = _
toKindRec {ℓ} {suc zero} x _ = x
toKindRec {ℓ} {suc (suc n)} x =
   appendValᵣ {n = suc n}  (KindSig ℓ ((suc n)))
     (λ r → Recᵣ {n = suc n} (fromKindRec {n = (suc n)} r) → Type _)
     (toKindRec {n = suc n} (fst x))
     (λ x₁ → snd x (tofromKindRec {n = suc n} (fst x) x₁))

tofromKindRec {n = zero} s x = _
tofromKindRec {ℓ} {n = suc zero} s x = x
tofromKindRec {ℓ} {n = suc (suc n)} s x = (tofromKindRec {n = suc n} (fst s) (fst x)) , snd x


iso-Π-Π' : ∀ {ℓ ℓ'} {A : Type ℓ}
               → (B : A → Type ℓ')
               → Iso (Π B) (Π' B)
iso-Π-Π' B = iso (λ x {y} → x y) (λ x y → x {y}) (λ b → refl) (λ b → refl)  

fromSigTypeₗ : ∀ {ℓ} → ∀ n → Vec Interval n → Sigₗ ℓ n → Type ℓ → Type ℓ 
fromSigTypeₗ zero _ _ Target = Target
fromSigTypeₗ (suc zero) v s Target =
    I-rec (isoToPath (iso-Π-Π' {A = s} λ x₂ → Target)) (head v) 
fromSigTypeₗ (suc (suc n)) v s Target =
   I-rec (isoToPath
    (iso-Π-Π' {A = fst s} λ x → fromSigTypeₗ (suc n) (tail v) (snd s x) Target))
      (head v)


constructorTypeₗ : ∀ {ℓ} → ∀ n → Vec Interval n → Sigₗ ℓ n → Type ℓ 
constructorTypeₗ n v s = fromSigTypeₗ n v s (Recₗ {n = n} s)






Sig*-concat : ∀ {ℓ} → ∀ {n m}
           → (vₙ : Vec Interval n)
           → (vₘ : Vec Interval m)
           → Sig* ℓ vₙ → Sig* ℓ vₘ
           → Sig* ℓ (vₙ ++ vₘ)
Sig*-concat {n = .0} [] vₘ x x₁ = x₁
Sig*-concat {n = .1} {m = m} (i' ∷ []) vₘ x x₁ =
   fromₗ (i' ∷ vₘ) (prependTyₗ {n = m} {A = x} (const (toₗ vₘ x₁)))
Sig*-concat {n = (suc (suc n))} {m} (x₂ ∷ x₃ ∷ vₙ) vₘ x x₁ =
        fromₗ ((x₂ ∷ x₃ ∷ vₙ) ++ vₘ) (prependTyₗ {n = (suc n) + m} {A = fst (toₗ (x₂ ∷ x₃ ∷ vₙ) x)}
           λ x₄ → toₗ ((corner0 {suc n}) ++ vₘ) (Sig*-concat {n = suc n} {m = m} corner0 vₘ
                    ((snd (toₗ (x₂ ∷ x₃ ∷ vₙ) x) x₄)) x₁)) 


Sigₗ-section-from : ∀ {ℓ} → ∀ {n m}
           → (sₙ : Sigₗ ℓ n)
           → (sₘ : Recₗ {n = n} sₙ →  Sigₗ ℓ m)
           → Sigₗ ℓ (n + m)
Sigₗ-section-from {n = zero} sₙ sₘ = sₘ _
Sigₗ-section-from {n = suc zero} {m} sₙ sₘ = prependTyₗ {n = m} {A = sₙ} sₘ
Sigₗ-section-from {n = suc (suc n)} {m} sₙ sₘ =
   prependTyₗ {n = (suc n) + m}
     λ x → Sigₗ-section-from {n = suc n} {m} (snd sₙ x) (sₘ ∘ (x ,_)) 

Sigₗ-section-to : ∀ {ℓ} → ∀ {n m}
           → Sigₗ ℓ (n + m)
           → Σ[ sₙ ∈  Sigₗ ℓ n ] (Recₗ {n = n} sₙ → Sigₗ ℓ m)
Sigₗ-section-to {n = zero} x = _ , const x
Sigₗ-section-to {n = suc zero} {zero} = _, _
Sigₗ-section-to {n = suc zero} {suc m} = idfun _
Sigₗ-section-to {n = suc (suc n)} x =
 let z = λ (y : fst x) → Sigₗ-section-to {n = suc n} (snd x y)
 in (fst x , fst ∘ z) ,  uncurry (snd ∘ z)

Sigₗ-section-to-from : ∀ {ℓ} → ∀ {n m}
    → section (Sigₗ-section-to {ℓ} {n} {m}) (uncurry (Sigₗ-section-from {ℓ} {n} {m}))
Sigₗ-section-to-from {n = zero} b = refl
Sigₗ-section-to-from {n = suc zero} {zero} b = refl
Sigₗ-section-to-from {n = suc zero} {suc m} b = refl
Sigₗ-section-to-from {n = suc (suc n)} {m} b i =
  let z = λ (y : fst (fst b)) →
            Sigₗ-section-to-from {n = (suc n)} {m = m} (snd (fst b) y , snd b ∘ (y ,_)) i
  in ((fst (fst b)) ,  fst ∘ z) , uncurry (snd ∘ z)

Sigₗ-section-from-to : ∀ {ℓ} → ∀ {n m}
    → retract (Sigₗ-section-to {ℓ} {n} {m}) (uncurry (Sigₗ-section-from {ℓ} {n} {m}))
Sigₗ-section-from-to {n = zero} a = refl
Sigₗ-section-from-to {n = suc zero} {zero} a = refl
Sigₗ-section-from-to {n = suc zero} {suc m} a = refl
Sigₗ-section-from-to {n = suc (suc n)} {m} a i =
  prependTyₗ {n = (suc n) + m} λ (y : fst a) → Sigₗ-section-from-to {n = suc n} {m} (snd a y) i

Sigₗ-section-Iso : ∀ {ℓ} → ∀ {n m}
                   → Iso (Sigₗ ℓ (n + m))
                         (Σ[ sₙ ∈  Sigₗ ℓ n ] (Recₗ {n = n} sₙ → Sigₗ ℓ m))
Sigₗ-section-Iso {ℓ} {n} {m} =
  iso (Sigₗ-section-to {n = n} {m}) (uncurry (Sigₗ-section-from {n = n} {m}))
      (Sigₗ-section-to-from {ℓ} {n} {m}) (Sigₗ-section-from-to {ℓ} {n} {m})


Recₗ-section-to :  ∀ {ℓ} → ∀ {n m} 
                       → (s : Sigₗ ℓ (n + m))
                       → Recₗ {n = n + m} s
                       → Σ (Recₗ {n = n} (fst (Sigₗ-section-to {n = n} s)))
                           (Recₗ {n = m} ∘ (snd (Sigₗ-section-to {n = n} {m = m} s))) 
Recₗ-section-to {n = zero} s x = _ , x
Recₗ-section-to {n = suc zero} {zero} s = _, _
Recₗ-section-to {n = suc zero} {suc m} s x = x
Recₗ-section-to {n = suc (suc n)} {m} s x =
   _ , snd (Recₗ-section-to {n = suc n} ((snd s) (fst x)) (snd x))

Recₗ-section-from :  ∀ {ℓ} → ∀ {n m} 
                       → (sₙ : Sigₗ ℓ n)
                       → (sₘ : Recₗ {n = n} sₙ →  Sigₗ ℓ m)
                       → Σ (Recₗ {n = n} sₙ)
                           (Recₗ {n = m} ∘ sₘ)
                       → Recₗ {n = n + m} (Sigₗ-section-from {n = n} {m = m}  sₙ sₘ)
Recₗ-section-from {n = zero} sₙ sₘ = snd
Recₗ-section-from {n = suc zero} {m} sₙ sₘ = prependValₗ {n = m} {A = sₙ} sₘ _ ∘ snd
Recₗ-section-from {n = suc (suc n)} {m} sₙ sₘ x =
     prependValₗ {n = suc n + m} (_) _
      (Recₗ-section-from {n = suc n} _ _ (_ , snd x))



-- KindSigₗ : ∀ ℓ → ∀ n → Sigₗ (ℓ-suc ℓ) n

-- fromKindRecₗ : ∀ {ℓ} → ∀ {n} → Recₗ {n = n} (KindSigₗ ℓ n) → Sigₗ ℓ n

-- toKindRecₗ : ∀ {ℓ} → ∀ {n} → Sigₗ ℓ n → Recₗ {n = n} (KindSigₗ ℓ n)


-- KindSigₗ ℓ zero = _
-- KindSigₗ ℓ (suc zero) = Type ℓ
-- KindSigₗ ℓ (suc (suc n)) =
--   Sigₗ-section-from {n = 1} {!!} λ x → {!!} 


-- fromKindRecₗ = {!!}

-- toKindRecₗ = {!!}

-- -- SigSig : ∀ {ℓ} → ∀ {n} → Σ (Sig (ℓ-suc ℓ) n ) λ x → Iso (Rec x) (Sig ℓ n)
-- -- SigSig {n = zero} =
-- --  ([] , lift tt) , (iso (λ x → [] , _) (λ _ → lift tt)
-- --                             (λ {([] , _) → refl}) λ _ → refl)

-- -- SigSig {n = suc zero} =
-- --   (zero ∷ [] , Type _) ,
--  --   (iso (λ x → zero ∷ [] , x)
-- --      (λ { (zero ∷ [] , x) → x ; (seg i ∷ [] , x) → x ; (one ∷ [] , x) → x } )
-- --      ((λ { (zero ∷ [] , x) → refl
-- --          ; (seg i ∷ [] , x) j → seg (i ∧ j ) ∷ []  , x
-- --          ; (one ∷ [] , x) j → seg j ∷ [] , x } ))
-- --       λ a → refl)
-- -- SigSig {ℓ} {n = suc (suc n)} =
-- --   let (prevSig , iso to from lInv rInv) = SigSig {ℓ} {n = suc n}
-- --   in  (appendTy prevSig) (const (Type _))
-- --       ,  (iso (λ x → {!!})
-- --               {!!}
-- --               {!!}
-- --               {!!})




-- -- SigSig [] = (lift tt) , refl
-- -- SigSig (x ∷ []) = Set _ , refl

-- -- SigSig (zero ∷ _ ∷ []) = (Type _ , λ x → x → Type _) , refl
-- -- SigSig (one ∷ _ ∷ []) = (Type _ , λ x → x → Type _) , refl
-- -- SigSig (seg i ∷ _ ∷ []) = (Type _ , λ x → x → Type _) , refl

-- -- SigSig (i' ∷ x₁ ∷ x ∷ v) = {!!}



-- -- -- test :  I → Set₁ 
-- -- -- test i = fst (RI {ℓ-zero} {3} (seg i ∷ seg i  ∷ seg i ∷ [])) 

-- -- -- test2 : {!!}
-- -- -- test2 = {!fst (RI {ℓ-zero} {6} corner1) !} 

-- -- -- -- Sigₗ : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)
-- -- -- -- Sigₗ ℓ 0 = Lift Unit
-- -- -- -- Sigₗ ℓ 1 = Type ℓ
-- -- -- -- Sigₗ ℓ (suc (suc n)) = Σ[ Ty ∈ Type ℓ ]  (Ty → Sigₗ ℓ (suc n))

-- -- -- -- Recₗ : ∀ {ℓ} → ∀ {n} → Sigₗ ℓ n → Type ℓ
-- -- -- -- Recₗ {n = 0} _ = Lift Unit
-- -- -- -- Recₗ {n = 1} x = x
-- -- -- -- Recₗ {n = suc (suc n)} x = Σ (fst x) (Recₗ ∘ snd x)


-- -- -- -- Sigᵣ : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)

-- -- -- -- Recᵣ : ∀ {ℓ} → ∀ {n} → Sigᵣ ℓ n → Type ℓ


-- -- -- -- Sigᵣ ℓ 0 = Lift Unit
-- -- -- -- Sigᵣ ℓ 1 = Type ℓ
-- -- -- -- Sigᵣ ℓ (suc (suc n)) = Σ (Sigᵣ ℓ (suc n)) (λ x → Recᵣ x → Type ℓ)

-- -- -- -- Recᵣ {ℓ} {0} x = Lift Unit
-- -- -- -- Recᵣ {ℓ} {1} x = x
-- -- -- -- Recᵣ {ℓ} {suc (suc n)} x = Σ (Recᵣ (fst x)) (snd x)



-- -- -- -- trim-sig :  ∀ {ℓ} → ∀ {n} → (s : Sigₗ ℓ n) → Sigₗ ℓ (predℕ n)
-- -- -- -- trim-sig {n = 0} s = _
-- -- -- -- trim-sig {n = 1} s = _
-- -- -- -- trim-sig {n = 2} s = fst s
-- -- -- -- trim-sig {n = suc (suc (suc n))} s = fst s , λ x → trim-sig (snd s x)


-- -- -- -- push-Type :  ∀ {ℓ} → ∀ {n} → (s : Sigₗ ℓ n)
-- -- -- --               → (Recₗ s → Type ℓ)
-- -- -- --               → Sigₗ ℓ (suc n)
-- -- -- -- push-Type {n = zero} s x = x _
-- -- -- -- push-Type {n = suc zero} s x = s , x
-- -- -- -- push-Type {n = suc (suc n)} s x = (fst s) , (λ a → push-Type (snd s a) (x ∘ (a ,_) ))

-- -- -- -- trim-rec :  ∀ {ℓ} → ∀ {n} → (s : Sigₗ ℓ n) → Recₗ s → Recₗ (trim-sig s)
-- -- -- -- trim-rec {n = zero} x = _
-- -- -- -- trim-rec {n = suc zero} s x = _
-- -- -- -- trim-rec {n = suc (suc zero)} s x = fst x
-- -- -- -- trim-rec {n = suc (suc (suc n))} s x = fst x , trim-rec (snd s (fst x)) (snd x)


-- -- -- -- -- This functions describes Type of maixmally curried type of last field in record in given signature
-- -- -- -- -- the purpose of Boolean and (List ℕ) arguments, is to controll
-- -- -- -- -- explicity of arguments in generated type:
-- -- -- -- --  * Bool controls the "default" mode (true → implicit , false  → explicit)
-- -- -- -- --  * List ℕ controls "exceptions", it stores the list of spaces
-- -- -- -- --    betwen arguments which are treated in oposite way
-- -- -- -- --    (if this list is to long, the remaing elements are ignored)

-- -- -- -- Type-in-sig : ∀ {ℓ} → Bool → List ℕ → ∀ {n} → Sigₗ ℓ n → Type (ℓ-suc ℓ)
-- -- -- -- Type-in-sig _ _ {zero} _ = Type _
-- -- -- -- Type-in-sig false [] {suc zero} x = x → Type _
-- -- -- -- Type-in-sig {ℓ} true [] {suc zero} x = {_ : x} → Type ℓ

-- -- -- -- Type-in-sig {ℓ} false (zero ∷ _) {suc zero} x = {_ : x} → Type ℓ
-- -- -- -- Type-in-sig true (zero ∷ _) {suc zero} x = x → Type _

-- -- -- -- Type-in-sig false (suc x₁ ∷ xs) {suc zero} x = x → Type _
-- -- -- -- Type-in-sig {ℓ} true (suc x₁ ∷ xs) {suc zero} x = {_ : x} → Type ℓ

-- -- -- -- Type-in-sig false [] {suc (suc n)} x = (a : fst x) → Type-in-sig false [] (snd x a) 
-- -- -- -- Type-in-sig true [] {suc (suc n)} x = {a : fst x} → Type-in-sig true [] (snd x a)
-- -- -- -- Type-in-sig false (zero ∷ xs) {suc (suc n)} x = {a : fst x} → Type-in-sig false (xs) (snd x a)
-- -- -- -- Type-in-sig false (suc k ∷ xs) {suc (suc n)} x = (a : fst x) → Type-in-sig false (k ∷ xs) (snd x a)
-- -- -- -- Type-in-sig true (zero ∷ xs) {suc (suc n)} x = (a : fst x) → Type-in-sig true (xs) (snd x a)
-- -- -- -- Type-in-sig true (suc k ∷ xs) {suc (suc n)} x = {a : fst x} → Type-in-sig true (k ∷ xs) (snd x a)

-- -- -- -- -- maixmally curried Type of last field for given signature
-- -- -- -- pop-Type : ∀ {ℓ} → ∀ {n}
-- -- -- --            → (b : Bool) → (l : List ℕ) → (A : Sigₗ ℓ n)
-- -- -- --            → Type-in-sig b l (trim-sig A)
-- -- -- -- pop-Type {n = zero} _ _ _ = Lift Unit
-- -- -- -- pop-Type {n = suc zero} _ _ A = A
-- -- -- -- pop-Type {n = suc (suc zero)} false [] A = snd A
-- -- -- -- pop-Type {n = suc (suc zero)} true [] A {a} = snd A a
-- -- -- -- pop-Type {n = suc (suc zero)} false (zero ∷ l) A {a} = snd A a
-- -- -- -- pop-Type {n = suc (suc zero)} false (suc k ∷ l) A = snd A
-- -- -- -- pop-Type {n = suc (suc zero)} true (zero ∷ l) A = snd A
-- -- -- -- pop-Type {n = suc (suc zero)} true (suc k ∷ l) A {a} = snd A a
-- -- -- -- pop-Type {n = suc (suc (suc n))} false [] A a = pop-Type false [] (snd A a)
-- -- -- -- pop-Type {n = suc (suc (suc n))} true [] A {a} = pop-Type true [] (snd A a)
-- -- -- -- pop-Type {n = suc (suc (suc n))} false (zero ∷ l) A {a} = pop-Type false l (snd A a)
-- -- -- -- pop-Type {n = suc (suc (suc n))} false (suc k ∷ l) A a = pop-Type false (k ∷ l) (snd A a)
-- -- -- -- pop-Type {n = suc (suc (suc n))} true (zero ∷ l) A a = pop-Type true l (snd A a)
-- -- -- -- pop-Type {n = suc (suc (suc n))} true (suc k ∷ l) A {a} = pop-Type true (k ∷ l) (snd A a)

-- -- -- -- -- maximally uncuried  Type of last field for given signature
-- -- -- -- pop-Type-overRecₗ : ∀ {ℓ} → ∀ {n}
-- -- -- --                      → (s : Sigₗ ℓ n)
-- -- -- --                      →  Recₗ (trim-sig s) → Type ℓ
-- -- -- -- pop-Type-overRecₗ {n = zero} _ _ = Lift Unit
-- -- -- -- pop-Type-overRecₗ {n = suc zero} A _ = A
-- -- -- -- pop-Type-overRecₗ {n = suc (suc zero)} x a = snd x a
-- -- -- -- pop-Type-overRecₗ {n = suc (suc (suc n))} x a = pop-Type-overRecₗ (snd x (fst a)) (snd a)


-- -- -- -- pushVal : ∀ {ℓ} → ∀ {n} → (A : Sigₗ ℓ n)
-- -- -- --         → (x : Recₗ (trim-sig A))
-- -- -- --         → (pop-Type-overRecₗ A x) → Recₗ A 
-- -- -- -- pushVal {n = zero} _ _ _ = _
-- -- -- -- pushVal {n = suc zero} _ _ a = a
-- -- -- -- pushVal {n = suc (suc zero)} _ x x₁ = x , x₁
-- -- -- -- pushVal {n = suc (suc (suc n))} A x x₁ = fst x , (pushVal (snd A (fst x)) (snd x) x₁)

-- -- -- -- popVal : ∀ {ℓ} → ∀ {n} → (A : Sigₗ ℓ n)
-- -- -- --         → (x : Recₗ A) → pop-Type-overRecₗ A (trim-rec A x) 
-- -- -- -- popVal {n = zero} _ _ = _
-- -- -- -- popVal {n = suc zero} _ x = x
-- -- -- -- popVal {n = suc (suc zero)} _ x = snd x
-- -- -- -- popVal {n = suc (suc (suc n))} A x = popVal (snd A (fst x)) (snd x)

-- -- -- -- push-trim : ∀ {ℓ} → ∀ {n} → {s : Sigₗ ℓ n}
-- -- -- --              → ∀ x → trim-sig (push-Type s x) ≡ s
-- -- -- -- push-trim {n = zero} x = refl
-- -- -- -- push-trim {n = suc zero} x = refl
-- -- -- -- push-trim {n = suc (suc n)} {s} x i = fst s , λ a → push-trim ( x ∘ (a ,_)) i

-- -- -- -- concatSigₗ : ∀ {ℓ} → ∀ {n m} → Sigₗ ℓ n → Sigₗ ℓ m → Sigₗ ℓ (n + m)
-- -- -- -- concatSigₗ {n = zero} {zero} x x₁ = _
-- -- -- -- concatSigₗ {n = zero} {suc m} x x₁ = x₁
-- -- -- -- concatSigₗ {n = suc n} {zero} x x₁ = subst (Sigₗ _) (sym (+-zero (suc n))) x 
-- -- -- -- concatSigₗ {n = suc zero} {suc m} x x₁ = x , (λ _ → x₁)
-- -- -- -- concatSigₗ {n = suc (suc n)} {suc m} x x₁ = (fst x) , λ a → concatSigₗ (snd x a) x₁

-- -- -- -- concatSigₗ-dep : ∀ {ℓ} → ∀ {n m}
-- -- -- --                  → (s : Sigₗ ℓ n)
-- -- -- --                  → (Recₗ s → Sigₗ ℓ m)
-- -- -- --                  → Sigₗ ℓ (n + m)
-- -- -- -- concatSigₗ-dep {n = zero} {m = m} s x = x _
-- -- -- -- concatSigₗ-dep {n = suc n} {m = zero} s x = subst (Sigₗ _) (sym (+-zero (suc n))) s 
-- -- -- -- concatSigₗ-dep {n = suc zero} {m = suc m} s x = s , x
-- -- -- -- concatSigₗ-dep {n = suc (suc n)} {m = suc m} s x =
-- -- -- --   (fst s) , (λ a → concatSigₗ-dep (snd s a) (x ∘ (a ,_ )))

-- -- -- -- splitSigₗ :  ∀ {ℓ} → ∀ {n m}
-- -- -- --                  → Sigₗ ℓ (n + m)
-- -- -- --                   → Σ[ sₙ ∈ Sigₗ ℓ n ] ((Recₗ sₙ → Sigₗ ℓ m))                  
-- -- -- -- splitSigₗ {n = zero} x = _ , const x
-- -- -- -- splitSigₗ {n = suc n} {zero} x = subst (Sigₗ _) (+-zero (suc n)) x , const _
-- -- -- -- splitSigₗ {n = suc zero} {suc m} x = x
-- -- -- -- splitSigₗ {ℓ} {n = suc (suc n)} {suc m} x =
-- -- -- --   let z : (a : fst x) → Σ (Sigₗ ℓ (suc n)) (λ sₙ → Recₗ sₙ → Sigₗ ℓ (suc m))
-- -- -- --       z a =  splitSigₗ ((snd x) a)

-- -- -- --   in (fst x , fst ∘ z) , λ x₁ →  snd (z (fst x₁)) (snd x₁)


-- -- -- -- fromVecOfTypes : ∀ {ℓ} → ∀ {n} → Vec (Type ℓ) n → Sigₗ ℓ n
-- -- -- -- fromVecOfTypes {n = 0} _ = _
-- -- -- -- fromVecOfTypes {n = 1} (x) = head x
-- -- -- -- fromVecOfTypes {n = (suc (suc n))} x = head x , const (fromVecOfTypes (tail x) )




-- -- -- -- -- This functions describes Type of maixmally curried type of last field in record in given signature
-- -- -- -- -- the purpose of Boolean and (List ℕ) arguments, is to controll
-- -- -- -- -- explicity of arguments in generated type:
-- -- -- -- --  * Bool controls the "default" mode (true → implicit , false  → explicit)
-- -- -- -- --  * List ℕ controls "exceptions", it stores the list of spaces
-- -- -- -- --    betwen arguments which are treated in oposite way
-- -- -- -- --    (if this list is to long, the remaing elements are ignored)

-- -- -- -- -- Type-in-sigᵣ : ∀ {ℓ} → ∀ {n} → Sigₗ ℓ n → Type (ℓ-suc ℓ)
-- -- -- -- -- Type-in-sigᵣ {n = zero} x = Lift Unit
-- -- -- -- -- Type-in-sigᵣ {n = suc zero} x = x → Type _
-- -- -- -- -- Type-in-sigᵣ {n = suc (suc n)} x = {!x!}
