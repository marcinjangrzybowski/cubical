{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Bisect where

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



≤^n : ∀ N n → N ℕ.< n →
        ([ 1 / 2 ] ℚ^ⁿ n) ℚ.≤ ([ 1 / 2 ] ℚ^ⁿ N)
≤^n N zero x = ⊥.rec (ℕ.¬-<-zero x)
≤^n zero (suc zero) x = ℚ.decℚ≤? {[ 1 / 2 ] ℚ.· 1} {1}
≤^n zero (suc (suc n)) x = ℚ.isTrans≤
  (([ 1 / 2 ] ℚ^ⁿ (suc n)) ℚ.· [ 1 / 2 ] )
  (([ 1 / 2 ] ℚ^ⁿ n) ℚ.· [ 1 / 2 ])
  _
  (ℚ.≤-·o _ _ [ 1 / 2 ] (ℚ.decℚ≤? {0} {[ 1 / 2 ]})
    (≤^n n (suc n) ℕ.≤-refl))
  (≤^n zero (suc n) (ℕ.suc-≤-suc ℕ.zero-≤))
≤^n (suc N) (suc n) x =
 ℚ.≤-·o _ _ [ 1 / 2 ] (ℚ.decℚ≤? {0} {[ 1 / 2 ]})
   (≤^n N n (ℕ.predℕ-≤-predℕ x))

Lipschitz-ℚ→ℝℙ : ℚ₊ → (P : ℙ ℚ) → (∀ x → x ∈ P  → ℝ) → Type
Lipschitz-ℚ→ℝℙ L P f =
  (∀ q q∈ r r∈ → (ε : ℚ₊) →
    ℚ.abs (q ℚ.- r) ℚ.< (fst ε) → absᵣ (f q q∈ -ᵣ f r r∈)
     <ᵣ rat (fst (L ℚ₊· ε  )))


Invlipschitz-ℚ→ℚℙ : ℚ₊ → (P : ℙ ℚ) → (∀ x → x ∈ P  → ℚ) → Type
Invlipschitz-ℚ→ℚℙ K P f =
  (∀ q q∈ r r∈ → (ε : ℚ₊) →
        ℚ.abs' (f q q∈ ℚ.- f r r∈) ℚ.< (fst ε)
     → ℚ.abs' (q ℚ.- r) ℚ.< fst (K ℚ₊· ε ) )


ℚintervalℙ : ℚ → ℚ → ℙ ℚ 
ℚintervalℙ a b x = ((a ℚ.≤ x) × (x ℚ.≤ b)) ,
  isProp× (ℚ.isProp≤ _ _)  (ℚ.isProp≤ _ _)



bisect : ∀ K a b → (a<b : a ℚ.< b) → ∀ f
           → Invlipschitz-ℚ→ℚℙ K (ℚintervalℙ a b) f

           → Σ _ (Lipschitz-ℚ→ℝℙ (K ℚ.ℚ₊· 2) (ℚintervalℙ
                 (f a (ℚ.isRefl≤ _  , ℚ.<Weaken≤ a b a<b))
                 (f b (ℚ.<Weaken≤ _ _ a<b , (ℚ.isRefl≤ _)))))
           
bisect K a b a<b f il  =
  f⁻¹ , L-f⁻¹

 where
 
 a≤b = ℚ.<Weaken≤ _ _ a<b
 Δ₀ = b ℚ.- a 

 record Step (y Δ : ℚ) : Type where
  field
   a' b' : ℚ
   a'≤b' : a' ℚ.≤ b'
   b'-a'≤Δ : b' ℚ.- a' ℚ.≤ Δ 
   a'∈ : a' ∈ ℚintervalℙ a b
   b'∈ : b' ∈ ℚintervalℙ a b
   a'≤ : f a' a'∈ ℚ.≤ y
   ≤b' : y ℚ.≤ f b' b'∈ 


 -- stepSubstHelp : ∀ y {Δ Δ'} → (p : Δ ≡ Δ') → (s : Step y Δ) →
 --                    Step.a' s ≡ Step.a' (subst (Step y) p s) 
 -- stepSubstHelp y p s = {!transportRefl _!}

 record Step⊃Step {y Δ ΔS : _} (s : Step y Δ) (sS : Step y ΔS) : Type where
  
  field
   a'≤a'S : Step.a' s ℚ.≤ Step.a' sS 
   bS≤b' : Step.b' sS ℚ.≤ Step.b' s
   -- distA' : (Step.a' sS) ℚ.≤ Δ ℚ.· [ 1 / 2 ] ℚ.+ (Step.a' s)
 
 module _ (y : ℚ) (y∈ : y ∈ _) where
   
  step0 : Step y Δ₀
  step0 .Step.a' = a
  step0 .Step.b' = b
  step0 .Step.a'≤b' = a≤b
  step0 .Step.b'-a'≤Δ = ℚ.isRefl≤ _
  step0 .Step.a'∈ = ℚ.isRefl≤ _  , a≤b
  step0 .Step.b'∈ = a≤b , (ℚ.isRefl≤ _)
  step0 .Step.a'≤ = fst y∈
  step0 .Step.≤b' = snd y∈

  stepS' : ∀ Δ → (s : Step y Δ) → Σ (Step y (Δ ℚ.· [ 1 / 2 ])) (Step⊃Step s)
  stepS' Δ s = w (ℚ.Dichotomyℚ y fMid)
   where
   open Step s

   mid : ℚ
   mid = b' ℚ.· [ 1 / 2 ] ℚ.+ a' ℚ.· [ 1 / 2 ]

   p = ℚ.≤-·o _ _ [ 1 / 2 ] (ℚ.decℚ≤? {0} {[ 1 / 2 ]}) a'≤b'

   a'≤mid : a' ℚ.≤ mid
   a'≤mid = ℚ.isTrans≤ _ _ _
     (ℚ.≡Weaken≤ _ _ (sym (ℚ.·IdR a') ∙ cong (a' ℚ.·_) ℚ.decℚ? ∙
       ℚ.·DistL+ a' _ _))
     (ℚ.≤-+o _ _ (a' ℚ.· [ 1 / 2 ]) p) 

   mid≤b' : mid ℚ.≤ b' 
   mid≤b' = ℚ.isTrans≤ _ _ _    
     (ℚ.≤-o+ _ _ (b' ℚ.· [ 1 / 2 ]) p) 
     (ℚ.≡Weaken≤ _ _ (sym (ℚ.·DistL+ b' _ _) ∙ cong (b' ℚ.·_) ℚ.decℚ? ∙
       ℚ.·IdR b'))
   mid∈ : mid ∈ ℚintervalℙ a b
   mid∈ = ℚ.isTrans≤ _ _ _ (fst (a'∈)) a'≤mid ,
           ℚ.isTrans≤ _ _ _ mid≤b' (snd b'∈)

   fMid = f mid mid∈
   a'-mid≤Δ/2 : (mid ℚ.- a') ℚ.≤ Δ ℚ.· [ 1 / 2 ]
   a'-mid≤Δ/2 = 
     ℚ.isTrans≤ _ _ _
      (ℚ.≡Weaken≤ (mid ℚ.- a') ((b' ℚ.- a') ℚ.· [ 1 / 2 ])
        (sym (ℚ.+Assoc _ _ _) ∙
         cong (b' ℚ.· [ 1 / 2 ] ℚ.+_)
          (cong (a' ℚ.· [ 1 / 2 ] ℚ.+_) (ℚ.·Comm -1 a')
           ∙ sym (ℚ.·DistL+ a' _ _) ∙
            ℚ.·Comm _ _ ∙
             sym (ℚ.·Assoc [ 1 / 2 ] -1 a') ∙  ℚ.·Comm [ 1 / 2 ] _)
          ∙ sym (ℚ.·DistR+ _ _ _)))
      (ℚ.≤-·o _ _ _ (ℚ.decℚ≤? {0} {[ 1 / 2 ]}) b'-a'≤Δ)

   w : (y ℚ.≤ fMid) ⊎ (fMid ℚ.< y) → Σ (Step y (Δ ℚ.· [ 1 / 2 ]))
             (Step⊃Step s) 
   w (inl x) .fst .Step.a' = a'
   w (inl x) .fst .Step.b' = mid
   w (inl x) .fst .Step.a'≤b' = a'≤mid
   w (inl x) .fst .Step.b'-a'≤Δ = a'-mid≤Δ/2
   w (inl x) .fst .Step.a'∈ = a'∈
   w (inl x) .fst .Step.b'∈ = mid∈ 
   w (inl x) .fst .Step.a'≤ = a'≤
   w (inl x) .fst .Step.≤b' = x
   w (inl x) .snd .Step⊃Step.a'≤a'S = ℚ.isRefl≤ a'
   w (inl x) .snd .Step⊃Step.bS≤b' = mid≤b'
   w (inr x) .fst .Step.a' = mid
   w (inr x) .fst .Step.b' = b'
   w (inr x) .fst .Step.a'≤b' = mid≤b'
   w (inr x) .fst .Step.b'-a'≤Δ =
     ℚ.isTrans≤ _ _ _
        (ℚ.≡Weaken≤ (b' ℚ.- mid)
                    ((b' ℚ.- a') ℚ.· [ 1 / 2 ])
                      ((cong (b' ℚ.+_) (ℚ.-Distr _ _ ) ∙
                       ℚ.+Assoc _ _ _ ∙
                        cong₂ ℚ._+_
                        (cong₂ ℚ._+_ (sym (ℚ.·IdR b'))
                         (ℚ.·Comm -1 _ ∙ sym (ℚ.·Assoc _ _ _))
                         ∙ sym (ℚ.·DistL+ b' 1 [ -1 / 2 ]))
                         (ℚ.·Assoc -1 _ _))
                       ∙ sym (ℚ.·DistR+ _ _ _)))
          (ℚ.≤-·o _ _ _ (ℚ.decℚ≤? {0} {[ 1 / 2 ]}) b'-a'≤Δ)

   w (inr x) .fst .Step.a'∈ = mid∈
   w (inr x) .fst .Step.b'∈ = b'∈
   w (inr x) .fst .Step.a'≤ = ℚ.<Weaken≤ _ _ x
   w (inr x) .fst .Step.≤b' = ≤b'
   w (inr x) .snd .Step⊃Step.a'≤a'S = a'≤mid
   w (inr x) .snd .Step⊃Step.bS≤b' = ℚ.isRefl≤ b'
   
  stepS : ∀ Δ → Step y Δ → Step y (Δ ℚ.· [ 1 / 2 ])
  stepS Δ s = fst (stepS' Δ s)
  
  ww : ∀ n → Step y (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n))
  ww zero = subst (Step y) (sym (ℚ.·IdR Δ₀)) step0
  ww (suc n) = subst (Step y) (sym (ℚ.·Assoc _ _ _)) (stepS _ (ww n))

  s = Step.a' ∘ ww


  ss≤-suc : ∀ n (z : Step y (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n))) → Step.a' z ℚ.≤
      Step.a' (subst (Step y) (sym (ℚ.·Assoc _ _ _)) (stepS
       (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n)) z))
  ss≤-suc n z = ℚ.isTrans≤ _ _ _ (Step⊃Step.a'≤a'S (snd (stepS'
       (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n)) z)))
         (ℚ.≡Weaken≤ _ _ (sym (transportRefl _)))
  
  ss≤ : ∀ n m → s n ℚ.≤ s (m ℕ.+ n) 
  ss≤ n zero = ℚ.isRefl≤ _ 
  ss≤ n (suc m) = ℚ.isTrans≤ _ _ _ (ss≤ n m) (ss≤-suc (m ℕ.+ n) (ww (m ℕ.+ n)))


  ww⊂ : ∀ n m → (s (m ℕ.+ n) ℚ.- s n) ℚ.≤ Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n)
  ww⊂ = {!!}
  
  www : {ε : ℚ₊} → (Σ[ n ∈ ℕ ] [ 1 / 2 ] ℚ^ⁿ n ℚ.<
            fst (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)))
         → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
            ℚ.abs ((s n) ℚ.- (s m)) ℚ.< (fst ε)   )
  www (N , P) .fst = N
  www {ε} (N , P) .snd = ℕ.elimBy≤+
    (λ n m X m< n< → subst (ℚ._< fst ε) (ℚ.absComm- _ _) (X n< m<))
    λ n m p N<n →
      let P' : Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ N) ℚ.< fst ε
          P' = ℚ.isTrans<≤ _ _ (fst ε) (ℚ.<-o· _ _ _ (ℚ.-< a b a<b) P)
                 (ℚ.≡Weaken≤ _ _
                    ((cong (fst (ℚ.<→ℚ₊ a b a<b) ℚ.·_) (ℚ.·Comm _ _))
                     ∙ ℚ.y·[x/y] (ℚ.<→ℚ₊ _ _ a<b) (fst ε)))
      in ℚ.isTrans≤< _ _ _
          (ℚ.isTrans≤ _ ((s (m ℕ.+ n)) ℚ.- (s n)) _
            (ℚ.≡Weaken≤ _ _ (ℚ.absNonNeg (s (m ℕ.+ n) ℚ.- s n)
              (ℚ.-≤ (s n) (s (m ℕ.+ n)) (ss≤ n m))))
              (ww⊂ n m))
          (ℚ.isTrans≤< _ (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ (N))) _
            (ℚ.≤-o· _ _ Δ₀ (ℚ.-≤ a b a≤b) (≤^n N n N<n)) P')

  f⁻¹-aprox-S : _
  f⁻¹-aprox-S = ww ∘ fst ∘ 1/2ⁿ<ε ∘
    (λ ε → ε ℚ.ℚ₊· ℚ.invℚ₊ (ℚ.<→ℚ₊ _ _ a<b))
  
  f⁻¹-aprox : ℚ₊ → ℚ
  f⁻¹-aprox = Step.a' ∘ f⁻¹-aprox-S

  f⁻¹-aprox' : ℚ₊ → ℚ
  f⁻¹-aprox' = (Step.b' ∘ ww ∘ fst) ∘ 1/2ⁿ<ε ∘
    (λ ε → ε ℚ.ℚ₊· ℚ.invℚ₊ (ℚ.<→ℚ₊ _ _ a<b))


  f⁻¹-cauchy' : ∀ ε δ → fst ε ℚ.≤ fst δ →
    ℚ.abs' (f⁻¹-aprox δ ℚ.- f⁻¹-aprox ε) ℚ.< fst (δ ℚ₊+ ε)
  f⁻¹-cauchy' = {!!}
  
  f⁻¹-cauchy : ∀ ε δ → ℚ.abs' (f⁻¹-aprox δ ℚ.- f⁻¹-aprox ε) ℚ.< fst (δ ℚ₊+ ε)
  f⁻¹-cauchy = {!ℚ.elimBy≤ ? ? !}
  -- subst (_<ᵣ rat (fst (δ ℚ₊+ ε)))
  --   {!!}
  --   {!!}
  
  f⁻¹ : ℝ
  f⁻¹ = lim (rat ∘ f⁻¹-aprox) 
   λ δ ε →  invEq (∼≃abs<ε _ _ _) (<ℚ→<ᵣ _ _ (f⁻¹-cauchy ε δ)) 


 L-f⁻¹ : Lipschitz-ℚ→ℝℙ (K ℚ.ℚ₊· 2)
           (ℚintervalℙ (f a _)
            (f b _))
           f⁻¹
 L-f⁻¹ q q∈ r r∈ ε q-r<ε =
  isTrans≤<ᵣ _ _ _ lipL (<ℚ→<ᵣ _ _ lf)
  where

  lf : ℚ.abs' (f⁻¹-aprox' r r∈ ε ℚ.- f⁻¹-aprox q q∈ ε) ℚ.<
           fst ((K ℚ.ℚ₊· 2) ℚ₊· ε)
  lf = {!!}
   where
    lf' : ℚ.abs' (f⁻¹-aprox' r r∈ ε ℚ.- f⁻¹-aprox q q∈ ε) ℚ.<
            fst (K ℚ₊· (2 ℚ₊· ε))
    lf' = il (f⁻¹-aprox' r r∈ ε) (Step.b'∈ (f⁻¹-aprox-S r r∈ ε))
          (f⁻¹-aprox q q∈ ε) (Step.a'∈ (f⁻¹-aprox-S q q∈ ε)) (2 ℚ.ℚ₊· ε)
           {!!}


 
  f⁻¹≤f⁻¹-aprox' : ∀ z z∈ → f⁻¹ z z∈ ≤ᵣ rat (f⁻¹-aprox' z z∈ ε) 
  f⁻¹≤f⁻¹-aprox' = {!!}
  
  f⁻¹-aprox≤f⁻¹ : ∀ z z∈ → rat (f⁻¹-aprox z z∈ ε)  ≤ᵣ f⁻¹ z z∈
  f⁻¹-aprox≤f⁻¹ = {!!}


  lipL' : ∀ q q∈ r r∈ → (f⁻¹ r r∈ -ᵣ f⁻¹ q q∈) ≤ᵣ
           (rat (f⁻¹-aprox' r r∈ ε) -ᵣ rat (f⁻¹-aprox q q∈ ε))  
  lipL' q q∈ r r∈ = 
    ≤ᵣMonotone+ᵣ _ _ _ _ (f⁻¹≤f⁻¹-aprox' r r∈)
      (-ᵣ≤ᵣ _ _ (f⁻¹-aprox≤f⁻¹ q q∈))
      


  lipL : absᵣ (f⁻¹ q q∈ -ᵣ f⁻¹ r r∈) ≤ᵣ
        absᵣ (rat (f⁻¹-aprox' r r∈ ε) -ᵣ rat (f⁻¹-aprox q q∈ ε))  
  lipL = {!!}
  


 -- L-f⁻¹ : Lipschitz-ℚ→ℝℙ K
 --           (ℚintervalℙ (f a _)
 --            (f b _))
 --           f⁻¹
 -- L-f⁻¹ q q∈ r r∈ = {!!}


-- -- bisect : ∀ K a b → (a<b : a ℚ.< b) → ∀ f → Invlipschitz-ℚ→ℚℙ K (ℚintervalℙ a b) f
-- --            → (y : ℚ)
-- --            → y ∈ ℚintervalℙ (f a (ℚ.isRefl≤ _  , ℚ.<Weaken≤ _ _ a<b))
-- --                             (f b (ℚ.<Weaken≤ _ _ a<b , (ℚ.isRefl≤ _)))
-- --            → Σ _ IsCauchySequence'ℚ
-- -- bisect K a b a<b f il y y∈ =
-- --   s , (λ {ε} → www {ε}) ∘ 1/2ⁿ<ε ∘
-- --     (λ ε → ε ℚ.ℚ₊· ℚ.invℚ₊ (ℚ.<→ℚ₊ _ _ a<b))
-- --  where
-- --  a≤b = ℚ.<Weaken≤ _ _ a<b
-- --  Δ₀ = b ℚ.- a 

-- --  record Step (Δ : ℚ) : Type where
-- --   field
-- --    a' b' : ℚ
-- --    a'≤b' : a' ℚ.≤ b'
-- --    b'-a'≤Δ : b' ℚ.- a' ℚ.≤ Δ 
-- --    a'∈ : a' ∈ ℚintervalℙ a b
-- --    b'∈ : b' ∈ ℚintervalℙ a b
-- --    a'≤ : f a' a'∈ ℚ.≤ y
-- --    ≤b' : y ℚ.≤ f b' b'∈ 

-- --  step0 : Step Δ₀
-- --  step0 .Step.a' = a
-- --  step0 .Step.b' = b
-- --  step0 .Step.a'≤b' = a≤b
-- --  step0 .Step.b'-a'≤Δ = ℚ.isRefl≤ _
-- --  step0 .Step.a'∈ = ℚ.isRefl≤ _  , a≤b
-- --  step0 .Step.b'∈ = a≤b , (ℚ.isRefl≤ _)
-- --  step0 .Step.a'≤ = fst y∈
-- --  step0 .Step.≤b' = snd y∈

-- --  stepS : ∀ Δ → Step Δ → Step (Δ ℚ.· [ 1 / 2 ])
-- --  stepS Δ s = w (ℚ.Dichotomyℚ y fMid)
-- --   where
-- --   open Step s

-- --   mid : ℚ
-- --   mid = b' ℚ.· [ 1 / 2 ] ℚ.+ a' ℚ.· [ 1 / 2 ]

-- --   p = ℚ.≤-·o _ _ [ 1 / 2 ] (ℚ.decℚ≤? {0} {[ 1 / 2 ]}) a'≤b'

-- --   a'≤mid : a' ℚ.≤ mid
-- --   a'≤mid = ℚ.isTrans≤ _ _ _
-- --     (ℚ.≡Weaken≤ _ _ (sym (ℚ.·IdR a') ∙ cong (a' ℚ.·_) ℚ.decℚ? ∙
-- --       ℚ.·DistL+ a' _ _))
-- --     (ℚ.≤-+o _ _ (a' ℚ.· [ 1 / 2 ]) p) 

-- --   mid≤b' : mid ℚ.≤ b' 
-- --   mid≤b' = ℚ.isTrans≤ _ _ _    
-- --     (ℚ.≤-o+ _ _ (b' ℚ.· [ 1 / 2 ]) p) 
-- --     (ℚ.≡Weaken≤ _ _ (sym (ℚ.·DistL+ b' _ _) ∙ cong (b' ℚ.·_) ℚ.decℚ? ∙
-- --       ℚ.·IdR b'))
-- --   mid∈ : mid ∈ ℚintervalℙ a b
-- --   mid∈ = ℚ.isTrans≤ _ _ _ (fst (a'∈)) a'≤mid ,
-- --           ℚ.isTrans≤ _ _ _ mid≤b' (snd b'∈)

-- --   fMid = f mid mid∈
-- --   a'-mid≤Δ/2 : (mid ℚ.- a') ℚ.≤ Δ ℚ.· [ 1 / 2 ]
-- --   a'-mid≤Δ/2 = 
-- --     ℚ.isTrans≤ _ _ _
-- --      (ℚ.≡Weaken≤ (mid ℚ.- a') ((b' ℚ.- a') ℚ.· [ 1 / 2 ])
-- --        (sym (ℚ.+Assoc _ _ _) ∙
-- --         cong (b' ℚ.· [ 1 / 2 ] ℚ.+_)
-- --          (cong (a' ℚ.· [ 1 / 2 ] ℚ.+_) (ℚ.·Comm -1 a')
-- --           ∙ sym (ℚ.·DistL+ a' _ _) ∙
-- --            ℚ.·Comm _ _ ∙
-- --             sym (ℚ.·Assoc [ 1 / 2 ] -1 a') ∙  ℚ.·Comm [ 1 / 2 ] _)
-- --          ∙ sym (ℚ.·DistR+ _ _ _)))
-- --      (ℚ.≤-·o _ _ _ (ℚ.decℚ≤? {0} {[ 1 / 2 ]}) b'-a'≤Δ)

-- --   w : (y ℚ.≤ fMid) ⊎ (fMid ℚ.< y) → Step (Δ ℚ.· [ 1 / 2 ])
-- --   w (inl x) .Step.a' = a'
-- --   w (inl x) .Step.b' = mid
-- --   w (inl x) .Step.a'≤b' = a'≤mid
-- --   w (inl x) .Step.b'-a'≤Δ = a'-mid≤Δ/2
-- --   w (inl x) .Step.a'∈ = a'∈
-- --   w (inl x) .Step.b'∈ = mid∈ 
-- --   w (inl x) .Step.a'≤ = a'≤
-- --   w (inl x) .Step.≤b' = x
-- --   w (inr x) .Step.a' = mid
-- --   w (inr x) .Step.b' = b'
-- --   w (inr x) .Step.a'≤b' = mid≤b'
-- --   w (inr x) .Step.b'-a'≤Δ =
-- --     ℚ.isTrans≤ _ _ _
-- --        (ℚ.≡Weaken≤ (b' ℚ.- mid)
-- --                    ((b' ℚ.- a') ℚ.· [ 1 / 2 ])
-- --                      ((cong (b' ℚ.+_) (ℚ.-Distr _ _ ) ∙
-- --                       ℚ.+Assoc _ _ _ ∙
-- --                        cong₂ ℚ._+_
-- --                        (cong₂ ℚ._+_ (sym (ℚ.·IdR b'))
-- --                         (ℚ.·Comm -1 _ ∙ sym (ℚ.·Assoc _ _ _))
-- --                         ∙ sym (ℚ.·DistL+ b' 1 [ -1 / 2 ]))
-- --                         (ℚ.·Assoc -1 _ _))
-- --                       ∙ sym (ℚ.·DistR+ _ _ _)))
-- --          (ℚ.≤-·o _ _ _ (ℚ.decℚ≤? {0} {[ 1 / 2 ]}) b'-a'≤Δ)
    
-- --   w (inr x) .Step.a'∈ = mid∈
-- --   w (inr x) .Step.b'∈ = b'∈
-- --   w (inr x) .Step.a'≤ = ℚ.<Weaken≤ _ _ x
-- --   w (inr x) .Step.≤b' = ≤b'

-- --  ww : ∀ n → Step (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n))
-- --  ww zero = subst Step (sym (ℚ.·IdR Δ₀)) step0
-- --  ww (suc n) = subst Step (sym (ℚ.·Assoc _ _ _)) (stepS _ (ww n))

-- --  s = Step.a' ∘ ww

-- --  ss≤ : ∀ n m → s n ℚ.≤ s (m ℕ.+ n) 
-- --  ss≤ = {!!}
 
-- --  ww⊂ : ∀ n m → (s (m ℕ.+ n) ℚ.- s n) ℚ.≤ Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n)
-- --  ww⊂ n m = {!!}

-- --  www : {ε : ℚ₊} → (Σ[ n ∈ ℕ ] [ 1 / 2 ] ℚ^ⁿ n ℚ.<
-- --            fst (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)))
-- --         → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
-- --            ℚ.abs ((s n) ℚ.- (s m)) ℚ.< (fst ε)   )
-- --  www (N , P) .fst = N
-- --  www {ε} (N , P) .snd = ℕ.elimBy≤+
-- --    (λ n m X m< n< → subst (ℚ._< fst ε) (ℚ.absComm- _ _) (X n< m<))
-- --    λ n m p N<n →
-- --      let P' : Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ N) ℚ.< fst ε
-- --          P' = ℚ.isTrans<≤ _ _ (fst ε) (ℚ.<-o· _ _ _ (ℚ.-< a b a<b) P)
-- --                 (ℚ.≡Weaken≤ _ _
-- --                    ((cong (fst (ℚ.<→ℚ₊ a b a<b) ℚ.·_) (ℚ.·Comm _ _))
-- --                     ∙ ℚ.y·[x/y] (ℚ.<→ℚ₊ _ _ a<b) (fst ε)))
-- --      in ℚ.isTrans≤< _ _ _
-- --          (ℚ.isTrans≤ _ ((s (m ℕ.+ n)) ℚ.- (s n)) _
-- --            (ℚ.≡Weaken≤ _ _ (ℚ.absNonNeg (s (m ℕ.+ n) ℚ.- s n)
-- --              (ℚ.-≤ (s n) (s (m ℕ.+ n)) (ss≤ n m))))
-- --              (ww⊂ n m))
-- --          (ℚ.isTrans≤< _ (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ N)) _
-- --            (ℚ.≤-o· _ _ Δ₀ (ℚ.-≤ a b a≤b) (≤^n N n N<n)) P')
