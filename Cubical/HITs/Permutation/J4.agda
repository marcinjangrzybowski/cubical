{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.J4 where

open import Cubical.Foundations.Everything
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.2GroupoidTruncation

data J₃S¹ : Type where
  base : J₃S¹
  loop : base ≡ base
  loop₂ : Square loop loop loop loop
  loop₃ : Cube loop₂ loop₂ loop₂ loop₂  loop₂ loop₂
  trunc : is2Groupoid J₃S¹

record J₃S¹-elim {ℓ} (A : J₃S¹ → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  abase : A base
  aloop : PathP (λ i → A (loop i)) abase abase
  aloop₂ : SquareP (λ j i → A (loop₂ j i))
             aloop aloop aloop aloop
  aloop₃ : PathP (λ k →
                 SquareP (λ j i → A (loop₃ k j i))
                      (aloop₂ k)
                      (aloop₂ k)
                      (aloop₂ k)
                      (aloop₂ k))
               aloop₂
               aloop₂
  atrunc : ∀ x → is2Groupoid (A x)

 f : ∀ x → A x
 f base = abase
 f (loop i) = aloop i
 f (loop₂ i i₁) = aloop₂ i i₁
 f (loop₃ i i₁ i₂) = aloop₃ i i₁ i₂
 f (trunc _ _ _ _ _ _ r s i i₁ i₂ i₃) =
      isOfHLevel→isOfHLevelDep 4 (atrunc)
     _ _ _ _ _ _
     (λ j k l → f (r j k l)) (λ j k l → f (s j k l))
     (trunc _ _ _ _ _ _ r s) i i₁ i₂ i₃


record J₃S¹-elimGrp {ℓ} (A : J₃S¹ → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  abase : A base
  aloop : PathP (λ i → A (loop i)) abase abase
  aloop₂ : SquareP (λ j i → A (loop₂ j i))
             aloop aloop aloop aloop
  atrunc : ∀ x → isGroupoid (A x)

 r : J₃S¹-elim A
 J₃S¹-elim.abase r = abase
 J₃S¹-elim.aloop r = aloop
 J₃S¹-elim.aloop₂ r = aloop₂
 J₃S¹-elim.aloop₃ r = {!!}
   -- isProp→PathP (λ i → {!!})
   --  _ _
   -- isGroupoid→isGroupoid' (atrunc (loop₃ k j i))
   --   (λ i₁ i₂ → {!!})
   --   {!!}
   --   {!!}
   --   {!!}
   --   {!!}
   --   {!!} k j i
  -- let z = 
  --         isOfHLevel→isOfHLevelDep 3 {!!} --atrunc
  --           _ _ _ _ {!!} {!!} {!loop₃!} k j i
  -- in {!z!}
 J₃S¹-elim.atrunc r = isGroupoid→is2Groupoid ∘ atrunc

 f : ∀ x → A x
 f = J₃S¹-elim.f r

record J₃S¹-elimSet {ℓ} (A : J₃S¹ → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  abase : A base
  aloop : PathP (λ i → A (loop i)) abase abase
  atrunc : ∀ x → isSet (A x)

 r : J₃S¹-elimGrp A
 J₃S¹-elimGrp.abase r = abase
 J₃S¹-elimGrp.aloop r = aloop
 J₃S¹-elimGrp.aloop₂ r = isSet→SquareP (λ j i → atrunc (loop₂ j i)) _ _ _ _
 J₃S¹-elimGrp.atrunc r = isSet→isGroupoid ∘ atrunc
 
 f : ∀ x → A x
 f = J₃S¹-elimGrp.f r


record J₃S¹-elimProp {ℓ} (A : J₃S¹ → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  abase : A base
  atrunc : ∀ x → isProp (A x)

 r : J₃S¹-elimSet A
 J₃S¹-elimSet.abase r = abase
 J₃S¹-elimSet.aloop r = isProp→PathP (λ i → atrunc (loop i)) _ _
 J₃S¹-elimSet.atrunc r = isProp→isSet ∘ atrunc
 
 f : ∀ x → A x
 f = J₃S¹-elimSet.f r

record J₃S¹-rec {ℓ} (A : Type ℓ) : Type ℓ where
 no-eta-equality
 field
  abase : A
  aloop : abase ≡ abase
  aloop₂ : Square aloop aloop aloop aloop
  aloop₃ : Cube aloop₂ aloop₂ aloop₂ aloop₂ aloop₂ aloop₂
  atrunc : is2Groupoid A

 f : J₃S¹ → A
 f base = abase
 f (loop i) = aloop i
 f (loop₂ i i₁) = aloop₂ i i₁
 f (loop₃ i i₁ i₂) = aloop₃ i i₁ i₂
 f (trunc _ _ _ _ _ _ r s i i₁ i₂ i₃) =
   atrunc _ _ _ _ _ _
      (λ i i₁ i₂ → f (r i i₁ i₂))
      (λ i i₁ i₂ → f (s i i₁ i₂))
       i i₁ i₂ i₃



data Co : Type where
 𝟘 : Co
 ↑ ↓ : Co → Co
 ↓↑ : ∀ x → ↓ (↑ x) ≡ x 
 ↑↓ : ∀ x → ↑ (↓ x) ≡ x
 ♯ : ∀ x → ↑ (↑ x) ≡ ↑ (↑ x)
 ↑♯≡♯↑ : ∀ x → Path (↑ (↑ (↑ x)) ≡ ↑ (↑ (↑ x)))
                 (λ i → ♯ (↑ x) i)
                 (λ i → ↑ (♯ x i))
 trunc : isGroupoid Co


record Co-elim {ℓ} (A : Co → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  abase : A 𝟘
  a↑ : ∀ {x} → (A x) → (A (↑ x))
  a↓ : ∀ {x} → (A x) → (A (↓ x))
  a↓↑ : ∀ {x} → (a : A x) → PathP (λ i → A (↓↑ x i)) (a↓ (a↑ a)) a
  a↑↓ : ∀ {x} → (a : A x) → PathP (λ i → A (↑↓ x i)) (a↑ (a↓ a)) a
  a♯ :  ∀ {x} → (a : A x) →
              PathP (λ i → A (♯ x i))
                (a↑ (a↑ a))
                (a↑ (a↑ a))
  a↑♯≡♯↑ : ∀ {x} → (a : A x) →
              SquareP (λ j i → A (↑♯≡♯↑ x j i))
                (λ i → a♯ (a↑ a) i)
                (λ i → a↑ (a♯ a i))
                refl
                refl
  atrunc : ∀ x → isGroupoid (A x)

 f : ∀ x → A x
 f 𝟘 = abase
 f (↑ x) = a↑ (f x) 
 f (↓ x) = a↓ (f x)
 f (↓↑ x i) = a↓↑ (f x) i
 f (↑↓ x i) = a↑↓ (f x) i
 f (♯ x i) = a♯ (f x) i
 f (↑♯≡♯↑ x j i) = a↑♯≡♯↑ (f x) j i
 f (trunc _ _ _ _ r s i i₁ i₂) =
   isOfHLevel→isOfHLevelDep 3 (atrunc)
     _ _ _ _ 
     (λ j k → f (r j k)) (λ j k → f (s j k))
     (trunc _ _ _ _ r s) i i₁ i₂

record Co-rec {ℓ} (A : Type ℓ) : Type ℓ where
 no-eta-equality
 field
  abase : A
  a↑ a↓ : A → A
  a↓↑ : ∀ a → (a↓ (a↑ a)) ≡ a
  a↑↓ : ∀ a → (a↑ (a↓ a)) ≡ a
  a♯ :  ∀ a → (a↑ (a↑ a)) ≡ (a↑ (a↑ a))
  a↑♯≡♯↑ : ∀ a → Square (λ i → a♯ (a↑ a) i) (λ i → a↑ (a♯ a i))
                refl
                refl
  atrunc : isGroupoid A

 f : Co → A
 f 𝟘 = abase
 f (↑ x) = a↑ (f x) 
 f (↓ x) = a↓ (f x)
 f (↓↑ x i) = a↓↑ (f x) i
 f (↑↓ x i) = a↑↓ (f x) i
 f (♯ x i) = a♯ (f x) i
 f (↑♯≡♯↑ x j i) = a↑♯≡♯↑ (f x) j i
 f (trunc _ _ _ _ r s i i₁ i₂) =
  atrunc _ _ _ _
    (λ i i₁ → f (r i i₁))
    (λ i i₁ → f (s i i₁)) i i₁ i₂
    
record Co-elimSet {ℓ} (A : Co → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  abase : A 𝟘
  a↑ : ∀ {x} → (A x) → (A (↑ x))
  a↓ : ∀ {x} → (A x) → (A (↓ x))
  a↓↑ : ∀ {x} → (a : A x) → PathP (λ i → A (↓↑ x i)) (a↓ (a↑ a)) a
  a↑↓ : ∀ {x} → (a : A x) → PathP (λ i → A (↑↓ x i)) (a↑ (a↓ a)) a
  a♯ :  ∀ {x} → (a : A x) →
              PathP (λ i → A (♯ x i))
                (a↑ (a↑ a))
                (a↑ (a↑ a))
  atrunc : ∀ x → isSet (A x)

 r : Co-elim (λ z → A z)
 Co-elim.abase r = abase
 Co-elim.a↑ r = a↑
 Co-elim.a↓ r = a↓
 Co-elim.a↓↑ r = a↓↑
 Co-elim.a↑↓ r = a↑↓
 Co-elim.a♯ r = a♯
 Co-elim.a↑♯≡♯↑ r _ = isSet→SquareP (λ j i → atrunc (↑♯≡♯↑ _ j i)) _ _ _ _
 Co-elim.atrunc r = isSet→isGroupoid ∘ atrunc

 f : ∀ x → A x
 f = Co-elim.f r


record Co-elimProp {ℓ} (A : Co → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  abase : A 𝟘
  a↑ : ∀ {x} → (A x) → (A (↑ x))
  a↓ : ∀ {x} → (A x) → (A (↓ x))
  atrunc : ∀ x → isProp (A x)

 r : Co-elimSet (λ z → A z)
 Co-elimSet.abase r = abase
 Co-elimSet.a↑ r = a↑
 Co-elimSet.a↓ r = a↓
 Co-elimSet.a↓↑ r _ = isProp→PathP (λ i → atrunc (↓↑ _ i)) _ _
 Co-elimSet.a↑↓ r _ = isProp→PathP (λ i → atrunc (↑↓ _ i)) _ _
 Co-elimSet.a♯ r _ = isProp→PathP (λ i → atrunc (♯ _ i)) _ _
 Co-elimSet.atrunc r = isProp→isSet ∘ atrunc
 
 f : ∀ x → A x
 f = Co-elimSet.f r


♯ₑ : ↑ ∘ ↑ ≡ ↑ ∘ ↑
♯ₑ = funExt ♯

↑Iso : Iso Co Co
Iso.fun ↑Iso = ↑
Iso.inv ↑Iso = ↓
Iso.rightInv ↑Iso = ↑↓
Iso.leftInv ↑Iso = ↓↑

↑≃ : Co ≃ Co
↑≃ = isoToEquiv ↑Iso

↓≃ : Co ≃ Co
↓≃ = isoToEquiv (invIso ↑Iso)

-- ↓' : Co → Co
-- ↓' = Co-rec.f w
--  where
--  open Co-elim
--  w : Co-elim ?
--  abase w = ↓ 𝟘
--  a↑ w x = {!!}
--  a↓ w = {!!}
--  a↓↑ w = {!!}
--  a↑↓ w = {!!}
--  a♯ w = {!!}
--  a↑♯≡♯↑ w = {!!}
--  atrunc w = {!!}

Co≡ : Co ≡ Co
Co≡ = ua ↑≃

♯≃ : ↑≃ ∙ₑ ↑≃ ≡ ↑≃ ∙ₑ ↑≃
♯≃ = equivEq (funExt ♯)

-- ♯≃-diag6 : ↑≃ ∙ₑ ↑≃ ∙ₑ ↑≃ ≡ ↑≃ ∙ₑ ↑≃ ∙ₑ ↑≃
-- ♯≃-diag6 = equivEq (funExt ⇅⇅⇅-diag)


-- ♯6-U : Square {A = Co ≃ Co}
--           (cong (↑≃ ∙ₑ_) ♯≃)
--           ♯≃-diag6
--           (equivEq (cong fst (cong (_∙ₑ ↑≃) ♯≃)))
--           (equivEq (cong fst (cong (_∙ₑ ↑≃) ♯≃)))
-- ♯6-U =
--   ΣSquarePSet (λ i j a → isProp→isSet (isPropIsEquiv a))
--     _ _ _ _ λ i j x → ⇅⇅⇅-U x i j

-- ♯6-D : Square {A = Co ≃ Co}
--           ♯≃-diag6
--           (equivEq (cong fst (cong (_∙ₑ ↑≃) ♯≃)))
--           (cong (↑≃ ∙ₑ_) ♯≃)
--           (cong (↑≃ ∙ₑ_) ♯≃)
          
-- ♯6-D =
--     ΣSquarePSet (λ i j a → isProp→isSet (isPropIsEquiv a))
--     _ _ _ _ λ i j x → ⇅⇅⇅-D x i j


-- ↑♯≡♯↑ :  congP (λ _ →  _∘' ↑) ♯ₑ ≡ congP (λ _ → ↑ ∘'_) ♯ₑ
-- ↑♯≡♯↑ = whiskSq.sq' _
--    {!!}
--    (λ i l x → ⇅⇅⇅-D x i l )
--    {!!} {!!} {!!}


-- -- G♯6 : Cube
-- --        {!!}
-- --        {!!}
-- --        {!!}
-- --        {!!}
-- --        {!!}
-- --        {!!} 
-- -- G♯6 i j k =
-- --   Glue {!!}
-- --        {!!}

CodeJ₃S¹-pa : ∀ i j → Partial (i ∨ ~ i ∨ j ∨ ~ j)
        (Σ Type (λ T → T ≃ Co))
CodeJ₃S¹-pa i j =
   λ {  (i = i0) → Co≡ j ,
                ua-unglueEquiv ↑≃ j ∙ₑ ♯≃ j
          ; (i = i1) → Co≡ j ,
                ua-unglueEquiv ↑≃ j ∙ₑ ↑≃ 
          ; (j = i0) → Co≡ i ,
                        (↑ ∘ ↑) ∘ fst (ua-unglueEquiv ↑≃ i) ,
                        isProp→PathP
                          (λ i → isPropIsEquiv
                            ((↑ ∘ ↑) ∘ fst (ua-unglueEquiv ↑≃ i)))
                          (snd (compEquiv ↑≃ (↑≃ ∙ₑ ↑≃)))
                          (snd (compEquiv ↑≃ ↑≃))
                           i

          ; (j = i1) → Co≡ i ,
                        ↑ ∘ fst (ua-unglueEquiv ↑≃ i) ,
                        isProp→PathP
                          (λ i → isPropIsEquiv
                            (↑ ∘ fst (ua-unglueEquiv ↑≃ i)))
                          (snd (compEquiv (idEquiv Co) (↑≃ ∙ₑ ↑≃)))
                          (snd (compEquiv (idEquiv Co) ↑≃))
                           i
          }




CoSq : Square Co≡ Co≡ Co≡ Co≡
CoSq i j =
    Glue Co {i ∨ ~ i ∨ j ∨ ~ j}
       (CodeJ₃S¹-pa i j)

CoSq' : Square (ua (↑≃ ∙ₑ ↑≃)) (ua (↑≃ ∙ₑ ↑≃)) refl refl
CoSq' = cong ua ♯≃


-- ∙ₑfiller : Square Co≡ (ua (↑≃ ∙ₑ ↑≃))
--                   refl
--                   Co≡
-- ∙ₑfiller = {!!}

-- ∙ₑfiller' : Square Co≡ (ua (↑≃ ∙ₑ ↑≃))
                  
--                   (sym Co≡)
--                   refl
-- ∙ₑfiller' = {!!}


-- CoSq≡CoSq' : Cube CoSq CoSq'
--                ∙ₑfiller
--                ∙ₑfiller'
--                (λ j i → Co≡ (~ j ∧ i))
--                λ j i → Co≡ (j ∨ i)
-- CoSq≡CoSq' = {!!}


-- uaGlue-rhomb : ∀ {ℓ} {A : Type ℓ} → (e : A ≃ A) →
--                  Square (ua e) (ua e) (ua e) (ua e) 
-- uaGlue-rhomb {A = A} e i j =
--    Glue A
--       λ {  (i = i0) → ua e j , ua-unglueEquiv e j ∙ₑ e
   
--            ; (i = i1) → ua e j , ua-unglue e j , {!!}
--           ; (j = i0) → ua e i , ua-unglueEquiv e i ∙ₑ e

--           ; (j = i1) → ua e i , ua-unglue e i , {!!}
--           }

-- invSidesFiller₃ :  ∀ {ℓ} {A : Type ℓ} →
--                   (a : A) →
--                   (p : a ≡ a)
--                   (s : Square p p p p)
--                   → Cube s s s s s s
-- invSidesFiller₃ = {!!}




-- record Bd₂P {ℓ} (A : I → I → Type ℓ) : Type ℓ where
--  field
--   a₀₋ : ∀ i → A i0 i 
--   a₁₋ : ∀ i → A i1 i
--   a₋₀ : PathP (λ j → A j i0) (a₀₋ i0) (a₁₋ i0)
--   a₋₁ : PathP (λ j → A j i1) (a₀₋ i1) (a₁₋ i1)

--  Inside : Type ℓ
--  Inside = SquareP A (λ i → a₀₋ i) (λ i → a₁₋ i) a₋₀ a₋₁

-- open Bd₂P

-- mapBd₂P : ∀ {ℓ ℓ'}
--              {A : I → I → Type ℓ}
--              {A' : I → I → Type ℓ'}
--              → (∀ i j → A i j → A' i j)
--              → Bd₂P A → Bd₂P A' 
-- Bd₂P.a₀₋ (mapBd₂P f x) i = f i0 i (Bd₂P.a₀₋ x i)
-- Bd₂P.a₁₋ (mapBd₂P f x) i = f i1 i (Bd₂P.a₁₋ x i)
-- Bd₂P.a₋₀ (mapBd₂P f x) j = f j i0 (Bd₂P.a₋₀ x j)
-- Bd₂P.a₋₁ (mapBd₂P f x) j = f j i1 (Bd₂P.a₋₁ x j)

-- -- bd-ung-♯ : Bd₂P λ _ _ → Co → Co
-- -- a₀₋ bd-ung-♯ i = funExt ♯ i
-- -- a₁₋ bd-ung-♯ _ = ↑
-- -- a₋₀ bd-ung-♯ _ = {!!}
-- -- a₋₁ bd-ung-♯ _ = {!↑!}


ung↑ : PathP (λ i → ua ↑≃ i → Co) (↑) (idfun Co)
ung↑ = ua-ungluePathExt ↑≃

ung↑≃ : PathP (λ i → ua ↑≃ i ≃ Co) (↑≃) (idEquiv Co)
ung↑≃ = ua-unglueEquiv ↑≃

ung♯ : SquareP (λ i k → CoSq i k → Co)
                          (λ k x → ♯ (ung↑ k x) k)
                          (λ k x → ↑ (ung↑ k x))
                          (λ i x → ↑ (↑ (ung↑ i x)))
                          (λ i x → ↑ (ung↑ i x))
ung♯ i k = unglue (i ∨ ~ i ∨ k ∨ ~ k)

-- ung♯≃ : SquareP (λ i k → CoSq i k ≃ Co)
--                           (λ k x → ♯ (ung↑ k x) k)
--                           (λ k x → ↑ (ung↑ k x))
--                           (λ i x → ↑ (↑ (ung↑ i x)))
--                           (λ i x → ↑ (ung↑ i x))
-- ung♯≃ i k = unglueEquiv (i ∨ ~ i ∨ k ∨ ~ k) ?


ung♯' : SquareP (λ i k → CoSq i k → Co)
                          (λ k x → ↑ (↑ (ung↑ k x)))
                          (λ k x → ↑ (ung↑ k x))
                          (λ i x → ↑ (↑ (ung↑ i x)))
                          (♯ₑ ◁ (λ i x → ↑ (ung↑ i x)))
ung♯' i k =
   hcomp
     (λ l → λ {
       (i = i0) → ♯ₑ (~ l ∧ k) ∘' ung↑ k
      ;(i = i1) → ↑ ∘' ung↑ k
      ;(k = i0) → ↑ ∘' ↑ ∘' ung↑ i
       })
     (unglue (i ∨ ~ i ∨ k ∨ ~ k))

ung♯'' : SquareP (λ i k → CoSq i k → Co)
                          (λ k x → ↑ (↑ (ung↑ k x)))
                          (sym ♯ₑ ◁ λ k x → ↑ (ung↑ k x))
                          (λ i x → ↑ (↑ (ung↑ i x)))
                          (λ i x → ↑ (ung↑ i x))
ung♯'' i k = hcomp
      (λ l → λ {
         (i = i0) → ♯ₑ (k ∨ l) ∘' ung↑ k
        ;(k = i0) → ♯ₑ l ∘' (ung↑ i)
        ;(k = i1) → ↑ ∘' (ung↑ i)
        })
      (ung♯ i k)


ung♯* : SquareP (λ k i → CoSq k i → Co)
                          (λ i x →  ↑ (↑ (ung↑ i x)))
                          ((sym ♯ₑ ◁ (λ k₁ x₁ → ↑ (ung↑ k₁ x₁))))
                          (λ k x → ↑ ((♯ₑ ◁ (congP (λ _ → ↑ ∘'_) (ung↑))) k x))
                          (♯ₑ ◁ (congP (λ _ → ↑ ∘'_) (ung↑)))
ung♯* k i =
   hcomp (λ l → 
        λ { (k = i0) → hcomp
               (λ l' → λ {
                 (l = i0) → ↑ ∘' ↑ ∘' ung↑ i
                ;(l = i1) → ↑ ∘' ↑ ∘' ung↑ i
                ;(i = i0) → λ x → ↑♯≡♯↑ x l' (~ l)
                ;(i = i1) → ♯ₑ (~ l)
                   })
               (♯ₑ (~ l) ∘' ung↑ i)
          ; (k = i1) → (sym ♯ₑ ◁ (congP (λ _ → ↑ ∘'_) (ung↑))) i
          ; (i = i0) → ↑ ∘'
            doubleWhiskFiller {A = λ i → Co≡ i → Co}
              ♯ₑ (congP (λ _ → ↑ ∘'_) (ung↑)) refl l k
          })
     (ung♯'' k i)


CoCu : Cube CoSq CoSq CoSq CoSq CoSq CoSq
CoCu k j i = 
    Glue Co
       λ {  (k = i0) → CoSq j i ,
                       (λ x → ↑ (ung♯ j i x)) ,
                       {!!}
                                                
          ; (j = i0) → CoSq k i ,
                       (λ x → ↑ (ung♯ k i x)) , --↑ (ung♯ k i x)
                       {!!}
                       -- fst (♯6-U k j) ∘' ung♯ k j ,
                       -- {!!}
                       -- -- unglueEquiv Co (j ∨ ~ j ∨ k ∨ ~ k ) (CodeJ₃S¹-pa j k)
                       -- --  ∙ₑ ♯6-U k j
          ; (i = i0) → CoSq k j ,
                       (λ x → ↑ (ung♯' k j x)) ,
                       {!!} 
                       -- CodeJ₃S¹J0 k i  ,
                       -- {!!}
          ; (k = i1) → CoSq j i ,
                    (λ x → ung♯'' j i x) ,  --(λ x → ung♯ j i x) ,
                    {!!}
          ; (j = i1) → CoSq k i ,
                        (ung♯* k i) , --(λ x → ung♯ k i x) ,
                        {!!}
          ; (i = i1) → CoSq k j ,
                     (λ x →  ung♯' k j x) ,
                    -- (λ x → fst (♯6-D (~ i) j) (ung♯ j i x)) ,
                    {!!}
                    -- fst (♯6-D (~ i) j) ∘'
                    -- fst (unglueEquiv Co (i ∨ ~ i ∨ j ∨ ~ j ) (CodeJ₃S¹-pa i j))
                    -- , {!!}
          }
  


-- -- CoCu : Cube CoSq CoSq CoSq CoSq CoSq CoSq
-- -- CoCu = {!!}


CodeJ₃S¹* : J₃S¹ → ∥ Type ∥₄
CodeJ₃S¹* = J₃S¹-rec.f w
 where
 open J₃S¹-rec
 w : J₃S¹-rec (∥ Type ∥₄)
 abase w = ∣ Co ∣₄
 aloop w = cong (λ x → ∣ x ∣₄) Co≡
 aloop₂ w = congSq (λ x → ∣ x ∣₄) CoSq
 aloop₃ w k j i = ∣ CoCu k j i ∣₄ 
 atrunc w = squash₄

isGrp₄ : ∥ Type ∥₄ → hProp ℓ-zero
isGrp₄ = rec (isOfHLevelPlus {n = 2} 2 isSetHProp)
   λ T → isGroupoid T , isPropIsOfHLevel 3


CodeJ₃S¹** : ∀ x → fst (isGrp₄ (CodeJ₃S¹* x))
CodeJ₃S¹** = J₃S¹-elimProp.f w
 where
 w : J₃S¹-elimProp _
 J₃S¹-elimProp.abase w = trunc
 J₃S¹-elimProp.atrunc w = snd ∘ isGrp₄ ∘ CodeJ₃S¹*

fromIsGrp₄ : ∀ x → fst (isGrp₄ x) → hGroupoid ℓ-zero 
fromIsGrp₄ = elim (λ x → isOfHLevelΠ 4 λ _ → isOfHLevelTypeOfHLevel 3)
  (_,_)


CodeJ₃S¹ : J₃S¹ → Type
CodeJ₃S¹ x = fst (fromIsGrp₄ (CodeJ₃S¹* x) (CodeJ₃S¹** x))



p∙[p⁻∙q]≡q : ∀ {ℓ} {A : Type ℓ} → {x y : A} → (p q : x ≡ y) → 
              p ∙ (sym p ∙ q) ≡ q
p∙[p⁻∙q]≡q p q i j =
   hcomp ( λ k → 
          λ { (j = i0) → p i0
            ; (j = i1) → compPath-filler' (sym p) q (~ i) k
            ; (i = i1) → q (k ∧ j)
            }) (p (j ∧ ~ i))

encode : ∀ x → base ≡ x → CodeJ₃S¹ x
encode x p = subst CodeJ₃S¹ p 𝟘


module hlp∙ {ℓ} {A : Type ℓ} {a b c d e f : A}  {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d} {u : e ≡ f} {v : d ≡ e} {w : d ≡ f} where

 sq : (S : Square r s p q) → (Q : Square v w refl u)
         → Square (p ∙ s ∙ v)
                  (r ∙ q ∙ w)
                 (λ _ → a)
                 u
 sq S Q  i = (λ j' → S (j' ∧ ~ i) (j' ∧ i))
           ∙ (λ j' → S (j' ∨ ~ i) (j' ∨ i)) ∙ Q i


loopSq : ∀ q → Square {A = J₃S¹}
             (loop ∙ loop ∙ q)
             (loop ∙ loop ∙ q)
             (λ _ → base)
             (λ _ → base)
loopSq q = hlp∙.sq loop₂ refl 


loopCu : (q : Path J₃S¹ base base) → Square {A = Path J₃S¹ base base}
           (loopSq (loop ∙ q))
           (λ j → loop ∙ loopSq (q) j)
           (refl {x = loop ∙ loop ∙ loop ∙ q})
           (refl {x = loop ∙ loop ∙ loop ∙ q})
loopCu q i j k =
    hcomp (λ l → λ {
          (i = i0) → loopSq (loop ∙ q) j (k ∧ l)
         ;(k = i0) → ff (~ k) i l
         ;(k = i1) → hlp∙.sq (loop₃ i) (λ _ → compPath-filler' loop q (~ i))
                        j l
         ;(j = i0) → ff (~ k) i l
         ;(j = i1) → ff (~ k) i l
         ;(i = i1) → compPath-filler loop (loopSq q j) l k
         })
         (loop (i ∧ k))

 where
  ff = whiskSq.sq'-fill (λ _ _ → J₃S¹)
    (λ i l → (loop₂ i ∙ loop₂ i ∙ compPath-filler' loop q (~ i)) l)
     
     (λ l k → (loop ∙ loop ∙ loop ∙ q) ((~ k) ∧ l))
     (λ l k → compPath-filler loop (loop ∙ loop ∙ q) l (~ k))
     (λ i k → loop (i ∧ (~ k)))
     λ i → sym (loop ∙ (loop ∙ loop ∙ q))

CoLoop : Co → Path J₃S¹ base base
CoLoop = Co-rec.f w
 where
 open Co-rec
 w : Co-rec _
 abase w = refl
 a↑ w = loop ∙_
 a↓ w = _∙ sym loop
 a↓↑ w a = {!!}
 a↑↓ w a = {!!}
 a♯ w = {!!}
 a↑♯≡♯↑ w = {!!}
 atrunc w = trunc base base

-- CoLoopComm : ∀ co → Square {A = J₃S¹}
--     (CoLoop co)
--     (CoLoop co)
--     loop
--     loop
-- CoLoopComm = Co-elimSet.f w
--  where
--  w : Co-elimSet _
--  Co-elimSet.abase w i _ = loop i
--  Co-elimSet.a↑ w s j = (loop₂ j ∙ s j)
--  Co-elimSet.a↓ w s j = sym (loop₂ j) ∙ s j
--  Co-elimSet.a↓↑ w s i j = p∙[p⁻∙q]≡q (sym (loop₂ j)) (s j) i
--  Co-elimSet.a↑↓ w s i j = p∙[p⁻∙q]≡q (loop₂ j) (s j) i
--  Co-elimSet.a♯ w s i j = hlp∙.sq (loop₃ j) (λ _ → s j) i
--  Co-elimSet.atrunc w x =
--    isOfHLevelPathP' 2
--     (trunc base base)
--      _ _
  
-- module CoLoopSqM = whiskSq _
--     (λ i j → (λ x → CoLoop x j) ∘' ung↑ i)
--     (λ j l x → compPath-filler' loop (CoLoop x) (~ l) j)
--     (λ j l x → CoLoopComm x l j)
--     (λ i l x → loop l)
--     (λ i l x → loop (i ∧ l))


-- CoLoopSq : SquareP (λ i j → Co≡ i → J₃S¹ )
--    (λ j p → CoLoop p j)
--    (λ j p → CoLoop p j)
--    (λ _ _ → base)
--    (λ i _ → loop i)
-- CoLoopSq = CoLoopSqM.sq' 

-- CoLoopSq' : SquareP (λ i j → Co≡ i → J₃S¹ )
--    (λ j p → CoLoop p j)
--    (λ j p → CoLoop p j)
--    (λ _ _ → base)
--    (λ i _ → loop i)
-- CoLoopSq' = {!!}


-- -- SquarePCong≃ : ∀ {ℓ ℓ'}
-- --   {A : I → I → Type ℓ}
-- --   {A' : I → I → Type ℓ'}
-- --   {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
-- --   {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
-- --   {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
-- --   → (e : ∀ i j → A' i j ≃ A i j)
-- --   → SquareP A'
-- --         (congP (λ j → invEq (e i0 j)) a₀₋)
-- --         (congP (λ j → invEq (e i1 j)) a₁₋)
-- --         (congP (λ i → invEq (e i i0)) a₋₀)
-- --         (congP (λ i → invEq (e i i1)) a₋₁)
        
-- --   → SquareP A a₀₋ a₁₋ a₋₀ a₋₁ 
-- -- SquarePCong≃ e s =
-- --  whiskSq.sq' _
-- --   (λ i j → fst (e i j) (s i j))
-- --   (λ j → secEq (e i0 j ) _)
-- --   (λ j → secEq (e i1 j ) _)
-- --   (λ i → secEq (e i i0 ) _)
-- --   (λ i → secEq (e i i1 ) _)



-- -- CoLoopCu≃ : ∀ j i → (Co → base ≡ loop₂ j i) ≃
-- --                              (CoSq j i → base ≡ loop₂ j i) 
-- --     -- SquareP (λ j i → (Co → base ≡ loop₂ j i) ≃
-- --     --                          (CoSq j i → base ≡ loop₂ j i) )

-- --     --               (λ i → preCompEquiv (fst (CodeJ₃S¹-pa i0 i 1=1 .snd) , {!!} ))
-- --     --               (λ i → preCompEquiv {!!})
-- --     --               (λ j → preCompEquiv (CodeJ₃S¹-pa j i0 1=1 .snd))
-- --     --               (λ j → preCompEquiv (CodeJ₃S¹-pa j i1 1=1 .snd))

-- --                   -- (λ i → preCompEquiv ((λ x → ♯ (ung↑ i x) i) , {!!}))
-- --                   -- (λ i → preCompEquiv ((λ x → ↑ (ung↑ i x) ) , {!!}))
-- --                   -- (λ j → preCompEquiv ((λ x → ↑ (↑ (ung↑ j x)) ) , {!!}))
-- --                   -- (λ j → preCompEquiv ((λ x → (↑ (ung↑ j x)) ) , {!!}))

-- -- CoLoopCu≃ j i =
-- --   preCompEquiv
-- --   (unglueEquiv Co _ (CodeJ₃S¹-pa j i))

-- -- -- CoLoopCu : SquareP (λ j i → CodeJ₃S¹ (loop₂ j i) → base ≡ loop₂ j i)
-- -- --       (λ i p j → CoLoopSq i j p)
-- -- --       (λ i p j → CoLoopSq i j p)
-- -- --       (λ i p j → CoLoopSq i j p)
-- -- --       (λ i p j → CoLoopSq i j p)
-- -- -- CoLoopCu =
-- -- --   SquarePCong≃
-- -- --      (λ j i → invEquiv (unglueEquiv (Co → base ≡ loop₂ j i)
-- -- --                (j ∨ ~ j ∨ i ∨ ~ i)
-- -- --                 λ o → ((fst (CodeJ₃S¹-pa j i o)) → base ≡ loop₂ j i) ,
-- -- --                   invEquiv (preCompEquiv {C = base ≡ loop₂ j i}
-- -- --                     ((snd (CodeJ₃S¹-pa j i o)))))
-- -- --                ∙ₑ domGlue (base ≡ loop₂ j i) Co
-- -- --               (j ∨ ~ j ∨ i ∨ ~ i) (CodeJ₃S¹-pa j i))
      
-- -- --    (funExtSq _ _ _ _ (Co-elimProp.f w))
-- -- --  where
-- -- --  open Co-elimProp
-- -- --  w : Co-elimProp _
-- -- --  abase w i j k = {!!}
-- -- --  a↑ w = {!!}
-- -- --  a↓ w = {!!}
-- -- --  atrunc w _ =
-- -- --    isOfHLevelPathP' 1
-- -- --     (isOfHLevelPathP' 2
-- -- --       (trunc base base)
-- -- --       _ _)
-- -- --     _ _


-- -- CoLoopCu' : SquareP (λ j i → CodeJ₃S¹ (loop₂ j i) → base ≡ loop₂ j i)
-- --       (λ i p j → CoLoopSq i j p)
-- --       (λ i p j → CoLoopSq i j p)
-- --       (λ i p j → CoLoopSq i j p)
-- --       (λ i p j → CoLoopSq i j p)
-- -- CoLoopCu' =
-- --   SquarePCong≃
-- --      (λ j i → preCompEquiv
-- --       (unglueEquiv Co _ (CodeJ₃S¹-pa j i)))
-- --    (funExtSq _ _ _ _ (Co-elimProp.f w))
-- --  where
-- --  open Co-elimProp
-- --  w : Co-elimProp _
-- --  abase w i j k = {!!}
-- --  a↑ w = {!!}
-- --  a↓ w = {!!}
-- --  atrunc w _ =
-- --    isOfHLevelPathP' 1
-- --     (isOfHLevelPathP' 2
-- --       (trunc base base)
-- --       _ _)
-- --     _ _
 
-- -- -- decode : ∀ x → CodeJ₃S¹ x → base ≡ x
-- -- -- decode = J₃S¹-elimGrp.f w
-- -- --  where
-- -- --  w : J₃S¹-elimGrp (λ z → CodeJ₃S¹ z → base ≡ z)
-- -- --  J₃S¹-elimGrp.abase w = CoLoop
-- -- --  J₃S¹-elimGrp.aloop w i p j = CoLoopSq i j p 
-- -- --  J₃S¹-elimGrp.aloop₂ w = CoLoopCu
-- -- --  J₃S¹-elimGrp.atrunc w x = isGroupoidΠ λ _ → trunc base x

-- -- -- decode↑ : ∀ x → decode base (↑ x) ≡ loop ∙ decode base x
-- -- -- decode↑ x = refl

-- -- -- subst-CodeJ₃S¹-loop-base : ∀ x → subst CodeJ₃S¹ loop x ≡ ↑ x
-- -- -- subst-CodeJ₃S¹-loop-base x = refl

-- -- -- comm-lopp-decode : ∀ x → loop ∙ decode base x ≡ decode base x ∙ loop
-- -- -- comm-lopp-decode = Co-elimSet.f w
-- -- --  where
-- -- --  open Co-elimSet
-- -- --  w : Co-elimSet _
-- -- --  abase w i = (λ j → loop (j ∧ (~ i))) ∙ λ j → loop (j ∨ (~ i))
-- -- --  a↑ w p = cong (loop ∙_) p ∙ assoc _ _ _
   
-- -- --  a↓ w p = {!!}
-- -- --  a↓↑ w = {!!}
-- -- --  a↑↓ w = {!!}
-- -- --  a♯ w = {!!}
-- -- --  atrunc w x = trunc _ _ _ _
 
-- -- -- encode-base-[decode-base-↑] : ∀ x →
-- -- --   encode base (decode base (↑ x)) ≡
-- -- --      ↑ (encode base (decode base x))
-- -- -- encode-base-[decode-base-↑] x =       
-- -- --    cong (encode base) (comm-lopp-decode x)
-- -- --    ∙ substComposite CodeJ₃S¹ (decode base x) loop 𝟘 

-- -- -- decode-encode : ∀ x y → decode x (encode x y) ≡ y
-- -- -- decode-encode _ = J (λ x y → decode x (encode x y) ≡ y) refl

-- -- -- encode-decode : ∀ x y → encode x (decode x y) ≡ y
-- -- -- encode-decode = J₃S¹-elimSet.f w
-- -- --  where
-- -- --  open J₃S¹-elimSet
-- -- --  w : J₃S¹-elimSet _
-- -- --  abase w = Co-elimSet.f ww
-- -- --   where
-- -- --   ww : Co-elimSet _
-- -- --   Co-elimSet.abase ww = refl
-- -- --   Co-elimSet.a↑ ww {x} p = encode-base-[decode-base-↑] x ∙ cong ↑ p
-- -- --   Co-elimSet.a↓ ww p = {!!} ∙ cong ↓ p
-- -- --   Co-elimSet.a↓↑ ww p = {!!}
-- -- --   Co-elimSet.a↑↓ ww p = {!!}
-- -- --   Co-elimSet.a♯ ww p = {!!}
-- -- --   Co-elimSet.atrunc ww x = trunc _ _
-- -- --  aloop w = {!!}
-- -- --  atrunc w x = isSetΠ λ _ → snd (fromIsGrp₄ (CodeJ₃S¹* x) (CodeJ₃S¹** x)) _ _

-- -- -- -- -- -- -- -- -- -- -- loop₃' : Cube loop₂ loop₂ loop₂ loop₂ loop₂ loop₂
-- -- -- -- -- -- -- -- -- -- -- loop₃' = loop₃

-- -- -- -- -- -- -- -- -- -- -- J₃S¹-hexa₀ J₃S¹-hexa₁ : (loop ∙∙ loop ∙∙ loop) ≡ (loop ∙∙ loop ∙∙ loop)
-- -- -- -- -- -- -- -- -- -- -- J₃S¹-hexa₀ = {!!}
-- -- -- -- -- -- -- -- -- -- -- J₃S¹-hexa₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- J₃S¹-hexa : Path ((loop ∙∙ loop ∙∙ loop) ≡ (loop ∙∙ loop ∙∙ loop))
-- -- -- -- -- -- -- -- -- -- --             {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- J₃S¹-hexa = {!!}

-- -- -- -- -- -- -- -- -- -- -- infixl 6 _⊕_

-- -- -- -- -- -- -- -- -- -- -- infixl 10 ─_


-- -- -- -- -- -- -- -- -- -- -- data ℤᵍ : Type where
-- -- -- -- -- -- -- -- -- -- --  zero one  : ℤᵍ
-- -- -- -- -- -- -- -- -- -- --  _⊕_ : ℤᵍ → ℤᵍ → ℤᵍ
-- -- -- -- -- -- -- -- -- -- --  ─_ : ℤᵍ → ℤᵍ
-- -- -- -- -- -- -- -- -- -- --  ⊕─ : ∀ x → x ⊕ ─ x ≡ zero

-- -- -- -- -- -- -- -- -- -- --  ⊕-assoc : ∀ x y z → x ⊕ (y ⊕ z) ≡ x ⊕ y ⊕ z
 
-- -- -- -- -- -- -- -- -- -- --  zero-⊕ : ∀ x → zero ⊕ x ≡ x
-- -- -- -- -- -- -- -- -- -- --  ⊕-zero : ∀ x → x ⊕ zero ≡ x

-- -- -- -- -- -- -- -- -- -- --  ⊕-triangle : ∀ x y  →
-- -- -- -- -- -- -- -- -- -- --     Square                      
-- -- -- -- -- -- -- -- -- -- --         (⊕-assoc x zero y)
-- -- -- -- -- -- -- -- -- -- --         refl
-- -- -- -- -- -- -- -- -- -- --         (cong (x ⊕_) (zero-⊕ y))
-- -- -- -- -- -- -- -- -- -- --         (cong (_⊕ y) (⊕-zero x))
        


-- -- -- -- -- -- -- -- -- -- --  ⊕-penta-diag : ∀ x y z w →
-- -- -- -- -- -- -- -- -- -- --    x ⊕ y ⊕ z ⊕ w ≡ x ⊕ (y ⊕ (z ⊕ w))
-- -- -- -- -- -- -- -- -- -- --  ⊕-penta-△ : ∀ x y z w →
-- -- -- -- -- -- -- -- -- -- --    Square
-- -- -- -- -- -- -- -- -- -- --      refl
-- -- -- -- -- -- -- -- -- -- --      (⊕-penta-diag x y z w)
-- -- -- -- -- -- -- -- -- -- --      (⊕-assoc _ _ _)
-- -- -- -- -- -- -- -- -- -- --      (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- -- -- --  ⊕-penta-□ : ∀ x y z w →
-- -- -- -- -- -- -- -- -- -- --     Square
-- -- -- -- -- -- -- -- -- -- --      (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- -- -- --      (⊕-penta-diag x y z w)
-- -- -- -- -- -- -- -- -- -- --      (cong (_⊕ w) (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- -- -- --      (cong (x ⊕_) (sym (⊕-assoc _ _ _)))

-- -- -- -- -- -- -- -- -- -- --  -- ⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
-- -- -- -- -- -- -- -- -- -- --  -- ⊕-hexa-diag : ∀ x y z → x ⊕ y ⊕ z ≡ y ⊕ (z ⊕ x)
-- -- -- -- -- -- -- -- -- -- --  -- ⊕-hexa-↑ : ∀ x y z →
-- -- -- -- -- -- -- -- -- -- --  --   Square
-- -- -- -- -- -- -- -- -- -- --  --      (⊕-comm x (y ⊕ z))
-- -- -- -- -- -- -- -- -- -- --  --      (⊕-hexa-diag x y z)
-- -- -- -- -- -- -- -- -- -- --  --      (⊕-assoc _ _ _)
-- -- -- -- -- -- -- -- -- -- --  --      (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- -- -- --  -- ⊕-hexa-↓ : ∀ x y z →
-- -- -- -- -- -- -- -- -- -- --  --    Square
-- -- -- -- -- -- -- -- -- -- --  --       (⊕-hexa-diag x y z)
-- -- -- -- -- -- -- -- -- -- --  --       (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- -- -- --  --       (cong (_⊕ z) (⊕-comm _ _))
-- -- -- -- -- -- -- -- -- -- --  --       (cong (y ⊕_) (⊕-comm _ _))

-- -- -- -- -- -- -- -- -- -- --  ⊕-comm : one ⊕ one ≡ one ⊕ one
-- -- -- -- -- -- -- -- -- -- --  ⊕-comm-assoc : one ⊕ (one ⊕ one) ≡ one ⊕ one ⊕ one 

-- -- -- -- -- -- -- -- -- -- --  ⊕-comp : Square
-- -- -- -- -- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- -- -- -- -- --            {!!}

-- -- -- -- -- -- -- -- -- -- --  -- ⊕-hexa-diag : one ⊕ one ⊕ one ≡ one ⊕ (one ⊕ one)
-- -- -- -- -- -- -- -- -- -- --  -- ⊕-hexa-L : 
-- -- -- -- -- -- -- -- -- -- --  --   Square
-- -- -- -- -- -- -- -- -- -- --  --      (cong (one ⊕_) ⊕-comm)
-- -- -- -- -- -- -- -- -- -- --  --      (cong (_⊕ one) ⊕-comm)
-- -- -- -- -- -- -- -- -- -- --  --      (⊕-assoc _ _ _ )
-- -- -- -- -- -- -- -- -- -- --  --      ({!!})
 
-- -- -- -- -- -- -- -- -- -- --  -- ⊕-hexa-↓ : ∀ x y z →
-- -- -- -- -- -- -- -- -- -- --  --    Square
-- -- -- -- -- -- -- -- -- -- --  --       (⊕-hexa-diag x y z)
-- -- -- -- -- -- -- -- -- -- --  --       (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- -- -- --  --       (cong (_⊕ z) (⊕-comm _ _))
-- -- -- -- -- -- -- -- -- -- --  --       (cong (y ⊕_) (⊕-comm _ _))


-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ : ℤᵍ → Co ≃ Co
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ zero = idEquiv _
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ one = ↑≃
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (x ⊕ x₁) = ℤᵍ→Co≃ x ∙ₑ ℤᵍ→Co≃ x₁
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (─ x) = invEquiv (ℤᵍ→Co≃ x)
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕─ x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-assoc x x₁ x₂ i) =
-- -- -- -- -- -- -- -- -- -- --   compEquiv-assoc (ℤᵍ→Co≃ x) (ℤᵍ→Co≃ x₁) (ℤᵍ→Co≃ x₂) i
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (zero-⊕ x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-zero x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-triangle x x₁ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-penta-diag x x₁ x₂ x₃ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-penta-△ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-penta-□ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-comm i) = ♯≃ i
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-comm-assoc i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-comp i i₁) = {!!}

-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' : Co → ℤᵍ
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' base = zero
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (↑ x) = one ⊕ ℤᵍ←Co≃' x
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (↓ x) = (─ one) ⊕ ℤᵍ←Co≃' x
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (↓↑ x i) = ({!!} ∙  ((⊕-assoc (─ one) one (ℤᵍ←Co≃' x))) ∙
-- -- -- -- -- -- -- -- -- -- --                             cong (_⊕ (ℤᵍ←Co≃' x)) {!⊕─ !}
-- -- -- -- -- -- -- -- -- -- --                              ∙ {!!}) i
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (↑↓ x i) = (((⊕-assoc (one) (─ one) (ℤᵍ←Co≃' x))) ∙
-- -- -- -- -- -- -- -- -- -- --                             cong (_⊕ (ℤᵍ←Co≃' x)) (⊕─ one )
-- -- -- -- -- -- -- -- -- -- --                              ∙ zero-⊕ (ℤᵍ←Co≃' x)) i
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (♯ x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (⇅⇅⇅-diag x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (⇅⇅⇅-U x i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (⇅⇅⇅-D x i i₁) = {!!}


-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃ : Co ≃ Co → ℤᵍ
-- -- -- -- -- -- -- -- -- -- -- ℤᵍ←Co≃ e = ℤᵍ←Co≃' (fst e base)

-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ : ℤᵍ → Path J₃S¹ base base
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ zero = refl
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ one = loop
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (x ⊕ x₁) = toJ₃S¹ x ∙ toJ₃S¹ x₁
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (─ x) = sym (toJ₃S¹ x)
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕─ x i) = rCancel (toJ₃S¹ x) i
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-comm x x₁ i) = {!PathP→comm loop₂!}
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-assoc x x₁ x₂ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (zero-⊕ x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-zero x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-triangle x x₁ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-penta-diag x x₁ x₂ x₃ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-penta-△ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-penta-□ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-hexa-diag x x₁ x₂ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-hexa-↑ x x₁ x₂ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-hexa-↓ x x₁ x₂ i i₁) = {!!}
