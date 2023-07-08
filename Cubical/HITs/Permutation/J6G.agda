{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.J6G where

open import Cubical.Foundations.Everything
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.2GroupoidTruncation




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

Co≡ : Co ≡ Co
Co≡ = ua ↑≃

♯≃ : ↑≃ ∙ₑ ↑≃ ≡ ↑≃ ∙ₑ ↑≃
♯≃ = equivEq (funExt ♯)

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
  

data 𝐵ₙ : Type where
  bone : 𝐵ₙ
  _b+_ : 𝐵ₙ → 𝐵ₙ → 𝐵ₙ

-- -- -- CoCu : Cube CoSq CoSq CoSq CoSq CoSq CoSq
-- -- -- CoCu = {!!}


-- -- CodeJ₃S¹* : J₃S¹ → ∥ Type ∥₄
-- -- CodeJ₃S¹* = J₃S¹-rec.f w
-- --  where
-- --  open J₃S¹-rec
-- --  w : J₃S¹-rec (∥ Type ∥₄)
-- --  abase w = ∣ Co ∣₄
-- --  aloop w = cong (λ x → ∣ x ∣₄) Co≡
-- --  aloop₂ w = congSq (λ x → ∣ x ∣₄) CoSq
-- --  aloop₃ w k j i = ∣ CoCu k j i ∣₄ 
-- --  atrunc w = squash₄

-- isGrp₄ : ∥ Type ∥₄ → hProp ℓ-zero
-- isGrp₄ = rec (isOfHLevelPlus {n = 2} 2 isSetHProp)
--    λ T → isGroupoid T , isPropIsOfHLevel 3


-- -- CodeJ₃S¹** : ∀ x → fst (isGrp₄ (CodeJ₃S¹* x))
-- -- CodeJ₃S¹** = J₃S¹-elimProp.f w
-- --  where
-- --  w : J₃S¹-elimProp _
-- --  J₃S¹-elimProp.abase w = trunc
-- --  J₃S¹-elimProp.atrunc w = snd ∘ isGrp₄ ∘ CodeJ₃S¹*

-- fromIsGrp₄ : ∀ x → fst (isGrp₄ x) → hGroupoid ℓ-zero 
-- fromIsGrp₄ = elim (λ x → isOfHLevelΠ 4 λ _ → isOfHLevelTypeOfHLevel 3)
--   (_,_)


-- -- CodeJ₃S¹ : J₃S¹ → Type
-- -- CodeJ₃S¹ x = fst (fromIsGrp₄ (CodeJ₃S¹* x) (CodeJ₃S¹** x))



-- p∙'[p⁻∙'q]≡q : ∀ {ℓ} {A : Type ℓ} → {x y : A} → (p q : x ≡ y) → 
--               p ∙' (sym p ∙' q) ≡ q
-- p∙'[p⁻∙'q]≡q p q i j =
--    hcomp ( λ k → 
--           λ { (j = i0) → p (~ i ∧ ~ k)
--             ; (j = i1) → q i1
--             ; (i = i1) → q j
--             }) (compPath'-filler (sym p) q (~ i) j)

-- -- encode : ∀ x → base ≡ x → CodeJ₃S¹ x
-- -- encode x p = subst CodeJ₃S¹ p 𝟘


-- -- module hlp∙ {ℓ} {A : Type ℓ} {a b c d e f : A}  {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d} {u : e ≡ f} {v : d ≡ e} {w : d ≡ f} where

-- --  sq : (S : Square r s p q) → (Q : Square v w refl u)
-- --          → Square (p ∙ s ∙ v)
-- --                   (r ∙ q ∙ w)
-- --                  (λ _ → a)
-- --                  u
-- --  sq S Q  i = (λ j' → S (j' ∧ ~ i) (j' ∧ i))
-- --            ∙ (λ j' → S (j' ∨ ~ i) (j' ∨ i)) ∙ Q i

-- -- module hlp∙' {ℓ} {A : Type ℓ} {a b c d e f : A}  {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d} {u : e ≡ f} {v : d ≡ e} {w : d ≡ f} where

-- --  sq : (S : Square r s p q) → (Q : Square v w refl u)
-- --          → Square (p ∙' (s ∙' v))
-- --                   (r ∙' (q ∙' w))
-- --                  (λ _ → a)
-- --                  u
-- --  sq S Q  i = (λ j' → S (j' ∧ ~ i) (j' ∧ i))
-- --            ∙' ((λ j' → S (j' ∨ ~ i) (j' ∨ i)) ∙' Q i)






-- -- loopCuHlp : (q : Path J₃S¹ base base) →
-- --         PathP (λ i →
-- --                 Square (loop₂ i ∙' (loop₂ i ∙' compPath'-filler loop q (~ i)))
-- --                   (loop₂ i ∙' (loop₂ i ∙' compPath'-filler loop q (~ i)))
-- --                  (λ _ → loop i)
-- --                  λ _ → base
-- --               )
-- --             (hlp∙'.sq loop₂ λ _ → loop ∙' q)
-- --             (hlp∙'.sq loop₂ λ _ → q)
-- -- loopCuHlp q i j l = hlp∙'.sq (loop₃ i) (λ _ → compPath'-filler loop q (~ i))
-- --                         j l







-- -- infixl 6 _⊕_

-- -- infixl 10 ─_


-- -- data ℤᵍ : Type where
-- --  zero one  : ℤᵍ
-- --  _⊕_ : ℤᵍ → ℤᵍ → ℤᵍ
-- --  ─_ : ℤᵍ → ℤᵍ
-- --  ⊕─ : ∀ x → x ⊕ ─ x ≡ zero

-- --  ⊕-assoc : ∀ x y z → x ⊕ (y ⊕ z) ≡ x ⊕ y ⊕ z
 
-- --  zero-⊕ : ∀ x → zero ⊕ x ≡ x
-- --  ⊕-zero : ∀ x → x ⊕ zero ≡ x

-- --  ⊕-triangle : ∀ x y  →
-- --     Square                      
-- --         (⊕-assoc x zero y)
-- --         refl
-- --         (cong (x ⊕_) (zero-⊕ y))
-- --         (cong (_⊕ y) (⊕-zero x))
        


-- --  ⊕-penta-diag : ∀ x y z w →
-- --    x ⊕ y ⊕ z ⊕ w ≡ x ⊕ (y ⊕ (z ⊕ w))
-- --  ⊕-penta-△ : ∀ x y z w →
-- --    Square
-- --      refl
-- --      (⊕-penta-diag x y z w)
-- --      (⊕-assoc _ _ _)
-- --      (sym (⊕-assoc _ _ _))
-- --  ⊕-penta-□ : ∀ x y z w →
-- --     Square
-- --      (sym (⊕-assoc _ _ _))
-- --      (⊕-penta-diag x y z w)
-- --      (cong (_⊕ w) (⊕-assoc _ _ _))
-- --      (cong (x ⊕_) (sym (⊕-assoc _ _ _)))

-- --  -- ⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
-- --  -- ⊕-hexa-diag : ∀ x y z → x ⊕ y ⊕ z ≡ y ⊕ (z ⊕ x)
-- --  -- ⊕-hexa-↑ : ∀ x y z →
-- --  --   Square
-- --  --      (⊕-comm x (y ⊕ z))
-- --  --      (⊕-hexa-diag x y z)
-- --  --      (⊕-assoc _ _ _)
-- --  --      (sym (⊕-assoc _ _ _))
-- --  -- ⊕-hexa-↓ : ∀ x y z →
-- --  --    Square
-- --  --       (⊕-hexa-diag x y z)
-- --  --       (sym (⊕-assoc _ _ _))
-- --  --       (cong (_⊕ z) (⊕-comm _ _))
-- --  --       (cong (y ⊕_) (⊕-comm _ _))

-- --  ⊕-comm : one ⊕ one ≡ one ⊕ one
-- --  ⊕-comm-assoc : one ⊕ (one ⊕ one) ≡ one ⊕ one ⊕ one 

-- --  ⊕-comp : Square
-- --            {!!}
-- --            {!!}
-- --            {!!}
-- --            {!!}

-- --  -- ⊕-hexa-diag : one ⊕ one ⊕ one ≡ one ⊕ (one ⊕ one)
-- --  -- ⊕-hexa-L : 
-- --  --   Square
-- --  --      (cong (one ⊕_) ⊕-comm)
-- --  --      (cong (_⊕ one) ⊕-comm)
-- --  --      (⊕-assoc _ _ _ )
-- --  --      ({!!})
 
-- --  -- ⊕-hexa-↓ : ∀ x y z →
-- --  --    Square
-- --  --       (⊕-hexa-diag x y z)
-- --  --       (sym (⊕-assoc _ _ _))
-- --  --       (cong (_⊕ z) (⊕-comm _ _))
-- --  --       (cong (y ⊕_) (⊕-comm _ _))



-- -- -- ℤᵍ→Co≃ : ℤᵍ → Co ≃ Co
-- -- -- ℤᵍ→Co≃ zero = idEquiv _
-- -- -- ℤᵍ→Co≃ one = ↑≃
-- -- -- ℤᵍ→Co≃ (x ⊕ x₁) = ℤᵍ→Co≃ x ∙ₑ ℤᵍ→Co≃ x₁
-- -- -- ℤᵍ→Co≃ (─ x) = invEquiv (ℤᵍ→Co≃ x)
-- -- -- ℤᵍ→Co≃ (⊕─ x i) = {!!}
-- -- -- ℤᵍ→Co≃ (⊕-assoc x x₁ x₂ i) =
-- -- --   compEquiv-assoc (ℤᵍ→Co≃ x) (ℤᵍ→Co≃ x₁) (ℤᵍ→Co≃ x₂) i
-- -- -- ℤᵍ→Co≃ (zero-⊕ x i) = {!!}
-- -- -- ℤᵍ→Co≃ (⊕-zero x i) = {!!}
-- -- -- ℤᵍ→Co≃ (⊕-triangle x x₁ i i₁) = {!!}
-- -- -- ℤᵍ→Co≃ (⊕-penta-diag x x₁ x₂ x₃ i) = {!!}
-- -- -- ℤᵍ→Co≃ (⊕-penta-△ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- ℤᵍ→Co≃ (⊕-penta-□ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- ℤᵍ→Co≃ (⊕-comm i) = ♯≃ i
-- -- -- ℤᵍ→Co≃ (⊕-comm-assoc i) = {!!}
-- -- -- ℤᵍ→Co≃ (⊕-comp i i₁) = {!!}

-- -- -- ℤᵍ←Co≃' : Co → ℤᵍ
-- -- -- ℤᵍ←Co≃' base = zero
-- -- -- ℤᵍ←Co≃' (↑ x) = one ⊕ ℤᵍ←Co≃' x
-- -- -- ℤᵍ←Co≃' (↓ x) = (─ one) ⊕ ℤᵍ←Co≃' x
-- -- -- ℤᵍ←Co≃' (↓↑ x i) = ({!!} ∙  ((⊕-assoc (─ one) one (ℤᵍ←Co≃' x))) ∙
-- -- --                             cong (_⊕ (ℤᵍ←Co≃' x)) {!⊕─ !}
-- -- --                              ∙ {!!}) i
-- -- -- ℤᵍ←Co≃' (↑↓ x i) = (((⊕-assoc (one) (─ one) (ℤᵍ←Co≃' x))) ∙
-- -- --                             cong (_⊕ (ℤᵍ←Co≃' x)) (⊕─ one )
-- -- --                              ∙ zero-⊕ (ℤᵍ←Co≃' x)) i
-- -- -- ℤᵍ←Co≃' (♯ x i) = {!!}
-- -- -- ℤᵍ←Co≃' (⇅⇅⇅-diag x i) = {!!}
-- -- -- ℤᵍ←Co≃' (⇅⇅⇅-U x i i₁) = {!!}
-- -- -- ℤᵍ←Co≃' (⇅⇅⇅-D x i i₁) = {!!}


-- -- -- ℤᵍ←Co≃ : Co ≃ Co → ℤᵍ
-- -- -- ℤᵍ←Co≃ e = ℤᵍ←Co≃' (fst e base)

-- -- -- -- toJ₃S¹ : ℤᵍ → Path J₃S¹ base base
-- -- -- -- toJ₃S¹ zero = refl
-- -- -- -- toJ₃S¹ one = loop
-- -- -- -- toJ₃S¹ (x ⊕ x₁) = toJ₃S¹ x ∙ toJ₃S¹ x₁
-- -- -- -- toJ₃S¹ (─ x) = sym (toJ₃S¹ x)
-- -- -- -- toJ₃S¹ (⊕─ x i) = rCancel (toJ₃S¹ x) i
-- -- -- -- toJ₃S¹ (⊕-comm x x₁ i) = {!PathP→comm loop₂!}
-- -- -- -- toJ₃S¹ (⊕-assoc x x₁ x₂ i) = {!!}
-- -- -- -- toJ₃S¹ (zero-⊕ x i) = {!!}
-- -- -- -- toJ₃S¹ (⊕-zero x i) = {!!}
-- -- -- -- toJ₃S¹ (⊕-triangle x x₁ i i₁) = {!!}
-- -- -- -- toJ₃S¹ (⊕-penta-diag x x₁ x₂ x₃ i) = {!!}
-- -- -- -- toJ₃S¹ (⊕-penta-△ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- toJ₃S¹ (⊕-penta-□ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- toJ₃S¹ (⊕-hexa-diag x x₁ x₂ i) = {!!}
-- -- -- -- toJ₃S¹ (⊕-hexa-↑ x x₁ x₂ i i₁) = {!!}
-- -- -- -- toJ₃S¹ (⊕-hexa-↓ x x₁ x₂ i i₁) = {!!}
