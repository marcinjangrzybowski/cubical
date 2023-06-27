{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.J where

open import Cubical.Foundations.Everything
open import Cubical.Functions.FunExtEquiv

data J₃S¹ : Type where
  base : J₃S¹
  loop : base ≡ base
  loop₂ : Square loop loop loop loop
  loop₃ : Cube loop₂ loop₂ loop₂ loop₂  loop₂ loop₂
      -- PathP (λ i → PathP (λ j → PathP (λ k → J₃S¹)
      --                                     (loop₂ i j)
      --                                     (loop₂ i j))
      --                        (λ k → loop₂ i k)
      --                        (λ k → loop₂ i k))
      --           (λ j k → loop₂ j k)
      --           (λ j k → loop₂ j k)
  -- trunc : isOfHLevel 4 J₃S¹

data Co : Type where
 base : Co
 ↑ ↓ : Co → Co
 ↓↑ : ∀ x → ↓ (↑ x) ≡ x 
 ↑↓ : ∀ x → ↑ (↓ x) ≡ x
 ♯ : ∀ x → ↑ (↑ x) ≡ ↑ (↑ x)
 ⇅⇅⇅-diag : ∀ x → ↑ (↑ (↑ x)) ≡ ↑ (↑ (↑ x))
 ⇅⇅⇅-U : ∀ x →
     Square
       (♯ (↑ x))
       (⇅⇅⇅-diag x)
       (cong ↑ (♯ x))
       (cong ↑ (♯ x))

 ⇅⇅⇅-D : ∀ x →
     Square
       (⇅⇅⇅-diag x)              
       (cong ↑ (♯ x))
       (♯ (↑ x))
       (♯ (↑ x))
 -- trunc : {!isGroupoid Co!}

♯ₑ : ↑ ∘ ↑ ≡ ↑ ∘ ↑
♯ₑ = funExt ♯

↑Iso : Iso Co Co
Iso.fun ↑Iso = ↑
Iso.inv ↑Iso = ↓
Iso.rightInv ↑Iso = ↑↓
Iso.leftInv ↑Iso = ↓↑

↑≃ : Co ≃ Co
↑≃ = isoToEquiv ↑Iso

Co≡ : Co ≡ Co
Co≡ = ua ↑≃

♯≃ : ↑≃ ∙ₑ ↑≃ ≡ ↑≃ ∙ₑ ↑≃
♯≃ = equivEq (funExt ♯)

♯≃-diag6 : ↑≃ ∙ₑ ↑≃ ∙ₑ ↑≃ ≡ ↑≃ ∙ₑ ↑≃ ∙ₑ ↑≃
♯≃-diag6 = equivEq (funExt ⇅⇅⇅-diag)


♯6-U : Square {A = Co ≃ Co}
          (cong (↑≃ ∙ₑ_) ♯≃)
          ♯≃-diag6
          (equivEq (cong fst (cong (_∙ₑ ↑≃) ♯≃)))
          (equivEq (cong fst (cong (_∙ₑ ↑≃) ♯≃)))
♯6-U =
  ΣSquarePSet (λ i j a → isProp→isSet (isPropIsEquiv a))
    _ _ _ _ λ i j x → ⇅⇅⇅-U x i j

♯6-D : Square {A = Co ≃ Co}
          ♯≃-diag6
          (equivEq (cong fst (cong (_∙ₑ ↑≃) ♯≃)))
          (cong (↑≃ ∙ₑ_) ♯≃)
          (cong (↑≃ ∙ₑ_) ♯≃)
          
♯6-D =
    ΣSquarePSet (λ i j a → isProp→isSet (isPropIsEquiv a))
    _ _ _ _ λ i j x → ⇅⇅⇅-D x i j


↑♯≡♯↑ :  congP (λ _ →  _∘' ↑) ♯ₑ ≡ congP (λ _ → ↑ ∘'_) ♯ₑ
↑♯≡♯↑ = whiskSq.sq' _
   {!!}
   (λ i l x → ⇅⇅⇅-D x i l )
   {!!} {!!} {!!}

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

-- CodeJ₃S¹-pa : ∀ i j → Partial (i ∨ ~ i ∨ j ∨ ~ j)
--         (Σ Type (λ T → T ≃ Co))
-- CodeJ₃S¹-pa i j =
--    λ {  (i = i0) → Co≡ j ,
--                 ua-unglueEquiv ↑≃ j ∙ₑ ♯≃ j
--           ; (i = i1) → Co≡ j ,
--                 ua-unglueEquiv ↑≃ j ∙ₑ ↑≃ 
--           ; (j = i0) → Co≡ i ,
--                         (↑ ∘ ↑) ∘ fst (ua-unglueEquiv ↑≃ i) ,
--                         isProp→PathP
--                           (λ i → isPropIsEquiv
--                             ((↑ ∘ ↑) ∘ fst (ua-unglueEquiv ↑≃ i)))
--                           (snd (compEquiv ↑≃ (↑≃ ∙ₑ ↑≃)))
--                           (snd (compEquiv ↑≃ ↑≃))
--                            i

--           ; (j = i1) → Co≡ i ,
--                         ↑ ∘ fst (ua-unglueEquiv ↑≃ i) ,
--                         isProp→PathP
--                           (λ i → isPropIsEquiv
--                             (↑ ∘ fst (ua-unglueEquiv ↑≃ i)))
--                           (snd (compEquiv (idEquiv Co) (↑≃ ∙ₑ ↑≃)))
--                           (snd (compEquiv (idEquiv Co) ↑≃))
--                            i
--           }




-- CoSq : Square Co≡ Co≡ Co≡ Co≡
-- CoSq i j =
--     Glue Co {i ∨ ~ i ∨ j ∨ ~ j}
--        (CodeJ₃S¹-pa i j)

-- CoSq' : Square (ua (↑≃ ∙ₑ ↑≃)) (ua (↑≃ ∙ₑ ↑≃)) refl refl
-- CoSq' = cong ua ♯≃


-- -- ∙ₑfiller : Square Co≡ (ua (↑≃ ∙ₑ ↑≃))
-- --                   refl
-- --                   Co≡
-- -- ∙ₑfiller = {!!}

-- -- ∙ₑfiller' : Square Co≡ (ua (↑≃ ∙ₑ ↑≃))
                  
-- --                   (sym Co≡)
-- --                   refl
-- -- ∙ₑfiller' = {!!}


-- -- CoSq≡CoSq' : Cube CoSq CoSq'
-- --                ∙ₑfiller
-- --                ∙ₑfiller'
-- --                (λ j i → Co≡ (~ j ∧ i))
-- --                λ j i → Co≡ (j ∨ i)
-- -- CoSq≡CoSq' = {!!}


-- -- uaGlue-rhomb : ∀ {ℓ} {A : Type ℓ} → (e : A ≃ A) →
-- --                  Square (ua e) (ua e) (ua e) (ua e) 
-- -- uaGlue-rhomb {A = A} e i j =
-- --    Glue A
-- --       λ {  (i = i0) → ua e j , ua-unglueEquiv e j ∙ₑ e
   
-- --            ; (i = i1) → ua e j , ua-unglue e j , {!!}
-- --           ; (j = i0) → ua e i , ua-unglueEquiv e i ∙ₑ e

-- --           ; (j = i1) → ua e i , ua-unglue e i , {!!}
-- --           }

-- -- invSidesFiller₃ :  ∀ {ℓ} {A : Type ℓ} →
-- --                   (a : A) →
-- --                   (p : a ≡ a)
-- --                   (s : Square p p p p)
-- --                   → Cube s s s s s s
-- -- invSidesFiller₃ = {!!}




-- -- record Bd₂P {ℓ} (A : I → I → Type ℓ) : Type ℓ where
-- --  field
-- --   a₀₋ : ∀ i → A i0 i 
-- --   a₁₋ : ∀ i → A i1 i
-- --   a₋₀ : PathP (λ j → A j i0) (a₀₋ i0) (a₁₋ i0)
-- --   a₋₁ : PathP (λ j → A j i1) (a₀₋ i1) (a₁₋ i1)

-- --  Inside : Type ℓ
-- --  Inside = SquareP A (λ i → a₀₋ i) (λ i → a₁₋ i) a₋₀ a₋₁

-- -- open Bd₂P

-- -- mapBd₂P : ∀ {ℓ ℓ'}
-- --              {A : I → I → Type ℓ}
-- --              {A' : I → I → Type ℓ'}
-- --              → (∀ i j → A i j → A' i j)
-- --              → Bd₂P A → Bd₂P A' 
-- -- Bd₂P.a₀₋ (mapBd₂P f x) i = f i0 i (Bd₂P.a₀₋ x i)
-- -- Bd₂P.a₁₋ (mapBd₂P f x) i = f i1 i (Bd₂P.a₁₋ x i)
-- -- Bd₂P.a₋₀ (mapBd₂P f x) j = f j i0 (Bd₂P.a₋₀ x j)
-- -- Bd₂P.a₋₁ (mapBd₂P f x) j = f j i1 (Bd₂P.a₋₁ x j)

-- -- -- bd-ung-♯ : Bd₂P λ _ _ → Co → Co
-- -- -- a₀₋ bd-ung-♯ i = funExt ♯ i
-- -- -- a₁₋ bd-ung-♯ _ = ↑
-- -- -- a₋₀ bd-ung-♯ _ = {!!}
-- -- -- a₋₁ bd-ung-♯ _ = {!↑!}


-- ung↑ : PathP (λ i → ua ↑≃ i → Co) (↑) (idfun Co)
-- ung↑ = ua-ungluePathExt ↑≃

-- ung♯ : SquareP (λ i k → CoSq i k → Co)
--                           (λ k x → ♯ (ung↑ k x) k)
--                           (λ k x → ↑ (ung↑ k x))
--                           (λ i x → ↑ (↑ (ung↑ i x)))
--                           (λ i x → ↑ (ung↑ i x))
-- ung♯ i k = unglue (i ∨ ~ i ∨ k ∨ ~ k)

-- ung♯' : SquareP (λ i k → CoSq i k → Co)
--                           (λ k x → ↑ (↑ (ung↑ k x)))
--                           (λ k x → ↑ (ung↑ k x))
--                           (λ i x → ↑ (↑ (ung↑ i x)))
--                           (♯ₑ ◁ (λ i x → ↑ (ung↑ i x)))
-- ung♯' i k =
--    hcomp
--      (λ l → λ {
--        (i = i0) → ♯ₑ (~ l ∧ k) ∘' ung↑ k
--       ;(i = i1) → ↑ ∘' ung↑ k
--       ;(k = i0) → ↑ ∘' ↑ ∘' ung↑ i
--        })
--      (unglue (i ∨ ~ i ∨ k ∨ ~ k))

-- ung♯'' : SquareP (λ i k → CoSq i k → Co)
--                           (λ k x → ↑ (↑ (ung↑ k x)))
--                           (sym ♯ₑ ◁ λ k x → ↑ (ung↑ k x))
--                           (λ i x → ↑ (↑ (ung↑ i x)))
--                           (λ i x → ↑ (ung↑ i x))
-- ung♯'' =
--   whiskSq.sq' _
--     ung♯
--       (λ k l → ♯ₑ (k ∨ l) ∘' ung↑ k)
--       (λ k l → doubleWhiskFiller {A = λ i → Co≡ i → Co}
--           (sym ♯ₑ) (λ k x → ↑ (ung↑ k x)) refl l k)
--       (λ i l x → ♯ₑ l (ung↑ i x))
--       λ i _ → λ x → ↑ (ung↑ i x)


-- ung♯* : SquareP (λ k i → CoSq k i → Co)
--                           (λ i x →  ↑ (↑ (ung↑ i x)))
--                           ((sym ♯ₑ ◁ (λ k₁ x₁ → ↑ (ung↑ k₁ x₁))))
--                           (λ k x → ↑ ((♯ₑ ◁ (congP (λ _ → ↑ ∘'_) (ung↑))) k x))
--                           (♯ₑ ◁ (congP (λ _ → ↑ ∘'_) (ung↑)))
-- ung♯* k i =
--    hcomp (λ l → 
--         λ { (k = i0) → hcomp
--                (λ l' → λ {
--                  (l = i0) → ↑ ∘' ↑ ∘' ung↑ i
--                 ;(l = i1) → ↑ ∘' ↑ ∘' ung↑ i
--                 ;(i = i0) → ↑♯≡♯↑ l' (~ l)
--                 ;(i = i1) → ♯ₑ (~ l)
--                    })
--                (♯ₑ (~ l) ∘' ung↑ i)
--           ; (k = i1) → (sym ♯ₑ ◁ (congP (λ _ → ↑ ∘'_) (ung↑))) i
--           ; (i = i0) → ↑ ∘'
--             doubleWhiskFiller {A = λ i → Co≡ i → Co}
--               ♯ₑ (congP (λ _ → ↑ ∘'_) (ung↑)) refl l k
--           })
--      (ung♯'' k i)

-- -- ung♯'' : SquareP (λ i k → CoSq i k → Co)
-- --                           (λ k x → ↑ (↑ (ung↑ k x)))
-- --                           (λ k x → ↑ (ung↑ k x))
-- --                           (cong (_∘' ↑) (sym ♯ₑ) ◁ λ i x → ↑ (↑ (ung↑ i x)))
-- --                           (λ i x → ↑ (ung↑ i x))
-- -- ung♯'' i k = 
-- --    hcomp
-- --      (λ l → λ {
-- --        (i = i0) → ♯ₑ (l ∨ k) ∘' ung↑ k
-- --       ;(i = i1) → ↑ ∘' ung↑ k
-- --       ;(k = i1) → ↑ ∘' ung↑ i
-- --        })
-- --      (unglue (i ∨ ~ i ∨ k ∨ ~ k))


-- ♯-rhomb : Square {A = Co → Co}
--             (λ i x → ♯ₑ i (↑ x))
--             (λ i x → ↑ (♯ₑ i x))
--             (λ j x → ↑ (♯ₑ (~ j) x))
--             (λ j x → ♯ₑ (~ j) (↑ x) )
-- ♯-rhomb = invSides-filler _ _


-- -- CodeJ₃S¹J0 : SquareP (λ k i → CoSq k i → Co)
-- --                  (λ i x → ↑ (♯ (↑ (♯ (ung↑ i x) i)) (~ i)))
-- --                  (λ i x → ♯ (↑ (♯ (ung↑ i x) i)) (~ i))
-- --                  (λ k x → ♯ₑ k (↑ (♯ₑ ( (~ k)) (↑ (ung↑ k x)))))
-- --                  (λ k x → ↑ (♯ (↑ (↑ (ung↑ k x))) k))
-- -- CodeJ₃S¹J0 =
-- --  whiskSq.sq' _
-- --    (λ k i x → ♯-rhomb i k (↑ (ung♯ k i x)))
-- --       (λ l i x → ↑ (♯ₑ (~ l)  (↑ (♯ₑ (l) (ung↑ l x)))))
-- --       (λ l i x → ♯ₑ (~ l) (↑ (♯ₑ (l ∨ (~ i)) (ung↑ l x))) )
-- --       (λ l k x → ♯ₑ l (↑ (♯ₑ (~ k ∨ (~ l)) (↑ (ung↑ l x)))))      
-- --        λ l k x → ↑ (♯ₑ l (↑ (↑ (ung↑ l x)))) 

-- -- CodeJ₃S¹K0 : SquareP (λ j i → CoSq j i → Co)
-- --                  (λ i x → ↑ (♯ₑ (~ i) (↑ (♯ₑ i (ung↑ i x)))) )
-- --                  (λ i x → ↑ (♯ₑ (~ i) (♯ₑ i (ung↑ i x))))
-- --                  (λ j x → {!!})
-- --                  (λ j x → ♯ₑ j (↑ (♯ₑ j (ung↑ j x))))
-- -- CodeJ₃S¹K0 = {!!}
--  -- -- λ j i x → {!ung♯ j i x!}
--  -- whiskSq.sq' _
--  --  {a₀₋' = λ i x → ↑ (♯ₑ (~ i) (↑ (♯ₑ i (ung↑ i x))))}
--  --  {a₁₋' = λ i x → ↑ (♯ₑ (~ i) (♯ₑ i (ung↑ i x)))}
--  --  {a₋₀' = λ i → {!!}}
--  --  {a₋₁' = λ i x → ♯ₑ i (↑ (♯ₑ i (ung↑ i x)))}
--  --  (λ j i x → ↑ ((♯ₑ (~ i))  (↑ (ung♯ j i x))))
--  --    (λ i l x  → ↑ (♯ (↑ (♯ (ung↑ i x) i)) (~ i)))
--  --    (λ i l x → ↑ (♯ (♯ (ung↑ i x) (i ∧ l)) (~ i)))
--  --    (λ j l x →  {!!}
--  --     -- ↑ (↑ (↑ (↑ (↑ (↑ (ung↑ j x))))))
--  --     )
--  --    λ j l x → {!↑ (↑ (↑ (♯ (ung↑ j x) (j ∧ l))))!} --
--  --     -- (↑ (↑ (↑ (↑ (↑ (ung↑ j x))))))
--  --     -- (λ l i x → ↑ (♯ₑ (~ l)  (↑ (♯ₑ (l) (ung↑ l x)))))
--  --     -- (λ l i x → ♯ₑ (~ l) (↑ (♯ₑ (l ∨ (~ i)) (ung↑ l x))) )
--  --     -- (λ l k x → ♯ₑ l (↑ (♯ₑ (~ k ∨ (~ l)) (↑ (ung↑ l x)))))      
--  --     --  λ l k x → ↑ (♯ₑ l (↑ (↑ (ung↑ l x)))) 

-- -- CodeJ₃S¹I0 : SquareP (λ k j → CoSq k j → Co)
-- --                  (λ j x → {!!})
-- --                  (λ j x → ↑ (♯ₑ j (↑ (↑ (ung↑ j x)))))
-- --                  (λ k x → ♯ₑ k (↑ (♯ₑ (~ k) (↑ (ung↑ k x)))))
-- --                  (λ k x → ♯ₑ k (↑ (↑ (↑ (ung↑ k x)))))
-- -- CodeJ₃S¹I0 = whiskSq.sq' _
-- --   (λ k j x → ♯ₑ k (↑ (↑ (ung♯ k j x))))
-- --   (λ j l x → {!!})
-- --   (λ j l x → ↑ {!♯ₑ (j ∧ l) ? !})
-- --   (λ k l x → ♯ₑ k (↑ (♯ₑ (~ k ∨ (~ l)) (↑ (ung↑ k x)))))
-- --   λ k l x → {!!}


-- -- module rhombCu {ℓ} {A : Type ℓ} {a : A} {p : a ≡ a} (s : Square p p p p) where

-- --  cu : Cube s s s s s s
-- --  cu k j i = {!!} 




-- CoCu : Cube CoSq CoSq CoSq CoSq CoSq CoSq
-- CoCu k j i = 
--     Glue Co
--        λ {  (k = i0) → CoSq j i ,
--                        (λ x → ↑ (ung♯ j i x)) ,
--                        {!!}
                                                
--           ; (j = i0) → CoSq k i ,
--                        (λ x → ↑ (ung♯ k i x)) , --↑ (ung♯ k i x)
--                        {!!}
--                        -- fst (♯6-U k j) ∘' ung♯ k j ,
--                        -- {!!}
--                        -- -- unglueEquiv Co (j ∨ ~ j ∨ k ∨ ~ k ) (CodeJ₃S¹-pa j k)
--                        -- --  ∙ₑ ♯6-U k j
--           ; (i = i0) → CoSq k j ,
--                        (λ x → ↑ (ung♯' k j x)) ,
--                        {!!} 
--                        -- CodeJ₃S¹J0 k i  ,
--                        -- {!!}
--           ; (k = i1) → CoSq j i ,
--                     (λ x → ung♯'' j i x) ,  --(λ x → ung♯ j i x) ,
--                     {!!}
--           ; (j = i1) → CoSq k i ,
--                         (ung♯* k i) , --(λ x → ung♯ k i x) ,
--                         {!!}
--           ; (i = i1) → CoSq k j ,
--                      (λ x →  ung♯' k j x) ,
--                     -- (λ x → fst (♯6-D (~ i) j) (ung♯ j i x)) ,
--                     {!!}
--                     -- fst (♯6-D (~ i) j) ∘'
--                     -- fst (unglueEquiv Co (i ∨ ~ i ∨ j ∨ ~ j ) (CodeJ₃S¹-pa i j))
--                     -- , {!!}
--           }
  


-- -- -- CoCu : Cube CoSq CoSq CoSq CoSq CoSq CoSq
-- -- -- CoCu = {!!}



-- -- -- CodeJ₃S¹ : J₃S¹ → Type
-- -- -- CodeJ₃S¹ base = Co
-- -- -- CodeJ₃S¹ (loop i) = Co≡ i
-- -- -- CodeJ₃S¹ (loop₂ j i) = CoSq j i
-- -- -- CodeJ₃S¹ (loop₃ k j i) = CoCu k j i 
-- -- --   -- Glue Co
-- -- --   --      λ {  (i = i0) → CoSq k j ,
-- -- --   --                      (CodeJ₃S¹I0 k j) ,
-- -- --   --                      {!!}
                                                
-- -- --   --         ; (i = i1) → CoSq k j ,
-- -- --   --                      fst (♯6-U k j) ∘' ung♯ k j ,
-- -- --   --                      {!!}
-- -- --   --                      -- unglueEquiv Co (j ∨ ~ j ∨ k ∨ ~ k ) (CodeJ₃S¹-pa j k)
-- -- --   --                      --  ∙ₑ ♯6-U k j
-- -- --   --         ; (j = i0) → CoSq k i ,
-- -- --   --                      CodeJ₃S¹J0 k i  ,
-- -- --   --                      {!!}
-- -- --   --         ; (j = i1) → CoSq k i ,
-- -- --   --                   (λ x → ♯-rhomb i k (ung♯ k i x)) ,
-- -- --   --                   {!!}
-- -- --   --         ; (k = i0) → CoSq j i ,
-- -- --   --                       (CodeJ₃S¹K0 j i) ,
-- -- --   --                       {!!}
-- -- --   --         ; (k = i1) → CoSq j i ,
-- -- --   --                   (λ x → fst (♯6-D (~ i) j) (ung♯ j i x)) ,
-- -- --   --                   {!!}
-- -- --   --                   -- fst (♯6-D (~ i) j) ∘'
-- -- --   --                   -- fst (unglueEquiv Co (i ∨ ~ i ∨ j ∨ ~ j ) (CodeJ₃S¹-pa i j))
-- -- --   --                   -- , {!!}
-- -- --   --         }

-- -- --   -- Glue Co
-- -- --   --      λ {  (i = i0) → CoSq k j ,
-- -- --   --                      (CodeJ₃S¹I0 k j) ,
-- -- --   --                      {!!}
                                                
-- -- --   --         ; (i = i1) → CoSq k j ,
-- -- --   --                      fst (♯6-U k j) ∘' ung♯ k j ,
-- -- --   --                      {!!}
-- -- --   --                      -- unglueEquiv Co (j ∨ ~ j ∨ k ∨ ~ k ) (CodeJ₃S¹-pa j k)
-- -- --   --                      --  ∙ₑ ♯6-U k j
-- -- --   --         ; (j = i0) → CoSq k i ,
-- -- --   --                      CodeJ₃S¹J0 k i  ,
-- -- --   --                      {!!}
-- -- --   --         ; (j = i1) → CoSq k i ,
-- -- --   --                   (λ x → ♯-rhomb i k (ung♯ k i x)) ,
-- -- --   --                   {!!}
-- -- --   --         ; (k = i0) → CoSq j i ,
-- -- --   --                       (CodeJ₃S¹K0 j i) ,
-- -- --   --                       {!!}
-- -- --   --         ; (k = i1) → CoSq j i ,
-- -- --   --                   (λ x → fst (♯6-D (~ i) j) (ung♯ j i x)) ,
-- -- --   --                   {!!}
-- -- --   --                   -- fst (♯6-D (~ i) j) ∘'
-- -- --   --                   -- fst (unglueEquiv Co (i ∨ ~ i ∨ j ∨ ~ j ) (CodeJ₃S¹-pa i j))
-- -- --   --                   -- , {!!}
-- -- --   --         }




-- -- -- -- -- lem-CodeJ₃S¹-lem : SquareP (λ i _ → Co≡ i → Co)
-- -- -- -- --                      (λ z x → ♯ (↑ (♯ (↑ x) z)) z)
-- -- -- -- --                      (λ z x → ↑ (↑ (↑ (♯ x z))))
-- -- -- -- --                      (λ i x → ↑ (↑ (↑ (↑ (↑ (ua-unglue ↑≃ i x) )))))
-- -- -- -- --                      λ i x → ♯ (↑ (↑ (↑ (ua-unglue ↑≃ i x) ))) (~ i)
-- -- -- -- -- lem-CodeJ₃S¹-lem i z x =
-- -- -- -- --   ♯ (↑ ( hcomp (λ q →
-- -- -- -- --                 λ { (i = i0) → ♯ (ua-unglue ↑≃ i0 x) (z ∨ ~ q)
-- -- -- -- --                   ; (i = i1) → ♯ x z
-- -- -- -- --                    ; (z = i0) → ♯ (ua-unglue ↑≃ i x) (~ i ∧ ~ q)
-- -- -- -- --                   ; (z = i1) → ↑ (↑ (ua-unglue ↑≃ i x))
-- -- -- -- --                   })
-- -- -- -- --               (♯ (ua-unglue ↑≃ i x) (z ∨ ~ i)) )) (z ∧   ~ i)

-- -- -- -- -- lem-CodeJ₃S¹ : SquareP (λ i k → CodeJ₃S¹-sq i k → Co)
-- -- -- -- --                    (λ k x →
-- -- -- -- --                      (((λ j' → ↑ (♯ (↑ (♯ (ua-unglue ↑≃ k x) j')) j')))
-- -- -- -- --                       ∙ λ z → ♯ (↑ (♯ (↑ (ua-unglue ↑≃ k x)) z)) z ) k )
-- -- -- -- --                    (λ k x →
-- -- -- -- --                       ↑ (♯ (♯ ((ua-unglue ↑≃ k x)) k) k))
-- -- -- -- --                    (λ i x → ↑ (↑ ( ↑ (↑ (↑ (↑ (ua-unglue ↑≃ i x)))))))
-- -- -- -- --                    (λ i x → ♯ (↑ (↑ (↑ (ua-unglue ↑≃ i x)))) (~ i))
-- -- -- -- -- lem-CodeJ₃S¹ = whiskSq.sq' (λ z k → CodeJ₃S¹-sq z k → Co)
-- -- -- -- --     (λ i k →  ↑ ∘' funExt ♯ k ∘' ↑ ∘' fst (unglueEquiv Co (i ∨ ~ i ∨ k ∨ ~ k ) (CodeJ₃S¹-pa i k)))
     
-- -- -- -- --     (λ j z x → (compPath-filler
-- -- -- -- --          (λ j' → ↑ (♯ (↑ (♯ (ua-unglue ↑≃ j x) j')) j'))
-- -- -- -- --          λ z → ♯ (↑ (♯ (↑ (ua-unglue ↑≃ j x)) z)) z ) z j)
-- -- -- -- --     (λ j z x → ↑ (♯ (♯ ((ua-unglue ↑≃ j x)) (z ∧ j)) j))
-- -- -- -- --     (λ i z x → ↑ (↑ (↑ (↑ (↑ (↑ (ua-unglue ↑≃ i x)))))))
-- -- -- -- --     lem-CodeJ₃S¹-lem


-- -- -- -- lem2-CodeJ₃S¹ : SquareP (λ i k → CodeJ₃S¹-sq i k → Co)

-- -- -- --                    (congP (λ k f → f ∘' ua-unglue ↑≃ k)
-- -- -- --                          ((λ i x → ↑ (♯ (♯ x i) i))
-- -- -- --                           ∙ λ i z → ♯ (↑ (↑ (↑ z))) i))
-- -- -- --                    (λ k x → ↑ (♯ (↑ (ua-unglue ↑≃ k x)) k))
-- -- -- --                    (λ i x → ↑ (↑ (↑ (↑ (↑ (ua-unglue ↑≃ i x))))) )
-- -- -- --                    (λ i x → ♯ (↑ (↑ (ua-unglue ↑≃ i x))) (~ i))
-- -- -- -- lem2-CodeJ₃S¹ =
-- -- -- --   congSqP (λ i k f → f ∘' (λ x → unglue (i ∨ ~ i ∨ k ∨ ~ k) x))
-- -- -- --     (symP (compPath-filler (cong (↑ ∘'_) ♯ₑ) (cong (_∘' ↑) ♯ₑ)))

-- -- -- -- -- lem3-CodeJ₃S¹-lem : SquareP (λ j i → Co≡ j → Co)
-- -- -- -- --                       ( refl)
-- -- -- -- --                       (λ i x → ♯ (↑ (♯ x i)) i)
-- -- -- -- --                       (λ j x → ↑ (♯ₑ j (↑ (↑ (ua-unglue ↑≃ j x)))))
-- -- -- -- --                       λ j x → ((λ j' →
-- -- -- -- --                          ↑ (♯ (♯ (ua-unglue ↑≃ j x) j') j'))
-- -- -- -- --                           ∙ λ j' → ♯ (↑ (↑ (↑ (ua-unglue ↑≃ j x)))) j') j
-- -- -- -- -- lem3-CodeJ₃S¹-lem j i x = {!!}

-- -- -- -- -- unglue-lem : SquareP (λ j k → CodeJ₃S¹-sq j k → Co)
-- -- -- -- --                  {!!}
-- -- -- -- --                  {!!}
-- -- -- -- --                  {!!}
-- -- -- -- --                  {!!}
-- -- -- -- -- unglue-lem j k x = {!unglue ? !}
-- -- -- -- -- lem3-CodeJ₃S¹-test :
-- -- -- -- --    SquareP (λ j k → CodeJ₃S¹-sq j k → Co)
-- -- -- -- --    {!!}
-- -- -- -- --    {!!}
-- -- -- -- --    {!!}
-- -- -- -- --    {!!}
-- -- -- -- -- lem3-CodeJ₃S¹-test =
-- -- -- -- --    whiskSq.sq' _
-- -- -- -- --       CodeJ₃S¹-sq-unglueSq
-- -- -- -- --       {!!}
-- -- -- -- --       {!!}
-- -- -- -- --       {!!}
-- -- -- -- --       {!!}

-- -- -- -- -- lem3-CodeJ₃S¹ : SquareP (λ j k → CodeJ₃S¹-sq j k → Co)
-- -- -- -- --   (congP (λ k f → f ∘' ua-unglue ↑≃ k)
-- -- -- -- --               ((λ k' x → ↑ (♯ (↑ (♯ x k')) k'))
-- -- -- -- --                       ∙ λ k' x → ♯ (↑ (♯ (↑ x) k')) k' ))
-- -- -- -- --   (congP (λ k f → f ∘' ua-unglue ↑≃ k)
-- -- -- -- --                          ((λ k' x → ↑ (♯ (♯ x k') k'))
-- -- -- -- --                           ∙ λ k' z → ♯ (↑ (↑ (↑ z))) k'))
-- -- -- -- --   (λ j z → ♯ (↑ (↑ (♯ (ua-unglue ↑≃ j z) j))) j)
-- -- -- -- --   (λ j z → ↑ (♯ (♯ (ua-unglue ↑≃ j z) j) j))
-- -- -- -- -- lem3-CodeJ₃S¹ =
-- -- -- -- --    {!!}
-- -- -- -- --   whiskSq.sq' _
-- -- -- -- --    (λ j k x → ↑ (♯ₑ j (CodeJ₃S¹-sq-unglueSq j k x)))
-- -- -- -- --       {{!!}}
-- -- -- -- --       {{!!}}    
-- -- -- -- --       {!!}
-- -- -- -- --       {{!!}}
-- -- -- -- --       {{!!}}
-- -- -- -- --       {!!}
-- -- -- -- --       {!!}
-- -- -- -- --       {!!}
-- -- -- -- --     -- (λ j i x →
-- -- -- -- --     --   compPath-filler ( λ j' → ↑ (♯ₑ j' (↑ (♯ₑ j' (ua-unglue ↑≃ j x)))))
-- -- -- -- --     --    (λ z → ♯ (↑ (♯ (↑ (ua-unglue ↑≃ j x)) z)) z) i j)
-- -- -- -- --     -- (lem3-CodeJ₃S¹-lem)
-- -- -- -- --     -- (λ i j → {!!})
-- -- -- -- --     -- λ i j → {!!}
-- -- -- -- --     -- (λ i i₁ x → ↑ ((↑ ∘ ↑) (↑ (↑ (↑ (ua-unglue ↑≃ i x))))))
-- -- -- -- --     -- (λ i i₁ x → ♯ (↑ (♯ (ua-unglue ↑≃ i x) i₁)) i₁) 



-- -- -- -- CodeJ₃S¹ : J₃S¹ → Type
-- -- -- -- CodeJ₃S¹ base = Co
-- -- -- -- CodeJ₃S¹ (loop i) = Co≡ i
-- -- -- -- CodeJ₃S¹ (loop₂ j i) = CodeJ₃S¹-sq j i
-- -- -- -- CodeJ₃S¹ (loop₃ k j i) =
-- -- -- --     Glue Co
-- -- -- --        λ {  (i = i0) → CodeJ₃S¹-sq k j , {!!} , {!!}
                                                
-- -- -- --           ; (i = i1) → CodeJ₃S¹-sq k j ,
-- -- -- --                 {!!} ∘ CodeJ₃S¹-sq-unglueSq k j
-- -- -- --                 , {!!}
-- -- -- --           ; (j = i0) → CodeJ₃S¹-sq k i , {!!} , {!!}
-- -- -- --           ; (j = i1) → CodeJ₃S¹-sq k i ,
-- -- -- --                 {!!} ∘ CodeJ₃S¹-sq-unglueSq k i
-- -- -- --                 , {!!}
-- -- -- --           ; (k = i0) → CodeJ₃S¹-sq j i , {!!} , {!!}
-- -- -- --           ; (k = i1) → CodeJ₃S¹-sq j i ,
-- -- -- --                 {!!} ∘ CodeJ₃S¹-sq-unglueSq j i
-- -- -- --                 , {!!}
-- -- -- --           }

-- -- -- --   -- Glue Co
-- -- -- --   --      λ {  (i = i0) → CodeJ₃S¹-sq j k ,
-- -- -- --   --                      lem3-CodeJ₃S¹ j k ,
-- -- -- --   --                      {!!}
                                                
-- -- -- --   --         ; (i = i1) → CodeJ₃S¹-sq j k ,
-- -- -- --   --                      unglueEquiv Co (j ∨ ~ j ∨ k ∨ ~ k ) (CodeJ₃S¹-pa j k)
-- -- -- --   --                       ∙ₑ ♯6-U k j
-- -- -- --   --         ; (j = i0) → CodeJ₃S¹-sq i k ,
-- -- -- --   --                    lem-CodeJ₃S¹ i k ,
-- -- -- --   --                      {!!}
-- -- -- --   --         ; (j = i1) → CodeJ₃S¹-sq i k ,
-- -- -- --   --                   lem2-CodeJ₃S¹ i k ,
-- -- -- --   --                   {!!}
-- -- -- --   --         ; (k = i0) → CodeJ₃S¹-sq i j ,
-- -- -- --   --                  fst (♯≃ j) ∘' ↑ ∘' ↑ ∘'
-- -- -- --   --                    fst (unglueEquiv Co (i ∨ ~ i ∨ j ∨ ~ j ) (CodeJ₃S¹-pa i j))
-- -- -- --   --                  , {!!}
-- -- -- --   --         ; (k = i1) → CodeJ₃S¹-sq i j ,
-- -- -- --   --                   fst (♯6-D (~ i) j) ∘'
-- -- -- --   --                   fst (unglueEquiv Co (i ∨ ~ i ∨ j ∨ ~ j ) (CodeJ₃S¹-pa i j))
-- -- -- --   --                   , {!!}
-- -- -- --   --         }


-- -- -- -- -- p∙[p⁻∙q]≡q : ∀ {ℓ} {A : Type ℓ} → {x y : A} → (p q : x ≡ y) → 
-- -- -- -- --               p ∙ (sym p ∙ q) ≡ q
-- -- -- -- -- p∙[p⁻∙q]≡q p q i j =
-- -- -- -- --    hcomp ( λ k → 
-- -- -- -- --           λ { (j = i0) → p i0
-- -- -- -- --             ; (j = i1) → compPath-filler' (sym p) q (~ i) k
-- -- -- -- --             ; (i = i1) → q (k ∧ j)
-- -- -- -- --             }) (p (j ∧ ~ i))

-- -- -- -- -- encode : ∀ x → base ≡ x → CodeJ₃S¹ x
-- -- -- -- -- encode x p = subst CodeJ₃S¹ p base


-- -- -- -- -- loopSqₓ : (loopₓ : Square loop loop loop loop) →
-- -- -- -- --            ∀ (q : base ≡ base) →  Square {A = J₃S¹}
-- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- --              (λ _ → base)
-- -- -- -- --              (λ _ → base)
-- -- -- -- -- loopSqₓ loopₓ q i =
-- -- -- -- --          (λ j' → loopₓ (j' ∧  ~ i) (j' ∧  i))
-- -- -- -- --        ∙ (λ j' → loopₓ (j' ∨ ~ i) (j' ∨ i)) ∙ q


-- -- -- -- -- loopSq : ∀ q → Square {A = J₃S¹}
-- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- --              (λ _ → base)
-- -- -- -- --              (λ _ → base)
-- -- -- -- -- loopSq = loopSqₓ loop₂

-- -- -- -- -- loopDiag : ∀ q → Square {A = J₃S¹}
-- -- -- -- --              (loop ∙ loop ∙ loop ∙ q)
-- -- -- -- --              (loop ∙ loop ∙ loop ∙ q)
-- -- -- -- --              (λ _ → base)
-- -- -- -- --              (λ _ → base)
-- -- -- -- -- loopDiag q =
-- -- -- -- --      cong (loop ∙_) (sym (loopSq q))
-- -- -- -- --   ∙∙ (λ i → (λ j' → loop₂ (j' ∧  ~ i) (j' ∧  i))
-- -- -- -- --             ∙ (λ j' → loop₂ (j' ∨ ~ i) (j' ∨ i)) ∙ loop ∙ q)
-- -- -- -- --   ∙∙ cong (loop ∙_) (loopSq q) 


-- -- -- -- -- loopSq₃' : ∀ (q : base ≡ base)
-- -- -- -- --             → Cube
-- -- -- -- --             (loopSq q) (loopSq (loop ∙ q))
-- -- -- -- --             (λ k → loop₂ (~ k) ∙ loop₂ (~ k)  ∙ compPath-filler' loop q k)
-- -- -- -- --             (λ k → loop₂ (~ k) ∙ loop₂ (~ k) ∙ compPath-filler' loop q k)
-- -- -- -- --            (λ i _ → loop (~ i)) refl
-- -- -- -- -- loopSq₃' q k i =
-- -- -- -- --      (λ j' → loop₃ (~ k) (j' ∧  ~ i) (j' ∧  i))
-- -- -- -- --        ∙ (λ j' → loop₃ (~ k) (j' ∨ ~ i) (j' ∨ i)) ∙
-- -- -- -- --           (compPath-filler' loop q k)


-- -- -- -- -- -- loopSq₃ : ∀ (q : base ≡ base) →
-- -- -- -- -- --            Cube
-- -- -- -- -- --             (cong (loop ∙_) (loopSq q))
-- -- -- -- -- --             (loopSq (loop ∙ q))
-- -- -- -- -- --             {!!}
-- -- -- -- -- --             {!!}
-- -- -- -- -- --             (λ _ _ → base)
-- -- -- -- -- --             λ _ _ → base
-- -- -- -- -- -- loopSq₃ q k i j =
-- -- -- -- -- --      hcomp (λ l →
-- -- -- -- -- --             λ { (j = i0) → base
-- -- -- -- -- --               ; (j = i1) → loopSq₃' q k i l
-- -- -- -- -- --               ; (k = i1) → loopSq (loop ∙ q) i (j ∧ l)
-- -- -- -- -- --               })
-- -- -- -- -- --               (loop (j ∧ ~ k))




-- -- -- -- -- loopSq₃ : ∀ (q : base ≡ base) →
-- -- -- -- --      Cube
-- -- -- -- --        (loopDiag q)
-- -- -- -- --        (cong (loop ∙_) (loopSq q))
-- -- -- -- --        (loopSq (loop ∙ q))
-- -- -- -- --        (loopSq (loop ∙ q))
-- -- -- -- --        refl
-- -- -- -- --        refl
-- -- -- -- -- loopSq₃ q k i j =
-- -- -- -- --    hcomp
-- -- -- -- --      (λ l →
-- -- -- -- --         λ { (k = i0) → doubleCompPath-filler
-- -- -- -- --                       (cong (loop ∙_) (sym (loopSq q)))
-- -- -- -- --                      (λ i → (λ j' → loop₂ (j' ∧  ~ i) (j' ∧  i))
-- -- -- -- --                       ∙ (λ j' → loop₂ (j' ∨ ~ i) (j' ∨ i)) ∙ loop ∙ q)
-- -- -- -- --                     (cong (loop ∙_) (loopSq q))
-- -- -- -- --                          l i j
-- -- -- -- --           ; (k = i1) → compPath-filler' loop (loopSq q i ) l j
-- -- -- -- --           ; (i = i0) → W.sq'-fill j l k
-- -- -- -- --           ; (i = i1) → W.sq'-fill j l k
-- -- -- -- --           ; (j = i0) → loop (k ∧ ~ l)
-- -- -- -- --           ; (j = i1) → W.sq'-fill j l k
-- -- -- -- --           })
-- -- -- -- --      (loopSq₃' q (~ k) i j)
-- -- -- -- --  where
-- -- -- -- --   module W = whiskSq (λ _ _ → J₃S¹)
-- -- -- -- --          (λ l k → loop (k ∧ ~ l))
-- -- -- -- --          ((λ k → loop₂ (k) ∙ loop₂ (k)  ∙ compPath-filler' loop q (~ k)))
-- -- -- -- --          (loopSq (loop ∙ q))
-- -- -- -- --          (λ l j → (loop ∙ loopSq q l) j)
-- -- -- -- --          (λ l j → compPath-filler' loop (loop ∙ loop ∙ q) l j)


-- -- -- -- -- loop₂' : Square loop loop loop loop
-- -- -- -- -- loop₂' = whiskSq.sq' (λ _ _ → J₃S¹)
-- -- -- -- --      loop₂ (λ k j → loop₂ (~ j) k) (λ k j → loop₂ (~ j) k)
-- -- -- -- --            (λ k i → loop₂ (~ i) k) (λ k i → loop₂ (~ i) k)

-- -- -- -- -- loop₂≡loop₂' : loop₂ ≡
-- -- -- -- --    (whiskSq.sq' (λ _ _ → J₃S¹)
-- -- -- -- --      loop₂ (λ k j → loop₂ (~ j) k) (λ k j → loop₂ (~ j) k)
-- -- -- -- --            (λ k i → loop₂ (~ i) k) (λ k i → loop₂ (~ i) k))
-- -- -- -- -- loop₂≡loop₂' k i j =
-- -- -- -- --   hcomp (λ l →
-- -- -- -- --       λ { (k = i0) → loop₂ i j
-- -- -- -- --         ; (i = i0) → loop₂ (k ∧ ~ l) j
-- -- -- -- --         ; (i = i1) → loop₂ (k ∧ ~ l) j
-- -- -- -- --         ; (j = i0) → loop₂ (k ∧ ~ l) i
-- -- -- -- --         ; (j = i1) → loop₂ (k ∧ ~ l) i
-- -- -- -- --         })
-- -- -- -- --         (loop₃ k i j) 

-- -- -- -- -- loopSq' : ∀ q → Square {A = J₃S¹}
-- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- --              (λ _ → base)
-- -- -- -- --              (λ _ → base)
-- -- -- -- -- loopSq' = loopSqₓ loop₂'

-- -- -- -- -- loopSq≡Sq' : ∀ q → loopSq q ≡ loopSq' q 
-- -- -- -- -- loopSq≡Sq' q i = loopSqₓ (loop₂≡loop₂' i) q




-- -- -- -- -- CoLoop : Co → Path J₃S¹ base base
-- -- -- -- -- CoLoop base = refl
-- -- -- -- -- CoLoop (↑ x) = loop ∙ CoLoop x
-- -- -- -- -- CoLoop (↓ x) = (sym loop) ∙ CoLoop x
-- -- -- -- -- CoLoop (↓↑ x i) = p∙[p⁻∙q]≡q (sym loop) (CoLoop x) i 
-- -- -- -- -- CoLoop (↑↓ x i) = p∙[p⁻∙q]≡q (loop) (CoLoop x) i
-- -- -- -- -- CoLoop (♯ x i) = loopSq (CoLoop x) i
-- -- -- -- -- CoLoop (⇅⇅⇅-diag x i) = loopDiag (CoLoop x) i
-- -- -- -- -- CoLoop (⇅⇅⇅-U x i i₁) =
-- -- -- -- --   let q = CoLoop x
-- -- -- -- --   in  doubleCompPath-filler
-- -- -- -- --      (cong (loop ∙_) (sym (loopSq q)))
-- -- -- -- --     (λ i → (λ j' → loop₂ (j' ∧  ~ i) (j' ∧  i))
-- -- -- -- --             ∙ (λ j' → loop₂ (j' ∨ ~ i) (j' ∨ i)) ∙ loop ∙ q)
-- -- -- -- --     (cong (loop ∙_) (loopSq q)) 
-- -- -- -- --       i i₁
-- -- -- -- -- CoLoop (⇅⇅⇅-D x i i₁) = loopSq₃ (CoLoop x) i i₁


-- -- -- -- -- decode : ∀ x → CodeJ₃S¹ x → base ≡ x
-- -- -- -- -- decode base p = CoLoop p
-- -- -- -- -- decode (loop i) = {!!}
-- -- -- -- -- decode (loop₂ i j) p = {!!}
-- -- -- -- -- decode (loop₃ i j k) p = {!!}


-- -- -- -- -- -- -- loop₃' : Cube loop₂ loop₂ loop₂ loop₂ loop₂ loop₂
-- -- -- -- -- -- -- loop₃' = loop₃

-- -- -- -- -- -- -- J₃S¹-hexa₀ J₃S¹-hexa₁ : (loop ∙∙ loop ∙∙ loop) ≡ (loop ∙∙ loop ∙∙ loop)
-- -- -- -- -- -- -- J₃S¹-hexa₀ = {!!}
-- -- -- -- -- -- -- J₃S¹-hexa₁ = {!!}

-- -- -- -- -- -- -- J₃S¹-hexa : Path ((loop ∙∙ loop ∙∙ loop) ≡ (loop ∙∙ loop ∙∙ loop))
-- -- -- -- -- -- --             {!!} {!!}
-- -- -- -- -- -- -- J₃S¹-hexa = {!!}

-- -- -- -- -- -- -- infixl 6 _⊕_

-- -- -- -- -- -- -- infixl 10 ─_


-- -- -- -- -- -- -- data ℤᵍ : Type where
-- -- -- -- -- -- --  zero one  : ℤᵍ
-- -- -- -- -- -- --  _⊕_ : ℤᵍ → ℤᵍ → ℤᵍ
-- -- -- -- -- -- --  ─_ : ℤᵍ → ℤᵍ
-- -- -- -- -- -- --  ⊕─ : ∀ x → x ⊕ ─ x ≡ zero

-- -- -- -- -- -- --  ⊕-assoc : ∀ x y z → x ⊕ (y ⊕ z) ≡ x ⊕ y ⊕ z
 
-- -- -- -- -- -- --  zero-⊕ : ∀ x → zero ⊕ x ≡ x
-- -- -- -- -- -- --  ⊕-zero : ∀ x → x ⊕ zero ≡ x

-- -- -- -- -- -- --  ⊕-triangle : ∀ x y  →
-- -- -- -- -- -- --     Square                      
-- -- -- -- -- -- --         (⊕-assoc x zero y)
-- -- -- -- -- -- --         refl
-- -- -- -- -- -- --         (cong (x ⊕_) (zero-⊕ y))
-- -- -- -- -- -- --         (cong (_⊕ y) (⊕-zero x))
        


-- -- -- -- -- -- --  ⊕-penta-diag : ∀ x y z w →
-- -- -- -- -- -- --    x ⊕ y ⊕ z ⊕ w ≡ x ⊕ (y ⊕ (z ⊕ w))
-- -- -- -- -- -- --  ⊕-penta-△ : ∀ x y z w →
-- -- -- -- -- -- --    Square
-- -- -- -- -- -- --      refl
-- -- -- -- -- -- --      (⊕-penta-diag x y z w)
-- -- -- -- -- -- --      (⊕-assoc _ _ _)
-- -- -- -- -- -- --      (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- --  ⊕-penta-□ : ∀ x y z w →
-- -- -- -- -- -- --     Square
-- -- -- -- -- -- --      (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- --      (⊕-penta-diag x y z w)
-- -- -- -- -- -- --      (cong (_⊕ w) (⊕-assoc _ _ _))
-- -- -- -- -- -- --      (cong (x ⊕_) (sym (⊕-assoc _ _ _)))

-- -- -- -- -- -- --  -- ⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
-- -- -- -- -- -- --  -- ⊕-hexa-diag : ∀ x y z → x ⊕ y ⊕ z ≡ y ⊕ (z ⊕ x)
-- -- -- -- -- -- --  -- ⊕-hexa-↑ : ∀ x y z →
-- -- -- -- -- -- --  --   Square
-- -- -- -- -- -- --  --      (⊕-comm x (y ⊕ z))
-- -- -- -- -- -- --  --      (⊕-hexa-diag x y z)
-- -- -- -- -- -- --  --      (⊕-assoc _ _ _)
-- -- -- -- -- -- --  --      (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- --  -- ⊕-hexa-↓ : ∀ x y z →
-- -- -- -- -- -- --  --    Square
-- -- -- -- -- -- --  --       (⊕-hexa-diag x y z)
-- -- -- -- -- -- --  --       (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- --  --       (cong (_⊕ z) (⊕-comm _ _))
-- -- -- -- -- -- --  --       (cong (y ⊕_) (⊕-comm _ _))

-- -- -- -- -- -- --  ⊕-comm : one ⊕ one ≡ one ⊕ one
-- -- -- -- -- -- --  ⊕-comm-assoc : one ⊕ (one ⊕ one) ≡ one ⊕ one ⊕ one 

-- -- -- -- -- -- --  ⊕-comp : Square
-- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- --            {!!}

-- -- -- -- -- -- --  -- ⊕-hexa-diag : one ⊕ one ⊕ one ≡ one ⊕ (one ⊕ one)
-- -- -- -- -- -- --  -- ⊕-hexa-L : 
-- -- -- -- -- -- --  --   Square
-- -- -- -- -- -- --  --      (cong (one ⊕_) ⊕-comm)
-- -- -- -- -- -- --  --      (cong (_⊕ one) ⊕-comm)
-- -- -- -- -- -- --  --      (⊕-assoc _ _ _ )
-- -- -- -- -- -- --  --      ({!!})
 
-- -- -- -- -- -- --  -- ⊕-hexa-↓ : ∀ x y z →
-- -- -- -- -- -- --  --    Square
-- -- -- -- -- -- --  --       (⊕-hexa-diag x y z)
-- -- -- -- -- -- --  --       (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- --  --       (cong (_⊕ z) (⊕-comm _ _))
-- -- -- -- -- -- --  --       (cong (y ⊕_) (⊕-comm _ _))


-- -- -- -- -- -- -- ℤᵍ→Co≃ : ℤᵍ → Co ≃ Co
-- -- -- -- -- -- -- ℤᵍ→Co≃ zero = idEquiv _
-- -- -- -- -- -- -- ℤᵍ→Co≃ one = ↑≃
-- -- -- -- -- -- -- ℤᵍ→Co≃ (x ⊕ x₁) = ℤᵍ→Co≃ x ∙ₑ ℤᵍ→Co≃ x₁
-- -- -- -- -- -- -- ℤᵍ→Co≃ (─ x) = invEquiv (ℤᵍ→Co≃ x)
-- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕─ x i) = {!!}
-- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-assoc x x₁ x₂ i) =
-- -- -- -- -- -- --   compEquiv-assoc (ℤᵍ→Co≃ x) (ℤᵍ→Co≃ x₁) (ℤᵍ→Co≃ x₂) i
-- -- -- -- -- -- -- ℤᵍ→Co≃ (zero-⊕ x i) = {!!}
-- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-zero x i) = {!!}
-- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-triangle x x₁ i i₁) = {!!}
-- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-penta-diag x x₁ x₂ x₃ i) = {!!}
-- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-penta-△ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-penta-□ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-comm i) = ♯≃ i
-- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-comm-assoc i) = {!!}
-- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-comp i i₁) = {!!}

-- -- -- -- -- -- -- ℤᵍ←Co≃' : Co → ℤᵍ
-- -- -- -- -- -- -- ℤᵍ←Co≃' base = zero
-- -- -- -- -- -- -- ℤᵍ←Co≃' (↑ x) = one ⊕ ℤᵍ←Co≃' x
-- -- -- -- -- -- -- ℤᵍ←Co≃' (↓ x) = (─ one) ⊕ ℤᵍ←Co≃' x
-- -- -- -- -- -- -- ℤᵍ←Co≃' (↓↑ x i) = ({!!} ∙  ((⊕-assoc (─ one) one (ℤᵍ←Co≃' x))) ∙
-- -- -- -- -- -- --                             cong (_⊕ (ℤᵍ←Co≃' x)) {!⊕─ !}
-- -- -- -- -- -- --                              ∙ {!!}) i
-- -- -- -- -- -- -- ℤᵍ←Co≃' (↑↓ x i) = (((⊕-assoc (one) (─ one) (ℤᵍ←Co≃' x))) ∙
-- -- -- -- -- -- --                             cong (_⊕ (ℤᵍ←Co≃' x)) (⊕─ one )
-- -- -- -- -- -- --                              ∙ zero-⊕ (ℤᵍ←Co≃' x)) i
-- -- -- -- -- -- -- ℤᵍ←Co≃' (♯ x i) = {!!}
-- -- -- -- -- -- -- ℤᵍ←Co≃' (⇅⇅⇅-diag x i) = {!!}
-- -- -- -- -- -- -- ℤᵍ←Co≃' (⇅⇅⇅-U x i i₁) = {!!}
-- -- -- -- -- -- -- ℤᵍ←Co≃' (⇅⇅⇅-D x i i₁) = {!!}


-- -- -- -- -- -- -- ℤᵍ←Co≃ : Co ≃ Co → ℤᵍ
-- -- -- -- -- -- -- ℤᵍ←Co≃ e = ℤᵍ←Co≃' (fst e base)

-- -- -- -- -- -- -- -- toJ₃S¹ : ℤᵍ → Path J₃S¹ base base
-- -- -- -- -- -- -- -- toJ₃S¹ zero = refl
-- -- -- -- -- -- -- -- toJ₃S¹ one = loop
-- -- -- -- -- -- -- -- toJ₃S¹ (x ⊕ x₁) = toJ₃S¹ x ∙ toJ₃S¹ x₁
-- -- -- -- -- -- -- -- toJ₃S¹ (─ x) = sym (toJ₃S¹ x)
-- -- -- -- -- -- -- -- toJ₃S¹ (⊕─ x i) = rCancel (toJ₃S¹ x) i
-- -- -- -- -- -- -- -- toJ₃S¹ (⊕-comm x x₁ i) = {!PathP→comm loop₂!}
-- -- -- -- -- -- -- -- toJ₃S¹ (⊕-assoc x x₁ x₂ i) = {!!}
-- -- -- -- -- -- -- -- toJ₃S¹ (zero-⊕ x i) = {!!}
-- -- -- -- -- -- -- -- toJ₃S¹ (⊕-zero x i) = {!!}
-- -- -- -- -- -- -- -- toJ₃S¹ (⊕-triangle x x₁ i i₁) = {!!}
-- -- -- -- -- -- -- -- toJ₃S¹ (⊕-penta-diag x x₁ x₂ x₃ i) = {!!}
-- -- -- -- -- -- -- -- toJ₃S¹ (⊕-penta-△ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- -- toJ₃S¹ (⊕-penta-□ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- -- toJ₃S¹ (⊕-hexa-diag x x₁ x₂ i) = {!!}
-- -- -- -- -- -- -- -- toJ₃S¹ (⊕-hexa-↑ x x₁ x₂ i i₁) = {!!}
-- -- -- -- -- -- -- -- toJ₃S¹ (⊕-hexa-↓ x x₁ x₂ i i₁) = {!!}
