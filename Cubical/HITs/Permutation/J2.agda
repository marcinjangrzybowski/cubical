{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.J2 where

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
 loop : ∀ x → x ≡ x
 ↑ ↓ : Co → Co
 ↓↑ : ∀ x → ↓ (↑ x) ≡ x 
 ↑↓ : ∀ x → ↑ (↓ x) ≡ x
 
 ⇅⇅⇅-diag : ∀ x → (↑ x) ≡ (↑ x)
 ⇅⇅⇅-U : ∀ x →
     Square
       (loop (↑ x))
       (⇅⇅⇅-diag x)
       (cong ↑ (loop x))
       (cong ↑ (loop x))

 ⇅⇅⇅-D : ∀ x →
     Square
       (⇅⇅⇅-diag x)              
       (cong ↑ (loop x))
       (loop (↑ x))
       (loop (↑ x))
 trunc : isGroupoid Co

loopExt : idfun Co ≡ idfun Co
loopExt = funExt loop

diagExt : ↑ ≡ ↑
diagExt = funExt ⇅⇅⇅-diag

⇅⇅⇅-Uext : 
     Square {A = Co → Co}
       (λ i x → loopExt i (↑ x))
       (λ i x → ⇅⇅⇅-diag x i)
       (λ i x → ↑ (loopExt i x))
       (λ i x → ↑ (loopExt i x))

⇅⇅⇅-Uext j i x = ⇅⇅⇅-U x j i 

_∙ₑloop : ∀ (e : Co ≃ Co) → e ≡ e
_∙ₑloop e = equivEq (cong (_∘' fst e) loopExt) 

loop∙ₑ : ∀ (e : Co ≃ Co) → e ≡ e
loop∙ₑ e = equivEq (cong (fst e ∘'_) loopExt) 


↑Iso : Iso Co Co
Iso.fun ↑Iso = ↑
Iso.inv ↑Iso = ↓
Iso.rightInv ↑Iso = ↑↓
Iso.leftInv ↑Iso = ↓↑

↑≃ : Co ≃ Co
↑≃ = isoToEquiv ↑Iso

Co≡ : Co ≡ Co
Co≡ = ua ↑≃

CodeJ₃S¹-pa : ∀ j i → Partial ((i ∧ j) ∨ ~ i ∨ ~ j)
        (Σ Type (λ T → T ≃ Co))
CodeJ₃S¹-pa j i =
      λ { (i = i1)(j = i1) → Co , idEquiv _
       ; (i = i0) → Co≡ j , loopExt j ∘ fst (ua-unglueEquiv ↑≃ j ∙ₑ ↑≃) , {!!} 
       ; (j = i0) → Co≡ i , fst (ua-unglueEquiv ↑≃ i ∙ₑ ↑≃) , {!!}
       }


CoSq : Square Co≡ Co≡ Co≡ Co≡
CoSq j i =
  Glue Co {(i ∧ j) ∨ ~ i ∨ ~ j}
    (CodeJ₃S¹-pa j i)

ung-↑ = ua-ungluePathExt ↑≃

CodeJ₃S¹-unglue : SquareP (λ j i → CoSq j i → Co)
                       (λ i x → ↑ (ung-↑ i x))
                       (ung-↑)
                       (λ i x → loop (↑ (ung-↑ i x)) i)
                       (ung-↑)
CodeJ₃S¹-unglue j i = unglue ((i ∧ j) ∨ ~ i ∨ ~ j)

CodeJ₃S¹-unglue' : SquareP (λ j i → CoSq j i → Co)
                       (λ i x → loopExt i (↑ (ung-↑ i x))) 
                       (λ i x → loopExt i ((ung-↑ i x)))
                       (λ i x → loopExt i (↑ (ung-↑ i x)))
                       (ung-↑)
CodeJ₃S¹-unglue' j i = loopExt i ∘ unglue ((i ∧ j) ∨ ~ i ∨ ~ j)

CodeJ₃S¹-unglue'' : SquareP (λ j i → CoSq j i → Co)
                       (λ i x → (loopExt i ∘ ↑) (↑ (ung-↑ i x))) 
                       (λ i x → diagExt i ((ung-↑ i x)))
                       (λ j x → ↑ (loopExt j (loopExt j (↑ (ung-↑ j x)))))
                       (λ j x → ↑ (loopExt j (ung-↑ j x)))
CodeJ₃S¹-unglue'' j i = ⇅⇅⇅-Uext j i ∘ unglue ((i ∧ j) ∨ ~ i ∨ ~ j)

-- CodeJ₃S¹-unglue'' : SquareP (λ j i → CoSq j i → Co)
--                        (λ i x → (loopExt i ∘ ↑) (↑ (ung-↑ i x))) 
--                        (λ i x → diagExt i ((ung-↑ i x)))
--                        (λ j x → ↑ (loopExt j (loopExt j (↑ (ung-↑ j x)))))
--                        (λ j x → ↑ (loopExt j (ung-↑ j x)))
-- CodeJ₃S¹-unglue'' j i = ⇅⇅⇅-Uext j i ∘ unglue ((i ∧ j) ∨ ~ i ∨ ~ j)


-- CodeJ₃S¹-unglue' : SquareP (λ j i → CoSq j i → Co)
--                        (congP (λ _ → ↑ ∘'_) (ua-ungluePathExt ↑≃))
--                        (ua-ungluePathExt ↑≃)
--                        ((congP (λ j → (loopExt j ∘' ↑) ∘'_) (ua-ungluePathExt ↑≃)))
--                        (ua-ungluePathExt ↑≃)
-- CodeJ₃S¹-unglue' j i = unglue ((i ∧ j) ∨ ~ i ∨ ~ j)



CoCu : Cube CoSq CoSq CoSq CoSq CoSq CoSq
CoCu k j i =   Glue Co
       λ {  (i = i0) → CoSq k j , (λ x → ↑ (loopExt k (loopExt k (loopExt j (loopExt j ( ↑ (CodeJ₃S¹-unglue k j x))))))) , {!!}
                                                
          ; (i = i1) → CoSq k j , CodeJ₃S¹-unglue'' k j , {!!}
          ; (j = i0) → CoSq k i , (λ x → loopExt (~ i) (↑ (loopExt k ( loopExt k (↑ ( CodeJ₃S¹-unglue k i x )))))) , {!!}
          ; (j = i1) → CoSq k i , (λ x → loop (↑ (loop (CodeJ₃S¹-unglue k i x) k)) (~ i)) , {!!}
          ; (k = i0) → CoSq j i , (λ x → {!CodeJ₃S¹-unglue j i x!}) , {!!}
          ; (k = i1) → CoSq j i , (λ x → ⇅⇅⇅-D (CodeJ₃S¹-unglue j i x) (~ i) j) , {!!}
          }


-- -- CoCu : Cube CoSq CoSq CoSq CoSq CoSq CoSq
-- -- CoCu k j i =
-- --    Glue Co {(i ∧ j ∧ k) ∨ (~ i) ∨ (~ j) ∨ (~ k)}
-- --      λ { (i = i1)(j = i1)(k = i1) → Co , idEquiv _
-- --        ; (i = i0) → CoSq k j , {!!} , {!!}
-- --        ; (j = i0) → CoSq k i , {!!} , {!!}
-- --        ; (k = i0) → CoSq j i , ↑ ∘' CodeJ₃S¹-unglue j i , {!!}
-- --        }

CodeJ₃S¹ : J₃S¹ → Type
CodeJ₃S¹ base = Co
CodeJ₃S¹ (loop i) = Co≡ i
CodeJ₃S¹ (loop₂ j i) = CoSq j i
CodeJ₃S¹ (loop₃ k j i) = CoCu k j i

p∙[p⁻∙q]≡q : ∀ {ℓ} {A : Type ℓ} → {x y : A} → (p q : x ≡ y) → 
              p ∙ (sym p ∙ q) ≡ q
p∙[p⁻∙q]≡q p q i j =
   hcomp ( λ k → 
          λ { (j = i0) → p i0
            ; (j = i1) → compPath-filler' (sym p) q (~ i) k
            ; (i = i1) → q (k ∧ j)
            }) (p (j ∧ ~ i))

encode : ∀ x → base ≡ x → CodeJ₃S¹ x
encode x p = subst CodeJ₃S¹ p base


CoLoop : Co → Path J₃S¹ base base
CoLoop base = refl
CoLoop (↑ x) = loop ∙ CoLoop x
CoLoop (↓ x) = (sym loop) ∙ CoLoop x
CoLoop (↓↑ x i) = p∙[p⁻∙q]≡q (sym loop) (CoLoop x) i 
CoLoop (↑↓ x i) = p∙[p⁻∙q]≡q (loop) (CoLoop x) i
CoLoop (loop x i) j = {!CoLoop x j!} --loopSq (CoLoop x) i
CoLoop (⇅⇅⇅-diag x i) j = {!!} --loopDiag (CoLoop x) i
CoLoop (⇅⇅⇅-U x i i₁) = {!!}
  -- let q = CoLoop x
  -- in  doubleCompPath-filler
  --    (cong (loop ∙_) (sym (loopSq q)))
  --   (λ i → (λ j' → loop₂ (j' ∧  ~ i) (j' ∧  i))
  --           ∙ (λ j' → loop₂ (j' ∨ ~ i) (j' ∨ i)) ∙ loop ∙ q)
  --   (cong (loop ∙_) (loopSq q)) 
  --     i i₁
CoLoop (⇅⇅⇅-D x i i₁) = {!!} --loopSq₃ (CoLoop x) i i₁
CoLoop (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) = {!!}

-- -- -- ♯≃-diag6 : ↑≃ ∙ₑ ↑≃ ∙ₑ ↑≃ ≡ ↑≃ ∙ₑ ↑≃ ∙ₑ ↑≃
-- -- -- ♯≃-diag6 = equivEq (funExt ⇅⇅⇅-diag)


-- -- -- ♯6-U : Square {A = Co ≃ Co}
-- -- --           (cong (↑≃ ∙ₑ_) ♯≃)
-- -- --           ♯≃-diag6
-- -- --           (equivEq (cong fst (cong (_∙ₑ ↑≃) ♯≃)))
-- -- --           (equivEq (cong fst (cong (_∙ₑ ↑≃) ♯≃)))
-- -- -- ♯6-U =
-- -- --   ΣSquarePSet (λ i j a → isProp→isSet (isPropIsEquiv a))
-- -- --     _ _ _ _ λ i j x → ⇅⇅⇅-U x i j

-- -- -- ♯6-D : Square {A = Co ≃ Co}
-- -- --           ♯≃-diag6
-- -- --           (equivEq (cong fst (cong (_∙ₑ ↑≃) ♯≃)))
-- -- --           (cong (↑≃ ∙ₑ_) ♯≃)
-- -- --           (cong (↑≃ ∙ₑ_) ♯≃)
          
-- -- -- ♯6-D =
-- -- --     ΣSquarePSet (λ i j a → isProp→isSet (isPropIsEquiv a))
-- -- --     _ _ _ _ λ i j x → ⇅⇅⇅-D x i j



-- -- -- module _ {ℓ} {A : Type ℓ} (e : A ≃ A) where

-- -- --  T₀ : Type ℓ
-- -- --  T₀ = ∀ x → (fst e (fst e x)) ≡ (fst e (fst e x)) 

-- -- --  T₁ : Type ℓ
-- -- --  T₁ = (x : A) → x ≡ x 


-- -- --  q : T₀ ≃ T₁
-- -- --  q = funExtEquiv ∙ₑ 
-- -- --          ( congEquiv (postCompEquiv (invEquiv e ∙ₑ invEquiv e))
-- -- --           ∙ₑ ∙∙≃ (funExt (retEq (e ∙ₑ e)))
-- -- --                   ((funExt (retEq (e ∙ₑ e)))))
-- -- --       ∙ₑ invEquiv funExtEquiv


-- -- -- -- -- G♯6 : Cube
-- -- -- -- --        {!!}
-- -- -- -- --        {!!}
-- -- -- -- --        {!!}
-- -- -- -- --        {!!}
-- -- -- -- --        {!!}
-- -- -- -- --        {!!} 
-- -- -- -- -- G♯6 i j k =
-- -- -- -- --   Glue {!!}
-- -- -- -- --        {!!}

-- -- -- -- CodeJ₃S¹-pa : ∀ i j → Partial (i ∨ ~ i ∨ j ∨ ~ j)
-- -- -- --         (Σ Type (λ T → T ≃ Co))
-- -- -- -- CodeJ₃S¹-pa i j =
-- -- -- --    λ {  (i = i0) → Co≡ j ,
-- -- -- --                 ua-unglueEquiv ↑≃ j ∙ₑ ♯≃ j
-- -- -- --           ; (i = i1) → Co≡ j ,
-- -- -- --                 ua-unglueEquiv ↑≃ j ∙ₑ ↑≃ 
-- -- -- --           ; (j = i0) → Co≡ i ,
-- -- -- --                         (↑ ∘ ↑) ∘ fst (ua-unglueEquiv ↑≃ i) ,
-- -- -- --                         isProp→PathP
-- -- -- --                           (λ i → isPropIsEquiv
-- -- -- --                             ((↑ ∘ ↑) ∘ fst (ua-unglueEquiv ↑≃ i)))
-- -- -- --                           (snd (compEquiv ↑≃ (↑≃ ∙ₑ ↑≃)))
-- -- -- --                           (snd (compEquiv ↑≃ ↑≃))
-- -- -- --                            i

-- -- -- --           ; (j = i1) → Co≡ i ,
-- -- -- --                         ↑ ∘ fst (ua-unglueEquiv ↑≃ i) ,
-- -- -- --                         isProp→PathP
-- -- -- --                           (λ i → isPropIsEquiv
-- -- -- --                             (↑ ∘ fst (ua-unglueEquiv ↑≃ i)))
-- -- -- --                           (snd (compEquiv (idEquiv Co) (↑≃ ∙ₑ ↑≃)))
-- -- -- --                           (snd (compEquiv (idEquiv Co) ↑≃))
-- -- -- --                            i
-- -- -- --           }




-- -- -- -- CodeJ₃S¹-sq : Square Co≡ Co≡ Co≡ Co≡
-- -- -- -- CodeJ₃S¹-sq i j =
-- -- -- --     Glue Co {i ∨ ~ i ∨ j ∨ ~ j}
-- -- -- --        (CodeJ₃S¹-pa i j)

-- -- -- -- -- CodeJ₃S¹-sq-unglueSq : 
-- -- -- -- --                   SquareP (λ i k → CodeJ₃S¹-sq i k → Co)
-- -- -- -- --                           (λ k x → ♯ (ua-unglue ↑≃ k x) k)
-- -- -- -- --                           (λ k x → ↑ (ua-unglue ↑≃ k x))
-- -- -- -- --                           (λ i x → ↑ (↑ (ua-unglue ↑≃ i x)))
-- -- -- -- --                           (λ i x → ↑ (ua-unglue ↑≃ i x))
-- -- -- -- -- CodeJ₃S¹-sq-unglueSq i k = unglue (i ∨ ~ i ∨ k ∨ ~ k)
                          

-- -- -- -- -- -- -- lem-CodeJ₃S¹-lem : SquareP (λ i _ → Co≡ i → Co)
-- -- -- -- -- -- --                      (λ z x → ♯ (↑ (♯ (↑ x) z)) z)
-- -- -- -- -- -- --                      (λ z x → ↑ (↑ (↑ (♯ x z))))
-- -- -- -- -- -- --                      (λ i x → ↑ (↑ (↑ (↑ (↑ (ua-unglue ↑≃ i x) )))))
-- -- -- -- -- -- --                      λ i x → ♯ (↑ (↑ (↑ (ua-unglue ↑≃ i x) ))) (~ i)
-- -- -- -- -- -- -- lem-CodeJ₃S¹-lem i z x =
-- -- -- -- -- -- --   ♯ (↑ ( hcomp (λ q →
-- -- -- -- -- -- --                 λ { (i = i0) → ♯ (ua-unglue ↑≃ i0 x) (z ∨ ~ q)
-- -- -- -- -- -- --                   ; (i = i1) → ♯ x z
-- -- -- -- -- -- --                    ; (z = i0) → ♯ (ua-unglue ↑≃ i x) (~ i ∧ ~ q)
-- -- -- -- -- -- --                   ; (z = i1) → ↑ (↑ (ua-unglue ↑≃ i x))
-- -- -- -- -- -- --                   })
-- -- -- -- -- -- --               (♯ (ua-unglue ↑≃ i x) (z ∨ ~ i)) )) (z ∧   ~ i)

-- -- -- -- -- -- -- lem-CodeJ₃S¹ : SquareP (λ i k → CodeJ₃S¹-sq i k → Co)
-- -- -- -- -- -- --                    (λ k x →
-- -- -- -- -- -- --                      (((λ j' → ↑ (♯ (↑ (♯ (ua-unglue ↑≃ k x) j')) j')))
-- -- -- -- -- -- --                       ∙ λ z → ♯ (↑ (♯ (↑ (ua-unglue ↑≃ k x)) z)) z ) k )
-- -- -- -- -- -- --                    (λ k x →
-- -- -- -- -- -- --                       ↑ (♯ (♯ ((ua-unglue ↑≃ k x)) k) k))
-- -- -- -- -- -- --                    (λ i x → ↑ (↑ ( ↑ (↑ (↑ (↑ (ua-unglue ↑≃ i x)))))))
-- -- -- -- -- -- --                    (λ i x → ♯ (↑ (↑ (↑ (ua-unglue ↑≃ i x)))) (~ i))
-- -- -- -- -- -- -- lem-CodeJ₃S¹ = whiskSq.sq' (λ z k → CodeJ₃S¹-sq z k → Co)
-- -- -- -- -- -- --     (λ i k →  ↑ ∘' funExt ♯ k ∘' ↑ ∘' fst (unglueEquiv Co (i ∨ ~ i ∨ k ∨ ~ k ) (CodeJ₃S¹-pa i k)))
     
-- -- -- -- -- -- --     (λ j z x → (compPath-filler
-- -- -- -- -- -- --          (λ j' → ↑ (♯ (↑ (♯ (ua-unglue ↑≃ j x) j')) j'))
-- -- -- -- -- -- --          λ z → ♯ (↑ (♯ (↑ (ua-unglue ↑≃ j x)) z)) z ) z j)
-- -- -- -- -- -- --     (λ j z x → ↑ (♯ (♯ ((ua-unglue ↑≃ j x)) (z ∧ j)) j))
-- -- -- -- -- -- --     (λ i z x → ↑ (↑ (↑ (↑ (↑ (↑ (ua-unglue ↑≃ i x)))))))
-- -- -- -- -- -- --     lem-CodeJ₃S¹-lem


-- -- -- -- -- -- lem2-CodeJ₃S¹ : SquareP (λ i k → CodeJ₃S¹-sq i k → Co)

-- -- -- -- -- --                    (congP (λ k f → f ∘' ua-unglue ↑≃ k)
-- -- -- -- -- --                          ((λ i x → ↑ (♯ (♯ x i) i))
-- -- -- -- -- --                           ∙ λ i z → ♯ (↑ (↑ (↑ z))) i))
-- -- -- -- -- --                    (λ k x → ↑ (♯ (↑ (ua-unglue ↑≃ k x)) k))
-- -- -- -- -- --                    (λ i x → ↑ (↑ (↑ (↑ (↑ (ua-unglue ↑≃ i x))))) )
-- -- -- -- -- --                    (λ i x → ♯ (↑ (↑ (ua-unglue ↑≃ i x))) (~ i))
-- -- -- -- -- -- lem2-CodeJ₃S¹ =
-- -- -- -- -- --   congSqP (λ i k f → f ∘' (λ x → unglue (i ∨ ~ i ∨ k ∨ ~ k) x))
-- -- -- -- -- --     (symP (compPath-filler (cong (↑ ∘'_) ♯ₑ) (cong (_∘' ↑) ♯ₑ)))

-- -- -- -- -- -- -- lem3-CodeJ₃S¹-lem : SquareP (λ j i → Co≡ j → Co)
-- -- -- -- -- -- --                       ( refl)
-- -- -- -- -- -- --                       (λ i x → ♯ (↑ (♯ x i)) i)
-- -- -- -- -- -- --                       (λ j x → ↑ (♯ₑ j (↑ (↑ (ua-unglue ↑≃ j x)))))
-- -- -- -- -- -- --                       λ j x → ((λ j' →
-- -- -- -- -- -- --                          ↑ (♯ (♯ (ua-unglue ↑≃ j x) j') j'))
-- -- -- -- -- -- --                           ∙ λ j' → ♯ (↑ (↑ (↑ (ua-unglue ↑≃ j x)))) j') j
-- -- -- -- -- -- -- lem3-CodeJ₃S¹-lem j i x = {!!}

-- -- -- -- -- -- -- unglue-lem : SquareP (λ j k → CodeJ₃S¹-sq j k → Co)
-- -- -- -- -- -- --                  {!!}
-- -- -- -- -- -- --                  {!!}
-- -- -- -- -- -- --                  {!!}
-- -- -- -- -- -- --                  {!!}
-- -- -- -- -- -- -- unglue-lem j k x = {!unglue ? !}
-- -- -- -- -- -- -- lem3-CodeJ₃S¹-test :
-- -- -- -- -- -- --    SquareP (λ j k → CodeJ₃S¹-sq j k → Co)
-- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- lem3-CodeJ₃S¹-test =
-- -- -- -- -- -- --    whiskSq.sq' _
-- -- -- -- -- -- --       CodeJ₃S¹-sq-unglueSq
-- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- --       {!!}

-- -- -- -- -- -- -- lem3-CodeJ₃S¹ : SquareP (λ j k → CodeJ₃S¹-sq j k → Co)
-- -- -- -- -- -- --   (congP (λ k f → f ∘' ua-unglue ↑≃ k)
-- -- -- -- -- -- --               ((λ k' x → ↑ (♯ (↑ (♯ x k')) k'))
-- -- -- -- -- -- --                       ∙ λ k' x → ♯ (↑ (♯ (↑ x) k')) k' ))
-- -- -- -- -- -- --   (congP (λ k f → f ∘' ua-unglue ↑≃ k)
-- -- -- -- -- -- --                          ((λ k' x → ↑ (♯ (♯ x k') k'))
-- -- -- -- -- -- --                           ∙ λ k' z → ♯ (↑ (↑ (↑ z))) k'))
-- -- -- -- -- -- --   (λ j z → ♯ (↑ (↑ (♯ (ua-unglue ↑≃ j z) j))) j)
-- -- -- -- -- -- --   (λ j z → ↑ (♯ (♯ (ua-unglue ↑≃ j z) j) j))
-- -- -- -- -- -- -- lem3-CodeJ₃S¹ =
-- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- --   whiskSq.sq' _
-- -- -- -- -- -- --    (λ j k x → ↑ (♯ₑ j (CodeJ₃S¹-sq-unglueSq j k x)))
-- -- -- -- -- -- --       {{!!}}
-- -- -- -- -- -- --       {{!!}}    
-- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- --       {{!!}}
-- -- -- -- -- -- --       {{!!}}
-- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- --     -- (λ j i x →
-- -- -- -- -- -- --     --   compPath-filler ( λ j' → ↑ (♯ₑ j' (↑ (♯ₑ j' (ua-unglue ↑≃ j x)))))
-- -- -- -- -- -- --     --    (λ z → ♯ (↑ (♯ (↑ (ua-unglue ↑≃ j x)) z)) z) i j)
-- -- -- -- -- -- --     -- (lem3-CodeJ₃S¹-lem)
-- -- -- -- -- -- --     -- (λ i j → {!!})
-- -- -- -- -- -- --     -- λ i j → {!!}
-- -- -- -- -- -- --     -- (λ i i₁ x → ↑ ((↑ ∘ ↑) (↑ (↑ (↑ (ua-unglue ↑≃ i x))))))
-- -- -- -- -- -- --     -- (λ i i₁ x → ♯ (↑ (♯ (ua-unglue ↑≃ i x) i₁)) i₁) 



-- -- -- -- -- -- CodeJ₃S¹ : J₃S¹ → Type
-- -- -- -- -- -- CodeJ₃S¹ base = Co
-- -- -- -- -- -- CodeJ₃S¹ (loop i) = Co≡ i
-- -- -- -- -- -- CodeJ₃S¹ (loop₂ j i) = CodeJ₃S¹-sq j i
-- -- -- -- -- -- CodeJ₃S¹ (loop₃ k j i) =
-- -- -- -- -- --     Glue Co
-- -- -- -- -- --        λ {  (i = i0) → CodeJ₃S¹-sq k j , {!!} , {!!}
                                                
-- -- -- -- -- --           ; (i = i1) → CodeJ₃S¹-sq k j ,
-- -- -- -- -- --                 {!!} ∘ CodeJ₃S¹-sq-unglueSq k j
-- -- -- -- -- --                 , {!!}
-- -- -- -- -- --           ; (j = i0) → CodeJ₃S¹-sq k i , {!!} , {!!}
-- -- -- -- -- --           ; (j = i1) → CodeJ₃S¹-sq k i ,
-- -- -- -- -- --                 {!!} ∘ CodeJ₃S¹-sq-unglueSq k i
-- -- -- -- -- --                 , {!!}
-- -- -- -- -- --           ; (k = i0) → CodeJ₃S¹-sq j i , {!!} , {!!}
-- -- -- -- -- --           ; (k = i1) → CodeJ₃S¹-sq j i ,
-- -- -- -- -- --                 {!!} ∘ CodeJ₃S¹-sq-unglueSq j i
-- -- -- -- -- --                 , {!!}
-- -- -- -- -- --           }

-- -- -- -- -- --   -- Glue Co
-- -- -- -- -- --   --      λ {  (i = i0) → CodeJ₃S¹-sq j k ,
-- -- -- -- -- --   --                      lem3-CodeJ₃S¹ j k ,
-- -- -- -- -- --   --                      {!!}
                                                
-- -- -- -- -- --   --         ; (i = i1) → CodeJ₃S¹-sq j k ,
-- -- -- -- -- --   --                      unglueEquiv Co (j ∨ ~ j ∨ k ∨ ~ k ) (CodeJ₃S¹-pa j k)
-- -- -- -- -- --   --                       ∙ₑ ♯6-U k j
-- -- -- -- -- --   --         ; (j = i0) → CodeJ₃S¹-sq i k ,
-- -- -- -- -- --   --                    lem-CodeJ₃S¹ i k ,
-- -- -- -- -- --   --                      {!!}
-- -- -- -- -- --   --         ; (j = i1) → CodeJ₃S¹-sq i k ,
-- -- -- -- -- --   --                   lem2-CodeJ₃S¹ i k ,
-- -- -- -- -- --   --                   {!!}
-- -- -- -- -- --   --         ; (k = i0) → CodeJ₃S¹-sq i j ,
-- -- -- -- -- --   --                  fst (♯≃ j) ∘' ↑ ∘' ↑ ∘'
-- -- -- -- -- --   --                    fst (unglueEquiv Co (i ∨ ~ i ∨ j ∨ ~ j ) (CodeJ₃S¹-pa i j))
-- -- -- -- -- --   --                  , {!!}
-- -- -- -- -- --   --         ; (k = i1) → CodeJ₃S¹-sq i j ,
-- -- -- -- -- --   --                   fst (♯6-D (~ i) j) ∘'
-- -- -- -- -- --   --                   fst (unglueEquiv Co (i ∨ ~ i ∨ j ∨ ~ j ) (CodeJ₃S¹-pa i j))
-- -- -- -- -- --   --                   , {!!}
-- -- -- -- -- --   --         }


-- -- -- -- -- -- -- p∙[p⁻∙q]≡q : ∀ {ℓ} {A : Type ℓ} → {x y : A} → (p q : x ≡ y) → 
-- -- -- -- -- -- --               p ∙ (sym p ∙ q) ≡ q
-- -- -- -- -- -- -- p∙[p⁻∙q]≡q p q i j =
-- -- -- -- -- -- --    hcomp ( λ k → 
-- -- -- -- -- -- --           λ { (j = i0) → p i0
-- -- -- -- -- -- --             ; (j = i1) → compPath-filler' (sym p) q (~ i) k
-- -- -- -- -- -- --             ; (i = i1) → q (k ∧ j)
-- -- -- -- -- -- --             }) (p (j ∧ ~ i))

-- -- -- -- -- -- -- encode : ∀ x → base ≡ x → CodeJ₃S¹ x
-- -- -- -- -- -- -- encode x p = subst CodeJ₃S¹ p base


-- -- -- -- -- -- -- loopSqₓ : (loopₓ : Square loop loop loop loop) →
-- -- -- -- -- -- --            ∀ (q : base ≡ base) →  Square {A = J₃S¹}
-- -- -- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- -- -- --              (λ _ → base)
-- -- -- -- -- -- --              (λ _ → base)
-- -- -- -- -- -- -- loopSqₓ loopₓ q i =
-- -- -- -- -- -- --          (λ j' → loopₓ (j' ∧  ~ i) (j' ∧  i))
-- -- -- -- -- -- --        ∙ (λ j' → loopₓ (j' ∨ ~ i) (j' ∨ i)) ∙ q


-- -- -- -- -- -- -- loopSq : ∀ q → Square {A = J₃S¹}
-- -- -- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- -- -- --              (λ _ → base)
-- -- -- -- -- -- --              (λ _ → base)
-- -- -- -- -- -- -- loopSq = loopSqₓ loop₂

-- -- -- -- -- -- -- loopDiag : ∀ q → Square {A = J₃S¹}
-- -- -- -- -- -- --              (loop ∙ loop ∙ loop ∙ q)
-- -- -- -- -- -- --              (loop ∙ loop ∙ loop ∙ q)
-- -- -- -- -- -- --              (λ _ → base)
-- -- -- -- -- -- --              (λ _ → base)
-- -- -- -- -- -- -- loopDiag q =
-- -- -- -- -- -- --      cong (loop ∙_) (sym (loopSq q))
-- -- -- -- -- -- --   ∙∙ (λ i → (λ j' → loop₂ (j' ∧  ~ i) (j' ∧  i))
-- -- -- -- -- -- --             ∙ (λ j' → loop₂ (j' ∨ ~ i) (j' ∨ i)) ∙ loop ∙ q)
-- -- -- -- -- -- --   ∙∙ cong (loop ∙_) (loopSq q) 


-- -- -- -- -- -- -- loopSq₃' : ∀ (q : base ≡ base)
-- -- -- -- -- -- --             → Cube
-- -- -- -- -- -- --             (loopSq q) (loopSq (loop ∙ q))
-- -- -- -- -- -- --             (λ k → loop₂ (~ k) ∙ loop₂ (~ k)  ∙ compPath-filler' loop q k)
-- -- -- -- -- -- --             (λ k → loop₂ (~ k) ∙ loop₂ (~ k) ∙ compPath-filler' loop q k)
-- -- -- -- -- -- --            (λ i _ → loop (~ i)) refl
-- -- -- -- -- -- -- loopSq₃' q k i =
-- -- -- -- -- -- --      (λ j' → loop₃ (~ k) (j' ∧  ~ i) (j' ∧  i))
-- -- -- -- -- -- --        ∙ (λ j' → loop₃ (~ k) (j' ∨ ~ i) (j' ∨ i)) ∙
-- -- -- -- -- -- --           (compPath-filler' loop q k)


-- -- -- -- -- -- -- -- loopSq₃ : ∀ (q : base ≡ base) →
-- -- -- -- -- -- -- --            Cube
-- -- -- -- -- -- -- --             (cong (loop ∙_) (loopSq q))
-- -- -- -- -- -- -- --             (loopSq (loop ∙ q))
-- -- -- -- -- -- -- --             {!!}
-- -- -- -- -- -- -- --             {!!}
-- -- -- -- -- -- -- --             (λ _ _ → base)
-- -- -- -- -- -- -- --             λ _ _ → base
-- -- -- -- -- -- -- -- loopSq₃ q k i j =
-- -- -- -- -- -- -- --      hcomp (λ l →
-- -- -- -- -- -- -- --             λ { (j = i0) → base
-- -- -- -- -- -- -- --               ; (j = i1) → loopSq₃' q k i l
-- -- -- -- -- -- -- --               ; (k = i1) → loopSq (loop ∙ q) i (j ∧ l)
-- -- -- -- -- -- -- --               })
-- -- -- -- -- -- -- --               (loop (j ∧ ~ k))




-- -- -- -- -- -- -- loopSq₃ : ∀ (q : base ≡ base) →
-- -- -- -- -- -- --      Cube
-- -- -- -- -- -- --        (loopDiag q)
-- -- -- -- -- -- --        (cong (loop ∙_) (loopSq q))
-- -- -- -- -- -- --        (loopSq (loop ∙ q))
-- -- -- -- -- -- --        (loopSq (loop ∙ q))
-- -- -- -- -- -- --        refl
-- -- -- -- -- -- --        refl
-- -- -- -- -- -- -- loopSq₃ q k i j =
-- -- -- -- -- -- --    hcomp
-- -- -- -- -- -- --      (λ l →
-- -- -- -- -- -- --         λ { (k = i0) → doubleCompPath-filler
-- -- -- -- -- -- --                       (cong (loop ∙_) (sym (loopSq q)))
-- -- -- -- -- -- --                      (λ i → (λ j' → loop₂ (j' ∧  ~ i) (j' ∧  i))
-- -- -- -- -- -- --                       ∙ (λ j' → loop₂ (j' ∨ ~ i) (j' ∨ i)) ∙ loop ∙ q)
-- -- -- -- -- -- --                     (cong (loop ∙_) (loopSq q))
-- -- -- -- -- -- --                          l i j
-- -- -- -- -- -- --           ; (k = i1) → compPath-filler' loop (loopSq q i ) l j
-- -- -- -- -- -- --           ; (i = i0) → W.sq'-fill j l k
-- -- -- -- -- -- --           ; (i = i1) → W.sq'-fill j l k
-- -- -- -- -- -- --           ; (j = i0) → loop (k ∧ ~ l)
-- -- -- -- -- -- --           ; (j = i1) → W.sq'-fill j l k
-- -- -- -- -- -- --           })
-- -- -- -- -- -- --      (loopSq₃' q (~ k) i j)
-- -- -- -- -- -- --  where
-- -- -- -- -- -- --   module W = whiskSq (λ _ _ → J₃S¹)
-- -- -- -- -- -- --          (λ l k → loop (k ∧ ~ l))
-- -- -- -- -- -- --          ((λ k → loop₂ (k) ∙ loop₂ (k)  ∙ compPath-filler' loop q (~ k)))
-- -- -- -- -- -- --          (loopSq (loop ∙ q))
-- -- -- -- -- -- --          (λ l j → (loop ∙ loopSq q l) j)
-- -- -- -- -- -- --          (λ l j → compPath-filler' loop (loop ∙ loop ∙ q) l j)


-- -- -- -- -- -- -- loop₂' : Square loop loop loop loop
-- -- -- -- -- -- -- loop₂' = whiskSq.sq' (λ _ _ → J₃S¹)
-- -- -- -- -- -- --      loop₂ (λ k j → loop₂ (~ j) k) (λ k j → loop₂ (~ j) k)
-- -- -- -- -- -- --            (λ k i → loop₂ (~ i) k) (λ k i → loop₂ (~ i) k)

-- -- -- -- -- -- -- loop₂≡loop₂' : loop₂ ≡
-- -- -- -- -- -- --    (whiskSq.sq' (λ _ _ → J₃S¹)
-- -- -- -- -- -- --      loop₂ (λ k j → loop₂ (~ j) k) (λ k j → loop₂ (~ j) k)
-- -- -- -- -- -- --            (λ k i → loop₂ (~ i) k) (λ k i → loop₂ (~ i) k))
-- -- -- -- -- -- -- loop₂≡loop₂' k i j =
-- -- -- -- -- -- --   hcomp (λ l →
-- -- -- -- -- -- --       λ { (k = i0) → loop₂ i j
-- -- -- -- -- -- --         ; (i = i0) → loop₂ (k ∧ ~ l) j
-- -- -- -- -- -- --         ; (i = i1) → loop₂ (k ∧ ~ l) j
-- -- -- -- -- -- --         ; (j = i0) → loop₂ (k ∧ ~ l) i
-- -- -- -- -- -- --         ; (j = i1) → loop₂ (k ∧ ~ l) i
-- -- -- -- -- -- --         })
-- -- -- -- -- -- --         (loop₃ k i j) 

-- -- -- -- -- -- -- loopSq' : ∀ q → Square {A = J₃S¹}
-- -- -- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- -- -- --              (loop ∙ loop ∙ q)
-- -- -- -- -- -- --              (λ _ → base)
-- -- -- -- -- -- --              (λ _ → base)
-- -- -- -- -- -- -- loopSq' = loopSqₓ loop₂'

-- -- -- -- -- -- -- loopSq≡Sq' : ∀ q → loopSq q ≡ loopSq' q 
-- -- -- -- -- -- -- loopSq≡Sq' q i = loopSqₓ (loop₂≡loop₂' i) q





-- -- -- -- -- -- -- decode : ∀ x → CodeJ₃S¹ x → base ≡ x
-- -- -- -- -- -- -- decode base p = CoLoop p
-- -- -- -- -- -- -- decode (loop i) = {!!}
-- -- -- -- -- -- -- decode (loop₂ i j) p = {!!}
-- -- -- -- -- -- -- decode (loop₃ i j k) p = {!!}


-- -- -- -- -- -- -- -- -- loop₃' : Cube loop₂ loop₂ loop₂ loop₂ loop₂ loop₂
-- -- -- -- -- -- -- -- -- loop₃' = loop₃

-- -- -- -- -- -- -- -- -- J₃S¹-hexa₀ J₃S¹-hexa₁ : (loop ∙∙ loop ∙∙ loop) ≡ (loop ∙∙ loop ∙∙ loop)
-- -- -- -- -- -- -- -- -- J₃S¹-hexa₀ = {!!}
-- -- -- -- -- -- -- -- -- J₃S¹-hexa₁ = {!!}

-- -- -- -- -- -- -- -- -- J₃S¹-hexa : Path ((loop ∙∙ loop ∙∙ loop) ≡ (loop ∙∙ loop ∙∙ loop))
-- -- -- -- -- -- -- -- --             {!!} {!!}
-- -- -- -- -- -- -- -- -- J₃S¹-hexa = {!!}

-- -- -- -- -- -- -- -- -- infixl 6 _⊕_

-- -- -- -- -- -- -- -- -- infixl 10 ─_


-- -- -- -- -- -- -- -- -- data ℤᵍ : Type where
-- -- -- -- -- -- -- -- --  zero one  : ℤᵍ
-- -- -- -- -- -- -- -- --  _⊕_ : ℤᵍ → ℤᵍ → ℤᵍ
-- -- -- -- -- -- -- -- --  ─_ : ℤᵍ → ℤᵍ
-- -- -- -- -- -- -- -- --  ⊕─ : ∀ x → x ⊕ ─ x ≡ zero

-- -- -- -- -- -- -- -- --  ⊕-assoc : ∀ x y z → x ⊕ (y ⊕ z) ≡ x ⊕ y ⊕ z
 
-- -- -- -- -- -- -- -- --  zero-⊕ : ∀ x → zero ⊕ x ≡ x
-- -- -- -- -- -- -- -- --  ⊕-zero : ∀ x → x ⊕ zero ≡ x

-- -- -- -- -- -- -- -- --  ⊕-triangle : ∀ x y  →
-- -- -- -- -- -- -- -- --     Square                      
-- -- -- -- -- -- -- -- --         (⊕-assoc x zero y)
-- -- -- -- -- -- -- -- --         refl
-- -- -- -- -- -- -- -- --         (cong (x ⊕_) (zero-⊕ y))
-- -- -- -- -- -- -- -- --         (cong (_⊕ y) (⊕-zero x))
        


-- -- -- -- -- -- -- -- --  ⊕-penta-diag : ∀ x y z w →
-- -- -- -- -- -- -- -- --    x ⊕ y ⊕ z ⊕ w ≡ x ⊕ (y ⊕ (z ⊕ w))
-- -- -- -- -- -- -- -- --  ⊕-penta-△ : ∀ x y z w →
-- -- -- -- -- -- -- -- --    Square
-- -- -- -- -- -- -- -- --      refl
-- -- -- -- -- -- -- -- --      (⊕-penta-diag x y z w)
-- -- -- -- -- -- -- -- --      (⊕-assoc _ _ _)
-- -- -- -- -- -- -- -- --      (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- --  ⊕-penta-□ : ∀ x y z w →
-- -- -- -- -- -- -- -- --     Square
-- -- -- -- -- -- -- -- --      (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- --      (⊕-penta-diag x y z w)
-- -- -- -- -- -- -- -- --      (cong (_⊕ w) (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- --      (cong (x ⊕_) (sym (⊕-assoc _ _ _)))

-- -- -- -- -- -- -- -- --  -- ⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
-- -- -- -- -- -- -- -- --  -- ⊕-hexa-diag : ∀ x y z → x ⊕ y ⊕ z ≡ y ⊕ (z ⊕ x)
-- -- -- -- -- -- -- -- --  -- ⊕-hexa-↑ : ∀ x y z →
-- -- -- -- -- -- -- -- --  --   Square
-- -- -- -- -- -- -- -- --  --      (⊕-comm x (y ⊕ z))
-- -- -- -- -- -- -- -- --  --      (⊕-hexa-diag x y z)
-- -- -- -- -- -- -- -- --  --      (⊕-assoc _ _ _)
-- -- -- -- -- -- -- -- --  --      (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- --  -- ⊕-hexa-↓ : ∀ x y z →
-- -- -- -- -- -- -- -- --  --    Square
-- -- -- -- -- -- -- -- --  --       (⊕-hexa-diag x y z)
-- -- -- -- -- -- -- -- --  --       (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- --  --       (cong (_⊕ z) (⊕-comm _ _))
-- -- -- -- -- -- -- -- --  --       (cong (y ⊕_) (⊕-comm _ _))

-- -- -- -- -- -- -- -- --  ⊕-comm : one ⊕ one ≡ one ⊕ one
-- -- -- -- -- -- -- -- --  ⊕-comm-assoc : one ⊕ (one ⊕ one) ≡ one ⊕ one ⊕ one 

-- -- -- -- -- -- -- -- --  ⊕-comp : Square
-- -- -- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- -- -- --            {!!}

-- -- -- -- -- -- -- -- --  -- ⊕-hexa-diag : one ⊕ one ⊕ one ≡ one ⊕ (one ⊕ one)
-- -- -- -- -- -- -- -- --  -- ⊕-hexa-L : 
-- -- -- -- -- -- -- -- --  --   Square
-- -- -- -- -- -- -- -- --  --      (cong (one ⊕_) ⊕-comm)
-- -- -- -- -- -- -- -- --  --      (cong (_⊕ one) ⊕-comm)
-- -- -- -- -- -- -- -- --  --      (⊕-assoc _ _ _ )
-- -- -- -- -- -- -- -- --  --      ({!!})
 
-- -- -- -- -- -- -- -- --  -- ⊕-hexa-↓ : ∀ x y z →
-- -- -- -- -- -- -- -- --  --    Square
-- -- -- -- -- -- -- -- --  --       (⊕-hexa-diag x y z)
-- -- -- -- -- -- -- -- --  --       (sym (⊕-assoc _ _ _))
-- -- -- -- -- -- -- -- --  --       (cong (_⊕ z) (⊕-comm _ _))
-- -- -- -- -- -- -- -- --  --       (cong (y ⊕_) (⊕-comm _ _))


-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ : ℤᵍ → Co ≃ Co
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ zero = idEquiv _
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ one = ↑≃
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (x ⊕ x₁) = ℤᵍ→Co≃ x ∙ₑ ℤᵍ→Co≃ x₁
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (─ x) = invEquiv (ℤᵍ→Co≃ x)
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕─ x i) = {!!}
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-assoc x x₁ x₂ i) =
-- -- -- -- -- -- -- -- --   compEquiv-assoc (ℤᵍ→Co≃ x) (ℤᵍ→Co≃ x₁) (ℤᵍ→Co≃ x₂) i
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (zero-⊕ x i) = {!!}
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-zero x i) = {!!}
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-triangle x x₁ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-penta-diag x x₁ x₂ x₃ i) = {!!}
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-penta-△ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-penta-□ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-comm i) = ♯≃ i
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-comm-assoc i) = {!!}
-- -- -- -- -- -- -- -- -- ℤᵍ→Co≃ (⊕-comp i i₁) = {!!}

-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' : Co → ℤᵍ
-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' base = zero
-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (↑ x) = one ⊕ ℤᵍ←Co≃' x
-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (↓ x) = (─ one) ⊕ ℤᵍ←Co≃' x
-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (↓↑ x i) = ({!!} ∙  ((⊕-assoc (─ one) one (ℤᵍ←Co≃' x))) ∙
-- -- -- -- -- -- -- -- --                             cong (_⊕ (ℤᵍ←Co≃' x)) {!⊕─ !}
-- -- -- -- -- -- -- -- --                              ∙ {!!}) i
-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (↑↓ x i) = (((⊕-assoc (one) (─ one) (ℤᵍ←Co≃' x))) ∙
-- -- -- -- -- -- -- -- --                             cong (_⊕ (ℤᵍ←Co≃' x)) (⊕─ one )
-- -- -- -- -- -- -- -- --                              ∙ zero-⊕ (ℤᵍ←Co≃' x)) i
-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (♯ x i) = {!!}
-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (⇅⇅⇅-diag x i) = {!!}
-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (⇅⇅⇅-U x i i₁) = {!!}
-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃' (⇅⇅⇅-D x i i₁) = {!!}


-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃ : Co ≃ Co → ℤᵍ
-- -- -- -- -- -- -- -- -- ℤᵍ←Co≃ e = ℤᵍ←Co≃' (fst e base)

-- -- -- -- -- -- -- -- -- -- toJ₃S¹ : ℤᵍ → Path J₃S¹ base base
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ zero = refl
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ one = loop
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (x ⊕ x₁) = toJ₃S¹ x ∙ toJ₃S¹ x₁
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (─ x) = sym (toJ₃S¹ x)
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕─ x i) = rCancel (toJ₃S¹ x) i
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-comm x x₁ i) = {!PathP→comm loop₂!}
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-assoc x x₁ x₂ i) = {!!}
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (zero-⊕ x i) = {!!}
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-zero x i) = {!!}
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-triangle x x₁ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-penta-diag x x₁ x₂ x₃ i) = {!!}
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-penta-△ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-penta-□ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-hexa-diag x x₁ x₂ i) = {!!}
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-hexa-↑ x x₁ x₂ i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- toJ₃S¹ (⊕-hexa-↓ x x₁ x₂ i i₁) = {!!}
