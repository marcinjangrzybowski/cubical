
{-# OPTIONS --cubical --safe #-}

module Cubical.Foundations.Pentagon where

open import Cubical.Foundations.Everything


-- private
--   variable
--     ℓ : Level
--     A : Type ℓ
--     a₁ a₂ a₃ a₄ a₅ : A


Comp : Typeω
Comp = ∀ {ℓ} → {A : Type ℓ} → {a₁ a₂ a₃ : A} → a₁ ≡ a₂ → a₂ ≡ a₃ → a₁ ≡ a₃

Assoc : Comp → Typeω 
Assoc _∘_ = ∀ {ℓ} → {A : Type ℓ} → {a₁ a₂ a₃ a₄ : A}
           → (p₁₂ : a₁ ≡ a₂) → (p₂₃ : a₂ ≡ a₃) → (p₃₄ : a₃ ≡ a₄)
           →  p₁₂ ∘ (p₂₃ ∘ p₃₄) ≡ (p₁₂ ∘ p₂₃) ∘ p₃₄ 

Pentagon : (_∘_ : Comp) → (Assoc _∘_) → Typeω
Pentagon _∘_ assoc =
           ∀ {ℓ} → {A : Type ℓ} → {a₁ a₂ a₃ a₄ a₅ : A}
           → (p₁₂ : a₁ ≡ a₂) → (p₂₃ : a₂ ≡ a₃) → (p₃₄ : a₃ ≡ a₄) → (p₄₅ : a₄ ≡ a₅)
           → _≡_ {A = (p₁₂ ∘ (p₂₃ ∘ (p₃₄ ∘ p₄₅))) ≡ (((p₁₂ ∘ p₂₃) ∘ p₃₄) ∘ p₄₅)} 
             (assoc _ _ _ ∘ assoc _ _ _)
            (((cong (_ ∘_) (assoc _ _ _)) ∘ assoc _ _ _) ∘ (cong (_∘ _) (assoc _ _ _)))
           
assoc' : Assoc _∙_
assoc' p q r k i =
  hcomp
    (λ j → λ
      { (i = i0) → p i0
      ; (i = i1) →
        hcomp
          (λ l → λ
            { (j = i0) → q k
            ; (j = i1) → r l
            ; (k = i1) → r (j ∧ l)
            })
          (q (j ∨ k))
      })
    (compPath-filler p q k i)

⬠ : Pentagon _∙_ assoc'
⬠ {A = A} {a₁ = x} {y} {z} {w} {v} p q r s =
   (cuBig) ∙ (doubleCompPath-elim _ _ _)

  where

    cc : I → I → I → A
    cc i j i₁ =
        (hcomp
        (λ k → λ {
         (j = i0) → p i₁ ;(i₁ = i0) → x
        ;(i₁ = i1) → hcomp
                     (λ k₁ → λ { (i = i0) → (q (j ∧ k)) ; (k = i0) → y ; (j = i0) → y
                               ; (j = i1)(k = i1) → r (k₁ ∧ i)})
                     (q (j ∧ k))  
        }) (p i₁))

    rr : I → I → I → A
    rr i j i₁ =
     (hcomp
        (λ k → λ {
         (j = i1) → hcomp (
          (λ k₁ → λ {
            (i₁ = i0) → r i
           ;(k = i0) → r i
           ;(i = i1) → s (k₁ ∧  k ∧  i₁)
           ;(i₁ = i1)(k = i1) →  s k₁
           })) (r ((i₁ ∧ k) ∨ (i)))
        ;(i₁ = i0) → compPath-filler q r i j
        ;(i₁ = i1) → hcomp (
          (λ k₁ → λ {
            (k = i0) → r i
           ;(k = i1) → s k₁
           ;(i = i1) → s (k ∧ k₁)   
           })) (r (i ∨ k))
        })
       (hfill (
         (λ k → λ {
            (j = i1) → r k
           ;(i₁ = i1) → r k
           ;(i₁ = i0)(j = i0) → y   
           })
        ) (inS (q (i₁ ∨ j))) i))

    cu2 : Square (assoc' p q (r ∙ s)) (assoc' p (q ∙ r) s)
                 _ 
                 λ i → refl ∙∙ (λ i₁ → cc i i1 i₁) ∙∙ λ i₁ → rr i i1 i₁ 
    cu2 i j = refl ∙∙ (λ i₁ → cc i j i₁) ∙∙ λ i₁ → rr i j i₁


    cc2 : I → I → I → A
    cc2 i j i₁ = 
       hcomp
       (λ k → λ {            
             (j = i0) → {!!}
           ; (i₁ = i0) → x
           ; (i₁ = i1) →
               hcomp
               (λ k₁ → λ {
                    (k = i0) → q (j ∨ ~ i)
                  ; (k = i1) → {!!}
                  ; (j = i1) → {!!}
                  ; (i = i0) → r (k ∧ j ∧ k₁)
                   })
               (q (j ∨ ~ i ∨ k))
           })
       (hcomp
        (λ k → λ {
             (i₁ = i0) → x
           ; (i₁ = i1) → q (k ∧ (j ∨ (~ i)))
           ; (i = i1)(j = i0) → p i₁
            })
        (p i₁))
       

    rr2 : I → I → I → A
    rr2 i j i₁ =
           hcomp
          (λ k → λ {
            (i = i1) → s (i₁ ∧ (k))
           ;(j = i1) → s (i₁ ∧ k)
           ;(i₁ = i0) → r (i ∨ j)
           ;(i₁ = i1) → s k
           }) (r (i ∨ j ∨ i₁))

    cu3 : I → I → I → A
    cu3 i j i₁ = (refl ∙∙ (λ i₁ → cc2 i j i₁) ∙∙ λ i₁ → rr2 i j i₁) i₁

    cuBig : _ ∙ _ ≡ ((cong (p ∙_) (assoc' q r s)) ∙∙ assoc' _ _ _ ∙∙ (cong (_∙ s) (assoc' p q r)))
    cuBig i =  (λ i₁ → (cong (p ∙_) (assoc' q r s)) (i ∧ i₁)) ∙∙ cu2 i ∙∙ λ i₁ i₂ → cu3 i i₁ i₂




-- ⬠ : Pentagon _∙_ assoc
-- ⬠ {A = A} {a₁ = x} {y} {z} {w} {v} p q r s =
--    (cuBig) ∙ (doubleCompPath-elim _ _ _)

--   where


--     cu1 : Square (λ _ → (p ∙ q ∙ r ∙ s))
--                (cong (p ∙_) (assoc q r s))
--                (λ i → p ∙ q ∙ r ∙ s)
--                (cong (p ∙_) (assoc q r s))
--     cu1 i i₁ = (cong (p ∙_) (assoc q r s)) (i ∧ i₁)

--     cu2 : Square (assoc p q (r ∙ s)) (assoc p (q ∙ r) s)
--                  ((cong (p ∙_) (assoc q r s)))
--                  ((assoc (p ∙ q) r s) ∙ cong (_∙ s) (sym (assoc p q r)) )
                
--     cu2 i j i₁ =
--       hcomp
--        (λ k → λ {
--           (j = i0) → hcomp (λ k₁ → λ {
--                                 (k = i0) → p i₁
--                                ;(i₁ = i0) → x
--                                ;(i₁ = i1) → {!!}
--                                 } ) (p i₁)
--          ;(j = i1) → {!!}
--          ;(i₁ = i0) → x
--          ;(i₁ = i1) → {!!}
--          })
--        (hcomp
--        (λ k → λ {
--           (j = i0) → p i₁
         
--          ;(i₁ = i0) → x
--          ;(i₁ = i1) → q (j ∧ k) 
--          })
--        (p i₁))
            

--     cu3 : Square (assoc (p ∙ q) r s)
--                  (cong (_∙ s) (assoc _ _ _))
--                 ((assoc (p ∙ q) r s) ∙ cong (_∙ s) (sym (assoc p q r)) )
--                 refl
--     cu3 = {!!}

--     cuBig : _ ∙ _ ≡ ((cong (p ∙_) (assoc q r s)) ∙∙ assoc _ _ _ ∙∙ (cong (_∙ s) (assoc p q r)))
--     cuBig i = cu1 i ∙∙ cu2 i ∙∙ cu3 i


-- pentTy : (p₁₂ : a₁ ≡ a₂) → (p₂₃ : a₁ ≡ a₂) → (p₃₄ : a₁ ≡ a₂) → (p₄₅ : a₁ ≡ a₂)
--            → {!!} 
-- pentTy = {!!}


-- pentTy : (p₁₂ : a₁ ≡ a₂) → (p₂₃ : a₁ ≡ a₂) → (p₃₄ : a₁ ≡ a₂) → (p₄₅ : a₁ ≡ a₂)
--            → {!!} 
-- pentTy = {!!}
