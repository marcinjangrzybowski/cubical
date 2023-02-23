{-

This file contains:

- The first Eilenberg–Mac Lane type as a HIT

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.EilenbergMacLane1.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
  renaming (assoc to assoc∙)
open import Cubical.Algebra.Group.Base

private
  variable ℓ : Level

module _ (Group@(G , str) : Group ℓ) where
  open GroupStr str

  data EM₁ : Type ℓ where
    embase : EM₁
    emloop : G → embase ≡ embase
    emcomp : (g h : G)
           → PathP (λ j → embase ≡ emloop h j) (emloop g) (emloop (g · h))
    emsquash : ∀ (x y : EM₁) (p q : x ≡ y) (r s : p ≡ q) → r ≡ s

  {- The emcomp constructor fills the square:
^
    emloop (g · h)
    [a]— — — >[c]
     ‖         ^
     ‖         | emloop h     ^
     ‖         |            j |
    [a]— — — >[b]          ∙ — >
       emloop g                i

    We use this to give another constructor-like construction:
  -}

  emloop-comp : (g h : G) → emloop (g · h) ≡ emloop g ∙ emloop h
  emloop-comp g h i j =
    hcomp
      (λ k → λ {
         (i = i0) → (emcomp g h) k j
         ;(j = i0) → embase
         ;(j = i1) →  emloop h k
         } ) (emloop g j)

  emloop-comp' : (g h : G) → emloop (g · h) ≡ emloop g ∙ emloop h
  emloop-comp' g h i = compPath-unique refl (emloop g) (emloop h)
    (emloop (g · h) , emcomp g h)
    (emloop g ∙ emloop h , compPath-filler (emloop g) (emloop h)) i .fst


  emloop-doubleComp : (g h l : G) → emloop (g · (h · l)) ≡ emloop g ∙∙ emloop h ∙∙ emloop l
  emloop-doubleComp g h l i j =
        hcomp
      (λ k → λ {
          (i = i0) → (emcomp g (h · l)) k j
         ;(j = i0) → emloop g (~ k ∧ i)
         ;(j = i1) → emloop (h · l) k
         ;(i = i1) → hcomp (λ k' →
             λ { (k = i0) → embase
               ; (j = i0) → emloop g (~ k ∨  ~ k')
               ; (j = i1) → emcomp h l k' k
               }) (emloop h (j ∧ k))
         }) (emloop g (j ∨ i))


  emloop-doubleCompFill : (g h l : G) → 
     Square
       (sym (emloop g))
       (emloop l)
       (emloop h)
       (emloop ((g · h) · l))
  emloop-doubleCompFill g h l i j =
      hcomp (λ l' → λ {
         (i = i0) → emcomp g h (~ l') (~ j) 
        ;(i = i1) → emloop l (l' ∧ j)
        ;(j = i0) → emloop h (~ l' ∨ i)
        ;(j = i1) → emcomp (g · h) l l' i  })
          (emloop (g · h) (~ j ∨ i))


  emcomp~-fill : (g h : G) → ∀ i j → I → Partial (i ∨ ~ i ∨ j ∨ ~ j) EM₁
  emcomp~-fill g h i j =    
      (λ k → λ {
          (i = i0) → emcomp g h k j
         ;(i = i1) → emloop h (k ∧ j)
         ;(j = i0) → emloop g i
         ;(j = i1) →  emloop h k
         } )
  
  emcomp~ : (g h : G)
           → PathP (λ i → emloop g i ≡ embase) (emloop (g · h)) (emloop h) 
  emcomp~ g h i j =
   hcomp  (emcomp~-fill g h i j) (emloop g (j ∨ i))

  emcomp∼-fill : ∀ {ℓ'} (A : EM₁ → Type ℓ') →
               {x y z : A embase} → (g h : G) 
               → (xy : PathP (λ j → A (emloop g j)) x y)
                  (yz : PathP (λ i → A (emloop h i)) y z)
                  (xz : PathP (λ j → A (emloop (g · h) j)) x z)
               → SquareP (λ i j → A (emcomp g h i j))
                   xy
                   xz
                   refl
                   yz
               → SquareP (λ i j → A (emcomp~ g h i j))
                   xz
                   yz
                   xy
                   refl
  emcomp∼-fill A g h xy yz xz x i j =
    comp (λ l → A
      (hfill (emcomp~-fill g h i j) (inS (emloop g (j ∨ i))) l))
       ((λ k → λ {
          (i = i0) → x k j
         ;(i = i1) → yz (k ∧ j)
         ;(j = i0) → xy i
         ;(j = i1) → yz k
         } ))
       (xy (j ∨ i))

  emloop-1g : emloop 1g ≡ refl
  emloop-1g =
       lUnit (emloop 1g)
    ∙∙ cong (_∙ emloop 1g) (sym (lCancel (emloop 1g)) )
    ∙∙ sym (assoc∙ _ _ _)
    ∙∙ cong (sym (emloop 1g) ∙_) (sym (emloop-comp 1g 1g) ∙ cong emloop (·IdL 1g))
    ∙∙ rCancel _

  emloop-sym : (g : G) → emloop (inv g) ≡ sym (emloop g)
  emloop-sym g =
       rUnit _
    ∙∙ cong (emloop (inv g) ∙_) (sym (rCancel (emloop g)))
    ∙∙ assoc∙ _ _ _
    ∙∙ cong (_∙ sym (emloop g)) (sym (emloop-comp (inv g) g) ∙∙ cong emloop (·InvL g) ∙∙ emloop-1g)
    ∙∙ sym (lUnit _)

  data EM₁-raw : Type ℓ where
    embase-raw : EM₁-raw
    emloop-raw : (g : G) → embase-raw ≡ embase-raw

  EM₁-raw→EM₁ : EM₁-raw → EM₁
  EM₁-raw→EM₁ embase-raw = embase
  EM₁-raw→EM₁ (emloop-raw g i) = emloop g i
