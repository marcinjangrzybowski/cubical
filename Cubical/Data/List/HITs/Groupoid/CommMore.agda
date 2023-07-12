{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Data.List.HITs.Groupoid.CommMore where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Empty renaming (elim to ⊥elim ; rec to ⊥rec)

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Nat.Order

open import Cubical.HITs.GroupoidTruncation


import Cubical.Data.List.Base as B
import Cubical.Data.List.Properties as BP

import Cubical.Functions.Logic as L

open import Cubical.Data.List.HITs.Groupoid.Base

open import Cubical.Data.List.HITs.Groupoid.Comm

private
  variable
    ℓ : Level

module _ (A : Type ℓ) where

 record Recℙ2' {ℓb} (B : Type ℓb) (isGroupoidB : isGroupoid B) : Type (ℓ-max ℓ ℓb) where
  no-eta-equality
  constructor recℙ2
  
  field
   r11 : List A → List A → B
   r12 : Recℙ.H2 (Recℙ.h1 r11)
   r13 : Recℙ.H3 r12
   truncHlp1 : _

  hhh = Recℙ.f₃ r13 truncHlp1
   
  field
   r21 : ∀ z → Recℙ.H2 {A = A} (Recℙ.h1 (hhh (𝕡base z)))
   r22 : Elimℙ.H2 {A = A} {B = λ z → Recℙ.H2 (Recℙ.h1 (hhh z))} (Elimℙ.h1 r21)
   trunncHlp2 : ∀ x → isSet (Recℙ.H2 (Recℙ.h1 (hhh x)))
   
  hh = Elimℙ.f₂ r22 trunncHlp2
   
  field
   r31 : Elimℙ.H1 {A = A} (λ z → Recℙ.H3 {A = A} (hh z))



  f2 : ℙ A → ℙ A → B
  f2 x = Recℙ.f₃ (Elimℙ.f₁ r31
    (λ x → Recℙ.isOfHLevelH3
           ((hh x)) 1 isGroupoidB) x) isGroupoidB

   -- fromH2* : H2* → H2
   -- bloopL (fromH2* x) = x
   -- bloopR (fromH2* x) xs ys zs ws =
   --   cong bbase (sym (++-assoc _ _ _))
   --    ∙∙ x xs ys zs ws ∙∙
   --   cong bbase  (++-assoc _ _ _)
   -- bhexDiagAB (fromH2* x) ls xs ys zs rs = 
   --    cong bbase (
   --            cong (λ x → ls ++ x ++ rs) (++-assoc _ _ _)  ∙
   --           sym (++-assoc _ _ _))
   --     ∙∙ x ls xs (ys ++ zs) rs ∙∙
   --    cong bbase (cong (λ x → (ls ++ x) ++ rs) (++-assoc _ _ _))
   -- bhexDiagBC (fromH2* x) ls xs ys zs rs =
   --   cong bbase (
   --      cong (ls ++_) (sym (++-assoc _ _ _))
   --      ∙∙ cong (ls ++_) (cong (_++ rs) (++-assoc _ _ _) ) ∙∙ (sym (++-assoc _ _ _))
   --        )
   --     ∙∙ x ls xs (ys ++ zs) rs ∙∙
   --      cong bbase (cong (_++ rs) (cong (ls ++_) (++-assoc _ _ _) ∙ sym (++-assoc _ _ _)))
   -- bhexDiagCD (fromH2* x) ls xs ys zs rs =
   --      x ls xs ys (zs ++ rs) ∙
   --      cong bbase (sym (++-assoc _ _ _) ∙∙
   --        cong (_++ rs) (cong (_++ zs) (sym (++-assoc _ _ _))) ∙∙ cong (_++ rs) (++-assoc _ _ _))


module _ {ℓ'} {A : Type ℓ} {B : ℙ A → Type ℓ'} (q : Elimℙ.H1 B) where

 fromH2P : (∀ xs ys zs ws →
        PathP (λ i → B (𝕡loopL xs ys zs ws i))
        (Elimℙ.H1.bbase q ((xs ++ (ys ++ zs)) ++ ws))
        (Elimℙ.H1.bbase q ((xs ++ (zs ++ ys)) ++ ws)))
          → Elimℙ.H2 q
 fromH2P p = w
  where
  open Elimℙ
  w : H2 q
  bloopL w = p
  bloopR w xs ys zs ws i =
    comp (λ j → B (𝕡loopAssoc xs ys zs ws j i))
         (λ j → λ { (i = i0) → bbase q _ 
                  ; (i = i1) → bbase q _
                  })
         (p xs ys zs ws i)
  bhexDiagAB w ls xs ys zs rs i =
         comp (λ j → B (𝕡hexA ls xs ys zs rs j i))
         (λ j → λ { (i = i0) → bbase q _ 
                  ; (i = i1) → bbase q _
                  })
         (p ls xs (ys ++ zs) rs i)
  bhexDiagBC w ls xs ys zs rs i =
    comp (λ j → B (𝕡hexB ls xs ys zs rs j i))
         (λ j → λ { (i = i0) → bbase q _ 
                  ; (i = i1) → bbase q _
                  })
                  (comp (λ j → B (𝕡hexA ls xs ys zs rs j i))
         (λ j → λ { (i = i0) → bbase q _ 
                  ; (i = i1) → bbase q _
                  })
         (p ls xs (ys ++ zs) rs i))
  bhexDiagCD w ls xs ys zs rs i =
      comp (λ j → B (𝕡hexD ls xs ys zs rs (~ j) i))
         (λ j → λ { (i = i0) → p ls xs ys (zs ++ rs) (~ j) 
                  ; (i = i1) → bbase q _
                  }) (bbase q _)


module _ {A : Type ℓ} where




 hlpSq : (l xs ys++zs ws : List A) →
     Square
        (sym (++-assoc l (xs ++ (ys++zs)) ws)
       ∙' cong (_++ ws) (sym (++-assoc _ _ _)))
        (sym (++-assoc l xs ((ys++zs) ++ ws)))
         (λ i → (l ++ ++-assoc xs (ys++zs) ws i))
        (++-assoc (l ++ xs) (ys++zs) ws)
 hlpSq l xs ys++zs ws j i =
   hcomp (λ k → λ {
          (i = i0) → ++-pentagon-□ l xs ys++zs ws (~ j) k
         ;(i = i1) → ++-assoc (l ++ xs) ys++zs ws j
         ;(j = i1) → ++-pentagon-△ l xs ys++zs ws (~ i) k
           }) (invSides-filler
                 (++-assoc (l ++ xs) ys++zs ws)
                 (cong (_++ ws) (++-assoc _ _ _))
                 (~ i) j)

 open Recℙ2'

 rℙ⊕ : Recℙ2' A (ℙ A) 𝕡trunc
 r11 rℙ⊕ x y = 𝕡base (x ++ y)
 Recℙ.bloopL (r12 rℙ⊕) xs ys zs ws =
   funExt λ l → cong 𝕡base (++-assoc _ _ _)
       ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
     cong 𝕡base (sym (++-assoc _ _ _))
 Recℙ.bloopR (r12 rℙ⊕) xs ys zs ws =
    funExt λ l → cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
      ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
    cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))
 Recℙ.bhexDiagAB (r12 rℙ⊕) ls xs ys zs rs =
    funExt λ l → cong 𝕡base (++-assoc _ _ _ ∙ cong (ls ++_) (++-assoc _ _ _))
         ∙∙ 𝕡hexDiagAB ls xs ys zs (rs ++ l) ∙∙
       cong 𝕡base (sym (++-assoc _ _ _))
 Recℙ.bhexDiagBC (r12 rℙ⊕) ls xs ys zs rs =
    funExt λ l → cong 𝕡base (cong (λ x → ((ls ++ x) ++ l))
                     (sym (++-assoc _ _ _))
                    ∙∙ ++-assoc _ _ _ ∙∙
                    cong (ls ++_) (++-pentagon-diag _ _ _ _))
         ∙∙ 𝕡hexDiagBC ls xs ys zs (rs ++ l) ∙∙
       cong 𝕡base (sym (++-assoc _ _ _))
 Recℙ.bhexDiagCD (r12 rℙ⊕) ls xs ys zs rs =
    funExt λ l → cong 𝕡base (++-assoc _ _ _ ∙ cong ((ls ++ xs ++ ys) ++_) (++-assoc _ _ _) )
         ∙∙ 𝕡hexDiagCD ls xs ys zs (rs ++ l) ∙∙
       cong 𝕡base (sym (++-assoc _ _ _))
 Recℙ.binvolL (r13 rℙ⊕) xs ys zs ws = funExtSq _ _ _ _
    λ l → refl ∙∙₂ 𝕡involL xs ys zs (ws ++ l) ∙∙₂ refl

 Recℙ.bloopAssoc (r13 rℙ⊕) xs ys zs ws = funExtSq _ _ _ _
    λ l → {!congSq 𝕡base (hlpSq l xs (ys ++ zs) ws)
       ∙∙₂ 𝕡loopAssoc xs ys zs (ws ++ l) ∙∙₂
     congSq 𝕡base (congP (λ _ → sym) (hlpSq l xs (zs ++ ys) ws))
!}
 Recℙ.bhexA (r13 rℙ⊕) = {!!}
 Recℙ.bhexB (r13 rℙ⊕) = {!!}
 Recℙ.bhexC (r13 rℙ⊕) = {!!}
 Recℙ.bhexD (r13 rℙ⊕) = {!!}
 truncHlp1 rℙ⊕ = {!!}
 Recℙ.bloopL (r21 rℙ⊕ l) xs ys zs ws = 
         (cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
              ∙' cong (_++ ws) (sym (++-assoc _ _ _))))
              
        ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
         ( sym (cong 𝕡base (sym (++-assoc l (xs ++ (zs ++ ys)) ws)
              ∙' cong (_++ ws) (sym (++-assoc _ _ _)))))
 Recℙ.bloopR (r21 rℙ⊕ l) xs ys zs ws =
        cong 𝕡base (sym (++-assoc _ _ _))
         ∙∙ 𝕡loopR (l ++ xs) ys zs ws ∙∙
       cong 𝕡base (++-assoc _ _ _)
 Recℙ.bhexDiagAB (r21 rℙ⊕ l) ls xs ys zs rs =
             (cong 𝕡base (sym (++-assoc _ _ _))
         ∙∙ 𝕡hexDiagAB (l ++ ls) xs ys zs rs ∙∙
       cong 𝕡base (cong (_++ rs) (++-assoc _ _ _) ∙ ++-assoc _ _  _))
 Recℙ.bhexDiagBC (r21 rℙ⊕ l) ls xs ys zs rs =
         cong 𝕡base (sym (++-assoc _ _ _))
         ∙∙ 𝕡hexDiagBC (l ++ ls) xs ys zs rs ∙∙
       cong 𝕡base (cong (_++ rs) (++-pentagon-diag _ _ _ _)
         ∙∙ (++-assoc _ _ _) ∙∙
         cong (λ x → (l ++ x ++ rs)) (sym (++-assoc _ _ _)))
 Recℙ.bhexDiagCD (r21 rℙ⊕ l) ls xs ys zs rs =
        cong 𝕡base ((sym (++-assoc _ _ _) ∙'
                  λ i → (++-assoc l ls (xs ++ ys) (~ i)) ++ zs ++ rs))
         ∙∙ 𝕡hexDiagCD (l ++ ls) xs ys zs rs ∙∙
       cong 𝕡base (cong ((_++ rs) ∘' (_++ (xs ++ zs))) (++-assoc _ _ _)
            ∙∙ cong (_++ rs) (++-assoc _ _ _)
            ∙∙ ++-assoc _ _ _)
 r22 rℙ⊕ = fromH2P (Elimℙ.h1 (r21 rℙ⊕)) w
  where
  w : (xs ys zs ws : List A) →
        PathP
        (λ i →
           Recℙ.H2
           (Recℙ.h1
            (Recℙ.f₃ (r13 rℙ⊕) (truncHlp1 rℙ⊕) (𝕡loopL xs ys zs ws i))))
        (r21 rℙ⊕ ((xs ++ ys ++ zs) ++ ws))
        (r21 rℙ⊕ ((xs ++ zs ++ ys) ++ ws))
  Recℙ.bloopL (w xs ys zs ws i) = {!!}
  Recℙ.bloopR (w xs ys zs ws i) = {!!}
  Recℙ.bhexDiagAB (w xs ys zs ws i) = {!!}
  Recℙ.bhexDiagBC (w xs ys zs ws i) = {!!}
  Recℙ.bhexDiagCD (w xs ys zs ws i) = {!!}
 
 trunncHlp2 rℙ⊕ = {!!}
 Recℙ.binvolL (Elimℙ.bbase (r31 rℙ⊕) l) xs ys zs ws =
    refl ∙∙₂ 𝕡involL (l ++ xs) ys zs ws ∙∙₂ refl

 Recℙ.bloopAssoc (Elimℙ.bbase (r31 rℙ⊕) l) xs ys zs ws = 
   congSq 𝕡base (hlpSq l xs (ys ++ zs) ws)
       ∙∙₂ 𝕡loopAssoc (l ++ xs) ys zs ws ∙∙₂
     congSq 𝕡base (congP (λ _ → sym) (hlpSq l xs (zs ++ ys) ws))
 Recℙ.bhexA (Elimℙ.bbase (r31 rℙ⊕) l) ls xs ys zs rs = 
   congSq 𝕡base (λ i → hlpSq l ls (++-assoc xs ys zs (~ i)) rs i)
       ∙∙₂ 𝕡hexA (l ++ ls) xs ys zs rs ∙∙₂
     congSq 𝕡base
       λ i j →
          ((λ j → (++-assoc l ls (++-assoc ys zs xs i) j) ++ rs) ∙
              ++-assoc l (ls ++ ++-assoc ys zs xs i) rs) j
   
 Recℙ.bhexB (Elimℙ.bbase (r31 rℙ⊕) l) ls xs ys zs rs =
      congSq 𝕡base
       (λ i → sym (++-assoc l ls (++-assoc (xs ++ ys) zs rs i)))
       ∙∙₂ 𝕡hexB (l ++ ls) xs ys zs rs ∙∙₂
     congSq 𝕡base {!!}

 Recℙ.bhexC (Elimℙ.bbase (r31 rℙ⊕) l) ls xs ys zs rs =
   congSq 𝕡base (symP (hlpSq  l ls (xs ++ ys) (zs ++ rs)))
     ∙∙₂  𝕡hexC (l ++ ls) xs ys zs rs  ∙∙₂
       {!!}
 Recℙ.bhexD (Elimℙ.bbase (r31 rℙ⊕) l) ls xs ys zs rs = {!!} 
    -- congSq 𝕡base {!!}
    --    ∙∙₂ 𝕡hexD (l ++ ls) xs ys zs rs ∙∙₂
    --  congSq  {!!}




 -- Recℙ2'.r21 rℙ⊕ = Elimℙ.h1 w 
 --  where
 --  w : (a : List A) →
 --    Recℙ.H2 (Recℙ.f₃ (_) (_) (𝕡base a))
 --  Recℙ.bloopL (w l) xs ys zs ws =
    
 --      (cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
 --              ∙' cong (_++ ws) (sym (++-assoc _ _ _))))
              
 --        ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
 --         ( sym (cong 𝕡base (sym (++-assoc l (xs ++ (zs ++ ys)) ws)
 --              ∙' cong (_++ ws) (sym (++-assoc _ _ _)))))
 --  Recℙ.bloopR (w l) xs ys zs ws =
 --    cong 𝕡base (sym (++-assoc _ _ _))
 --         ∙∙ 𝕡loopR (l ++ xs) ys zs ws ∙∙
 --       cong 𝕡base (++-assoc _ _ _)




 --  Recℙ.bhexDiagAB (w l) ls xs ys zs rs =
 --          (cong 𝕡base (sym (++-assoc _ _ _))
 --         ∙∙ 𝕡hexDiagAB (l ++ ls) xs ys zs rs ∙∙
 --       cong 𝕡base (cong (_++ rs) (++-assoc _ _ _) ∙ ++-assoc _ _  _))
 --  Recℙ.bhexDiagBC (w l) ls xs ys zs rs =
 --      cong 𝕡base (sym (++-assoc _ _ _))
 --         ∙∙ 𝕡hexDiagBC (l ++ ls) xs ys zs rs ∙∙
 --       cong 𝕡base (cong (_++ rs) (++-pentagon-diag _ _ _ _)
 --         ∙∙ (++-assoc _ _ _) ∙∙
 --         cong (λ x → (l ++ x ++ rs)) (sym (++-assoc _ _ _)))
 --  Recℙ.bhexDiagCD (w l) ls xs ys zs rs =
 --      cong 𝕡base ((sym (++-assoc _ _ _) ∙'
 --                  λ i → (++-assoc l ls (xs ++ ys) (~ i)) ++ zs ++ rs))
 --         ∙∙ 𝕡hexDiagCD (l ++ ls) xs ys zs rs ∙∙
 --       cong 𝕡base (cong ((_++ rs) ∘' (_++ (xs ++ zs))) (++-assoc _ _ _)
 --            ∙∙ cong (_++ rs) (++-assoc _ _ _)
 --            ∙∙ ++-assoc _ _ _)

--  Recℙ2'.r11 rℙ⊕ = w
--   where
--   w : Recℙ.H1 (Recℙ.H1 (ℙ A))
--   Recℙ.bbase (Recℙ.bbase w x) y = 𝕡base (x ++ y)
--  Recℙ2'.r12 rℙ⊕ = w
--   where
--   w : Recℙ.H2 (Recℙ2'.r11 rℙ⊕)
--   Recℙ.bbase (Recℙ.bloopL w xs ys zs ws i) l =
--     (cong 𝕡base (++-assoc _ _ _)
--        ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
--      cong 𝕡base (sym (++-assoc _ _ _))) i
--   Recℙ.bbase (Recℙ.bloopR w xs ys zs ws i) l =
--     (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
--       ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
--     cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))) i
--   Recℙ.bbase (Recℙ.bhexDiagAB w ls xs ys zs rs i) l = 
--     (cong 𝕡base (++-assoc _ _ _ ∙ cong (ls ++_) (++-assoc _ _ _))
--          ∙∙ 𝕡hexDiagAB ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))) i
--   Recℙ.bbase (Recℙ.bhexDiagBC w ls xs ys zs rs i) l =
--     (cong 𝕡base (cong (λ x → ((ls ++ x) ++ l))
--                      (sym (++-assoc _ _ _))
--                     ∙∙ ++-assoc _ _ _ ∙∙
--                     cong (ls ++_) (++-pentagon-diag _ _ _ _))
--          ∙∙ 𝕡hexDiagBC ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))) i
--   Recℙ.bbase (Recℙ.bhexDiagCD w ls xs ys zs rs i) l =
--     (cong 𝕡base (++-assoc _ _ _ ∙ cong ((ls ++ xs ++ ys) ++_) (++-assoc _ _ _) )
--          ∙∙ 𝕡hexDiagCD ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))) i


--  Recℙ.bbase (Recℙ.binvolL (Recℙ2'.r13 rℙ⊕) xs ys zs ws j i) l =
--    (cong 𝕡base (++-assoc _ _ _)
--        ∙∙ 𝕡involL xs ys zs (ws ++ l) j ∙∙
--      cong 𝕡base (sym (++-assoc _ _ _))) i
--  Recℙ.bbase (Recℙ.bloopAssoc (Recℙ2'.r13 rℙ⊕) xs ys zs ws i i₁) x = {!!}
--  Recℙ.bhexA (Recℙ2'.r13 rℙ⊕) = {!!}
--  Recℙ.bhexB (Recℙ2'.r13 rℙ⊕) = {!!}
--  Recℙ.bhexC (Recℙ2'.r13 rℙ⊕) = {!!}
--  Recℙ.bhexD (Recℙ2'.r13 rℙ⊕) = {!!}



   



-- module _ (A : Type ℓ) where

--  record Recℙ2' {ℓb} (B : Type ℓb) (isGroupoidB : isGroupoid B) : Type (ℓ-max ℓ ℓb) where
--   no-eta-equality
--   constructor recℙ2
  
--   field
--    r11 : Recℙ.H1 {A = A} (Recℙ.H1 {A = A} B)
--    r12 : Recℙ.H2 r11
--    r13 : Recℙ.H3 r12
--    truncHlp1 : _

--   hhh = Recℙ.f₃ r13 truncHlp1
   
--   field
--    r21 : Elimℙ.H1 {A = A} (λ z → Recℙ.H2 {A = A} (hhh z))
--    r22 : Elimℙ.H2 {A = A} {B = λ z → Recℙ.H2 (Recℙ.f₃ r13 truncHlp1 z)} r21
--    trunncHlp2 : ∀ x → isSet (Recℙ.H2 (Recℙ.f₃ r13 truncHlp1 x))
   
--   hh = Elimℙ.f₂ r22 trunncHlp2
   
--   field
--    r31 : Elimℙ.H1 {A = A} (λ z → Recℙ.H3 {A = A} (hh z))



--   f2 : ℙ A → ℙ A → B
--   f2 x = Recℙ.f₃ (Elimℙ.f₁ r31
--     (λ x → Recℙ.isOfHLevelH3
--            ((hh x)) 1 isGroupoidB) x) isGroupoidB





-- module _ {A : Type ℓ} where



--  hlpSq : (l xs ys++zs ws : List A) →
--      Square
--         (sym (++-assoc l (xs ++ (ys++zs)) ws)
--        ∙' cong (_++ ws) (sym (++-assoc _ _ _)))
--         (sym (++-assoc l xs ((ys++zs) ++ ws)))
--          (λ i → (l ++ ++-assoc xs (ys++zs) ws i))
--         (++-assoc (l ++ xs) (ys++zs) ws)
--  hlpSq l xs ys++zs ws j i =
--    hcomp (λ k → λ {
--           (i = i0) → ++-pentagon-□ l xs ys++zs ws (~ j) k
--          ;(i = i1) → ++-assoc (l ++ xs) ys++zs ws j
--          ;(j = i1) → ++-pentagon-△ l xs ys++zs ws (~ i) k
--            }) (invSides-filler
--                  (++-assoc (l ++ xs) ys++zs ws)
--                  (cong (_++ ws) (++-assoc _ _ _))
--                  (~ i) j)



--  rℙ⊕ : Recℙ2' A (ℙ A) 𝕡trunc 
--  Recℙ2'.r11 rℙ⊕ = w
--   where
--   w : Recℙ.H1 (Recℙ.H1 (ℙ A))
--   Recℙ.bbase (Recℙ.bbase w x) y = 𝕡base (x ++ y)
--  Recℙ2'.r12 rℙ⊕ = w
--   where
--   w : Recℙ.H2 (Recℙ2'.r11 rℙ⊕)
--   Recℙ.bbase (Recℙ.bloopL w xs ys zs ws i) l =
--     (cong 𝕡base (++-assoc _ _ _)
--        ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
--      cong 𝕡base (sym (++-assoc _ _ _))) i
--   Recℙ.bbase (Recℙ.bloopR w xs ys zs ws i) l =
--     (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
--       ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
--     cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))) i
--   Recℙ.bbase (Recℙ.bhexDiagAB w ls xs ys zs rs i) l = 
--     (cong 𝕡base (++-assoc _ _ _ ∙ cong (ls ++_) (++-assoc _ _ _))
--          ∙∙ 𝕡hexDiagAB ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))) i
--   Recℙ.bbase (Recℙ.bhexDiagBC w ls xs ys zs rs i) l =
--     (cong 𝕡base (cong (λ x → ((ls ++ x) ++ l))
--                      (sym (++-assoc _ _ _))
--                     ∙∙ ++-assoc _ _ _ ∙∙
--                     cong (ls ++_) (++-pentagon-diag _ _ _ _))
--          ∙∙ 𝕡hexDiagBC ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))) i
--   Recℙ.bbase (Recℙ.bhexDiagCD w ls xs ys zs rs i) l =
--     (cong 𝕡base (++-assoc _ _ _ ∙ cong ((ls ++ xs ++ ys) ++_) (++-assoc _ _ _) )
--          ∙∙ 𝕡hexDiagCD ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))) i


--  Recℙ.bbase (Recℙ.binvolL (Recℙ2'.r13 rℙ⊕) xs ys zs ws j i) l =
--    (cong 𝕡base (++-assoc _ _ _)
--        ∙∙ 𝕡involL xs ys zs (ws ++ l) j ∙∙
--      cong 𝕡base (sym (++-assoc _ _ _))) i
--  Recℙ.bbase (Recℙ.bloopAssoc (Recℙ2'.r13 rℙ⊕) xs ys zs ws i i₁) x = {!!}
--  Recℙ.bhexA (Recℙ2'.r13 rℙ⊕) = {!!}
--  Recℙ.bhexB (Recℙ2'.r13 rℙ⊕) = {!!}
--  Recℙ.bhexC (Recℙ2'.r13 rℙ⊕) = {!!}
--  Recℙ.bhexD (Recℙ2'.r13 rℙ⊕) = {!!}


-- -- -- --  hlpSq : (l xs ys++zs ws : List A) →
-- -- -- --      Square
-- -- -- --         (sym (++-assoc l (xs ++ (ys++zs)) ws)
-- -- -- --        ∙' cong (_++ ws) (sym (++-assoc _ _ _)))
-- -- -- --         (sym (++-assoc l xs ((ys++zs) ++ ws)))
-- -- -- --          (λ i → (l ++ ++-assoc xs (ys++zs) ws i))
-- -- -- --         (++-assoc (l ++ xs) (ys++zs) ws)
-- -- -- --  hlpSq l xs ys++zs ws j i =
-- -- -- --    hcomp (λ k → λ {
-- -- -- --           (i = i0) → ++-pentagon-□ l xs ys++zs ws (~ j) k
-- -- -- --          ;(i = i1) → ++-assoc (l ++ xs) ys++zs ws j
-- -- -- --          ;(j = i1) → ++-pentagon-△ l xs ys++zs ws (~ i) k
-- -- -- --            }) (invSides-filler
-- -- -- --                  (++-assoc (l ++ xs) ys++zs ws)
-- -- -- --                  (cong (_++ ws) (++-assoc _ _ _))
-- -- -- --                  (~ i) j)


-- -- -- --  ℙ++G3 : H3 ℙ++G2
-- -- -- --  binvolL ℙ++G3 xs ys zs ws =
-- -- -- --    refl
-- -- -- --     ∙∙₂ 𝕡involL (l ++ xs) ys zs ws ∙∙₂
-- -- -- --     refl

-- -- -- --  bloopAssoc ℙ++G3 xs ys zs ws =
-- -- -- --     congSq 𝕡base (hlpSq l xs (ys ++ zs) ws)
-- -- -- --        ∙∙₂ 𝕡loopAssoc (l ++ xs) ys zs ws ∙∙₂
-- -- -- --      congSq 𝕡base (congP (λ _ → sym) (hlpSq l xs (zs ++ ys) ws))
   
-- -- -- --  bhexA ℙ++G3 ls xs ys zs rs =
-- -- -- --     congSq 𝕡base (λ i → hlpSq l ls (++-assoc xs ys zs (~ i)) rs i)
-- -- -- --        ∙∙₂ 𝕡hexA (l ++ ls) xs ys zs rs ∙∙₂
-- -- -- --      congSq 𝕡base
-- -- -- --        λ i j →
-- -- -- --           ((λ j → (++-assoc l ls (++-assoc ys zs xs i) j) ++ rs) ∙
-- -- -- --               ++-assoc l (ls ++ ++-assoc ys zs xs i) rs) j
   
-- -- -- --  bhexB ℙ++G3 ls xs ys zs rs =
-- -- -- --     congSq 𝕡base
-- -- -- --        (λ i → sym (++-assoc l ls (++-assoc (xs ++ ys) zs rs i)))
-- -- -- --        ∙∙₂ 𝕡hexB (l ++ ls) xs ys zs rs ∙∙₂
-- -- -- --      congSq 𝕡base {!!}

-- -- -- --  bhexC ℙ++G3 ls xs ys zs rs =
-- -- -- --    congSq 𝕡base (symP (hlpSq  l ls (xs ++ ys) (zs ++ rs)))
-- -- -- --      ∙∙₂  𝕡hexC (l ++ ls) xs ys zs rs  ∙∙₂
-- -- -- --        {!!}

-- -- -- --  bhexD ℙ++G3 ls xs ys zs rs = {!!}
-- -- -- --     -- congSq 𝕡base {!!}
-- -- -- --     --    ∙∙₂ 𝕡hexD (l ++ ls) xs ys zs rs ∙∙₂
-- -- -- --     --  congSq 𝕡base {!!}




--  Recℙ2'.truncHlp1 rℙ⊕ = (Recℙ.isOfHLevelH1 _ 3 𝕡trunc)
--  Recℙ2'.r21 rℙ⊕ = Elimℙ.h1 w 
--   where
--   w : (a : List A) →
--     Recℙ.H2 (Recℙ.f₃ (_) (_) (𝕡base a))
--   Recℙ.bloopL (w l) xs ys zs ws =
    
--       (cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
--               ∙' cong (_++ ws) (sym (++-assoc _ _ _))))
              
--         ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
--          ( sym (cong 𝕡base (sym (++-assoc l (xs ++ (zs ++ ys)) ws)
--               ∙' cong (_++ ws) (sym (++-assoc _ _ _)))))
--   Recℙ.bloopR (w l) xs ys zs ws =
--     cong 𝕡base (sym (++-assoc _ _ _))
--          ∙∙ 𝕡loopR (l ++ xs) ys zs ws ∙∙
--        cong 𝕡base (++-assoc _ _ _)




--   Recℙ.bhexDiagAB (w l) ls xs ys zs rs =
--           (cong 𝕡base (sym (++-assoc _ _ _))
--          ∙∙ 𝕡hexDiagAB (l ++ ls) xs ys zs rs ∙∙
--        cong 𝕡base (cong (_++ rs) (++-assoc _ _ _) ∙ ++-assoc _ _  _))
--   Recℙ.bhexDiagBC (w l) ls xs ys zs rs =
--       cong 𝕡base (sym (++-assoc _ _ _))
--          ∙∙ 𝕡hexDiagBC (l ++ ls) xs ys zs rs ∙∙
--        cong 𝕡base (cong (_++ rs) (++-pentagon-diag _ _ _ _)
--          ∙∙ (++-assoc _ _ _) ∙∙
--          cong (λ x → (l ++ x ++ rs)) (sym (++-assoc _ _ _)))
--   Recℙ.bhexDiagCD (w l) ls xs ys zs rs =
--       cong 𝕡base ((sym (++-assoc _ _ _) ∙'
--                   λ i → (++-assoc l ls (xs ++ ys) (~ i)) ++ zs ++ rs))
--          ∙∙ 𝕡hexDiagCD (l ++ ls) xs ys zs rs ∙∙
--        cong 𝕡base (cong ((_++ rs) ∘' (_++ (xs ++ zs))) (++-assoc _ _ _)
--             ∙∙ cong (_++ rs) (++-assoc _ _ _)
--             ∙∙ ++-assoc _ _ _)
--  Recℙ2'.r22 rℙ⊕ = {!!}
--  Recℙ2'.trunncHlp2 rℙ⊕ = {!!}
--  Recℙ2'.r31 rℙ⊕ = {!!}
 
--  -- Recℙ.bbase (Recℙ.bbase (Recℙ2'.r11 rℙ⊕) x) y = 𝕡base (x ++ y)
--  -- Recℙ.bbase (Recℙ.bloopL (Recℙ2'.r12 rℙ⊕) xs ys zs ws i) l =
   
--  --   (cong 𝕡base (++-assoc _ _ _)
--  --       ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
--  --     cong 𝕡base (sym (++-assoc _ _ _))) i
   
--  -- Recℙ.bbase (Recℙ.bloopR (Recℙ2'.r12 rℙ⊕) xs ys zs ws i) l =
--  --   (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
--  --         ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
--  --       cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))) i
       
--  -- Recℙ.bhexDiagAB (Recℙ2'.r12 rℙ⊕) = {!!}
--  -- Recℙ.bhexDiagBC (Recℙ2'.r12 rℙ⊕) = {!!}
--  -- Recℙ.bhexDiagCD (Recℙ2'.r12 rℙ⊕) = {!!}
--  -- Recℙ2'.r13 rℙ⊕ = {!!}
--  -- Recℙ2'.truncHlp1 rℙ⊕ = {!!}
--  -- Recℙ2'.r21 rℙ⊕ = {!!}
--  -- Recℙ2'.r22 rℙ⊕ = {!!}
--  -- Recℙ2'.trunncHlp2 rℙ⊕ = {!!}
--  -- Elimℙ.bbase (Recℙ2'.r31 rℙ⊕) a = {!!}

--  -- ℙ⊕ : ℙ A → ℙ A → ℙ A
--  -- ℙ⊕ = Recℙ2'.f2 rℙ⊕
 



-- -- module _ {ℓ} {A : Type ℓ} (l : List A) where
-- --  open Recℙ {A = A} (Σ (ℙ A × ℙ A) (uncurry _≡_))

-- --  ℙ++G1 : H1
-- --  fst (bbase ℙ++G1 x) = 𝕡base (l ++ x) , 𝕡base (x ++ l)
-- --  snd (bbase ℙ++G1 x) =
-- --   cong 𝕡base (λ i → ++-unit-r (++-unit-l (l ++ x) (~ i)) (~ i) )
-- --   ∙∙ 𝕡loopL [] l x [] ∙∙
-- --   cong 𝕡base (λ i → ++-unit-r (++-unit-l (x ++ l) (i)) (i) )

-- --  ℙ++G2 : H2 ℙ++G1
-- --  Recℙ.bloopL ℙ++G2 xs ys zs ws =
-- --    ΣPathP ((cong₂ _,_
-- --       (cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
-- --               ∙' cong (_++ ws) (sym (++-assoc _ _ _)))
-- --             ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
-- --           cong 𝕡base (cong (_++ ws) ((++-assoc _ _ _)) ∙ (++-assoc _ _ _)))
-- --       (cong 𝕡base (++-assoc _ _ _)
-- --         ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
-- --         cong 𝕡base (sym (++-assoc _ _ _))))
-- --      , {!!}
-- --          -- (flipSquare
-- --          -- ({!!} ∙∙₂ refl ∙∙₂ {!!})
-- --          --  ∙∙₂ {!!} ∙∙₂
-- --          --  flipSquare
-- --          -- ({!!} ∙∙₂ refl ∙∙₂ {!!}) )
-- --          )
-- --  Recℙ.bloopR ℙ++G2 xs ys zs ws =
-- --    ΣPathP ((cong₂ _,_
-- --       (cong 𝕡base (sym (++-assoc _ _ _))
-- --          ∙∙ 𝕡loopR (l ++ xs) ys zs ws ∙∙
-- --        cong 𝕡base (++-assoc _ _ _))
-- --       (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
-- --          ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
-- --        cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))))
-- --     , {!!})
-- --  Recℙ.bhexDiagAB ℙ++G2 ls xs ys zs rs =
-- --    ΣPathP ((cong₂ _,_
-- --       (cong 𝕡base (sym (++-assoc _ _ _))
-- --          ∙∙ 𝕡hexDiagAB (l ++ ls) xs ys zs rs ∙∙
-- --        cong 𝕡base (cong (_++ rs) (++-assoc _ _ _) ∙ ++-assoc _ _  _))
-- --       (cong 𝕡base (++-assoc _ _ _ ∙ cong (ls ++_) (++-assoc _ _ _))
-- --          ∙∙ 𝕡hexDiagAB ls xs ys zs (rs ++ l) ∙∙
-- --        cong 𝕡base (sym (++-assoc _ _ _))))
-- --     , {!!})
-- --  Recℙ.bhexDiagBC ℙ++G2 ls xs ys zs rs =
-- --    ΣPathP ((cong₂ _,_
-- --       (cong 𝕡base (sym (++-assoc _ _ _))
-- --          ∙∙ 𝕡hexDiagBC (l ++ ls) xs ys zs rs ∙∙
-- --        cong 𝕡base (cong (_++ rs) (++-pentagon-diag _ _ _ _)
-- --          ∙∙ (++-assoc _ _ _) ∙∙
-- --          cong (λ x → (l ++ x ++ rs)) (sym (++-assoc _ _ _))))
-- --       (cong 𝕡base (cong (λ x → ((ls ++ x) ++ l))
-- --                      (sym (++-assoc _ _ _))
-- --                     ∙∙ ++-assoc _ _ _ ∙∙
-- --                     cong (ls ++_) (++-pentagon-diag _ _ _ _))
-- --          ∙∙ 𝕡hexDiagBC ls xs ys zs (rs ++ l) ∙∙
-- --        cong 𝕡base (sym (++-assoc _ _ _))))
-- --     , {!!})
-- --  Recℙ.bhexDiagCD ℙ++G2 ls xs ys zs rs =
-- --    ΣPathP ((cong₂ _,_
-- --       (cong 𝕡base ((sym (++-assoc _ _ _) ∙'
-- --                   λ i → (++-assoc l ls (xs ++ ys) (~ i)) ++ zs ++ rs))
-- --          ∙∙ 𝕡hexDiagCD (l ++ ls) xs ys zs rs ∙∙
-- --        cong 𝕡base (cong ((_++ rs) ∘' (_++ (xs ++ zs))) (++-assoc _ _ _)
-- --             ∙∙ cong (_++ rs) (++-assoc _ _ _)
-- --             ∙∙ ++-assoc _ _ _))
-- --       (cong 𝕡base (++-assoc _ _ _ ∙ cong ((ls ++ xs ++ ys) ++_) (++-assoc _ _ _) )
-- --          ∙∙ 𝕡hexDiagCD ls xs ys zs (rs ++ l) ∙∙
-- --        cong 𝕡base (sym (++-assoc _ _ _))))
-- --     , {!!})





--  -- record Recℙ2 {ℓb} (B : Type ℓb) (isGroupoidB : isGroupoid B) : Type (ℓ-max ℓ ℓb) where
--  --  no-eta-equality
--  --  constructor recℙ2
  
--  --  field
--  --   r11 : Recℙ.H1 {A = A} (Recℙ.H1 {A = A} B)
--  --   r12 : Recℙ.H2 r11
--  --   r13 : Recℙ.H3 r12

--  --  hhh = Recℙ.f₃ r13 (Recℙ.isOfHLevelH1 _ 3 isGroupoidB)
   
--  --  field
--  --   r21 : Elimℙ.H1 {A = A} (λ z → Recℙ.H2 {A = A} (hhh z))
--  --   r22 : Elimℙ.H2 {A = A} r21
   
--  --  hh = Elimℙ.f₂ r22 λ x → Recℙ.isOfHLevelH2 (hhh x) 2 isGroupoidB
   
--  --  -- field
--  --  --  r31 : Elimℙ.H1 {A = A} (λ z → Recℙ.H3 {A = A} (hh z))

--  --  -- -- f2 : ℙ A → ℙ A → B
--  --  -- -- f2 x = Recℙ.f₃ (Elimℙ.f₁ r31
--  --  -- --   (λ x → Recℙ.isOfHLevelH3
--  --  -- --          ((hh x)) 1 isGroupoidB) x) isGroupoidB

