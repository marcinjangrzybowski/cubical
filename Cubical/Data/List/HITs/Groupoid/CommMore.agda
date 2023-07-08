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
   r11 : Recℙ.H1 {A = A} (Recℙ.H1 {A = A} B)
   r12 : Recℙ.H2 r11
   r13 : Recℙ.H3 r12
   truncHlp1 : _

  hhh = Recℙ.f₃ r13 truncHlp1
   
  field
   r21 : Elimℙ.H1 {A = A} (λ z → Recℙ.H2 {A = A} (hhh z))
   r22 : Elimℙ.H2 {A = A} r21
   trunncHlp2 : ∀ x → isSet (Recℙ.H2 (Recℙ.f₃ r13 truncHlp1 x))
   
  hh = Elimℙ.f₂ r22 trunncHlp2
   
  field
   r31 : Elimℙ.H1 {A = A} (λ z → Recℙ.H3 {A = A} (hh z))



  f2 : ℙ A → ℙ A → B
  f2 x = Recℙ.f₃ (Elimℙ.f₁ r31
    (λ x → Recℙ.isOfHLevelH3
           ((hh x)) 1 isGroupoidB) x) isGroupoidB


module _ {A : Type ℓ} where



 rℙ⊕ : Recℙ2' A (ℙ A) 𝕡trunc 
 Recℙ2'.r11 rℙ⊕ = w
  where
  w : Recℙ.H1 (Recℙ.H1 (ℙ A))
  Recℙ.bbase (Recℙ.bbase w x) y = 𝕡base (x ++ y)
 Recℙ2'.r12 rℙ⊕ = w
  where
  w : Recℙ.H2 (Recℙ2'.r11 rℙ⊕)
  Recℙ.bbase (Recℙ.bloopL w xs ys zs ws i) l =
    (cong 𝕡base (++-assoc _ _ _)
       ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
     cong 𝕡base (sym (++-assoc _ _ _))) i
  Recℙ.bbase (Recℙ.bloopR w xs ys zs ws i) l =
    (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
      ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
    cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))) i
  Recℙ.bhexDiagAB w = {!!}
  Recℙ.bhexDiagBC w = {!!}
  Recℙ.bhexDiagCD w = {!!}
 Recℙ2'.r13 rℙ⊕ = {!!}
 Recℙ2'.truncHlp1 rℙ⊕ = (Recℙ.isOfHLevelH1 _ 3 𝕡trunc)
 Recℙ2'.r21 rℙ⊕ = Elimℙ.h1 w 
  where
  w : (a : List A) →
    Recℙ.H2 (Recℙ.f₃ (_) (_) (𝕡base a))
  Recℙ.bloopL (w l) xs ys zs ws =
    
      (cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
              ∙' cong (_++ ws) (sym (++-assoc _ _ _))))
              
        ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
         ( sym (cong 𝕡base (sym (++-assoc l (xs ++ (zs ++ ys)) ws)
              ∙' cong (_++ ws) (sym (++-assoc _ _ _)))))
  Recℙ.bloopR (w l) = {!!}
  Recℙ.bhexDiagAB (w l) = {!!}
  Recℙ.bhexDiagBC (w l) = {!!}
  Recℙ.bhexDiagCD (w l) = {!!}
 Recℙ2'.r22 rℙ⊕ = {!!}
 Recℙ2'.trunncHlp2 rℙ⊕ = {!!}
 Recℙ2'.r31 rℙ⊕ = {!!}
 
 -- Recℙ.bbase (Recℙ.bbase (Recℙ2'.r11 rℙ⊕) x) y = 𝕡base (x ++ y)
 -- Recℙ.bbase (Recℙ.bloopL (Recℙ2'.r12 rℙ⊕) xs ys zs ws i) l =
   
 --   (cong 𝕡base (++-assoc _ _ _)
 --       ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
 --     cong 𝕡base (sym (++-assoc _ _ _))) i
   
 -- Recℙ.bbase (Recℙ.bloopR (Recℙ2'.r12 rℙ⊕) xs ys zs ws i) l =
 --   (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
 --         ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
 --       cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))) i
       
 -- Recℙ.bhexDiagAB (Recℙ2'.r12 rℙ⊕) = {!!}
 -- Recℙ.bhexDiagBC (Recℙ2'.r12 rℙ⊕) = {!!}
 -- Recℙ.bhexDiagCD (Recℙ2'.r12 rℙ⊕) = {!!}
 -- Recℙ2'.r13 rℙ⊕ = {!!}
 -- Recℙ2'.truncHlp1 rℙ⊕ = {!!}
 -- Recℙ2'.r21 rℙ⊕ = {!!}
 -- Recℙ2'.r22 rℙ⊕ = {!!}
 -- Recℙ2'.trunncHlp2 rℙ⊕ = {!!}
 -- Elimℙ.bbase (Recℙ2'.r31 rℙ⊕) a = {!!}

 -- ℙ⊕ : ℙ A → ℙ A → ℙ A
 -- ℙ⊕ = Recℙ2'.f2 rℙ⊕
 



-- module _ {ℓ} {A : Type ℓ} (l : List A) where
--  open Recℙ {A = A} (Σ (ℙ A × ℙ A) (uncurry _≡_))

--  ℙ++G1 : H1
--  fst (bbase ℙ++G1 x) = 𝕡base (l ++ x) , 𝕡base (x ++ l)
--  snd (bbase ℙ++G1 x) =
--   cong 𝕡base (λ i → ++-unit-r (++-unit-l (l ++ x) (~ i)) (~ i) )
--   ∙∙ 𝕡loopL [] l x [] ∙∙
--   cong 𝕡base (λ i → ++-unit-r (++-unit-l (x ++ l) (i)) (i) )

--  ℙ++G2 : H2 ℙ++G1
--  Recℙ.bloopL ℙ++G2 xs ys zs ws =
--    ΣPathP ((cong₂ _,_
--       (cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
--               ∙' cong (_++ ws) (sym (++-assoc _ _ _)))
--             ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
--           cong 𝕡base (cong (_++ ws) ((++-assoc _ _ _)) ∙ (++-assoc _ _ _)))
--       (cong 𝕡base (++-assoc _ _ _)
--         ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
--         cong 𝕡base (sym (++-assoc _ _ _))))
--      , {!!}
--          -- (flipSquare
--          -- ({!!} ∙∙₂ refl ∙∙₂ {!!})
--          --  ∙∙₂ {!!} ∙∙₂
--          --  flipSquare
--          -- ({!!} ∙∙₂ refl ∙∙₂ {!!}) )
--          )
--  Recℙ.bloopR ℙ++G2 xs ys zs ws =
--    ΣPathP ((cong₂ _,_
--       (cong 𝕡base (sym (++-assoc _ _ _))
--          ∙∙ 𝕡loopR (l ++ xs) ys zs ws ∙∙
--        cong 𝕡base (++-assoc _ _ _))
--       (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
--          ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))))
--     , {!!})
--  Recℙ.bhexDiagAB ℙ++G2 ls xs ys zs rs =
--    ΣPathP ((cong₂ _,_
--       (cong 𝕡base (sym (++-assoc _ _ _))
--          ∙∙ 𝕡hexDiagAB (l ++ ls) xs ys zs rs ∙∙
--        cong 𝕡base (cong (_++ rs) (++-assoc _ _ _) ∙ ++-assoc _ _  _))
--       (cong 𝕡base (++-assoc _ _ _ ∙ cong (ls ++_) (++-assoc _ _ _))
--          ∙∙ 𝕡hexDiagAB ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))))
--     , {!!})
--  Recℙ.bhexDiagBC ℙ++G2 ls xs ys zs rs =
--    ΣPathP ((cong₂ _,_
--       (cong 𝕡base (sym (++-assoc _ _ _))
--          ∙∙ 𝕡hexDiagBC (l ++ ls) xs ys zs rs ∙∙
--        cong 𝕡base (cong (_++ rs) (++-pentagon-diag _ _ _ _)
--          ∙∙ (++-assoc _ _ _) ∙∙
--          cong (λ x → (l ++ x ++ rs)) (sym (++-assoc _ _ _))))
--       (cong 𝕡base (cong (λ x → ((ls ++ x) ++ l))
--                      (sym (++-assoc _ _ _))
--                     ∙∙ ++-assoc _ _ _ ∙∙
--                     cong (ls ++_) (++-pentagon-diag _ _ _ _))
--          ∙∙ 𝕡hexDiagBC ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))))
--     , {!!})
--  Recℙ.bhexDiagCD ℙ++G2 ls xs ys zs rs =
--    ΣPathP ((cong₂ _,_
--       (cong 𝕡base ((sym (++-assoc _ _ _) ∙'
--                   λ i → (++-assoc l ls (xs ++ ys) (~ i)) ++ zs ++ rs))
--          ∙∙ 𝕡hexDiagCD (l ++ ls) xs ys zs rs ∙∙
--        cong 𝕡base (cong ((_++ rs) ∘' (_++ (xs ++ zs))) (++-assoc _ _ _)
--             ∙∙ cong (_++ rs) (++-assoc _ _ _)
--             ∙∙ ++-assoc _ _ _))
--       (cong 𝕡base (++-assoc _ _ _ ∙ cong ((ls ++ xs ++ ys) ++_) (++-assoc _ _ _) )
--          ∙∙ 𝕡hexDiagCD ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))))
--     , {!!})





 -- record Recℙ2 {ℓb} (B : Type ℓb) (isGroupoidB : isGroupoid B) : Type (ℓ-max ℓ ℓb) where
 --  no-eta-equality
 --  constructor recℙ2
  
 --  field
 --   r11 : Recℙ.H1 {A = A} (Recℙ.H1 {A = A} B)
 --   r12 : Recℙ.H2 r11
 --   r13 : Recℙ.H3 r12

 --  hhh = Recℙ.f₃ r13 (Recℙ.isOfHLevelH1 _ 3 isGroupoidB)
   
 --  field
 --   r21 : Elimℙ.H1 {A = A} (λ z → Recℙ.H2 {A = A} (hhh z))
 --   r22 : Elimℙ.H2 {A = A} r21
   
 --  hh = Elimℙ.f₂ r22 λ x → Recℙ.isOfHLevelH2 (hhh x) 2 isGroupoidB
   
 --  -- field
 --  --  r31 : Elimℙ.H1 {A = A} (λ z → Recℙ.H3 {A = A} (hh z))

 --  -- -- f2 : ℙ A → ℙ A → B
 --  -- -- f2 x = Recℙ.f₃ (Elimℙ.f₁ r31
 --  -- --   (λ x → Recℙ.isOfHLevelH3
 --  -- --          ((hh x)) 1 isGroupoidB) x) isGroupoidB

