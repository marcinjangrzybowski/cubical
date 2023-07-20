{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Data.List.HITs.Groupoid.Comm2More where

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
open import Cubical.Data.List.HITs.Groupoid.BaseMore

open import Cubical.Data.List.HITs.Groupoid.Comm2

private
  variable
    ℓ : Level


-- module _ (A : Type ℓ) where

--  fromList : List A → FCM₃ A
--  fromList = RecList.f₃ w trunc
--   where

--   w'' : RecList.H1 (FCM₃ A)
--   RecList.H1.b[] w'' = []
--   RecList.H1.b[ w'' ] = [_]
--   RecList.H1._b++_ w'' = _⊙_

--   w' : RecList.H2 w''
--   RecList.H2.b++ur w' = ⊙-unit-r
--   RecList.H2.b++ul w' = ⊙-unit-l
--   RecList.H2.b++-assoc w' = ⊙-assoc
--   RecList.H2.b++-pent-diag w' = ⊙-pentagon-diag

--   w : RecList.H3 w'
--   RecList.H3.b++-triangle w = ⊙-triangle
--   RecList.H3.b++-pent-△ w = ⊙-pentagon-△
--   RecList.H3.b++-pent-□ w = ⊙-pentagon-□


--  fromℙ : ℙ A → FCM₃ A
--  fromℙ = Recℙ.f₃ w trunc
--   where
--   w'' : Recℙ.H1 (FCM₃ A)
--   Recℙ.bbase w'' = fromList

--   wloop : (xs ys zs ws : List A) →
--       fromList (xs ++ ys ++ zs ++ ws) ≡
--       fromList (((xs ++ zs) ++ ys) ++ ws)
--   wloop xs ys zs ws =
--         cong ((fromList xs) ⊙_) (sym (⊙-assoc _ _ _))
--       ∙∙ (λ i → ⊙-assoc (fromList xs) (⊙-comm (fromList ys) (fromList zs) i) (fromList ws) (~ i))
--            ∙∙
--       cong (_⊙ (fromList ws)) (sym (⊙-assoc _ _ _))

--   w' : Recℙ.H2 w''
--   Recℙ.bloop w' = wloop

--   Recℙ.bhexDiag w' ls xs ys zs rs =
--      cong (fromList ls ⊙_) (sym (⊙-pentagon-diag _ _ _ _))
--       ∙∙ (λ i → ⊙-assoc (fromList ls) (⊙-hex-diag (fromList xs) (fromList ys) (fromList zs) i) (fromList rs) (~ i)) ∙∙
--       cong (_⊙ fromList rs) (sym (⊙-pentagon-diag _ _ _ _))
--   Recℙ.bcommDiag w' xs ys zs ws++xs' ys' zs' ws' =
--     wloop _ _ _ _ ∙∙ sym (⊙-assoc _ _ _)  ∙∙ wloop _ _ _ _
    
--   Recℙ.bcommDiag' w' xs ys zs ws++xs' ys' zs' ws' =
--     cong fromList (sym (++-pentagon-diag _ _ _ _)
--          ∙∙ sym (++-assoc _ _ _) ∙∙
--          sym (++-pentagon-diag _ _ _ _)) 

--   w : Recℙ.H3 w'
--   Recℙ.binvol w xs ys zs ws =
--     flipSquare (congP (λ _ → sym) (⊙-pentagon-□ _ _ _ _)) ∙∙₂
--       {!!}
--      ∙∙₂ flipSquare (symP (⊙-pentagon-□ _ _ _ _))
--   Recℙ.bhexU w ls xs ys zs rs =
--      {!!}
--   Recℙ.bhexD w = {!!}
--   Recℙ.bcommA w xs ys zs ws++xs' ys' zs' ws' =
--     symP (doubleCompPath-filler _ _ _)
--   Recℙ.bcommB w xs ys zs ws++xs' ys' zs' ws' =
--     congSq fromList (symP (doubleCompPath-filler _ _ _))
--   Recℙ.bcomm w xs ys zs ws++xs' ys' zs' ws' =
--     {!!} ∙∙₂ (λ i i₁ → {!!}) ∙∙₂ {!!}


module _ {ℓ'} {A : Type ℓ} {B : ℙ A → Type ℓ'} (q : Elimℙ.H1 B) where

 fromH2P : (∀ xs ys zs ws →
        PathP (λ i → B (𝕡loop xs ys zs ws i))
        (Elimℙ.H1.bbase q (xs ++ ys ++ zs ++ ws))
        (Elimℙ.H1.bbase q (((xs ++ zs) ++ ys) ++ ws)))
          → Elimℙ.H2 q
 fromH2P p = w
  where
  open Elimℙ
  w : H2 q
  bloop w = p

  bhexDiag w ls xs ys zs rs i =
         comp (λ j → B (𝕡hexU ls xs ys zs rs j i))
         (λ j → λ { (i = i0) → bbase q _ 
                  ; (i = i1) → bbase q _
                  })
         (p ls xs (ys ++ zs) rs i)
  bcommDiag w xs ys zs ws++xs' ys' zs' ws' i =
               comp (λ j → B (𝕡commA xs ys zs ws++xs' ys' zs' ws' (~ j) i))
         (λ j → λ { (i = i0) → p xs ys zs (ws++xs' ++ ys' ++ zs' ++ ws') (~ j)
                  ; (i = i1) → p (((xs ++ zs) ++ ys) ++ ws++xs') ys' zs' ws' j
                  })
         (bbase q _)
  bcommDiag' w xs ys zs ws++xs' ys' zs' ws' i =
        comp (λ j → B (𝕡commB xs ys zs ws++xs' ys' zs' ws' (~ j) i))
         (λ j → λ { (i = i0) → bbase q _
                  ; (i = i1) → bbase q _
                  })
         (bbase q _)


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

 record Elimℙ2Set {ℓb} (B : ℙ A → ℙ A → Type ℓb) (isSetB : ∀ x y → isSet (B x y)) : Type (ℓ-max ℓ ℓb) where
  field
   r11 : ∀ x y → B (𝕡base x) (𝕡base y)
   r12 : ∀ x → (xs ys zs ws : List A) →
           PathP (λ i → B (𝕡loop xs ys zs ws i) (𝕡base x))
           (r11 (xs ++ ys ++ zs ++ ws) x) (r11 (((xs ++ zs) ++ ys) ++ ws) x)
   r21 : ∀ x → (xs ys zs ws : List A) →
      PathP (λ i → B (𝕡base x) (𝕡loop xs ys zs ws i))
      (r11 x (xs ++ ys ++ zs ++ ws))
      (r11 x (((xs ++ zs) ++ ys) ++ ws))


  r12* : Elimℙ.H2 (Elimℙ.h1 r11)
  r12* = fromH2P _ λ xs ys zs ws i x → r12 x xs ys zs ws i 


  r21* : Elimℙ.H1 (λ v → Elimℙ.H2 (Elimℙ.h1 (Elimℙ.f₂ r12* (λ x → isSetΠ λ _ → isSetB x _) v )))
  Elimℙ.bbase r21* x = fromH2P _ (r21 x)

  f2 : ∀ x y → B x y
  f2 x = Elimℙ.f₂ (Elimℙ.f₁ r21*
      (λ x' → Elimℙ.isOfHLevelH2 {B = B x'}
              (Elimℙ.h1 ((Elimℙ.f₂ r12* (λ x → isSetΠ λ _ → isSetB x _) x' ))) (suc zero) λ x'' → isSetB x' x'') x)
       λ _ → isSetB x _


module _ {A : Type ℓ} where

 hexDiagL : ∀ (ls xs ys zs rs l : List A) →
         ((ls ++ xs ++ ys ++ zs ++ rs) ++ l) ≡
         (ls ++ xs ++ ys ++ zs ++ rs ++ l)
 hexDiagL ls xs ys zs rs l =
      (λ i → ++-assoc ls (++-pentagon-diag xs ys zs rs (~ i)) l i)
       ∙∙ (cong (ls ++_) (++-pentagon-diag _ _ _ _ ))
       ∙∙ cong (ls ++_) (++-assoc _ _ _)


 pop4 : ∀ (xs ys zs rs l : List A) →
         ((xs ++ ys ++ zs ++ rs) ++ l) ≡
         (xs ++ ys ++ zs ++ rs ++ l)
 pop4 xs ys zs rs l =
      cong (_++ l) (sym (++-pentagon-diag _ _ _ _))
       ∙∙ ++-assoc _ _ _ ∙∙ ++-pentagon-diag _ _ _ _ 

 pop4' : ∀ (l xs ys zs ws : List A) →
            (((l ++ xs) ++ zs) ++ ys) ++ ws ≡
                  l ++ ((xs ++ zs) ++ ys) ++ ws
 pop4' l xs ys zs ws = 
      ( (++-pentagon-diag _ _ _ _))
       ∙∙ (++-assoc _ _ _) ∙∙ cong (l ++_) (sym (++-pentagon-diag _ _ _ _ ))



 pop5 = hexDiagL

 pop5' : ∀ (l ls xs ys zs rs : List A) →
            ((((l ++ ls) ++ xs) ++ ys) ++ zs) ++ rs ≡
                  l ++ (((ls ++ xs) ++ ys) ++ zs) ++ rs
 pop5' l ls xs ys zs rs =
    cong (_++ rs) ( (++-assoc _ _ _))
     ∙∙ cong (_++ rs) (++-pentagon-diag _ _ _ _) ∙∙
     λ i → ++-assoc l (++-pentagon-diag ls xs ys zs (~ i)) rs i

 pop7 : ∀ (xs ys zs ws++xs' ys' zs' ws' l : List A) →
          (xs ++ ys ++ zs ++ ws++xs' ++ ys' ++ zs' ++ ws') ++ l ≡
          xs ++ ys ++ zs ++ ws++xs' ++ ys' ++ zs' ++ ws' ++ l
 pop7 xs ys zs ws++xs' ys' zs' ws' l =
   (cong (_++ l) ((cong (xs ++_) (sym (++-pentagon-diag ys zs ws++xs' _) )) ∙ sym (++-assoc xs ((ys ++ zs) ++ ws++xs') _))
          ∙∙ (λ i → ++-pentagon-diag xs (++-assoc ys zs ws++xs' (i0)) (++-assoc ys' zs' ws' (~ i)) l i) ∙∙
           (λ i → (xs ++ ++-pentagon-diag ys zs ws++xs' (++-pentagon-diag ys' zs' ws' l i ) i) ) )

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

 -- hlp1 : ∀ xs ys zs ws l → Square {A = List A}
 --      (λ i →
         
 --         (((λ i₁ → ++-pentagon-diag xs ys zs ws (~ i₁) ++ l) ∙∙
 --           ++-assoc ((xs ++ ys) ++ zs) ws l ∙∙
 --           ++-pentagon-diag xs ys zs (ws ++ l))
 --          i))
 --      (λ i → (++-assoc ((xs ++ ys) ++ zs) ws l i))
 --      (λ i → (++-pentagon-diag xs ys zs ws (~ i) ++ l))
 --       λ i → (++-pentagon-diag xs ys zs (ws ++ l) (~ i))
 -- hlp1 xs ys zs ws l = {!!}

 -- sqHlp1 : {!!}
 -- sqHlp1 = {!!}

 -- biAssoc : (ls xs ys zs rs l : List A) →
 --     {!!} ≡ {!!}
 -- biAssoc ls xs ys zs rs l i =
 --   ++-assoc (++-assoc zs rs l i) xs ys  i
 
 

 hexUL : ∀ (ls xs ys zs rs l : List A) →  Square {A = List A}
      (λ i →
         ((λ i₁ → ++-pentagon-diag ls xs (ys ++ zs) rs (~ i₁) ++ l) ∙∙
          ++-assoc ((ls ++ xs) ++ ys ++ zs) rs l ∙∙
          ++-pentagon-diag ls xs (ys ++ zs) (rs ++ l))
         i)
      (λ i → hexDiagL ls xs ys zs rs l i)
      (λ i → (ls ++ xs ++ ++-assoc ys zs rs i) ++ l)
      (λ i → ls ++ xs ++ ++-assoc ys zs (rs ++ l) i)
 hexUL ls xs ys zs rs l =
   let p : _
       p = (Listₐ-sqHlp
                (fL (ls B.∷ xs B.∷ ys B.∷ zs B.∷ rs B.∷ l B.∷ B.[]))
                {a₀₋ = (λ i →
                ((λ i₁ → ++-pentagon-diag [ 0 ] [ 1 ] ([ 2 ] ++ [ 3 ]) [ 4 ] (~ i₁) ++ [ 5 ]) ∙∙
                 ++-assoc (([ 0 ] ++ [ 1 ]) ++ [ 2 ] ++ [ 3 ]) [ 4 ] [ 5 ] ∙∙
                 ++-pentagon-diag [ 0 ] [ 1 ] ([ 2 ] ++ [ 3 ]) ([ 4 ] ++ [ 5 ]))
                i)}
                {a₁₋ = hexDiagL [ 0 ] [ 1 ] [ 2 ] [ 3 ] [ 4 ] [ 5 ]}
                {a₋₀ = λ i → ([ 0 ] ++ [ 1 ] ++ ++-assoc [ 2 ] [ 3 ] [ 4 ] i) ++ [ 5 ]}
                {a₋₁ = λ i → [ 0 ] ++ [ 1 ] ++ ++-assoc [ 2 ] [ 3 ] ([ 4 ] ++ [ 5 ]) i}
                refl) 
   in  sym (cong-∙∙ _ _ _ _) ◁ p ▷ cong-∙∙ _ _ _ _

 hexDlem1 : ∀ (ls xs ys zs rs l : List A) →  Square {A = List A}
      (λ k → (ls ++ xs ++ ys ++ ++-assoc zs rs l (~ k)))
      (λ k → (hexDiagL ls xs ys zs rs l (~ k)))
      (λ k' → (ls ++ xs ++ ys ++ zs ++ rs ++ l))
      (λ k' → (((λ i₁ →
              ++-pentagon-diag ls xs ys (zs ++ rs) (~ i₁) ++ l)
           ∙∙ ++-assoc ((ls ++ xs) ++ ys) (zs ++ rs) l ∙∙
           ++-pentagon-diag ls xs ys ((zs ++ rs) ++ l))
          (~ k')))
 hexDlem1 ls xs ys zs rs l =
      whiskSq.sq' _
       ((Listₐ-sqHlp
                (fL (ls B.∷ xs B.∷ ys B.∷ zs B.∷ rs B.∷ l B.∷ B.[]))
                {a₀₋ = (λ k → ([ 0 ] ++ [ 1 ] ++ [ 2 ]  ++ ++-assoc [ 3 ] [ 4 ] [ 5 ] (~ k)))}
                {a₁₋ =  (λ k → (hexDiagL [ 0 ] [ 1 ] [ 2 ] [ 3 ] [ 4 ] [ 5 ] (~ k)))}
                {a₋₀ = refl}
                λ i i₁ → 0 B.∷ 1 B.∷ 2 B.∷ 3 B.∷ 4 B.∷ 5 B.∷ B.[]) )
       (λ j i → ls ++ xs ++ ys ++ ++-assoc zs rs l (~ j))
       (flipSquare (cong-∙∙ _ _ _ _))
       (λ i i₁ → ls ++ xs ++ ys ++ zs ++ rs ++ l)
       (flipSquare (cong-∙∙ _
          (λ i →
              ++-pentagon-diag [ 0 ] [ 1 ] [ 2 ] (([ 3 ] ++ [ 4 ]) ++ [ 5 ])
              (~ i))
              (λ i →
                  ++-assoc (([ 0 ] ++ [ 1 ]) ++ [ 2 ]) ([ 3 ] ++ [ 4 ]) [ 5 ] (~ i))
          (λ i → ++-pentagon-diag [ 0 ] [ 1 ] [ 2 ] ([ 3 ] ++ [ 4 ]) (~ (~ i)) ++ [ 5 ])))


 hexDlem2 : ∀ (ls xs ys zs rs l : List A) →  Square {A = List A}

      (λ k → hcomp
          (doubleComp-faces (λ _ → ((ls ++ ys) ++ xs) ++ zs ++ rs ++ l)
           (λ i₁ → ++-assoc ((ls ++ ys) ++ xs) (zs ++ rs) l (~ i₁)) k)
          (((ls ++ ys) ++ xs) ++ ++-assoc zs rs l (~ k)))
      (λ k → ((λ i₁ →
              ++-pentagon-diag (ls ++ ys) xs zs rs (~ i₁) ++ l)
           ∙∙ ++-assoc (((ls ++ ys) ++ xs) ++ zs) rs l ∙∙
           ++-pentagon-diag (ls ++ ys) xs zs (rs ++ l))
          (~ k))
           (++-assoc (ls ++ ys) xs (zs ++ rs ++ l))
      (λ j → ++-assoc (ls ++ ys) xs (zs ++ rs) j ++ l)
 hexDlem2 ls xs ys zs rs l =
     (sym (cong-∙∙ _ _ _ _)) ◁
      (Listₐ-sqHlp
                (fL (ls B.∷ ys B.∷ xs B.∷ zs B.∷ rs B.∷ l B.∷ B.[]))
                {a₀₋ = (λ i → (([ 0 ] ++ [ 1 ]) ++ [ 2 ]) ++ ++-assoc [ 3 ] [ 4 ] [ 5 ] (~ i)) ∙
                       sym (++-assoc (([ 0 ] ++ [ 1 ]) ++ [ 2 ]) ([ 3 ] ++ [ 4 ] ) [ 5 ])}
                {a₁₋ =  sym ((λ i → ++-pentagon-diag ([ 0 ] ++ [ 1 ]) [ 2 ] [ 3 ] [ 4 ] (~ i) ++ [ 5 ])
                      ∙∙ ++-assoc ((([ 0 ] ++ [ 1 ]) ++ [ 2 ]) ++ [ 3 ]) [ 4 ] [ 5 ]
                           ∙∙ ++-pentagon-diag ([ 0 ] ++ [ 1 ]) [ 2 ] [ 3 ] ([ 4 ] ++ [ 5 ]))}
                {a₋₀ = ++-assoc ([ 0 ] ++ [ 1 ]) [ 2 ] ([ 3 ] ++ [ 4 ] ++ [ 5 ])}
                {a₋₁ = λ i → ++-assoc ([ 0 ] ++ [ 1 ]) [ 2 ] ([ 3 ] ++ [ 4 ]) i  ++ [ 5 ]}
                λ i i₁ → 0 B.∷ 1 B.∷ 2 B.∷ 3 B.∷ 4 B.∷ 5 B.∷ B.[])
      ▷  (cong-∙∙ _ _ _ _)
 

 R12 : Recℙ.H2 {ℓ} {A} {ℓ} {List {ℓ} A → ℙ {ℓ} A}
         (Recℙ.h1 ((λ x y → 𝕡base (x ++ y))))
 Recℙ.bloop R12 xs ys zs ws =
   funExt λ l →
       cong 𝕡base (pop4 xs ys zs ws l) ∙∙
         𝕡loop xs ys zs (ws ++ l)
        ∙∙ cong 𝕡base (sym (++-assoc _ _ _))
 Recℙ.bhexDiag R12 ls xs ys zs rs =
   funExt λ l →
          (cong 𝕡base (hexDiagL ls xs ys zs rs l))
       ∙∙ 𝕡hexDiag ls xs ys zs (rs ++ l) ∙∙
       cong 𝕡base (sym (++-assoc _ _ _))
 Recℙ.bcommDiag R12 xs ys zs ws++xs' ys' zs' ws' = funExt λ l →
    cong 𝕡base (pop7 xs ys zs ws++xs' ys' zs' ws' l)
      ∙∙ 𝕡commDiag xs ys zs ws++xs' ys' zs' (ws' ++ l) ∙∙
      cong 𝕡base (sym (++-assoc _ _ _))
 Recℙ.bcommDiag' R12 xs ys zs ws++xs' ys' zs' ws' = funExt λ l →
     ( cong 𝕡base
        (pop7 xs ys zs ws++xs' ys' zs' ws' l)
        ∙∙ 𝕡commDiag' xs ys zs ws++xs' ys' zs' (ws' ++ l)
            ∙∙ cong 𝕡base (sym (++-assoc _ _ _)) )
 
 R13 : Recℙ.H3 R12
 Recℙ.binvol R13 xs ys zs ws =
      funExtSq _ _ _ _ λ l →
     congSq 𝕡base (symP (doubleCompPath-filler _ _ _)) 
      ∙∙₂ 𝕡invol _ _ _ _ ∙∙₂
      congSq 𝕡base (doubleCompPath-filler _ _ _)
 Recℙ.bhexU R13 ls xs ys zs rs =
          funExtSq _ _ _ _ λ l →
       (congSq 𝕡base (hexUL ls xs ys zs rs l))
     ∙∙₂ 𝕡hexU _ _ _ _ _ ∙∙₂
     congSq 𝕡base λ i i₁ → ++-assoc (++-assoc ls ys zs (~ i) ++ xs) rs l (~ i₁)
 Recℙ.bhexD R13 ls xs ys zs rs i j l =
              hcomp
               (λ k → λ {
                   (j = i0) → hcomp
                               (λ k' → λ {
                                     (k = i0) → 𝕡loop ls xs ys (zs ++ rs ++ l) i
                                    ;(i = i0) → 𝕡base (hexDlem1 ls xs ys zs rs l k' k) 
                                    ;(i = i1) → 𝕡base (compPath-filler
                                           (λ i₁ → ((ls ++ ys) ++ xs) ++ ++-assoc zs rs l (~ i₁))
                                           (λ i₁ → ++-assoc ((ls ++ ys) ++ xs) (zs ++ rs) l (~ i₁)) k' k)
                                      })
                               (𝕡loop ls xs ys (++-assoc zs rs l (~ k)) i)
                  ;(j = i1)(i = i0) → 𝕡base (++-assoc (((ls ++ ys) ++ zs) ++ xs) rs l (~ k))
                  ;(i = i1) → 𝕡base (hexDlem2 ls xs ys zs rs l j k)  
                  })
               (𝕡hexD ls xs ys zs (rs ++ l) i j)
 Recℙ.bcommA R13 xs ys zs ws++xs' ys' zs' ws' i j l =
    hcomp
      (λ k →
         λ { (j = i0) → hcomp (λ k' →
                         λ { (k = i0) → 𝕡loop xs ys zs (ws++xs' ++ ys' ++ zs' ++ ws' ++ l) i
                           ; (i = i0) → 𝕡base {!!}
                           ; (i = i1) → 𝕡base {!!}
                          })
                      (𝕡loop xs ys zs (pop4 ws++xs' ys' zs' ws' l (~ k)) i)
            ; (j = i1)(i = i0) → 𝕡base
                  (++-assoc (((((xs ++ zs) ++ ys) ++ ws++xs') ++ zs') ++ ys') ws' l
                   (~ k)) 
            ; (i = i1) → 𝕡base (doubleCompPath-filler
                 (sym (++-assoc ((xs ++ zs) ++ ys) ws++xs' (ys' ++ zs' ++ ws' ++ l)))
                 (sym (pop4 _ _ _ _ _))
                 (λ j →  (++-assoc ((xs ++ zs) ++ ys) ws++xs' (ys' ++ zs' ++ ws')) j ++ l) (~ j) k
                 )
            })
      (𝕡commA xs ys zs ws++xs' ys' zs' (ws' ++ l) i j)
 Recℙ.bcommB R13 xs ys zs ws++xs' ys' zs' ws' =
    funExtSq _ _ _ _ λ l →
      symP (whiskSqComp.sq' _ 
         (symP (𝕡commB xs ys zs ws++xs' ys' zs' (ws' ++ l)))
          {p₀₀ = cong 𝕡base (sym (pop5 _ _ _ _ _ _))}
          {p₀₁ = cong 𝕡base (sym (pop4 _ _ _ _ _))}
          (congSq' {a₋₁ = λ j → (++-assoc ((xs ++ ys) ++ zs) ws++xs' (ys' ++ zs' ++ ws') (~ j) ++
            l)} 𝕡base {!!})
          (congSq 𝕡base {!!})
          (congSq 𝕡base {!!}))
 Recℙ.bcomm R13 xs ys zs ws++xs' ys' zs' ws' =
    λ i j l →
       hcomp (λ k → λ {
           (i = i0)(j = i0) → _
          ;(i = i0)(j = i1) → _
          ;(i = i1)(j = i0) → _
          ;(i = i1)(j = i1) → _
                }) ( 𝕡comm xs ys zs ws++xs' ys' zs' (ws' ++ l) i j)


 R21 : (z : List A) → Recℙ.H2 (Recℙ.h1 (λ y → 𝕡base (z ++ y)))
 Recℙ.bloop (R21 l) xs ys zs ws =
    cong 𝕡base (sym (++-assoc _ _ _))
    ∙∙ 𝕡loop (l ++ xs) ys zs ws ∙∙
    (cong 𝕡base (pop4' _ _ _ _ _))
 Recℙ.bhexDiag (R21 l) ls xs ys zs rs =
      cong 𝕡base (sym (++-assoc _ _ _))
     ∙∙ 𝕡hexDiag (l ++ ls) xs ys zs rs ∙∙
     cong 𝕡base (pop5' _ _ _ _ _ _)
 Recℙ.bcommDiag (R21 l) xs ys zs ws++xs' ys' zs' ws' = {!!}
 Recℙ.bcommDiag' (R21 l) xs ys zs ws++xs' ys' zs' ws' = {!!}

 rℙ⊕ : Recℙ2' A (ℙ A) 𝕡trunc
 r11 rℙ⊕ x y = 𝕡base (x ++ y)
 r12 rℙ⊕ = R12
 r13 rℙ⊕ = R13
 truncHlp1 rℙ⊕ = isGroupoidΠ λ _ → 𝕡trunc 
 r21 rℙ⊕ = R21
 r22 rℙ⊕ = {!!}
 trunncHlp2 rℙ⊕ _ = Recℙ.isOfHLevelH2 _ 2 𝕡trunc
 r31 rℙ⊕ = {!!}

 _ℙ⊕_ : ℙ A → ℙ A → ℙ A
 _ℙ⊕_ = Recℙ2'.f2 rℙ⊕ 

 ℙ⊕-symR : Elimℙ2Set A (λ z z₁ → (z ℙ⊕ z₁) ≡ (z₁ ℙ⊕ z)) λ _ _ → 𝕡trunc _ _
 Elimℙ2Set.r11 ℙ⊕-symR x y =
   cong 𝕡base (λ i → ++-unit-l (x ++ ++-unit-r y (~ i)) (~ i) )
     ∙∙ 𝕡loop [] x y [] ∙∙
     cong 𝕡base λ i → ++-unit-r ((++-unit-l y i) ++ x) i
 Elimℙ2Set.r12 ℙ⊕-symR x xs ys zs ws = 
   {!!} ∙∙₂ {!!} ∙∙₂ {!!}
 
 Elimℙ2Set.r21 ℙ⊕-symR x xs ys zs ws = {!!}

 ℙ⊕-sym : ∀ x y → x ℙ⊕ y ≡ y ℙ⊕ x
 ℙ⊕-sym = Elimℙ2Set.f2 ℙ⊕-symR 

--  rℙ⊕ : Recℙ2' A (ℙ A) 𝕡trunc
--  r11 rℙ⊕ x y = 𝕡base (x ++ y)
--  Recℙ.bloop (r12 rℙ⊕) xs ys zs ws =
--    funExt λ l →
--        (cong 𝕡base ( (cong (_++ l) (sym (++-pentagon-diag _ _ _ _)))
--         ∙∙   (++-assoc _ _ _) ∙∙  (++-pentagon-diag _ _ _ _))) ∙∙
--          𝕡loop xs ys zs (ws ++ l)
--         ∙∙ cong 𝕡base (sym (++-assoc _ _ _))
--  Recℙ.bhexDiag (r12 rℙ⊕) ls xs ys zs rs =
--     funExt λ l →
--           (cong 𝕡base (hexDiagL ls xs ys zs rs l))
--        ∙∙ 𝕡hexDiag ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))
--  Recℙ.bcommDiag (r12 rℙ⊕) xs ys zs ws++xs' ys' zs' ws' = {!!}
--  Recℙ.bcommDiag' (r12 rℙ⊕) xs ys zs ws++xs' ys' zs' ws' = {!!}

--  Recℙ.binvol (r13 rℙ⊕) xs ys zs ws =
--    funExtSq _ _ _ _ λ l →
--      congSq 𝕡base (symP (doubleCompPath-filler _ _ _)) 
--       ∙∙₂ 𝕡invol _ _ _ _ ∙∙₂
--       congSq 𝕡base (doubleCompPath-filler _ _ _)
--  Recℙ.bhexU (r13 rℙ⊕) ls xs ys zs rs = funExtSq _ _ _ _ λ l → 
--     (congSq 𝕡base (hexUL ls xs ys zs rs l))
--      ∙∙₂ 𝕡hexU _ _ _ _ _ ∙∙₂
--      congSq 𝕡base λ i i₁ → ++-assoc (++-assoc ls ys zs (~ i) ++ xs) rs l (~ i₁)
--  Recℙ.bhexD (r13 rℙ⊕) ls xs ys zs rs i j l = 
--     hcomp
--       (λ k → λ {
--           (j = i0) → hcomp
--                       (λ k' → λ {
--                             (k = i0) → 𝕡loop ls xs ys (zs ++ rs ++ l) i
--                            ;(i = i0) → 𝕡base (hexDlem1 ls xs ys zs rs l k' k) 
--                            ;(i = i1) → 𝕡base (compPath-filler
--                                   (λ i₁ → ((ls ++ ys) ++ xs) ++ ++-assoc zs rs l (~ i₁))
--                                   (λ i₁ → ++-assoc ((ls ++ ys) ++ xs) (zs ++ rs) l (~ i₁)) k' k)
--                              })
--                       (𝕡loop ls xs ys (++-assoc zs rs l (~ k)) i)
--          ;(j = i1)(i = i0) → 𝕡base (++-assoc (((ls ++ ys) ++ zs) ++ xs) rs l (~ k))
--          ;(i = i1) → 𝕡base (hexDlem2 ls xs ys zs rs l j k)  
--          })
--       (𝕡hexD ls xs ys zs (rs ++ l) i j)

--  Recℙ.bcommA (r13 rℙ⊕) xs ys zs ws++xs' ys' zs' ws' = {!!}
--  Recℙ.bcommB (r13 rℙ⊕) xs ys zs ws++xs' ys' zs' ws' = {!!}
--  Recℙ.bcomm (r13 rℙ⊕) xs ys zs ws++xs' ys' zs' ws' = {!!}

--  truncHlp1 rℙ⊕ = isGroupoidΠ λ _ → 𝕡trunc 
--  Recℙ.bloop (r21 rℙ⊕ l) xs ys zs ws =
--     cong 𝕡base (sym (++-assoc _ _ _))
--     ∙∙ 𝕡loop (l ++ xs) ys zs ws ∙∙
--     ( (cong 𝕡base (++-pentagon-diag _ _ _ _)
--         ∙∙  cong 𝕡base (++-assoc _ _ _) ∙∙
--         cong 𝕡base (cong (l ++_) (sym (++-pentagon-diag _ _ _ _)))))
--  Recℙ.bhexDiag (r21 rℙ⊕ l) ls xs ys zs rs =
--    cong 𝕡base (sym (++-assoc _ _ _))
--    ∙∙ 𝕡hexDiag (l ++ ls) xs ys zs rs ∙∙
--    ((λ i → 𝕡base ((++-assoc (l ++ ls) ys zs i ++ xs) ++ rs)) ∙∙
--     (λ i → 𝕡base (++-pentagon-diag (l ++ ls) (ys ++ zs) xs rs i)) ∙∙
--     (λ i → 𝕡base (++-assoc l ls ((ys ++ zs) ++ xs ++ rs) i)) ∙∙
--     (λ i → 𝕡base (l ++ ++-pentagon-diag ls (ys ++ zs) xs rs (~ i))) ∙∙
--     λ i → 𝕡base (l ++ (++-assoc ls ys zs (~ i) ++ xs) ++ rs))

--  Recℙ.bcommDiag (r21 rℙ⊕ z) xs ys zs ws++xs' ys' zs' ws' = {!!}
--  Recℙ.bcommDiag' (r21 rℙ⊕ z) xs ys zs ws++xs' ys' zs' ws' = {!!}

--  r22 rℙ⊕ = fromH2P _ w
--   where
--   w : (xs ys zs ws : List A) →
--         PathP
--         (λ i →
--            Recℙ.H2
--            (Recℙ.h1
--             (Recℙ.f₃ (r13 rℙ⊕) (truncHlp1 rℙ⊕) (𝕡loop xs ys zs ws i))))
--         (r21 rℙ⊕ (xs ++ ys ++ zs ++ ws))
--         (r21 rℙ⊕ (((xs ++ zs) ++ ys) ++ ws))
--   Recℙ.bloop (w xs ys zs ws i) xs₁ ys₁ zs₁ ws₁ j = {!!}
--   Recℙ.bhexDiag (w xs ys zs ws i) ls xs₁ ys₁ zs₁ rs i₁ = {!!}
--   Recℙ.bcommDiag (w xs ys zs ws i) xs₁ ys₁ zs₁ ws++xs' ys' zs' ws' = {!!}
--   Recℙ.bcommDiag' (w xs ys zs ws i) xs₁ ys₁ zs₁ ws++xs' ys' zs' ws' = {!!}
--  trunncHlp2 rℙ⊕ x = Recℙ.isOfHLevelH2 _ 2 𝕡trunc
--  Recℙ.binvol (Elimℙ.bbase (r31 rℙ⊕) l) xs ys zs ws =
--    doubleCompPath-filler _ _ _
--    ∙∙₂ 𝕡invol (l ++ xs) ys zs ws ∙∙₂
--    symP (doubleCompPath-filler _ _ _)
--  Recℙ.bhexU (Elimℙ.bbase (r31 rℙ⊕) l) ls xs ys zs rs =
--    (congSq 𝕡base λ i i₁ → ++-assoc l ls (xs ++ ++-assoc ys zs rs i) (~ i₁))
--     ∙∙₂ 𝕡hexU _ _ _ _ _ ∙∙₂
--     doubleCompPath-filler _ _ _
--  Recℙ.bhexD (Elimℙ.bbase (r31 rℙ⊕) a) ls xs ys zs rs i i₁ = {!!}

--  Recℙ.bcommA (Elimℙ.bbase (r31 rℙ⊕) a) xs ys zs ws++xs' ys' zs' ws' = {!!}
--  Recℙ.bcommB (Elimℙ.bbase (r31 rℙ⊕) a) xs ys zs ws++xs' ys' zs' ws' = {!!}
--  Recℙ.bcomm (Elimℙ.bbase (r31 rℙ⊕) a) xs ys zs ws++xs' ys' zs' ws' = {!!}

--  _ℙ⊕_ : ℙ A → ℙ A → ℙ A
--  _ℙ⊕_ = Recℙ2'.f2 rℙ⊕ 

-- --  r11 rℙ⊕ x y = 𝕡base (x ++ y)
-- --  Recℙ.bloopL (r12 rℙ⊕) xs ys zs ws =
-- --    funExt λ l → cong 𝕡base (++-assoc _ _ _)
-- --        ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
-- --      cong 𝕡base (sym (++-assoc _ _ _))
-- --  Recℙ.bloopR (r12 rℙ⊕) xs ys zs ws =
-- --     funExt λ l → cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
-- --       ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
-- --     cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))
-- --  Recℙ.bhexDiagAB (r12 rℙ⊕) ls xs ys zs rs =
-- --     funExt λ l → cong 𝕡base (++-assoc _ _ _ ∙ cong (ls ++_) (++-assoc _ _ _))
-- --          ∙∙ 𝕡hexDiagAB ls xs ys zs (rs ++ l) ∙∙
-- --        cong 𝕡base (sym (++-assoc _ _ _))
-- --  Recℙ.bhexDiagBC (r12 rℙ⊕) ls xs ys zs rs =
-- --     funExt λ l → cong 𝕡base (cong (λ x → ((ls ++ x) ++ l))
-- --                      (sym (++-assoc _ _ _))
-- --                     ∙∙ ++-assoc _ _ _ ∙∙
-- --                     cong (ls ++_) (++-pentagon-diag _ _ _ _))
-- --          ∙∙ 𝕡hexDiagBC ls xs ys zs (rs ++ l) ∙∙
-- --        cong 𝕡base (sym (++-assoc _ _ _))
-- --  Recℙ.bhexDiagCD (r12 rℙ⊕) ls xs ys zs rs =
-- --     funExt λ l → cong 𝕡base (++-assoc _ _ _ ∙ cong ((ls ++ xs ++ ys) ++_) (++-assoc _ _ _) )
-- --          ∙∙ 𝕡hexDiagCD ls xs ys zs (rs ++ l) ∙∙
-- --        cong 𝕡base (sym (++-assoc _ _ _))
-- --  Recℙ.binvolL (r13 rℙ⊕) xs ys zs ws = funExtSq _ _ _ _
-- --     λ l → refl ∙∙₂ 𝕡involL xs ys zs (ws ++ l) ∙∙₂ refl

-- --  Recℙ.bloopAssoc (r13 rℙ⊕) xs ys zs ws = funExtSq _ _ _ _
-- --     λ l → {!congSq 𝕡base (hlpSq l xs (ys ++ zs) ws)
-- --        ∙∙₂ 𝕡loopAssoc xs ys zs (ws ++ l) ∙∙₂
-- --      congSq 𝕡base (congP (λ _ → sym) (hlpSq l xs (zs ++ ys) ws))
-- -- !}
-- --  Recℙ.bhexA (r13 rℙ⊕) = {!!}
-- --  Recℙ.bhexB (r13 rℙ⊕) = {!!}
-- --  Recℙ.bhexC (r13 rℙ⊕) = {!!}
-- --  Recℙ.bhexD (r13 rℙ⊕) = {!!}
-- --  truncHlp1 rℙ⊕ = {!!}
-- --  Recℙ.bloopL (r21 rℙ⊕ l) xs ys zs ws = 
-- --          (cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
-- --               ∙' cong (_++ ws) (sym (++-assoc _ _ _))))
              
-- --         ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
-- --          ( sym (cong 𝕡base (sym (++-assoc l (xs ++ (zs ++ ys)) ws)
-- --               ∙' cong (_++ ws) (sym (++-assoc _ _ _)))))
-- --  Recℙ.bloopR (r21 rℙ⊕ l) xs ys zs ws =
-- --         cong 𝕡base (sym (++-assoc _ _ _))
-- --          ∙∙ 𝕡loopR (l ++ xs) ys zs ws ∙∙
-- --        cong 𝕡base (++-assoc _ _ _)
-- --  Recℙ.bhexDiagAB (r21 rℙ⊕ l) ls xs ys zs rs =
-- --              (cong 𝕡base (sym (++-assoc _ _ _))
-- --          ∙∙ 𝕡hexDiagAB (l ++ ls) xs ys zs rs ∙∙
-- --        cong 𝕡base (cong (_++ rs) (++-assoc _ _ _) ∙ ++-assoc _ _  _))
-- --  Recℙ.bhexDiagBC (r21 rℙ⊕ l) ls xs ys zs rs =
-- --          cong 𝕡base (sym (++-assoc _ _ _))
-- --          ∙∙ 𝕡hexDiagBC (l ++ ls) xs ys zs rs ∙∙
-- --        cong 𝕡base (cong (_++ rs) (++-pentagon-diag _ _ _ _)
-- --          ∙∙ (++-assoc _ _ _) ∙∙
-- --          cong (λ x → (l ++ x ++ rs)) (sym (++-assoc _ _ _)))
-- --  Recℙ.bhexDiagCD (r21 rℙ⊕ l) ls xs ys zs rs =
-- --         cong 𝕡base ((sym (++-assoc _ _ _) ∙'
-- --                   λ i → (++-assoc l ls (xs ++ ys) (~ i)) ++ zs ++ rs))
-- --          ∙∙ 𝕡hexDiagCD (l ++ ls) xs ys zs rs ∙∙
-- --        cong 𝕡base (cong ((_++ rs) ∘' (_++ (xs ++ zs))) (++-assoc _ _ _)
-- --             ∙∙ cong (_++ rs) (++-assoc _ _ _)
-- --             ∙∙ ++-assoc _ _ _)
-- --  r22 rℙ⊕ = fromH2P (Elimℙ.h1 (r21 rℙ⊕)) w
-- --   where
-- --   w : (xs ys zs ws : List A) →
-- --         PathP
-- --         (λ i →
-- --            Recℙ.H2
-- --            (Recℙ.h1
-- --             (Recℙ.f₃ (r13 rℙ⊕) (truncHlp1 rℙ⊕) (𝕡loopL xs ys zs ws i))))
-- --         (r21 rℙ⊕ ((xs ++ ys ++ zs) ++ ws))
-- --         (r21 rℙ⊕ ((xs ++ zs ++ ys) ++ ws))
-- --   Recℙ.bloopL (w xs ys zs ws i) = {!!}
-- --   Recℙ.bloopR (w xs ys zs ws i) = {!!}
-- --   Recℙ.bhexDiagAB (w xs ys zs ws i) = {!!}
-- --   Recℙ.bhexDiagBC (w xs ys zs ws i) = {!!}
-- --   Recℙ.bhexDiagCD (w xs ys zs ws i) = {!!}
 
-- --  trunncHlp2 rℙ⊕ = {!!}
-- --  Recℙ.binvolL (Elimℙ.bbase (r31 rℙ⊕) l) xs ys zs ws =
-- --     refl ∙∙₂ 𝕡involL (l ++ xs) ys zs ws ∙∙₂ refl

-- --  Recℙ.bloopAssoc (Elimℙ.bbase (r31 rℙ⊕) l) xs ys zs ws = 
-- --    congSq 𝕡base (hlpSq l xs (ys ++ zs) ws)
-- --        ∙∙₂ 𝕡loopAssoc (l ++ xs) ys zs ws ∙∙₂
-- --      congSq 𝕡base (congP (λ _ → sym) (hlpSq l xs (zs ++ ys) ws))
-- --  Recℙ.bhexA (Elimℙ.bbase (r31 rℙ⊕) l) ls xs ys zs rs = 
-- --    congSq 𝕡base (λ i → hlpSq l ls (++-assoc xs ys zs (~ i)) rs i)
-- --        ∙∙₂ 𝕡hexA (l ++ ls) xs ys zs rs ∙∙₂
-- --      congSq 𝕡base
-- --        λ i j →
-- --           ((λ j → (++-assoc l ls (++-assoc ys zs xs i) j) ++ rs) ∙
-- --               ++-assoc l (ls ++ ++-assoc ys zs xs i) rs) j
   
-- --  Recℙ.bhexB (Elimℙ.bbase (r31 rℙ⊕) l) ls xs ys zs rs =
-- --       congSq 𝕡base
-- --        (λ i → sym (++-assoc l ls (++-assoc (xs ++ ys) zs rs i)))
-- --        ∙∙₂ 𝕡hexB (l ++ ls) xs ys zs rs ∙∙₂
-- --      congSq 𝕡base {!!}

-- --  Recℙ.bhexC (Elimℙ.bbase (r31 rℙ⊕) l) ls xs ys zs rs =
-- --    congSq 𝕡base (symP (hlpSq  l ls (xs ++ ys) (zs ++ rs)))
-- --      ∙∙₂  𝕡hexC (l ++ ls) xs ys zs rs  ∙∙₂
-- --        {!!}
-- --  Recℙ.bhexD (Elimℙ.bbase (r31 rℙ⊕) l) ls xs ys zs rs = {!!} 
-- --     -- congSq 𝕡base {!!}
-- --     --    ∙∙₂ 𝕡hexD (l ++ ls) xs ys zs rs ∙∙₂
-- --     --  congSq  {!!}




-- --  -- Recℙ2'.r21 rℙ⊕ = Elimℙ.h1 w 
-- --  --  where
-- --  --  w : (a : List A) →
-- --  --    Recℙ.H2 (Recℙ.f₃ (_) (_) (𝕡base a))
-- --  --  Recℙ.bloopL (w l) xs ys zs ws =
    
-- --  --      (cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
-- --  --              ∙' cong (_++ ws) (sym (++-assoc _ _ _))))
              
-- --  --        ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
-- --  --         ( sym (cong 𝕡base (sym (++-assoc l (xs ++ (zs ++ ys)) ws)
-- --  --              ∙' cong (_++ ws) (sym (++-assoc _ _ _)))))
-- --  --  Recℙ.bloopR (w l) xs ys zs ws =
-- --  --    cong 𝕡base (sym (++-assoc _ _ _))
-- --  --         ∙∙ 𝕡loopR (l ++ xs) ys zs ws ∙∙
-- --  --       cong 𝕡base (++-assoc _ _ _)




-- --  --  Recℙ.bhexDiagAB (w l) ls xs ys zs rs =
-- --  --          (cong 𝕡base (sym (++-assoc _ _ _))
-- --  --         ∙∙ 𝕡hexDiagAB (l ++ ls) xs ys zs rs ∙∙
-- --  --       cong 𝕡base (cong (_++ rs) (++-assoc _ _ _) ∙ ++-assoc _ _  _))
-- --  --  Recℙ.bhexDiagBC (w l) ls xs ys zs rs =
-- --  --      cong 𝕡base (sym (++-assoc _ _ _))
-- --  --         ∙∙ 𝕡hexDiagBC (l ++ ls) xs ys zs rs ∙∙
-- --  --       cong 𝕡base (cong (_++ rs) (++-pentagon-diag _ _ _ _)
-- --  --         ∙∙ (++-assoc _ _ _) ∙∙
-- --  --         cong (λ x → (l ++ x ++ rs)) (sym (++-assoc _ _ _)))
-- --  --  Recℙ.bhexDiagCD (w l) ls xs ys zs rs =
-- --  --      cong 𝕡base ((sym (++-assoc _ _ _) ∙'
-- --  --                  λ i → (++-assoc l ls (xs ++ ys) (~ i)) ++ zs ++ rs))
-- --  --         ∙∙ 𝕡hexDiagCD (l ++ ls) xs ys zs rs ∙∙
-- --  --       cong 𝕡base (cong ((_++ rs) ∘' (_++ (xs ++ zs))) (++-assoc _ _ _)
-- --  --            ∙∙ cong (_++ rs) (++-assoc _ _ _)
-- --  --            ∙∙ ++-assoc _ _ _)

-- -- --  Recℙ2'.r11 rℙ⊕ = w
-- -- --   where
-- -- --   w : Recℙ.H1 (Recℙ.H1 (ℙ A))
-- -- --   Recℙ.bbase (Recℙ.bbase w x) y = 𝕡base (x ++ y)
-- -- --  Recℙ2'.r12 rℙ⊕ = w
-- -- --   where
-- -- --   w : Recℙ.H2 (Recℙ2'.r11 rℙ⊕)
-- -- --   Recℙ.bbase (Recℙ.bloopL w xs ys zs ws i) l =
-- -- --     (cong 𝕡base (++-assoc _ _ _)
-- -- --        ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
-- -- --      cong 𝕡base (sym (++-assoc _ _ _))) i
-- -- --   Recℙ.bbase (Recℙ.bloopR w xs ys zs ws i) l =
-- -- --     (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
-- -- --       ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
-- -- --     cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))) i
-- -- --   Recℙ.bbase (Recℙ.bhexDiagAB w ls xs ys zs rs i) l = 
-- -- --     (cong 𝕡base (++-assoc _ _ _ ∙ cong (ls ++_) (++-assoc _ _ _))
-- -- --          ∙∙ 𝕡hexDiagAB ls xs ys zs (rs ++ l) ∙∙
-- -- --        cong 𝕡base (sym (++-assoc _ _ _))) i
-- -- --   Recℙ.bbase (Recℙ.bhexDiagBC w ls xs ys zs rs i) l =
-- -- --     (cong 𝕡base (cong (λ x → ((ls ++ x) ++ l))
-- -- --                      (sym (++-assoc _ _ _))
-- -- --                     ∙∙ ++-assoc _ _ _ ∙∙
-- -- --                     cong (ls ++_) (++-pentagon-diag _ _ _ _))
-- -- --          ∙∙ 𝕡hexDiagBC ls xs ys zs (rs ++ l) ∙∙
-- -- --        cong 𝕡base (sym (++-assoc _ _ _))) i
-- -- --   Recℙ.bbase (Recℙ.bhexDiagCD w ls xs ys zs rs i) l =
-- -- --     (cong 𝕡base (++-assoc _ _ _ ∙ cong ((ls ++ xs ++ ys) ++_) (++-assoc _ _ _) )
-- -- --          ∙∙ 𝕡hexDiagCD ls xs ys zs (rs ++ l) ∙∙
-- -- --        cong 𝕡base (sym (++-assoc _ _ _))) i


-- -- --  Recℙ.bbase (Recℙ.binvolL (Recℙ2'.r13 rℙ⊕) xs ys zs ws j i) l =
-- -- --    (cong 𝕡base (++-assoc _ _ _)
-- -- --        ∙∙ 𝕡involL xs ys zs (ws ++ l) j ∙∙
-- -- --      cong 𝕡base (sym (++-assoc _ _ _))) i
-- -- --  Recℙ.bbase (Recℙ.bloopAssoc (Recℙ2'.r13 rℙ⊕) xs ys zs ws i i₁) x = {!!}
-- -- --  Recℙ.bhexA (Recℙ2'.r13 rℙ⊕) = {!!}
-- -- --  Recℙ.bhexB (Recℙ2'.r13 rℙ⊕) = {!!}
-- -- --  Recℙ.bhexC (Recℙ2'.r13 rℙ⊕) = {!!}
-- -- --  Recℙ.bhexD (Recℙ2'.r13 rℙ⊕) = {!!}



   



-- -- -- module _ (A : Type ℓ) where

-- -- --  record Recℙ2' {ℓb} (B : Type ℓb) (isGroupoidB : isGroupoid B) : Type (ℓ-max ℓ ℓb) where
-- -- --   no-eta-equality
-- -- --   constructor recℙ2
  
-- -- --   field
-- -- --    r11 : Recℙ.H1 {A = A} (Recℙ.H1 {A = A} B)
-- -- --    r12 : Recℙ.H2 r11
-- -- --    r13 : Recℙ.H3 r12
-- -- --    truncHlp1 : _

-- -- --   hhh = Recℙ.f₃ r13 truncHlp1
   
-- -- --   field
-- -- --    r21 : Elimℙ.H1 {A = A} (λ z → Recℙ.H2 {A = A} (hhh z))
-- -- --    r22 : Elimℙ.H2 {A = A} {B = λ z → Recℙ.H2 (Recℙ.f₃ r13 truncHlp1 z)} r21
-- -- --    trunncHlp2 : ∀ x → isSet (Recℙ.H2 (Recℙ.f₃ r13 truncHlp1 x))
   
-- -- --   hh = Elimℙ.f₂ r22 trunncHlp2
   
-- -- --   field
-- -- --    r31 : Elimℙ.H1 {A = A} (λ z → Recℙ.H3 {A = A} (hh z))



-- -- --   f2 : ℙ A → ℙ A → B
-- -- --   f2 x = Recℙ.f₃ (Elimℙ.f₁ r31
-- -- --     (λ x → Recℙ.isOfHLevelH3
-- -- --            ((hh x)) 1 isGroupoidB) x) isGroupoidB





-- -- -- module _ {A : Type ℓ} where



-- -- --  hlpSq : (l xs ys++zs ws : List A) →
-- -- --      Square
-- -- --         (sym (++-assoc l (xs ++ (ys++zs)) ws)
-- -- --        ∙' cong (_++ ws) (sym (++-assoc _ _ _)))
-- -- --         (sym (++-assoc l xs ((ys++zs) ++ ws)))
-- -- --          (λ i → (l ++ ++-assoc xs (ys++zs) ws i))
-- -- --         (++-assoc (l ++ xs) (ys++zs) ws)
-- -- --  hlpSq l xs ys++zs ws j i =
-- -- --    hcomp (λ k → λ {
-- -- --           (i = i0) → ++-pentagon-□ l xs ys++zs ws (~ j) k
-- -- --          ;(i = i1) → ++-assoc (l ++ xs) ys++zs ws j
-- -- --          ;(j = i1) → ++-pentagon-△ l xs ys++zs ws (~ i) k
-- -- --            }) (invSides-filler
-- -- --                  (++-assoc (l ++ xs) ys++zs ws)
-- -- --                  (cong (_++ ws) (++-assoc _ _ _))
-- -- --                  (~ i) j)



-- -- --  rℙ⊕ : Recℙ2' A (ℙ A) 𝕡trunc 
-- -- --  Recℙ2'.r11 rℙ⊕ = w
-- -- --   where
-- -- --   w : Recℙ.H1 (Recℙ.H1 (ℙ A))
-- -- --   Recℙ.bbase (Recℙ.bbase w x) y = 𝕡base (x ++ y)
-- -- --  Recℙ2'.r12 rℙ⊕ = w
-- -- --   where
-- -- --   w : Recℙ.H2 (Recℙ2'.r11 rℙ⊕)
-- -- --   Recℙ.bbase (Recℙ.bloopL w xs ys zs ws i) l =
-- -- --     (cong 𝕡base (++-assoc _ _ _)
-- -- --        ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
-- -- --      cong 𝕡base (sym (++-assoc _ _ _))) i
-- -- --   Recℙ.bbase (Recℙ.bloopR w xs ys zs ws i) l =
-- -- --     (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
-- -- --       ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
-- -- --     cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))) i
-- -- --   Recℙ.bbase (Recℙ.bhexDiagAB w ls xs ys zs rs i) l = 
-- -- --     (cong 𝕡base (++-assoc _ _ _ ∙ cong (ls ++_) (++-assoc _ _ _))
-- -- --          ∙∙ 𝕡hexDiagAB ls xs ys zs (rs ++ l) ∙∙
-- -- --        cong 𝕡base (sym (++-assoc _ _ _))) i
-- -- --   Recℙ.bbase (Recℙ.bhexDiagBC w ls xs ys zs rs i) l =
-- -- --     (cong 𝕡base (cong (λ x → ((ls ++ x) ++ l))
-- -- --                      (sym (++-assoc _ _ _))
-- -- --                     ∙∙ ++-assoc _ _ _ ∙∙
-- -- --                     cong (ls ++_) (++-pentagon-diag _ _ _ _))
-- -- --          ∙∙ 𝕡hexDiagBC ls xs ys zs (rs ++ l) ∙∙
-- -- --        cong 𝕡base (sym (++-assoc _ _ _))) i
-- -- --   Recℙ.bbase (Recℙ.bhexDiagCD w ls xs ys zs rs i) l =
-- -- --     (cong 𝕡base (++-assoc _ _ _ ∙ cong ((ls ++ xs ++ ys) ++_) (++-assoc _ _ _) )
-- -- --          ∙∙ 𝕡hexDiagCD ls xs ys zs (rs ++ l) ∙∙
-- -- --        cong 𝕡base (sym (++-assoc _ _ _))) i


-- -- --  Recℙ.bbase (Recℙ.binvolL (Recℙ2'.r13 rℙ⊕) xs ys zs ws j i) l =
-- -- --    (cong 𝕡base (++-assoc _ _ _)
-- -- --        ∙∙ 𝕡involL xs ys zs (ws ++ l) j ∙∙
-- -- --      cong 𝕡base (sym (++-assoc _ _ _))) i
-- -- --  Recℙ.bbase (Recℙ.bloopAssoc (Recℙ2'.r13 rℙ⊕) xs ys zs ws i i₁) x = {!!}
-- -- --  Recℙ.bhexA (Recℙ2'.r13 rℙ⊕) = {!!}
-- -- --  Recℙ.bhexB (Recℙ2'.r13 rℙ⊕) = {!!}
-- -- --  Recℙ.bhexC (Recℙ2'.r13 rℙ⊕) = {!!}
-- -- --  Recℙ.bhexD (Recℙ2'.r13 rℙ⊕) = {!!}


-- -- -- -- -- --  hlpSq : (l xs ys++zs ws : List A) →
-- -- -- -- -- --      Square
-- -- -- -- -- --         (sym (++-assoc l (xs ++ (ys++zs)) ws)
-- -- -- -- -- --        ∙' cong (_++ ws) (sym (++-assoc _ _ _)))
-- -- -- -- -- --         (sym (++-assoc l xs ((ys++zs) ++ ws)))
-- -- -- -- -- --          (λ i → (l ++ ++-assoc xs (ys++zs) ws i))
-- -- -- -- -- --         (++-assoc (l ++ xs) (ys++zs) ws)
-- -- -- -- -- --  hlpSq l xs ys++zs ws j i =
-- -- -- -- -- --    hcomp (λ k → λ {
-- -- -- -- -- --           (i = i0) → ++-pentagon-□ l xs ys++zs ws (~ j) k
-- -- -- -- -- --          ;(i = i1) → ++-assoc (l ++ xs) ys++zs ws j
-- -- -- -- -- --          ;(j = i1) → ++-pentagon-△ l xs ys++zs ws (~ i) k
-- -- -- -- -- --            }) (invSides-filler
-- -- -- -- -- --                  (++-assoc (l ++ xs) ys++zs ws)
-- -- -- -- -- --                  (cong (_++ ws) (++-assoc _ _ _))
-- -- -- -- -- --                  (~ i) j)


-- -- -- -- -- --  ℙ++G3 : H3 ℙ++G2
-- -- -- -- -- --  binvolL ℙ++G3 xs ys zs ws =
-- -- -- -- -- --    refl
-- -- -- -- -- --     ∙∙₂ 𝕡involL (l ++ xs) ys zs ws ∙∙₂
-- -- -- -- -- --     refl

-- -- -- -- -- --  bloopAssoc ℙ++G3 xs ys zs ws =
-- -- -- -- -- --     congSq 𝕡base (hlpSq l xs (ys ++ zs) ws)
-- -- -- -- -- --        ∙∙₂ 𝕡loopAssoc (l ++ xs) ys zs ws ∙∙₂
-- -- -- -- -- --      congSq 𝕡base (congP (λ _ → sym) (hlpSq l xs (zs ++ ys) ws))
   
-- -- -- -- -- --  bhexA ℙ++G3 ls xs ys zs rs =
-- -- -- -- -- --     congSq 𝕡base (λ i → hlpSq l ls (++-assoc xs ys zs (~ i)) rs i)
-- -- -- -- -- --        ∙∙₂ 𝕡hexA (l ++ ls) xs ys zs rs ∙∙₂
-- -- -- -- -- --      congSq 𝕡base
-- -- -- -- -- --        λ i j →
-- -- -- -- -- --           ((λ j → (++-assoc l ls (++-assoc ys zs xs i) j) ++ rs) ∙
-- -- -- -- -- --               ++-assoc l (ls ++ ++-assoc ys zs xs i) rs) j
   
-- -- -- -- -- --  bhexB ℙ++G3 ls xs ys zs rs =
-- -- -- -- -- --     congSq 𝕡base
-- -- -- -- -- --        (λ i → sym (++-assoc l ls (++-assoc (xs ++ ys) zs rs i)))
-- -- -- -- -- --        ∙∙₂ 𝕡hexB (l ++ ls) xs ys zs rs ∙∙₂
-- -- -- -- -- --      congSq 𝕡base {!!}

-- -- -- -- -- --  bhexC ℙ++G3 ls xs ys zs rs =
-- -- -- -- -- --    congSq 𝕡base (symP (hlpSq  l ls (xs ++ ys) (zs ++ rs)))
-- -- -- -- -- --      ∙∙₂  𝕡hexC (l ++ ls) xs ys zs rs  ∙∙₂
-- -- -- -- -- --        {!!}

-- -- -- -- -- --  bhexD ℙ++G3 ls xs ys zs rs = {!!}
-- -- -- -- -- --     -- congSq 𝕡base {!!}
-- -- -- -- -- --     --    ∙∙₂ 𝕡hexD (l ++ ls) xs ys zs rs ∙∙₂
-- -- -- -- -- --     --  congSq 𝕡base {!!}




-- -- --  Recℙ2'.truncHlp1 rℙ⊕ = (Recℙ.isOfHLevelH1 _ 3 𝕡trunc)
-- -- --  Recℙ2'.r21 rℙ⊕ = Elimℙ.h1 w 
-- -- --   where
-- -- --   w : (a : List A) →
-- -- --     Recℙ.H2 (Recℙ.f₃ (_) (_) (𝕡base a))
-- -- --   Recℙ.bloopL (w l) xs ys zs ws =
    
-- -- --       (cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
-- -- --               ∙' cong (_++ ws) (sym (++-assoc _ _ _))))
              
-- -- --         ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
-- -- --          ( sym (cong 𝕡base (sym (++-assoc l (xs ++ (zs ++ ys)) ws)
-- -- --               ∙' cong (_++ ws) (sym (++-assoc _ _ _)))))
-- -- --   Recℙ.bloopR (w l) xs ys zs ws =
-- -- --     cong 𝕡base (sym (++-assoc _ _ _))
-- -- --          ∙∙ 𝕡loopR (l ++ xs) ys zs ws ∙∙
-- -- --        cong 𝕡base (++-assoc _ _ _)




-- -- --   Recℙ.bhexDiagAB (w l) ls xs ys zs rs =
-- -- --           (cong 𝕡base (sym (++-assoc _ _ _))
-- -- --          ∙∙ 𝕡hexDiagAB (l ++ ls) xs ys zs rs ∙∙
-- -- --        cong 𝕡base (cong (_++ rs) (++-assoc _ _ _) ∙ ++-assoc _ _  _))
-- -- --   Recℙ.bhexDiagBC (w l) ls xs ys zs rs =
-- -- --       cong 𝕡base (sym (++-assoc _ _ _))
-- -- --          ∙∙ 𝕡hexDiagBC (l ++ ls) xs ys zs rs ∙∙
-- -- --        cong 𝕡base (cong (_++ rs) (++-pentagon-diag _ _ _ _)
-- -- --          ∙∙ (++-assoc _ _ _) ∙∙
-- -- --          cong (λ x → (l ++ x ++ rs)) (sym (++-assoc _ _ _)))
-- -- --   Recℙ.bhexDiagCD (w l) ls xs ys zs rs =
-- -- --       cong 𝕡base ((sym (++-assoc _ _ _) ∙'
-- -- --                   λ i → (++-assoc l ls (xs ++ ys) (~ i)) ++ zs ++ rs))
-- -- --          ∙∙ 𝕡hexDiagCD (l ++ ls) xs ys zs rs ∙∙
-- -- --        cong 𝕡base (cong ((_++ rs) ∘' (_++ (xs ++ zs))) (++-assoc _ _ _)
-- -- --             ∙∙ cong (_++ rs) (++-assoc _ _ _)
-- -- --             ∙∙ ++-assoc _ _ _)
-- -- --  Recℙ2'.r22 rℙ⊕ = {!!}
-- -- --  Recℙ2'.trunncHlp2 rℙ⊕ = {!!}
-- -- --  Recℙ2'.r31 rℙ⊕ = {!!}
 
-- -- --  -- Recℙ.bbase (Recℙ.bbase (Recℙ2'.r11 rℙ⊕) x) y = 𝕡base (x ++ y)
-- -- --  -- Recℙ.bbase (Recℙ.bloopL (Recℙ2'.r12 rℙ⊕) xs ys zs ws i) l =
   
-- -- --  --   (cong 𝕡base (++-assoc _ _ _)
-- -- --  --       ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
-- -- --  --     cong 𝕡base (sym (++-assoc _ _ _))) i
   
-- -- --  -- Recℙ.bbase (Recℙ.bloopR (Recℙ2'.r12 rℙ⊕) xs ys zs ws i) l =
-- -- --  --   (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
-- -- --  --         ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
-- -- --  --       cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))) i
       
-- -- --  -- Recℙ.bhexDiagAB (Recℙ2'.r12 rℙ⊕) = {!!}
-- -- --  -- Recℙ.bhexDiagBC (Recℙ2'.r12 rℙ⊕) = {!!}
-- -- --  -- Recℙ.bhexDiagCD (Recℙ2'.r12 rℙ⊕) = {!!}
-- -- --  -- Recℙ2'.r13 rℙ⊕ = {!!}
-- -- --  -- Recℙ2'.truncHlp1 rℙ⊕ = {!!}
-- -- --  -- Recℙ2'.r21 rℙ⊕ = {!!}
-- -- --  -- Recℙ2'.r22 rℙ⊕ = {!!}
-- -- --  -- Recℙ2'.trunncHlp2 rℙ⊕ = {!!}
-- -- --  -- Elimℙ.bbase (Recℙ2'.r31 rℙ⊕) a = {!!}

-- -- --  -- ℙ⊕ : ℙ A → ℙ A → ℙ A
-- -- --  -- ℙ⊕ = Recℙ2'.f2 rℙ⊕
 



-- -- -- -- module _ {ℓ} {A : Type ℓ} (l : List A) where
-- -- -- --  open Recℙ {A = A} (Σ (ℙ A × ℙ A) (uncurry _≡_))

-- -- -- --  ℙ++G1 : H1
-- -- -- --  fst (bbase ℙ++G1 x) = 𝕡base (l ++ x) , 𝕡base (x ++ l)
-- -- -- --  snd (bbase ℙ++G1 x) =
-- -- -- --   cong 𝕡base (λ i → ++-unit-r (++-unit-l (l ++ x) (~ i)) (~ i) )
-- -- -- --   ∙∙ 𝕡loopL [] l x [] ∙∙
-- -- -- --   cong 𝕡base (λ i → ++-unit-r (++-unit-l (x ++ l) (i)) (i) )

-- -- -- --  ℙ++G2 : H2 ℙ++G1
-- -- -- --  Recℙ.bloopL ℙ++G2 xs ys zs ws =
-- -- -- --    ΣPathP ((cong₂ _,_
-- -- -- --       (cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
-- -- -- --               ∙' cong (_++ ws) (sym (++-assoc _ _ _)))
-- -- -- --             ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
-- -- -- --           cong 𝕡base (cong (_++ ws) ((++-assoc _ _ _)) ∙ (++-assoc _ _ _)))
-- -- -- --       (cong 𝕡base (++-assoc _ _ _)
-- -- -- --         ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
-- -- -- --         cong 𝕡base (sym (++-assoc _ _ _))))
-- -- -- --      , {!!}
-- -- -- --          -- (flipSquare
-- -- -- --          -- ({!!} ∙∙₂ refl ∙∙₂ {!!})
-- -- -- --          --  ∙∙₂ {!!} ∙∙₂
-- -- -- --          --  flipSquare
-- -- -- --          -- ({!!} ∙∙₂ refl ∙∙₂ {!!}) )
-- -- -- --          )
-- -- -- --  Recℙ.bloopR ℙ++G2 xs ys zs ws =
-- -- -- --    ΣPathP ((cong₂ _,_
-- -- -- --       (cong 𝕡base (sym (++-assoc _ _ _))
-- -- -- --          ∙∙ 𝕡loopR (l ++ xs) ys zs ws ∙∙
-- -- -- --        cong 𝕡base (++-assoc _ _ _))
-- -- -- --       (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
-- -- -- --          ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
-- -- -- --        cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))))
-- -- -- --     , {!!})
-- -- -- --  Recℙ.bhexDiagAB ℙ++G2 ls xs ys zs rs =
-- -- -- --    ΣPathP ((cong₂ _,_
-- -- -- --       (cong 𝕡base (sym (++-assoc _ _ _))
-- -- -- --          ∙∙ 𝕡hexDiagAB (l ++ ls) xs ys zs rs ∙∙
-- -- -- --        cong 𝕡base (cong (_++ rs) (++-assoc _ _ _) ∙ ++-assoc _ _  _))
-- -- -- --       (cong 𝕡base (++-assoc _ _ _ ∙ cong (ls ++_) (++-assoc _ _ _))
-- -- -- --          ∙∙ 𝕡hexDiagAB ls xs ys zs (rs ++ l) ∙∙
-- -- -- --        cong 𝕡base (sym (++-assoc _ _ _))))
-- -- -- --     , {!!})
-- -- -- --  Recℙ.bhexDiagBC ℙ++G2 ls xs ys zs rs =
-- -- -- --    ΣPathP ((cong₂ _,_
-- -- -- --       (cong 𝕡base (sym (++-assoc _ _ _))
-- -- -- --          ∙∙ 𝕡hexDiagBC (l ++ ls) xs ys zs rs ∙∙
-- -- -- --        cong 𝕡base (cong (_++ rs) (++-pentagon-diag _ _ _ _)
-- -- -- --          ∙∙ (++-assoc _ _ _) ∙∙
-- -- -- --          cong (λ x → (l ++ x ++ rs)) (sym (++-assoc _ _ _))))
-- -- -- --       (cong 𝕡base (cong (λ x → ((ls ++ x) ++ l))
-- -- -- --                      (sym (++-assoc _ _ _))
-- -- -- --                     ∙∙ ++-assoc _ _ _ ∙∙
-- -- -- --                     cong (ls ++_) (++-pentagon-diag _ _ _ _))
-- -- -- --          ∙∙ 𝕡hexDiagBC ls xs ys zs (rs ++ l) ∙∙
-- -- -- --        cong 𝕡base (sym (++-assoc _ _ _))))
-- -- -- --     , {!!})
-- -- -- --  Recℙ.bhexDiagCD ℙ++G2 ls xs ys zs rs =
-- -- -- --    ΣPathP ((cong₂ _,_
-- -- -- --       (cong 𝕡base ((sym (++-assoc _ _ _) ∙'
-- -- -- --                   λ i → (++-assoc l ls (xs ++ ys) (~ i)) ++ zs ++ rs))
-- -- -- --          ∙∙ 𝕡hexDiagCD (l ++ ls) xs ys zs rs ∙∙
-- -- -- --        cong 𝕡base (cong ((_++ rs) ∘' (_++ (xs ++ zs))) (++-assoc _ _ _)
-- -- -- --             ∙∙ cong (_++ rs) (++-assoc _ _ _)
-- -- -- --             ∙∙ ++-assoc _ _ _))
-- -- -- --       (cong 𝕡base (++-assoc _ _ _ ∙ cong ((ls ++ xs ++ ys) ++_) (++-assoc _ _ _) )
-- -- -- --          ∙∙ 𝕡hexDiagCD ls xs ys zs (rs ++ l) ∙∙
-- -- -- --        cong 𝕡base (sym (++-assoc _ _ _))))
-- -- -- --     , {!!})





-- -- --  -- record Recℙ2 {ℓb} (B : Type ℓb) (isGroupoidB : isGroupoid B) : Type (ℓ-max ℓ ℓb) where
-- -- --  --  no-eta-equality
-- -- --  --  constructor recℙ2
  
-- -- --  --  field
-- -- --  --   r11 : Recℙ.H1 {A = A} (Recℙ.H1 {A = A} B)
-- -- --  --   r12 : Recℙ.H2 r11
-- -- --  --   r13 : Recℙ.H3 r12

-- -- --  --  hhh = Recℙ.f₃ r13 (Recℙ.isOfHLevelH1 _ 3 isGroupoidB)
   
-- -- --  --  field
-- -- --  --   r21 : Elimℙ.H1 {A = A} (λ z → Recℙ.H2 {A = A} (hhh z))
-- -- --  --   r22 : Elimℙ.H2 {A = A} r21
   
-- -- --  --  hh = Elimℙ.f₂ r22 λ x → Recℙ.isOfHLevelH2 (hhh x) 2 isGroupoidB
   
-- -- --  --  -- field
-- -- --  --  --  r31 : Elimℙ.H1 {A = A} (λ z → Recℙ.H3 {A = A} (hh z))

-- -- --  --  -- -- f2 : ℙ A → ℙ A → B
-- -- --  --  -- -- f2 x = Recℙ.f₃ (Elimℙ.f₁ r31
-- -- --  --  -- --   (λ x → Recℙ.isOfHLevelH3
-- -- --  --  -- --          ((hh x)) 1 isGroupoidB) x) isGroupoidB

