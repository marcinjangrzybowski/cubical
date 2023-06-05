{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.Group where

open import Cubical.Data.Nat.Base as ℕ hiding (_·_)
open import Cubical.Data.Nat.Properties


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution

open import Cubical.Foundations.Everything
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Nat.Order.Permutation
-- open import Cubical.Data.Nat.Order.RecursiveMoreEquiv

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group

open import Cubical.Algebra.SymmetricGroup

import Cubical.Functions.Logic as L

open import Cubical.Functions.Embedding

open import Cubical.Data.List as Li

import Cubical.Data.Nat.FinGenAut2 as A

import Cubical.HITs.PropositionalTruncation as Prop



open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SequentialColimit as SC


-- open import Cubical.Data.FinData.GTrun

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)

open import Cubical.Relation.Binary

import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.Permutation.Base

private
  variable
    ℓ : Level
    A : Type ℓ




toℙrmR≡ : ∀ n → Rrec {n = n} (Path (ℙrm {true} n) 𝕡base 𝕡base)
Rrec.isSetA (toℙrmR≡ n) = 𝕡squash _ _ _
Rrec.εA (toℙrmR≡ n) = refl
Rrec.∷A (toℙrmR≡ n) k = 𝕡loop k ∙_ 
Rrec.invoA (toℙrmR≡ n) k x i j = 
  hcomp (λ l →
       λ { (i = i1) → x (j ∧ l)
         ; (j = i0) → 𝕡base
         ; (j = i1) → (hcomp (λ l' →
                 λ { (i = i1) → x (l' ∧ l)
                   ; (l = i0) → 𝕡invol k l' i
                   ; (l = i1) → x l'
                   }) (𝕡loop k (l ∨ i)))
         }) (𝕡loop k (~ i ∧ j))

Rrec.braidA (toℙrmR≡ n) k k< x i =
    𝕡comp' (k , <-weaken {n = n} k<) (suc k , k<) i
  ∙ 𝕡braid k k< i
  ∙ 𝕡comp (k , <-weaken {n = n} k<) (suc k , k<) i ∙ x

Rrec.commA (toℙrmR≡ n) k l z x i =
    𝕡comp' k l i
    ∙ (𝕡comm k l z i ∙∙ 𝕡comp l k i ∙∙ x)
  

toℙrmRsq : ∀ n → (h : Perm n) → RelimProp
      (λ z →
         
         Square (Rrec.f (toℙrmR≡ n) z)
         (Rrec.f (toℙrmR≡ n) ((snd (PermG n) GroupStr.· z) h)) refl
         (Rrec.f (toℙrmR≡ n) h))
RelimProp.isPropA (toℙrmRsq n h) _ =
  isOfHLevelRetractFromIso
    1 (invIso PathP→comm-Iso) (𝕡squash _ _ _ _ _)
RelimProp.εA (toℙrmRsq n h) i j = (Rrec.f (toℙrmR≡ n) h) (i ∧ j)
RelimProp.∷A (toℙrmRsq n h) k x i = 𝕡loop k ∙ x i

toℙrmR : ∀ n → EMrec (PermG n) {B = ℙrm n} (𝕡squash _)
EMrec.b (toℙrmR n) = 𝕡base
EMrec.bloop (toℙrmR n) = Rrec.f (toℙrmR≡ n)
EMrec.bComp (toℙrmR n) g h = RelimProp.f (toℙrmRsq n h) g 

ℙrm' : ℕ → Type
ℙrm' n = EM₁ (PermG n)


toℙrm : ∀ n → ℙrm' n → ℙrm n
toℙrm n = EMrec.f (toℙrmR n)

toℙrmInv : ∀ n xs → (sym (cong (toℙrm n) (emloop xs))) ≡ cong (toℙrm n) (emloop (inv xs))
toℙrmInv n = RelimProp.f {n = n} (w n)
 where
  w : ∀ n → RelimProp
        (λ z →
           sym (cong (toℙrm n) (emloop z)) ≡ cong (toℙrm n) (emloop (inv z)))
  RelimProp.isPropA (w n) x = 𝕡squash _ _ _ _ _
  RelimProp.εA (w n) = refl
  RelimProp.∷A (w n) k {xs} X =
    symDistr (𝕡loop k) _ ∙     
     cong′ (_∙ (sym (𝕡loop k))) X ∙
        (( cong₂ _∙_ (cong (cong (toℙrm n)) (emloop-sym _ xs))
            (doubleCompPath-filler refl _ refl) ∙
          sym (cong-∙ (toℙrm n) (sym (emloop xs)) (sym (emloop (k ∷ ε))))
          ) ∙
          cong (cong (toℙrm n))
            (sym (symDistr (emloop (k ∷ ε)) _) ∙ cong sym (sym (emloop-comp' _ (k ∷ ε) xs))
              ∙ sym (emloop-sym _ (k ∷ xs))))

commSq : ∀ n → ∀ k xs → Square {A = ℙrm' n}
           (emloop (η k))
           (emloop xs)
           refl
           (emloop (η k · xs))
commSq n k xs i j =
  hcomp (λ l' → λ {
       (i = i0) → emloop (η k) j
      ;(i = i1) → emloop (invo k xs l') j
      ;(j = i0) → embase
      ;(j = i1) → emloop (k ∷ xs) i
      }) (emcomp (η k) (η k · xs) i j)

-- commSq' : ∀ n → ∀ k l → Square {A = ℙrm' n}
--            (emloop (η l))
--            (emloop (η k))
--            refl
--            (emloop (η l · η k))
           
-- commSq' n k l i j = {!!}
--   -- hcomp (λ l' → λ {
--   --      (i = i0) → emloop (η k) j
--   --     ;(i = i1) → emloop (invo k (η l) l') j
--   --     ;(j = i0) → embase
--   --     ;(j = i1) → emloop (k ∷ η l) i
--   --     }) (emcomp (η k) (η k · η l) i j)

involSq : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
      emloop (η {n = n} k) ≡ sym (emloop (η k))
involSq n k i j =
  hcomp (λ l → λ {
       (i = i0) → emcomp (η k) (η k) j l
      ;(i = i1) → emcomp ε (η k) (~ j) l
      ;(j = i0) → emloop (k ∷ ε) l
      ;(j = i1) → emloop {Group = PermG n} ((invo {n = n} k ε) i) l
      }) embase


braidSq : ∀ n k l →
   Square {A = ℙrm' n}
     (emloop (η k))
     (emloop (η k))
     (emloop (η l))
     (emloop (k  ∷ l ∷ k ∷ ε))
braidSq n k l =
    (involSq n k) ◁
      emloop-doubleCompFill (PermG n) (η k) (η l) (η k)
braidSq' : ∀ n k l →
   Square {A = ℙrm' n}
     (sym (emloop (η l)))
     (sym (emloop (η l)))
     (emloop (l ∷ k ∷ l ∷ ε))
     (emloop (η k))
braidSq' n k l =
  (sym (involSq n l)) ◁
     λ i j → emloop-doubleCompFill (PermG n) (η l) (η k) (η l) i (~ j)


braidSqC : ∀ n k k< →
   Square {A = ℙrm' n}
     refl
     refl
     (emloop ((k , <-weaken {n = n} k<)
         ∷ (suc k , k<) ∷ (k , <-weaken  {n = n} k<) ∷ ε))
     (emloop ((suc k , k<) ∷ (k , <-weaken  {n = n} k<) ∷ (suc k , k<) ∷ ε))
      
braidSqC n k k< i j = emloop (braid k k< ε j ) i
  -- (braidSqC0 n k k< j
  --   ∙∙ (λ i → emloop (braid k k< ε i ) j)
  --   ∙∙
  --   braidSqC1 n k k< j) i

Rfromℙrm : ∀ n → R𝕡rec {n = n} (ℙrm' n)
R𝕡rec.abase (Rfromℙrm n) = embase
R𝕡rec.aloop (Rfromℙrm n) = emloop ∘ η
R𝕡rec.alooop (Rfromℙrm n) k l i =
  hcomp (λ z → λ {(i = i0) → emloop (η k) (~ z)
                ; (i = i1) → emloop (η l) (~ z)} ) embase

R𝕡rec.acomp (Rfromℙrm n) k l i j =
  doubleCompPath-filler (emloop (η k)) refl (sym (emloop (η l))) (~ j) i
R𝕡rec.ainvol (Rfromℙrm n) = involSq n
    
R𝕡rec.acomm (Rfromℙrm n) k l x i j =
  (commSq n k (η l) j ∙∙
    (λ i → emloop (comm k l x ε i ) j)
   ∙∙ sym (commSq n l (η k) j)) i
R𝕡rec.abraid (Rfromℙrm n) k k< i j =
  (braidSq n (k , (<-weaken {n = n} k<) ) (suc k , k<) j ∙∙
   (braidSqC n k k< j)
   ∙∙ braidSq' n (k , (<-weaken {n = n} k<) ) (suc k , k<) j) i

-- R𝕡rec.asquash (Rfromℙrm n) = emsquash

fromℙrm : ∀ n → ℙrm {true} n → ℙrm' n
fromℙrm n = R𝕡rec.f (Rfromℙrm n) {true} {emsquash}

emloop-ε : ∀ n → refl ≡ emloop {Group = PermG n} ε 
emloop-ε n i j =
  hcomp (λ l →
    primPOr i (~ i ∨ j ∨ ~ j)
      (λ _ → emcomp ε ε j l)
       λ _ → emloop ε l)
    embase 

RelimProp≡ : ∀ n → RelimProp
      λ z →
        Square
         (λ j → fromℙrm n (Rrec.f (toℙrmR≡ n) z j))
         (emloop z)
        refl
        refl
RelimProp.isPropA (RelimProp≡ n) x = emsquash _ _ _ _
RelimProp.εA (RelimProp≡ n) = emloop-ε n
RelimProp.∷A (RelimProp≡ n) k {xs} X =
  (cong-∙ (fromℙrm n) (𝕡loop k) (cong (toℙrm n) (emloop xs))
    ∙ cong (emloop (η k) ∙_) X) ∙ sym (emloop-comp _ (η k) xs)
   
RfromToℙrm : ∀ n → EMelimSet (PermG n) (λ z → fromℙrm n (toℙrm n z) ≡ z)
EMelimSet.isSetB (RfromToℙrm n) x = emsquash _ _
EMelimSet.b (RfromToℙrm n) = refl
EMelimSet.bPathP (RfromToℙrm n) = flipSquare ∘ RelimProp.f (RelimProp≡ n)

fromToℙrm : ∀ n → section (fromℙrm n) (toℙrm n)
fromToℙrm n = EMelimSet.f (RfromToℙrm n)


RtoFromℙrm : ∀ n → 
     R𝕡elimSet {n = n} (λ z → toℙrm n (fromℙrm n z) ≡ z)
R𝕡elimSet.isSetA (RtoFromℙrm n) _ = 𝕡squash _ _ _
R𝕡elimSet.abase (RtoFromℙrm n) = refl
R𝕡elimSet.aloop (RtoFromℙrm n) k i j =
   (compPath-filler (𝕡loop k) refl) (~ j) i
R𝕡elimSet.alooop (RtoFromℙrm n) k l i j = 
  
   hcomp (λ l' → λ {
       (i = i0) → compPath-filler (𝕡loop k) refl (~ j) (~ l')
      ;(i = i1) → compPath-filler (𝕡loop l) refl (~ j) (~ l')
      ;(j = i0) → toℙrm n
         (doubleCompPath-filler
            (emloop (η k)) refl
             (sym (emloop (η l))) l' i)
      ;(j = i1) → 𝕡comp k l i (~ l')
      }) 𝕡base

toFromℙrm : ∀ n → retract (fromℙrm n) (toℙrm n)
toFromℙrm n = R𝕡elimSet.f (RtoFromℙrm n)

IsoEmℙrm : ∀ n →  Iso (ℙrm n) (ℙrm' n)
Iso.fun (IsoEmℙrm n) = fromℙrm n
Iso.inv (IsoEmℙrm n) = toℙrm n
Iso.rightInv (IsoEmℙrm n) = fromToℙrm n
Iso.leftInv (IsoEmℙrm n) = toFromℙrm n

𝕡Ω₂ : ∀ n → Group₀
fst (𝕡Ω₂ n) = Path (ℙrm {true} n) 𝕡base 𝕡base 
GroupStr.1g (snd (𝕡Ω₂ n)) = refl
GroupStr._·_ (snd (𝕡Ω₂ n)) = _∙_
GroupStr.inv (snd (𝕡Ω₂ n)) = sym
GroupStr.isGroup (snd (𝕡Ω₂ n)) =
 makeIsGroup
   (𝕡squash _ _ _)
   assoc 
   (sym ∘ rUnit)
   (sym ∘ lUnit)
   rCancel
   lCancel


emℙrm : ∀ n → Type
emℙrm = EM₁ ∘' 𝕡Ω₂

GIso-𝕡Ω₂-PermG-pres· : ∀ n → 
 (x y : Perm n) →
       Iso.fun (congIso (invIso (IsoEmℙrm n)))
       (emloop ((PermG n .snd GroupStr.· x) y))
       ≡
       Iso.fun (congIso (invIso (IsoEmℙrm n))) (emloop x) ∙
       Iso.fun (congIso (invIso (IsoEmℙrm n))) (emloop y)
GIso-𝕡Ω₂-PermG-pres· n = flip (RelimProp.f w)
 where
 w : RelimProp _
 RelimProp.isPropA w _ = isPropΠ λ _ → 𝕡squash _ _ _ _ _
 RelimProp.εA w x =
   cong′ (Rrec.f (toℙrmR≡ n)) (idr x)
      ∙ rUnit _
 RelimProp.∷A w k {xs} X y =
  let p = assoc· y (η k) xs
      pp = _
  in cong′ (cong′ (toℙrm n) ∘ emloop) p ∙
       X (y · η k) ∙
       cong′ (_∙ pp)
         
         (cong′ (cong′ (toℙrm n))
           (emloop-comp _ y (η k)) ∙ 
            cong′ (λ v → cong′ (toℙrm n) (emloop y ∙ emloop v))
             {η k} {(EMP.encode (PermG n) embase
        (Iso.inv (congIso (invIso (IsoEmℙrm n))) (𝕡loop k)))}
              (sym (transportRefl _) ∙ sym (transportRefl _))
             ∙
            congFunct (Iso.fun (invIso (IsoEmℙrm n)))
              (emloop y)
              (emloop ((Iso.inv
                     (compIso (invIso (EMP.ΩEM₁Iso (PermG n)))
                      (congIso (invIso (IsoEmℙrm n))))
                     (𝕡loop k)))) ∙
          cong′ ((λ i₁ → Iso.fun (congIso (invIso (IsoEmℙrm n))) (emloop y) i₁)
             ∙_)  
               (Iso.rightInv (compIso (invIso (EMP.ΩEM₁Iso (PermG n)))
                 (congIso (invIso (IsoEmℙrm n)))) (𝕡loop k)) )
        ∙ sym (assoc _ _ pp)


module _ {ℓG ℓH} {(G , strG) : Group ℓG} {(H , strH) : Group ℓH} where

  module H'' =  GroupStr strH
  module G'' =  GroupStr strG

  gi→em₂→ : GroupIso ((G , strG)) ((H , strH)) →
            Iso (EM₁ (G , strG)) (EM₁ (H , strH))
  Iso.fun (gi→em₂→ (fst₁ , snd₁)) = gh→em₂→ ((G , strG)) (_ , snd₁)
  Iso.inv (gi→em₂→ (fst₁ , snd₁)) =
    gh→em₂→ ((H , strH)) (_ , snd (invGroupIso (fst₁ , snd₁)))
  Iso.rightInv (gi→em₂→ (fst₁ , snd₁)) =
    EMelimSet.f w
   where
   w : EMelimSet _ _
   EMelimSet.isSetB w _ = emsquash _ _
   EMelimSet.b w = refl
   EMelimSet.bPathP w g = flipSquare (cong emloop (Iso.rightInv fst₁ g))
   
  Iso.leftInv (gi→em₂→ (fst₁ , snd₁)) =
   EMelimSet.f w
   where
   w : EMelimSet _ _
   EMelimSet.isSetB w _ = emsquash _ _
   EMelimSet.b w = refl
   EMelimSet.bPathP w g = flipSquare (cong emloop (Iso.leftInv fst₁ g))


GIso-𝕡Ω₂-PermG : ∀ n → GroupIso (PermG n) (𝕡Ω₂ n)
fst (GIso-𝕡Ω₂-PermG n) = compIso (invIso (EMP.ΩEM₁Iso (PermG n)))
  (congIso (invIso (IsoEmℙrm n)))
IsGroupHom.pres· (snd (GIso-𝕡Ω₂-PermG n)) = GIso-𝕡Ω₂-PermG-pres· n  
IsGroupHom.pres1 (snd (GIso-𝕡Ω₂-PermG n)) = refl
IsGroupHom.presinv (snd (GIso-𝕡Ω₂-PermG n)) = RelimProp.f w
 where
 w : RelimProp _
 RelimProp.isPropA w _ = 𝕡squash _ _ _ _ _
 RelimProp.εA w = refl
 RelimProp.∷A w (k , k<) {xs} x =    
    GIso-𝕡Ω₂-PermG-pres· n (inv xs) (η (k , k<))
   ∙ (assoc _ _ _ ∙
     sym (rUnit _) ∙
      cong (Iso.fun (congIso (invIso (IsoEmℙrm n)))
       (emloop (GroupStr.inv (PermG n .snd) xs)) ∙_)
       (𝕡invol (k , k<))
       ∙ compPath≡compPath' _ _)
   ∙ cong′ (_∙' (sym (𝕡loop (k , k<)))) x


elimℙrm≡ : ∀ n → (A : Path (ℙrm {true } n) 𝕡base 𝕡base → Type ℓ)
                 → (∀ p → isProp (A p))
                 → A refl
                 → (∀ k xs → A xs → A (𝕡loop k ∙ xs) )
                 → ∀ p → A p
elimℙrm≡ n A isPrpA Arefl A∙ =
  λ p →  subst A (Iso.rightInv (fst (GIso-𝕡Ω₂-PermG n)) p)
      (w ((Iso.inv (fst (GIso-𝕡Ω₂-PermG n)) p)))
 where
 w : (p : Perm n) → A (Iso.fun (fst (GIso-𝕡Ω₂-PermG n)) p) 
 w = RelimProp.f w'
  where
  w' : RelimProp (λ z → A (Iso.fun (fst (GIso-𝕡Ω₂-PermG n)) z))
  RelimProp.isPropA w' = isPrpA ∘ _
  RelimProp.εA w' = Arefl
  RelimProp.∷A w' k {xs} y =
   let z = IsGroupHom.pres· (snd (GIso-𝕡Ω₂-PermG n))
            (η k) xs
   in subst A
       (cong′ (_∙ (Rrec.f (toℙrmR≡ n) xs)) (rUnit _) ∙ sym z)
        (A∙ k (Iso.fun (fst (GIso-𝕡Ω₂-PermG n)) xs) y)

emℙrmIso : ∀ n → Iso (ℙrm {true} n) (emℙrm n) 
emℙrmIso n = compIso (IsoEmℙrm n)
                  (gi→em₂→ (GIso-𝕡Ω₂-PermG n))
