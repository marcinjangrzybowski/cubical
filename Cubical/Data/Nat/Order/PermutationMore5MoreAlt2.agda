{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.PermutationMore5MoreAlt2 where

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
open import Cubical.Data.Nat.Order.RecursiveMoreEquiv

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group

open import Cubical.Algebra.SymmetricGroup

import Cubical.Functions.Logic as L

open import Cubical.Functions.Embedding

open import Cubical.Data.List as Li

import Cubical.Data.Nat.FinGenAut2 as A

import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SequentialColimit as SC

open import Cubical.Data.Nat.Order.Permutation
-- open import Cubical.Data.Nat.Order.PermutationMore


-- open import Cubical.Data.FinData.GTrun

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)

open import Cubical.HITs.ListedFiniteSet.Base3
import Cubical.HITs.ListedFiniteSet.Base22Star2 as S
import Cubical.HITs.ListedFiniteSet.Base22Star3 as S'

open import Cubical.Relation.Binary

import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Data.Nat.Order.PermutationMore5

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


toℙrm : ∀ n → ℙrm' n → ℙrm n
toℙrm n = EMrec.f (toℙrmR n)


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

module _ (A : Type ℓ) where

 em𝕍 : ∀ n → emℙrm n → Type ℓ
 em𝕍 n = 𝕍₃ A n ∘' Iso.inv (emℙrmIso n) 

 -- ↔× : ∀ n → Rel (A ×^ n) (A ×^ n) ℓ
 -- ↔× n x y =
 --    Σ (Path (emℙrm n) embase embase)
 --      λ p → PathP (λ i → em𝕍 n (p i)) x y

 -- ↔×-trans : ∀ n → BinaryRelation.isTrans (↔× n)
 -- ↔×-trans n _ _ _ (p , P) (q , Q) =
 --   (p ∙ q) , (compPathP' {x = embase} {embase} {embase}
 --      {B = em𝕍 n} {p = p} {q = q} P Q)

 record 𝑽 (n : ℕ) : Type ℓ where
  constructor _𝒗_
  field
   𝕡𝑽 : ℙrm {true} n
   𝕧 : 𝕍₃ A n 𝕡𝑽

--  ↔× : ∀ n → Rel (A ×^ n) (A ×^ n) ℓ
--  ↔× n x y = Path (Σ (ℙrm {true} n) (𝕍₃ A n))
--              (𝕡base , x) (𝕡base , y)
--     -- Σ ⟨ 𝕡Ω₂ n ⟩ 
--     --   λ p → PathP (λ i → 𝕍₃ A n (p i)) x y

 ↔× : ∀ n → Rel (A ×^ n) (A ×^ n) ℓ
 ↔× n x y = Path (𝑽 n)
             (𝕡base 𝒗 x) (𝕡base 𝒗 y)
    -- Σ ⟨ 𝕡Ω₂ n ⟩ 
    --   λ p → PathP (λ i → 𝕍₃ A n (p i)) x y

 ↔×𝕡 : ∀ n 𝕡 → Rel (𝕍₃ A n 𝕡) (𝕍₃ A n 𝕡) ℓ
 ↔×𝕡 n 𝕡 x y = Path (𝑽 n) (𝕡 𝒗 x) (𝕡 𝒗 y)



 ↔×-trans : (n : ℕ) → (a b c : A ×^ n) → ↔× n a b → ↔× n b c → ↔× n a c
 ↔×-trans n _ _ _ = _∙_

 ↔×𝕡-trans : (n : ℕ) → ∀ 𝕡 → (a b c : _)
    → ↔×𝕡 n 𝕡 a b → ↔×𝕡 n 𝕡 b c → ↔×𝕡 n 𝕡 a c
 ↔×𝕡-trans n _ _ _ _ = _∙_

--     hcomp {A = Σ (ℙrm n) (𝕍₃ A n)}
--       (λ j → λ {(i = i0) → p i0
--                ;(i = i1) → q j
--         })
--       (p i) 
--    -- (p ∙ q) , (compPathP' {B = 𝕍₃ A n} {p = p} {q = q} P Q)

 ↔// : ∀ n → Type ℓ
 ↔// n = (A ×^ n) // ↔×-trans n

 ↔//𝕡 : ∀ n → ℙrm {true} n → Type ℓ
 ↔//𝕡 n 𝕡 = 𝕍₃ A n 𝕡 // (↔×𝕡-trans n 𝕡)
 
 adjT'// : ∀ n k → (a : A ×^ n)  → Path (↔// n) [ adjT×^ (fst k) a ]// [ a ]// 
 adjT'// n k a = eq// λ i → 𝕡loop k i 𝒗 glue'AdjT× n (fst k) i a

 adjT// : ∀ n k → (a : A ×^ n)  → Path (↔// n) [ a ]// [ adjT×^ (fst k) a ]// 
 adjT// n k a = eq// λ i → 𝕡loop k i 𝒗 glueAdjT× n (fst k) i a


 module _ (isGrpA : isGroupoid A) where

  cons↔𝕡 : ∀ n p a x y → (↔×𝕡 n p x y)
                    → (↔×𝕡 (suc n) (sucℙrm n p)
                      (cons𝕍₃ A isGrpA n p a x)
                      (cons𝕍₃ A isGrpA n p a y))
  cons↔𝕡 n _ a x y =
    cong′ λ (𝕡 𝒗 v) → sucℙrm n 𝕡 𝒗 cons𝕍₃ A isGrpA n 𝕡 a v



  cons↔ : ∀ n a x y → (↔× n x y)
                    → (↔× (suc n) (a , x) (a , y))
  cons↔ n a x y =
    cong λ (𝕡 𝒗 v) → sucℙrm n 𝕡 𝒗 cons𝕍₃ A isGrpA n 𝕡 a v

  cong//𝕡 : ∀ n 𝕡 → A → ↔//𝕡 n 𝕡 → ↔//𝕡 (suc n) (sucℙrm n 𝕡)
  cong//𝕡 n 𝕡 a' = GQ.Rrec.f w
   where
   w : Rrec// (↔//𝕡 (suc n) (sucℙrm n 𝕡))
   Rrec//.Bgpd w = squash//
   Rrec//.fb w = [_]// ∘' (cons𝕍₃ A isGrpA n 𝕡 a')
   Rrec//.feq w = eq// ∘ cons↔𝕡 n 𝕡 a' _ _ 
   Rrec//.fsq w p r =
      comp// _ _ ▷ 
        cong′ eq// (sym (congFunct
           (λ (𝕡 𝒗 v) → sucℙrm n 𝕡
             𝒗 cons𝕍₃ A isGrpA n 𝕡 a' v) p r))

  []//𝕡 : ∀ n 𝕡 → (𝕍₃ A n) 𝕡 → ↔//𝕡 n 𝕡 
  []//𝕡 n 𝕡 = [_]//

  -- []//𝕡 : ∀ n 𝕡 → ↔//𝕡 n 𝕡 → (𝕍₃ A n) 𝕡  
  -- []//𝕡 n 𝕡 = ?


  -- consTrans↔ : ∀  n (a' : A) {a b c : A ×^ n}
  --         (p : ↔× n a b) (r₁ : ↔× n b c) →
  --       ↔×-trans (suc n) (a' , a) (a' , b) (a' , c) (cons↔ n a' a b p)
  --             (cons↔ n a' b c r₁)
  --             ≡ (λ z → cons↔ n a' a c (↔×-trans n a b c p r₁) z)
  -- consTrans↔ n a' p r =
  --   sym (congFunct
  --    (λ (𝕡 , v) → sucℙrm n 𝕡 , cons𝕍₃ A isGrpA n 𝕡 a' v)
  --     p r)
  
  cong// : ∀ n → A → ↔// n → ↔// (suc n)
  cong// n a' = GQ.Rrec.f w
   where
   w : Rrec// (↔// (suc n))
   Rrec//.Bgpd w = squash//
   Rrec//.fb w = [_]// ∘' (a' ,_)
   Rrec//.feq w = eq// ∘ cons↔ n a' _ _ 
   Rrec//.fsq w p r =
      comp// _ _ ▷
        cong′ eq// (sym (congFunct
           (λ (𝕡 𝒗 v) → sucℙrm n 𝕡
             𝒗 cons𝕍₃ A isGrpA n 𝕡 a' v) p r))
  
--  --  -- _++//_ : ∀ {m n} → ↔// m → ↔// n → ↔// (m + n)
--  --  -- _++//_ {m} {n} = GQ.Rrec.f (w m)
--  --  --  where
--  --  --  w : ∀ m → Rrec// (↔// n → ↔// (m + n))
--  --  --  Rrec//.Bgpd (w m) = isGroupoidΠ λ _ → squash//
--  --  --  Rrec//.fb (w zero) _ x = x
--  --  --  Rrec//.fb (w (suc m)) = {!!}
--  --  --  Rrec//.feq (w m) = {!!}
--  --  --  Rrec//.fsq (w m) = {!!}



  eq//-refl↔ : ∀ n → (a b : A ×^ n) → (P : a ≡ b) →
        (cong [_]// P) ≡ (eq// λ i → 𝕡base 𝒗 P i) 
  eq//-refl↔ n a b P =
   let s : Square _ _ _ _
       s i j = comp// {Rt = ↔×-trans n}
          {P i} {b} {b} (λ i' → 𝕡base 𝒗 P (i ∨ i')) refl i j
       
   in λ i j →
      hcomp (λ z →
        λ {  (i = i0) → s (~ z ∨ j) i0
           ; (i = i1) → s (~ z) j
           ; (j = i0) → s (~ z) j
           ; (j = i1) → refl≡Id
              (↔×-trans n) {b} refl (sym compPathRefl) (~ i) (~ z)
           })
        (refl≡Id (↔×-trans n) {b} (↔×-trans n b b b refl refl)
          (cong (λ q → ↔×-trans n b b b q q) (sym compPathRefl))
           (~ i) j)


  eq//-invol'' : ∀ n → (v : A ×^ (suc (suc n))) → 
    Square {A = ↔// (suc (suc n))}
      (λ z →
          eq// (λ i → 𝕡loop (zero , tt) i 𝒗 glue'AdjT× (2 + n) zero i v) z)
      (λ z →
          eq// (λ i → 𝕡loop (zero , tt) i 𝒗 glueAdjT× (2 + n) zero i v) (~ z))
      refl
      refl
      
  eq//-invol'' n v =
     whiskSq.sq' (λ _ _ → ↔// (2 + n))
       (λ _ _ → [ v ]//)
       (λ i z → (comp// {Rt = ↔×-trans (2 + n)}
           (λ i → 𝕡loop (zero , _) (~ i) 𝒗 glue'AdjT× (2 + n) zero (~ i) v)
           (λ i → 𝕡loop (zero , _) i 𝒗 glue'AdjT× (2 + n) zero i v))
            i z )
          (λ i z → eq//
         (λ i → 𝕡loop (zero , _) i 𝒗 glueAdjT× (2 + n) zero i v)
             (~ i ∧ (z)))
       (cong eq// λ i j → 𝕡invol (zero , _) (~ i) j 𝒗
           Σ-swap-01-≡-invol-ua-glue (~ i) j v)
       ((cong′ eq// (rCancel _))
         ∙ sym (eq//-refl↔ (2 + n) v v refl))

  -- eq//-adjT : ∀ n → (a a' : A) → (v : ↔// n) →
  --     cong// (suc n) a (cong// n a' v) ≡
  --     cong// (suc n) a' (cong// n a v)
  -- eq//-adjT n a a' = GQ.RelimSet.f w
  --  where
  --  w : RelimSet
  --        (λ z →
  --           cong// (suc n) a (cong// n a' z) ≡
  --           cong// (suc n) a' (cong// n a z))
  --  RelimSet.truncB w _ = squash// _ _
  --  RelimSet.fb w v = adjT// (2 + n) (zero , _) (a , a' , v)   
  --  RelimSet.fbEq w = {!!}




--   eq//-invol : ∀ n → SquareP
--       (λ i j → 𝕍₃ A (suc (suc n)) (𝕡invol (zero , _) i j) → ↔// (suc (suc n)))
--       (λ j x → eq// (λ i' → 𝕡loop (zero , _) i' 𝒗 glue'AdjT× (2 + n) zero i'
--             (unglue (j ∨ ~ j) x)) j)
--       ((λ j x → eq// (λ i' → 𝕡loop (zero , _) i' 𝒗 glue'AdjT× (2 + n) zero i'
--             (unglue (j ∨ ~ j) x)) (~ j)))
--       refl
--       refl
      
--   eq//-invol n i j x = 
--    eq//-invol'' n
--      (swap-01 (unglue (i ∨ ~ i) (unglue (j ∨ ~ j) x)))
--       i j



  P-adjT : ∀ n → (a b : A ×^ n) → ∀ (xs : ⟨ 𝕡Ω₂ n ⟩) k →
               (PathP (λ i → 𝕍₃ A n ((𝕡loop k ∙ xs) i)) a b)
              → PathP (λ i → 𝕍₃ A n (xs i)) (adjT×^ (fst k) a) b 
  P-adjT n a b xs k x i =
     comp (λ z → 𝕍₃ A n (compPath-filler (𝕡loop k) xs i z ))
       (λ z → λ {(i = i0) → glueAdjT× n (fst k) z a
                ;(i = i1) → x z
                }) a


  P-adjT-fill : ∀ n → (a b : A ×^ n) → ∀ (xs : ⟨ 𝕡Ω₂ n ⟩) k →
               (P : PathP (λ i → 𝕍₃ A n ((𝕡loop k ∙ xs) i)) a b)
              → SquareP (λ i j →
                    𝕍₃ A n (compPath-filler (𝕡loop k) xs i j))
                  (λ i → glueAdjT× n (fst k) i a)
                  P
                  refl
                  (P-adjT n a b xs k P)
  P-adjT-fill n a b xs k x i z =
     fill (λ z → 𝕍₃ A n (compPath-filler (𝕡loop k) xs i z ))
       (λ z → λ {(i = i0) → glueAdjT× n (fst k) z a
                ;(i = i1) → x z
                }) (inS a) z

  P-adjT-comp : ∀ n → (a b : A ×^ n) → ∀ (xs : ⟨ 𝕡Ω₂ n ⟩) k →
               (P : PathP (λ i → 𝕍₃ A n ((𝕡loop k ∙ xs) i)) a b)
              → Path ((𝕡base 𝒗 a) ≡ (𝕡base 𝒗 b))
                (↔×-trans n _ (adjT×^ (fst k) a) _
                (λ i → 𝕡loop k i 𝒗 glueAdjT× n (fst k) i a)
                (λ i → xs i 𝒗 P-adjT n a b xs k P i))               
                (λ i → (𝕡loop k ∙ xs) i 𝒗 P i)
  P-adjT-comp n a b xs k P =
    sym (PathP∙∙→compPathR
          {p = refl}
          {sym (λ i → xs i 𝒗 P-adjT n a b xs k P i)}
        λ i j → compPath-filler (𝕡loop k) xs (~ i) j 𝒗
                (P-adjT-fill n a b  xs k P) (~ i) j)


  adjSq : ∀ n l → SquareP (λ i i' →
          adjT×^≡ {A = A} {n = n} l (~ i) → adjT×^≡ {A = A} {n = n} l (~ i'))
            {idfun _}
            {adjT×^ l}
            (symP (glue'AdjT× n l))
            {adjT×^ l}
            {idfun _}
            (symP (glueAdjT× n l))
            (symP (unglue'AdjT× n l))
            (symP (unglueAdjT× n l))
  adjSq zero l i i' = _
  adjSq (suc n) (suc l) i i' = map-snd (adjSq n l i i')
  adjSq (suc zero) zero i i' x = x
  adjSq (suc (suc n)) zero i i' =
   ua-gluePathExt (adjT×^≃ zero) (~ i') ∘ swap-01
    ∘  ua-ungluePathExt (adjT×^≃ zero) (~ i)

  -- adjT×^≡-invol-unglue'' : ∀ n l →
    
  --     --   fst (adjT×^≃ l) (adjT×^≡-invol-unglue n l i j v)
  --     -- ≡ idfun (A ×^ n) (adjT×^≡-invol-unglue' n l i j v)
  -- adjT×^≡-invol-unglue'' = ?
  
  eq//-commSS : ∀ n l → 
     SquareP
       (λ i j → A × A × adjT×^≡-invol {A = A} n (fst l) j (~ i)
          → ↔// (suc (suc n)))
      (λ j → [_]//) 
      (λ j → [_]// ∘' swap-01)
      (λ i x → eq// (λ i' →
         𝕡looop (zero , _) (suc (suc (fst l)) , (snd l)) i'
         𝒗
          glueBiAdjT×<SS n l (~ i')
              (map-snd (map-snd (adjSq n (fst l) i i')) (swap-01  x))) i
         )
      (λ i x → eq// (λ i' →
         𝕡looop (suc (suc (fst l)) , (snd l)) (zero , _)  i'
         𝒗
         -- glueBiAdjT×<SS n l i'
         -- (fst x , fst (snd x) , {!adjSq n (fst l) (~ i) (~ i') (snd (snd x))!})
         glueBiAdjT×<SS n l i'
           ((map-snd (map-snd (adjSq n (fst l) (~ i) (~ i')))
             (x)))
         ) i)
  eq//-commSS n l i j (a , a' , v) =
    let v* = (adjT×^≡-invol-unglue n (fst l) i j) v
        v' = (adjT×^≡-invol-unglue' n (fst l) i j) v
    in eq// {a = a , a' , v*}
         {b = a' , a , v'}
      (isGroupoid→isGroupoid' {A = 𝑽 (2 + n)} {!!}
          (λ j i' → 𝕡looop (zero , _) (suc (suc (fst l)) , snd l) i'
                   𝒗 glueBiAdjT×<SS n l (~ i')
                   (a' , a ,
                    glueAdjT× n (fst l) (~ i') v*))
          
          (λ j' i' → 𝕡looop (suc (suc (fst l)) , (snd l)) (zero , _) i'
                   𝒗
                   glueBiAdjT×<SS n l i' (a , a' , glueAdjT× n (fst l) i' v'))
          
          {cong′ (λ w → 𝕡base 𝒗 (a , a' , w)) {!!}}
          {cong′ (λ w → 𝕡base 𝒗 (a' , a , w)) {!!}}
          (λ i i' → 𝕡comm (zero , _) (suc (suc (fst l)) , snd l) _ i i' 𝒗
                   {!!} )
          {cong′ (λ w → 𝕡base 𝒗 (a , a' , w)) {!!}}
          {cong′ (λ w → 𝕡base 𝒗 (a' , a , w)) {!!}}
          (λ i i' → 𝕡comm (zero , _) (suc (suc (fst l)) , snd l) _ i i' 𝒗
                   {!!})
          (λ i j → 𝕡base 𝒗 (a , a' , {!(adjT×^≡-invol-unglue n (fst l) i j) ?!}))
          (λ i j → 𝕡base 𝒗 (a' , a , {!!})) i j ) i
          
-- -- (adjCu n l i i' j)

--   Iso-//→ : ∀ n → ∀ 𝕡 → (𝕍₃ A n) 𝕡 → (↔// n)
--   Iso-//→ n 𝕡base = [_]//

--   Iso-//→ (suc n) (𝕡loop (suc k , k<) i) (a , x) =
--     cong// n a (Iso-//→ n (𝕡loop (k , k<) i) x)
--   Iso-//→ (suc (suc n)) (𝕡loop (zero , tt) i) x =
--     eq// (λ i' → 𝕡loop (zero , _) i' 𝒗 glue'AdjT× (2 + n) zero i'
--       (unglue (i ∨ ~ i) x)) i

--   Iso-//→ n (𝕡looop (zero , k<) (zero , l<) i) = [_]//
--   Iso-//→ (suc n) (𝕡looop (suc k , k<) (suc l , l<) i) (a , x) =
--     cong// n a (Iso-//→ n (𝕡looop (k , k<) (l , l<) i) x)
--   Iso-//→ (suc (suc n)) (𝕡looop (zero , _) (suc (suc l) , l<) i) x =
--     eq// (λ i' → 𝕡looop (zero , _) (suc (suc l) , l<) i'
--                𝒗 glueBiAdjT×<SS n (l , l<) (~ i')
--                  (adjSq (2 + n) (2 + l) i i' (unglue (i ∨ ~ i) x))) i
--   Iso-//→ (suc (suc (suc n))) (𝕡looop (zero , _) (suc zero , _) i) x =
--     eq// (λ i' → 𝕡looop (zero , _) (suc zero , _) i'
--                𝒗 glueBiAdjT×< n (~ i') (unglue (i ∨ ~ i) x)) i
--   Iso-//→ (suc (suc n)) (𝕡looop (suc (suc k) , k<) (zero , _) i) x =
--     eq// (λ i' → 𝕡looop (suc (suc k) , k<) (zero , _) i'
--                𝒗 glueBiAdjT×<SS n (k , k<) i'
--                  (adjSq (2 + n) (2 + k) (~ i) (~ i') (unglue (i ∨ ~ i) x))) i

--   Iso-//→ (suc (suc (suc n))) (𝕡looop (suc zero , _) (zero , _) i) x =
--     eq// (λ i' → 𝕡looop (suc zero , _) (zero , _) i'
--                𝒗 glueBiAdjT×< n i' (unglue (i ∨ ~ i) x)) i

--   Iso-//→ (suc n) (𝕡comp (suc k , k<) (suc l , l<) i i₁) (a , x) =
--     cong// n a (Iso-//→ n  (𝕡comp (k , k<) (l , l<) i i₁) x)
--   Iso-//→ (suc (suc n)) (𝕡comp (zero , k<) (zero , l<) i i₁) x =
--     Iso-//→ (suc (suc n)) (𝕡loop (zero , l<) i₁) x

--   Iso-//→ (suc (suc n)) (𝕡comp (zero , _) (suc (suc l) , l<) i i₁) x =
--     {!!}
--   Iso-//→ (suc (suc (suc n))) (𝕡comp (zero , _) (suc zero , l<) i i₁) x =
--     {!!}

--   Iso-//→ (suc (suc n)) (𝕡comp (suc zero , k<) (zero , l<) i i₁) x =
--     {!!}
--   Iso-//→ (suc (suc (suc n))) (𝕡comp (suc (suc k) , k<) (zero , l<) i i₁) x =
--     {!!}

--   Iso-//→ (suc n) (𝕡invol (suc k , k<) i i₁) (a , x) =
--     cong// n a (Iso-//→ n  (𝕡invol (k , k<) i i₁) x)
--   Iso-//→ (suc (suc n)) (𝕡invol (zero , _) i j) =
--      (λ x → eq//-invol'' n x i j) ∘' 
--      (swap-01 ∘' unglue (i ∨ ~ i) ∘' unglue (j ∨ ~ j))
      
--   Iso-//→ (suc n) (𝕡comm (suc k , k<) (suc l , l<) x₁ i j) (a , x) =
--     cong// n a (Iso-//→ n (𝕡comm (k , k<) (l , l<) (pred-commT k l x₁) i j) x)
--   Iso-//→ (suc (suc n)) (𝕡comm (zero , k<) (suc (suc l) , l<) x₁ i j) =
--        eq//-commSS n (l , l<) i j
--     ∘' unglue (j ∨ ~ j)
--     ∘' unglue (i ∨ ~ i)

--   Iso-//→ n (𝕡braid k k< i i₁) x = {!!}
--   Iso-//→ n (𝕡squash x₁ 𝕡 𝕡₁ x₂ y x₃ y₁ i i₁ x₄) x = {!!}
  

-- -- --  -- -- --  Iso-//← : ∀ n → (↔// n) → Σ _ (𝕍₃ A n) 
-- -- --  -- -- --  Iso-//← n [ a ]// = 𝕡base , a 
-- -- --  -- -- --  Iso-//← n (eq// r i) = r i
-- -- --  -- -- --  Iso-//← n (comp// r s j i) = compPath-filler r s j i
-- -- --  -- -- --  Iso-//← n (squash// x x₁ p q r s i i₁ i₂) =
-- -- --  -- -- --    isGroupoidΣ (𝕡squash _ ) (isGroupoid𝕍₃ A isGrpA n)
-- -- --  -- -- --      _ _ _ _
-- -- --  -- -- --       (λ i j → Iso-//← n (r i j))
-- -- --  -- -- --       (λ i j → Iso-//← n (s i j))
-- -- --  -- -- --       i i₁ i₂
       
-- -- --  -- -- --  adjT-sec : ∀ n k a →
-- -- --  -- -- --    (cong (uncurry (Iso-//→ n)) (λ i → (𝕡loop k i) , (glueAdjT× n (fst k) i a)))
-- -- --  -- -- --    ≡ eq// (λ i → 𝕡loop k i , glueAdjT× n (fst k) i a) 
-- -- --  -- -- --  adjT-sec (suc n) (suc k , k<) (x , xs)  =
-- -- --  -- -- --    cong′ (cong′ (cong// n x)) (adjT-sec (n) (k , k<) (xs))
-- -- --  -- -- --  adjT-sec (suc (suc n)) (zero , _) _ = refl
  
-- -- --  -- -- --  Iso-//-sec-eq' :  ∀ n (p : ⟨ 𝕡Ω₂ n ⟩) a b
-- -- --  -- -- --      (P : PathP (λ i → 𝕍₃ A n (p i)) a b) →
-- -- --  -- -- --     (cong (uncurry (Iso-//→ n)) (λ i → p i , P i))
-- -- --  -- -- --       ≡ eq// (λ i → p i , P i)
-- -- --  -- -- --  Iso-//-sec-eq' n = elimℙrm≡ _ _
-- -- --  -- -- --      (λ _ → isPropΠ3 λ _ _ _ → squash// _ _ _ _)
-- -- --  -- -- --    (eq//-refl↔ n)
-- -- --  -- -- --    λ k xs x a b P →
-- -- --  -- -- --      let x' : cong (uncurry (Iso-//→ n))
-- -- --  -- -- --               (λ i → xs i , P-adjT n a b xs k P i) ≡
-- -- --  -- -- --                 eq// (λ i → xs i , P-adjT n a b xs k P i)
-- -- --  -- -- --          x' = x (adjT×^ (fst k) a) b (P-adjT n a b xs k P)

-- -- --  -- -- --          pp : cong (uncurry (Iso-//→ n))
-- -- --  -- -- --                 ((λ i → 𝕡loop k i , glueAdjT× n (fst k) i a) ∙
-- -- --  -- -- --                  (λ i → xs i , P-adjT n a b xs k P i))
-- -- --  -- -- --                 ≡
-- -- --  -- -- --                 eq//
-- -- --  -- -- --                 (↔×-trans n (glueAdjT× n (fst k) i0 a) (P-adjT n a b xs k P i0)
-- -- --  -- -- --                  (P-adjT n a b xs k P i1)
-- -- --  -- -- --                  (λ i → 𝕡loop k i , glueAdjT× n (fst k) i a)
-- -- --  -- -- --                  (λ i → xs i , P-adjT n a b xs k P i))
-- -- --  -- -- --          pp = (
-- -- --  -- -- --            congFunct (uncurry (Iso-//→ n))
-- -- --  -- -- --               (λ i → 𝕡loop k i , glueAdjT× n (fst k) i a)
-- -- --  -- -- --                (λ i → xs i , P-adjT n a b xs k P i))
-- -- --  -- -- --           ∙∙ (λ i → adjT-sec n k a i ∙ x' i) ∙∙
-- -- --  -- -- --            (sym (comp'// _  (↔×-trans n) _ _))
-- -- --  -- -- --      in  cong′ (cong (uncurry (Iso-//→ n)))
-- -- --  -- -- --            (sym (P-adjT-comp n a b xs k P))
-- -- --  -- -- --         ∙∙ pp ∙∙
-- -- --  -- -- --          cong′ eq// (P-adjT-comp n a b xs k P)


-- -- --  -- -- --  Iso-//-sec : ∀ n → section (uncurry (Iso-//→ n)) (Iso-//← n)
-- -- --  -- -- --  Iso-//-sec n = GQ.RelimSet.f (w n)
-- -- --  -- -- --   where
-- -- --  -- -- --   w : ∀ n → GQ.RelimSet (λ z → uncurry (Iso-//→ n) (Iso-//← n z) ≡ z)
-- -- --  -- -- --   RelimSet.truncB (w _) _ = squash// _ _
-- -- --  -- -- --   RelimSet.fb (w n) _ = refl
-- -- --  -- -- --   RelimSet.fbEq (w n) p = flipSquare
-- -- --  -- -- --     (Iso-//-sec-eq' n (cong fst p) _ _ (cong snd p))
   
-- -- --  -- -- -- --     -- funExt⁻
-- -- --  -- -- -- --     -- (congP (λ _ → funExt⁻)
-- -- --  -- -- -- --     --   (flipSquare
-- -- --  -- -- -- --     --     {!!}))
-- -- --  -- -- -- --   -- RelimSet.truncB (w _) x = squash// _ _
-- -- --  -- -- -- --   -- RelimSet.fb (w zero) a = refl
-- -- --  -- -- -- --   -- RelimSet.fb (w (suc n)) a = refl
-- -- --  -- -- -- --   -- RelimSet.fbEq (w zero) (p , P) i = {!!}
-- -- --  -- -- -- --   -- RelimSet.fbEq (w (suc n)) (p , P) =
-- -- --  -- -- -- --   --   {!!}
-- -- --  -- -- -- --   --   -- uncurry (Iso-//→ (suc n)) (Iso-//← (suc n) (Iso-//→ (suc n) {!p i!} {!!}))


-- -- --  -- -- -- --  Iso-//-ret-lem' : ∀ n k k< (a : A) (x// : ↔// n) → 
-- -- --  -- -- -- --     SquareP (λ i _ → Σ (ℙrm (suc n)) (𝕍₃ A (suc n)))
-- -- --  -- -- -- --       {!!}
-- -- --  -- -- -- --       {!!}
-- -- --  -- -- -- --       (λ i →
-- -- --  -- -- -- --         let (q , v) = Iso-//← n x// 
-- -- --  -- -- -- --         in (sucℙrm n q) ,
-- -- --  -- -- -- --            cons𝕍₃ A isGrpA n q a (v))
-- -- --  -- -- -- --       (λ i → Iso-//← (suc n)
-- -- --  -- -- -- --         (cong// n a x//))
-- -- --  -- -- -- --       -- (λ i v → Iso-//← (suc n)
-- -- --  -- -- -- --       --   (uncurry (Iso-//→ (suc n)) (𝕡loop (suc k , k<) i , (a , v))))
-- -- --  -- -- -- --  Iso-//-ret-lem' n k k< a i j = {!!}


-- -- --  -- -- --  Iso-//-ret-lem : ∀ n k k< (a : A) →
-- -- --  -- -- --     SquareP (λ i _ → adjT×^≡ {A = A} {n = n} k i → Σ (ℙrm (suc n)) (𝕍₃ A (suc n)))
-- -- --  -- -- --       refl
-- -- --  -- -- --       refl
-- -- --  -- -- --       (λ i v' →
-- -- --  -- -- --         let (q , v) = Iso-//← n (uncurry (Iso-//→ n)
-- -- --  -- -- --                       (𝕡loop (k , k<) i , (v'))) 
-- -- --  -- -- --         in (sucℙrm n q) ,
-- -- --  -- -- --            cons𝕍₃ A isGrpA n q a (v))
-- -- --  -- -- --       (λ i v → Iso-//← (suc n)
-- -- --  -- -- --         (cong// n a (Iso-//→ n (𝕡loop (k , k<) i) v)))
-- -- --  -- -- --       -- (λ i v → Iso-//← (suc n)
-- -- --  -- -- --       --   (uncurry (Iso-//→ (suc n)) (𝕡loop (suc k , k<) i , (a , v))))
-- -- --  -- -- --  Iso-//-ret-lem n k k< a i j = {!!}

-- -- --  -- -- --  Iso-//-ret : ∀ n → retract (uncurry (Iso-//→ n)) (Iso-//← n)
-- -- --  -- -- --  Iso-//-ret n = uncurry (R𝕡elimSet'.f (w n))
-- -- --  -- -- --   where
-- -- --  -- -- --   w : ∀ n → R𝕡elimSet'
-- -- --  -- -- --         (λ z →
-- -- --  -- -- --            (y : 𝕍₃ A n z) → Iso-//← n (uncurry (Iso-//→ n) (z , y)) ≡ (z , y))
-- -- --  -- -- --   R𝕡elimSet'.isSetA (w n) _ = isSetΠ
-- -- --  -- -- --     λ _ → isGroupoidΣ (𝕡squash _ ) (isGroupoid𝕍₃ A isGrpA n) _ _
-- -- --  -- -- --   R𝕡elimSet'.abase (w n) y = refl


-- -- --  -- -- --   R𝕡elimSet'.aloop (w (suc n)) (suc k , k<) = 
-- -- --  -- -- --     let X = R𝕡elimSet'.aloop (w n) (k , k<)
-- -- --  -- -- --     in  λ i (a , v) j →
-- -- --  -- -- --          hcomp
-- -- --  -- -- --              (λ z →
-- -- --  -- -- --                λ { (i = i0) →
-- -- --  -- -- --                 Iso-//← (suc n) (uncurry (Iso-//→ (suc n)) (𝕡base , (a , v)))
-- -- --  -- -- --                  ; (i = i1) →
-- -- --  -- -- --                 Iso-//← (suc n) (uncurry (Iso-//→ (suc n)) (𝕡base , (a , v)))
-- -- --  -- -- --                  ; (j = i0) → Iso-//-ret-lem n k k< a i z v
-- -- --  -- -- --                  ; (j = i1) → (𝕡loop (suc k , k<) i , (a , v))
-- -- --  -- -- --                  })
-- -- --  -- -- --              (sucℙrm n (fst (X i v j)) ,
-- -- --  -- -- --                cons𝕍₃ A isGrpA n (fst (X i v j)) a (snd (X i v j))) 

-- -- --  -- -- --   R𝕡elimSet'.aloop (w (suc (suc n))) (zero , tt) i (y) i₁ =
-- -- --  -- -- --     𝕡loop (zero , tt) i , y
   
-- -- --  -- -- -- -- -- --  -- Iso-//← : ∀ n → (↔// n) → {!Σ ? ?!}
-- -- --  -- -- -- -- -- --  -- Iso-//← = {!!}

-- -- --  -- -- -- -- -- -- -- -- EMelim.f w
-- -- --  -- -- -- -- -- -- -- --  where
-- -- --  -- -- -- -- -- -- -- --  w : EMelim (𝕡Ω₂ n) (λ z → em𝕍 n z → ↔// n)
-- -- --  -- -- -- -- -- -- -- --  EMelim.isGrpB w _ = isGroupoidΠ λ _ →  squash//
-- -- --  -- -- -- -- -- -- -- --  EMelim.b w = [_]//
-- -- --  -- -- -- -- -- -- -- --  EMelim.bPathP w g i xᵍ =
-- -- --  -- -- -- -- -- -- -- --    let x = {!xᵍ!}
-- -- --  -- -- -- -- -- -- -- --    in {!!}
-- -- --  -- -- -- -- -- -- -- --  -- eq// (g , {!x!}) i
-- -- --  -- -- -- -- -- -- -- --  EMelim.bSqP w = {!!}


-- -- --  -- -- -- -- -- -- -- -- Iso-//→ : ∀ n → ∀ emp →  (em𝕍 n) emp → (↔// n)
-- -- --  -- -- -- -- -- -- -- -- Iso-//→ n = EMelim.f w
-- -- --  -- -- -- -- -- -- -- --  where
-- -- --  -- -- -- -- -- -- -- --  w : EMelim (𝕡Ω₂ n) (λ z → em𝕍 n z → ↔// n)
-- -- --  -- -- -- -- -- -- -- --  EMelim.isGrpB w _ = isGroupoidΠ λ _ →  squash//
-- -- --  -- -- -- -- -- -- -- --  EMelim.b w = [_]//
-- -- --  -- -- -- -- -- -- -- --  EMelim.bPathP w g i xᵍ =
-- -- --  -- -- -- -- -- -- -- --    let x = {!xᵍ!}
-- -- --  -- -- -- -- -- -- -- --    in {!!}
-- -- --  -- -- -- -- -- -- -- --  -- eq// (g , {!x!}) i
-- -- --  -- -- -- -- -- -- -- --  EMelim.bSqP w = {!!}

-- -- --  -- -- -- -- -- -- -- -- -- Iso-// : ∀ n → Iso (Σ _ (em𝕍 n)) (↔// n)
-- -- --  -- -- -- -- -- -- -- -- -- Iso.fun (Iso-// n) = {!!}
-- -- --  -- -- -- -- -- -- -- -- -- Iso.inv (Iso-// n) = {!!}
-- -- --  -- -- -- -- -- -- -- -- -- Iso.rightInv (Iso-// n) = {!!}
-- -- --  -- -- -- -- -- -- -- -- -- Iso.leftInv (Iso-// n) = {!!}



-- --  module direct-FMSet₂-≃ (isGrpA : isGroupoid A) where

-- --   cons↔ : ∀ n a x y → (↔× n x y)
-- --                     → (↔× (suc n) (a , x) (a , y))
-- --   cons↔ n a x y =
-- --     cong λ (𝕡 , v) → sucℙrm n 𝕡 , cons𝕍₃ A isGrpA n 𝕡 a v


-- --   cong// : ∀ n → A → ↔// n → ↔// (suc n)
-- --   cong// n a' = GQ.Rrec.f w
-- --    where
-- --    w : Rrec// (↔// (suc n))
-- --    Rrec//.Bgpd w = squash//
-- --    Rrec//.fb w = [_]// ∘' (a' ,_)
-- --    Rrec//.feq w = eq// ∘ cons↔ n a' _ _ 
-- --    Rrec//.fsq w p r =
-- --       comp// _ _ ▷
-- --         cong′ eq// (sym (congFunct
-- --            (λ (𝕡 , v) → sucℙrm n 𝕡
-- --              , cons𝕍₃ A isGrpA n 𝕡 a' v) p r))

-- --   -- cong//' : ∀ n → A → ↔// n → ↔// (suc n)
-- --   -- cong//' n a' [ a ]// = [ a' , a ]//
-- --   -- cong//' n a' (eq// r₁ i) = eq// (cons↔ n a' _ _ r₁) i
-- --   -- cong//' n a' (comp// p r j i) =
-- --   --         (comp// _ _ ▷
-- --   --       cong′ eq// (sym (congFunct
-- --   --          (λ (𝕡 , v) → sucℙrm n 𝕡
-- --   --            , cons𝕍₃ A isGrpA n 𝕡 a' v) p r))) j i

-- --   -- cong//' n a' (squash// x x₁ p q r₁ s₁ i i₁ i₂) = {!!}

-- -- -- GQ.Rrec.f w
-- -- --    where
-- -- --    w : Rrec// (↔// (suc n))
-- -- --    Rrec//.Bgpd w = squash//
-- -- --    Rrec//.fb w = [_]// ∘' (a' ,_)
-- -- --    Rrec//.feq w = eq// ∘ cons↔ n a' _ _ 
-- -- --    Rrec//.fsq w p r =
-- -- --       comp// _ _ ▷
-- -- --         cong′ eq// (sym (congFunct
-- -- --            (λ (𝕡 , v) → sucℙrm n 𝕡
-- -- --              , cons𝕍₃ A isGrpA n 𝕡 a' v) p r))


-- --   cons↔-comm : ∀ (n : ℕ) → ∀ x y → (v : ↔// n) →
-- --       cong// (suc n) x (cong// n y v) ≡
-- --       cong// (suc n) y (cong// n x v) 
-- --   cons↔-comm n a a' [ v ]// = adjT// _ (zero , _) _
-- --   cons↔-comm n a a' (eq// r i) = {!!}
-- --   cons↔-comm n a a' (comp// r s j i) = {!!}
-- --   cons↔-comm n a a' (squash// v v₁ p q r₁ s₁ i i₁ i₂) = {!!}
-- --     -- GQ.RelimSet.f w
-- --     -- where
-- --     -- w : RelimSet
-- --     --       (λ z →
-- --     --          cong// (suc n) a (cong// n a' z) ≡
-- --     --          cong// (suc n) a' (cong// n a z))
-- --     -- RelimSet.truncB w = {!!}
-- --     -- RelimSet.fb w _ = adjT// _ (zero , _) _
-- --     -- RelimSet.fbEq w r = {!!}
-- --       -- adjT// (suc (suc n)) (zero , tt) () j

-- -- -- --   w : RRec {A = A} {B = Σ ℕ (↔//)}
-- -- -- --              (isGroupoidΣ
-- -- -- --                   (isSet→isGroupoid isSetℕ) λ _ → squash//)
-- -- -- --   RRec.[]* w = zero , [ _ ]//
-- -- -- --   RRec._∷*_ w a (k , v) = suc k , cong// k a v 
-- -- -- --   RRec.comm* w x y = uncurry {!!}
   
-- -- -- --   RRec.comm-inv* w = {!!}
-- -- -- --   RRec.commmL* w = {!!}
-- -- -- --   RRec.commmR* w = {!!}
-- -- -- --   RRec.commpL* w = {!!}
-- -- -- --   RRec.commpR* w = {!!}
-- -- -- --   RRec.hex* w = {!!}

-- -- -- --   f : FMSet2 A → Σ _ (↔//)
-- -- -- --   f = RRec.f {B = Σ ℕ (↔//)} w


-- -- module FMSet₂-≃ (A : Type ℓ) (isGrpA : isGroupoid A) where
-- --  w : RRec {B = Σ (Σ _ (ℙrm {true})) (λ (n , 𝕡) → (𝕍₃ A n 𝕡))}
-- --              (isGroupoidΣ
-- --                (isGroupoidΣ
-- --                  (isSet→isGroupoid isSetℕ) {!!})
-- --                 {!!}
-- --                 )
-- --  w = {!!}

-- --  f : FMSet2 A → Σ (Σ _ (ℙrm {true})) (uncurry (𝕍₃ A))
-- --  f = RRec.f w
  
