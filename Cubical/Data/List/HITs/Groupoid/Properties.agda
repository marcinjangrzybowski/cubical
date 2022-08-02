{-# OPTIONS --safe #-}

module Cubical.Data.List.HITs.Groupoid.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence


open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Data.List.HITs.Groupoid.Base

open import Cubical.Data.Empty as ⊥

import Cubical.Data.List.Base as B
import Cubical.Data.List.Properties as BP

import Cubical.Functions.Logic as L

open import Cubical.HITs.GroupoidTruncation using (∥_∥₃;∣_∣₃;squash₃)
import Cubical.HITs.GroupoidTruncation as GT


open Iso


private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

fromList : B.List A → List A
fromList = B.foldr _∷_ []


module _ (isGroupoidA : isGroupoid A) where

  toList : List A → B.List A
  toList =
    Rec.f
     (BP.isOfHLevelList 1 isGroupoidA)
     B.[] B.[_] B._++_ BP.++-unit-r (λ _ → refl) BP.++-assoc
     (B.ind (λ _ → refl) λ a → congSqP (λ _ _ → a B.∷_) ∘_)
     (B.ind (BP.++-assoc) λ a f _ _ → cong (a B.∷_) ∘ (f _ _))
     (B.ind (λ by bz bw i j → BP.++-assoc by bz bw (j ∨ (~ i)))
       (λ a x _ _ → congSqP (λ _ _ → a B.∷_) ∘ (x _ _)))
     (B.ind (λ by bz bw i j → BP.++-assoc by bz bw (j ∧ (~ i)))
       λ a x _ _ _ → congSqP (λ _ _ → a B.∷_) (x _ _ _))
     
  toList-fromList : ∀ l → toList (fromList l) ≡ l
  toList-fromList B.[] = refl
  toList-fromList (_ B.∷ l) = cong (_ B.∷_) (toList-fromList l)

  fromList-toList : ∀ l → fromList (toList l) ≡ l
  fromList-toList =
     ElimSet.f (λ _ → trunc _ _)
       refl
       (++-unit-r ∘ [_])
       (λ {xs} {ys} x y → h (toList xs) (toList ys) ∙ cong₂ _++_ x y)
       unit-r-case
       (λ b i j → hcomp
         (λ k →
           λ { (i = i1) → b (j ∧ k)
             ; (j = i0) → fromList (toList (b i1))
             ; (j = i1) → ++-unit-l (b k) i
              }) (++-unit-l (b i0) (i ∨  ~ j)))
       assoc-case
  
   where

     h : ∀ (xs ys : B.List A) → fromList (xs B.++ ys) ≡ fromList xs ++ fromList ys
     h = B.ind (sym ∘ ++-unit-l ∘ fromList) (λ _ → (_∙ (sym (++-assoc _ _ _)) ∘ cong (_ ∷_ )) ∘_)
     
     unit-r-case : {xs : List A} (b : fromList (toList xs) ≡ xs) → _
     unit-r-case b i j =
       hcomp (λ k →
           λ { (i = i1) → b (j ∧ k)
             ; (j = i0) → fromList (BP.++-unit-r (toList (b i1)) i)
             ; (j = i1) → ++-unit-r (b k) i
              }) (sq (toList (b i1)) i j)

       where
        sq : (xs : B.List A) → Square (h xs B.[]) (λ _ → fromList xs) _ _
        sq B.[] i j = lem-pqpr⁻ {p = refl} {q = sym (++-unit-l [])} {sym (++-unit-r [])}
             (cong sym (sym ++-unit-lr[])) (~ i) j

        sq xs'@(x B.∷ xs) i j = 
          hcomp (λ k →
              λ { (i = i1) → fromList xs'
                ; (j = i0) → cong fromList (BP.++-unit-r xs') i
                ; (j = i1) → ++-assoc-[]-r [ x ] (fromList xs) i (~ k)
                 }) ([ x ] ++ sq xs i j)    


     assoc-case : {xs ys zs : List A} (bx : fromList (toList xs) ≡ xs)
      (by : fromList (toList ys) ≡ ys) (bz : fromList (toList zs) ≡ zs) →
      _
     assoc-case bx by bz =
       (cong ((h (toList (bx i1 ++ by i1)) (toList (bz i1))) ∙_)
          (cong₂-∙L _++_ _ (cong₂ _++_ bx by) bz))
           ∙ assoc _ _ _ ◁
          (λ i →
            (sq (toList (bx i1)) (toList (by i1)) (toList (bz i1)) i)
            ∙ λ j → ++-assoc (bx j) (by j) (bz j) i)
       ▷ (sym (assoc _ _ _)
         ∙ cong ((h (toList (bx i1)) (toList (by i1 ++ bz i1))) ∙_)
           (sym (cong₂-∙L (λ a b → b ++ a) _ _ _)))

      where
        sq : (xs ys zs : B.List A) → Square
           (h (xs B.++ ys) zs ∙ cong (_++ _) (h xs ys))
           (h xs (ys B.++ zs) ∙ cong (_ ++_) (h ys zs))
           (cong (fromList) (BP.++-assoc xs ys zs))
           (++-assoc _ _ _)
        sq B.[] by bz i j = hcomp
                 (λ k → λ { (i = i1) → hcomp
                             (λ l → λ { (k = i0) → (h by bz) (j ∧ l)
                                      ; (j = i0) → fromList (by B.++ bz)
                                      ; (j = i1) → ++-unit-l (h by bz l) (~ k)
                                      }) (++-unit-l (fromList (by B.++ bz)) (~ k ∨ ~ j))
                          ; (j = i0) → fromList (by B.++ bz)
                          ; (j = i1) → ++-assoc-[]-l (fromList by) (fromList bz) (~ k) i
                          }) (h by bz j)

        sq (x B.∷ bx) by bz i j =
         hcomp
         (λ k → λ {
              (i = i0) →
                ((λ j → hcomp
              (λ l → λ { (j = i0) → x ∷ compPath-filler pUl pUr l (~ k)
                       ; (j = i1) → ++-assoc [ x ] ((h bx by) (l ∧ ~ k)) bz' (~ l ∨ ~ k)
                       ; (k = i0) → x ∷ pUr l }) (x ∷ pUl (j ∨ ~ k)))
              ∙ λ j → hcomp
              (λ l → λ { (j = i0) → ++-assoc [ x ] ((h bx by) (~ k)) bz' (~ k)
                       ; (j = i1) → ++-pentagon-□ [ x ] bx' by' bz' (~ l) (~ k)
                       ; (k = i0) → [ x ] ++ ++-assoc bx' by' bz' (l ∧ j) 
                       ; (k = i1) → compPath-filler (cong (x ∷_) (h bx by))
                            (sym (++-assoc [ x ] bx' by')) l j ++ bz' 
                       }) (++-assoc [ x ] ((h bx by) (j ∨ ~ k)) bz' (~ k))) j
            ; (i = i1) → ((λ j → hcomp
              (λ l → λ { (j = i0) → x ∷ compPath-filler pDl pDr l (~ k)
                       ; (j = i1) → ++-assoc [ x ] bx' ((h by bz) (l ∧ ~ k)) (~ l ∨ ~ k)
                       ; (k = i0) → x ∷ pDr l
                       }) (x ∷ pDl (j ∨ ~ k)))
                ∙ λ j → ++-assoc [ x ] bx' ((h by bz) (j ∨ ~ k)) (~ j ∧ ~ k)) j
            ; (j = i0) → x ∷ sq bx by bz i (~ k)
            ; (j = i1) → ++-pentagon-△ [ x ] bx' by' bz' (~ i) (~ k)
            })                    
         (((λ _ → x ∷ ++-assoc bx' by' bz' i)
            ∙ invSides-filler (sym (++-assoc [ x ] bx' (by' ++ bz')))
               (cong (x ∷_) (sym (++-assoc bx' by' bz'))) (~ i)) j)

           where
             bx' = fromList bx
             by' = fromList by
             bz' = fromList bz          

             pUl = h (bx B.++ by) bz
             pUr = cong (_++ bz') (h bx by)
             pDl = h bx (by B.++ bz)
             pDr = cong (_++_ bx') (h by bz)


  isoList : Iso (B.List A) (List A) 
  fun isoList = fromList
  inv isoList = toList
  rightInv isoList = fromList-toList
  leftInv isoList = toList-fromList

  ≃List : B.List A ≃ List A
  ≃List = isoToEquiv isoList

  lengthB : PathP (λ i → ua ≃List i → ℕ)           
           B.length
           length
  lengthB =
    ua→ (B.ind refl (λ _ → cong suc))

  ++-B : PathP (λ i → ua ≃List i → ua ≃List i → ua ≃List i)
           B._++_
           _++_
  ++-B = ua→ λ a → ua→ λ b → ua-gluePath _ (h a b) 

       where
         h : (a b : B.List A) → _ ≡ _
         h B.[] b = sym (++-unit-l _)
         h (x B.∷ a) b = cong (x ∷_) (h a b) ∙ sym (++-assoc [ x ] _ _)


map-ListG : ( A → ∥ B ∥₃) → List A → List B
map-ListG f =
  Rec.f trunc
   []
   ((GT.rec trunc [_]) ∘ f) _++_
   ++-unit-r ++-unit-l ++-assoc ++-triangle
   ++-pentagon-diag ++-pentagon-△ ++-pentagon-□

map-List : (A → B) → List A → List B
map-List f =
  Rec.f trunc
   []
   ([_] ∘ f) _++_
   ++-unit-r ++-unit-l ++-assoc ++-triangle
   ++-pentagon-diag ++-pentagon-△ ++-pentagon-□


IsoTrunc : Iso (List A) (List ∥ A ∥₃)
Iso.fun IsoTrunc = map-List ∣_∣₃
Iso.inv IsoTrunc = map-ListG (idfun _)
Iso.rightInv IsoTrunc = 
  Elim.f
    (λ _ → isSet→isGroupoid (trunc _ _))
    refl
    (GT.elim (λ _ → isSet→isGroupoid (trunc _ _)) λ _ → refl)
    (λ x y → cong₂ _++_ x y)
    (λ b i j → ++-unit-r (b j) i)
    (λ b i j → ++-unit-l (b j) i)
    (λ bx by bz i j → ++-assoc (bx j) (by j) (bz j) i)
    (λ bx by i j k → ++-triangle (bx k) (by k) i j)
    (λ bx by bz bw i j → ++-pentagon-diag (bx j) (by j) (bz j) (bw j) i)
    (λ bx by bz bw i j k → ++-pentagon-△ (bx k) (by k) (bz k) (bw k) i j)
    (λ bx by bz bw i j k → ++-pentagon-□ (bx k) (by k) (bz k) (bw k) i j)
    
Iso.leftInv IsoTrunc = 
  Elim.f
    (λ _ → isSet→isGroupoid (trunc _ _))
    refl
    (λ _ → refl)
    (λ x y → cong₂ _++_ x y)
    (λ b i j → ++-unit-r (b j) i)
    (λ b i j → ++-unit-l (b j) i)
    (λ bx by bz i j → ++-assoc (bx j) (by j) (bz j) i)
    (λ bx by i j k → ++-triangle (bx k) (by k) i j)
    (λ bx by bz bw i j → ++-pentagon-diag (bx j) (by j) (bz j) (bw j) i)
    (λ bx by bz bw i j k → ++-pentagon-△ (bx k) (by k) (bz k) (bw k) i j)
    (λ bx by bz bw i j k → ++-pentagon-□ (bx k) (by k) (bz k) (bw k) i j)


IsoTrunc₃ : Iso (List A) (∥ B.List A ∥₃)
IsoTrunc₃ = compIso IsoTrunc (compIso (invIso (isoList (squash₃))) BP.ListTrunc₃Iso)
