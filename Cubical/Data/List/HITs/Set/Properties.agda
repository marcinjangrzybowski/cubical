{-# OPTIONS --safe #-}

module Cubical.Data.List.HITs.Set.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Data.List.HITs.Set.Base

open import Cubical.Data.Empty as ⊥

import Cubical.Data.List.Base as B
import Cubical.Data.List.Properties as BP

import Cubical.Functions.Logic as L

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ


length0≡[] : ∀ {x : List A} → length x ≡ 0 → x ≡ []
length0≡[] =
  ElimProp.f
     (λ x → isPropΠ λ _ → trunc x [])
     (λ z → refl)
     (λ a p → ⊥.rec (snotz p))
     (λ {xs} {ys} px py p →
       let (px0 , py0) = m+n≡0→m≡0×n≡0 {length xs} {length ys} p
       in cong₂ _++_ (px px0) (py py0) ∙' ++-unit-r [])
      _



isContrLen0 : isContr (Σ (List A) λ x → length x ≡ 0)
fst isContrLen0 = [] , refl
snd isContrLen0 = λ y → Σ≡Prop (λ _ → isSetℕ _ _) (sym (length0≡[] (snd y)))

isContr[]≡[] : isContr ([] {A = A} ≡ [])
isContr[]≡[] = refl , λ p j i → length0≡[] {x = p i} (λ i₁ → length (p (i₁ ∨ i))) (~ j)

Iso-length0≡[] : ∀ {x : List A} → Iso (length x ≡ 0) (x ≡ [])
Iso.fun Iso-length0≡[] = length0≡[]
Iso.inv Iso-length0≡[] = cong length
Iso.rightInv Iso-length0≡[] _ = trunc _ _ _ _
Iso.leftInv Iso-length0≡[] a = isSetℕ _ _ _ _


IsEmpty : List A → hProp ℓ-zero
IsEmpty = 
   Rec.f isSetHProp
   L.⊤ (λ _ → L.⊥) L._⊓_
   L.⊓-identityʳ  L.⊓-identityˡ (λ _ by bz → sym (L.⊓-assoc _ by bz))



length0-≡-IsEmpty : (x : List A) → ((length x ≡ 0) , isSetℕ _ _) ≡ (IsEmpty x)
length0-≡-IsEmpty =
     ElimProp.f
      (λ _ → isSetHProp _ _)
      (L.⇔toPath (λ _ → _) λ _ → refl)
      (λ _ → L.⇔toPath snotz ⊥.rec)
      λ {xs} {ys} x y → L.⇔toPath
        (map-× (L.pathTo⇒ x) (L.pathTo⇒ y)
          ∘ m+n≡0→m≡0×n≡0 {length xs} {length ys})
      λ (isExs , isEys)  → cong₂ _+_ (L.pathTo⇐ x isExs) (L.pathTo⇐ y isEys)
       

fromList : B.List A → List A
fromList B.[] = []
fromList (x B.∷ xs) = x ∷ fromList xs

module _ (isSetA : isSet A) where

  isSetListA = BP.isOfHLevelList 0 isSetA

  toList : List A → B.List A
  toList =
    Rec.f
     isSetListA
     B.[] B.[_] B._++_ BP.++-unit-r (λ _ → refl) BP.++-assoc


  toList-fromList : ∀ l → toList (fromList l) ≡ l
  toList-fromList B.[] = refl
  toList-fromList (x B.∷ l) = cong (_ B.∷_) (toList-fromList l)

  fromList-toList : ∀ l → fromList (toList l) ≡ l
  fromList-toList =
    ElimProp.f (λ _ → trunc _ _)
      refl
      (++-unit-r ∘ [_])
      λ {xs} {ys} x y → h _ _ ∙ cong₂ _++_ x y
   where
     h : ∀ (xs ys : B.List A) →
          fromList (xs B.++ ys) ≡ fromList xs ++ fromList ys 
     h B.[] _ = sym (++-unit-l _)
     h (x B.∷ xs) ys = cong ([ x ] ++_) (h xs ys) ∙ (sym (++-assoc _ _ _)) 

  isoList : Iso (List A) (B.List A)
  fun isoList = toList
  inv isoList = fromList
  rightInv isoList = toList-fromList
  leftInv isoList = fromList-toList
