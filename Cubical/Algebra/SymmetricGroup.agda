{-# OPTIONS --safe #-}
module Cubical.Algebra.SymmetricGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Fin using (Fin ; isSetFin)
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
-- open import Cubical.Algebra.Group.Subgroup

private
  variable
    ℓ : Level

Symmetric-Group : (X : Type ℓ) → isSet X → Group ℓ
Symmetric-Group X isSetX = makeGroup (idEquiv X) compEquiv invEquiv (isOfHLevel≃ 2 isSetX isSetX)
  compEquiv-assoc compEquivEquivId compEquivIdEquiv invEquiv-is-rinv invEquiv-is-linv

SetIso-Group : (X : Type ℓ) → isSet X → Group ℓ
SetIso-Group X isSetX = makeGroup (idIso)
  compIso invIso (isSet-SetsIso isSetX isSetX)
  (λ _ _ _ → iso= refl refl)
  (λ _ → iso= refl refl)
  (λ _ → iso= refl refl)
  (λ x → iso= (funExt (Iso.leftInv x)) (funExt (Iso.leftInv x)))
  (λ x → iso= (funExt (Iso.rightInv x)) (funExt (Iso.rightInv x)))

 where

  iso= = SetsIso≡ isSetX isSetX 

hSetLoop-Group : (X : Type ℓ) → isSet X → Group (ℓ-suc ℓ)
hSetLoop-Group X isSetX = makeGroup {G = X ≡ X} refl
  _∙_ sym (isOfHLevel≡ 2 isSetX isSetX)
  assoc
  (sym ∘ rUnit)
  (sym ∘ lUnit)
  rCancel
  lCancel

-- Finite symmetrics groups

SG-SI : (X : Type ℓ) → (isSetX : isSet X) →
         GroupIso
           (SetIso-Group X isSetX)
           (Symmetric-Group X isSetX)
fst (SG-SI X isSetX) = isSet→Iso-Iso-≃ isSetX isSetX
IsGroupHom.pres· (snd (SG-SI X isSetX)) _ _ = equivEq refl
IsGroupHom.pres1 (snd (SG-SI X isSetX)) = equivEq refl
IsGroupHom.presinv (snd (SG-SI X isSetX)) _ = equivEq refl

Sym : ℕ → Group _
Sym n = Symmetric-Group (Fin n) isSetFin

SymmetricGroup→Hom : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (isSetA : isSet A) (isSetB : isSet B)
                      → GroupHom (Symmetric-Group A isSetA)
                                 (Symmetric-Group (A → B) (isSet→ isSetB))
fst (SymmetricGroup→Hom isSetA  isSetB) = preCompEquiv ∘ invEquiv
IsGroupHom.pres· (snd (SymmetricGroup→Hom isSetA isSetB)) _ _ = equivEq refl
IsGroupHom.pres1 (snd (SymmetricGroup→Hom isSetA isSetB)) = equivEq refl
IsGroupHom.presinv (snd (SymmetricGroup→Hom isSetA  isSetB)) _ = equivEq refl

