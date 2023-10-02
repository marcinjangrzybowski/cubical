{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Groups where

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Categories.Category.Base renaming (isIso to  isIsoC) 
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor.Base
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Foundations.Function


open import Cubical.Data.Sigma

module _ {ℓ : Level} where
  open Category hiding (_∘_)

  GroupCategory : Category (ℓ-suc ℓ) ℓ
  GroupCategory .ob = Group ℓ
  GroupCategory .Hom[_,_] = GroupHom
  GroupCategory .id = idGroupHom
  GroupCategory ._⋆_ = compGroupHom
  GroupCategory .⋆IdL f = GroupHom≡ refl
  GroupCategory .⋆IdR f = GroupHom≡ refl
  GroupCategory .⋆Assoc f g h = GroupHom≡ refl
  GroupCategory .isSetHom = isSetGroupHom

  Forget : Functor GroupCategory (SET ℓ) 
  Functor.F-ob Forget G = fst G , GroupStr.is-set (snd G)
  Functor.F-hom Forget = fst
  Functor.F-id Forget = refl
  Functor.F-seq Forget _ _ = refl

  isUnivalentGrp : isUnivalent {ℓ' = ℓ} GroupCategory
  isUnivalent.univ isUnivalentGrp G G' =
    precomposesToId→Equiv _
      (fst e) (funExt (Σ≡Prop isPropIsIso
              ∘ Σ≡Prop (λ _ → isPropIsGroupHom _ _)
              ∘ λ _ → transportRefl _)) (snd e)
    where

     e : CatIso _ G G' ≃ (G ≡ G')
     e = Σ-cong-equiv-prop (idEquiv _)
            isPropIsIso (λ x → isPropIsEquiv (fst x)) w w'
       ∙ₑ Σ-assoc-swap-≃ ∙ₑ GroupPath G G'
      where
       w : ∀ x → isIsoC GroupCategory x → isEquiv (fst x)
       w x (isiso (f , _) sec ret) =
         isoToIsEquiv w' where
          w' : Iso _ _
          Iso.fun w' = _
          Iso.inv w' = f
          Iso.rightInv w' b i = fst (sec i) b
          Iso.leftInv w' a i = fst (ret i) a
       w' : ∀ x → isEquiv (fst x) → isIsoC GroupCategory x
       isIsoC.inv (w' x x₁) = invEq (_ , x₁) ,
         isGroupHomInv ((fst x , x₁) , (snd x))
       isIsoC.sec (w' x x₁) =
         Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt (secEq (_ , x₁)))
       isIsoC.ret (w' x x₁) =
         Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt (retEq (_ , x₁)))
