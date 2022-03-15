-- The (pre)category of (small) categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Categories where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Category.Precategory
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.HITs.SetTruncation

open import Cubical.Data.Sigma

module _ (ℓ ℓ' : Level) where
  open Precategory

  CatPrecategory : Precategory (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  CatPrecategory .ob = Category ℓ ℓ'
  CatPrecategory .Hom[_,_] = Functor
  CatPrecategory .id = 𝟙⟨ _ ⟩
  CatPrecategory ._⋆_ G H = H ∘F G
  CatPrecategory .⋆IdL _ = F-lUnit
  CatPrecategory .⋆IdR _ = F-rUnit
  CatPrecategory .⋆Assoc _ _ _ = F-assoc

-- TODO: what is required for Functor C D to be a set?

module _ (ℓ ℓ' : Level) where
  open Category

  Cat : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  Cat .ob = Σ (Category ℓ ℓ') λ x → isSet (x .ob)
  Cat .Hom[_,_] (A , _) (B , _) = Functor A B
  Cat .id = 𝟙⟨ _ ⟩ 
  Cat ._⋆_ G H = H ∘F G
  Cat .⋆IdL _ = F-lUnit
  Cat .⋆IdR _ = F-rUnit
  Cat .⋆Assoc _ _ _ = F-assoc
  Cat .isSetHom {y = (_ , B-isSet)} = isSet-Functor B-isSet

module _ (ℓ ℓ' : Level) where
  open Category

  CatT : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  CatT .ob = Category ℓ ℓ'
  CatT .Hom[_,_] A B = ∥ Functor A B ∥₂
  CatT .id = ∣ 𝟙⟨ _ ⟩ ∣₂  
  CatT ._⋆_ =  elim2 (λ _ _ → squash₂) λ G H → ∣ H ∘F G ∣₂
  CatT .⋆IdL = elim (λ _ → isProp→isSet (squash₂ _ _)) λ _ → cong ∣_∣₂ F-lUnit
  CatT .⋆IdR = elim (λ _ → isProp→isSet (squash₂ _ _)) λ _ → cong ∣_∣₂ F-rUnit
  CatT .⋆Assoc = elim3 (λ _ _ _ → isProp→isSet (squash₂ _ _)) λ _ _ _ →  cong ∣_∣₂ F-assoc
  CatT .isSetHom  = squash₂

