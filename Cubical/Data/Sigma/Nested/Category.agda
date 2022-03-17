{-

The purpose of this module is to provide the way of
turning functions from nested Sigma Types into functions of multiple arguments

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Sigma.Nested.Category where


open import Cubical.Data.Nat

open import Cubical.Data.Vec
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything renaming (_∘_ to _∘→_)

open import Cubical.Categories.Category.Precategory
open import Cubical.Categories.Category

open import Cubical.Categories.TypesOfCategories.TypeCategory

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying




module ContextesPrecategory (ℓ : Level) where

  open Precategory

  CTX : Precategory (ℓ-suc ℓ) ℓ
  ob CTX = Σ _ (Sig ℓ)
  CTX .Hom[_,_] Γ Δ = NestedΣᵣ (snd Γ) → NestedΣᵣ (snd Δ) 
  Precategory.id CTX = idfun _
  _⋆_ CTX F G = G ∘→ F
  ⋆IdL CTX _ = refl
  ⋆IdR CTX _ = refl
  ⋆Assoc CTX _ _ _ = refl


module ContextesCategory (ℓ : Level) where

  open Category

  CTX : Category (ℓ-suc ℓ) ℓ
  ob CTX = Σ _ (Sig ℓ)
  CTX .Hom[_,_] Γ Δ = NestedΣᵣ (snd Γ) → NestedΣᵣ (snd Δ) 
  Category.id CTX = idfun _
  _⋆_ CTX F G = G ∘→ F
  ⋆IdL CTX _ = refl
  ⋆IdR CTX _ = refl
  ⋆Assoc CTX _ _ _ = refl
  isSetHom CTX = {!!}


  
  isTypeCategory-CTX : isTypeCategory CTX
  isTypeCategory-CTX .isTypeCategory.Ty[_] (_ , Γ) = NestedΣᵣ Γ → Type ℓ
  fst (isTypeCategory.cext isTypeCategory-CTX (n , Γ) A) = (suc n) , sig-n+1.from n (Γ , A) 
  snd (isTypeCategory.cext isTypeCategory-CTX (n , Γ) A) x = {!dropLastΣᵣ {n = n} _ ?!}  
  isTypeCategory.reindex isTypeCategory-CTX = {!!}
  isTypeCategory.q⟨_,_⟩ isTypeCategory-CTX = {!!}
  isTypeCategory.sq isTypeCategory-CTX = {!!}
  isTypeCategory.isPB isTypeCategory-CTX = {!!}
