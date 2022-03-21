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

open import Cubical.Categories.Category.Precategory hiding (_^op)
open import Cubical.Categories.Category

open import Cubical.Categories.TypesOfCategories.TypeCategory

open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf


open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying


open import Cubical.Categories.Yoneda

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
  open Functor

  CTX : Category (ℓ-suc ℓ) ℓ
  ob CTX = Σ[ n ∈ ℕ ] Σ[ Γ ∈ Sig ℓ n ] isSet (NestedΣᵣ Γ)
  CTX .Hom[_,_] (_ , Γ , _) (_ , Δ , _) = NestedΣᵣ Γ → NestedΣᵣ Δ 
  Category.id CTX = idfun _
  _⋆_ CTX F G = G ∘→ F
  ⋆IdL CTX _ = refl
  ⋆IdR CTX _ = refl
  ⋆Assoc CTX _ _ _ = refl
  isSetHom CTX {_} {_ , _ , isSet-NestedΣᵣ-Γ } = isSet→ isSet-NestedΣᵣ-Γ

  isTypeCategory-CTX : isTypeCategory CTX
  isTypeCategory-CTX .isTypeCategory.Ty[_] (_ , Γ , _) = NestedΣᵣ Γ → hSet ℓ
  fst (isTypeCategory.cext isTypeCategory-CTX (n , Γ , isSet-NestedΣᵣ-Γ) A) =
     (suc n) , sig-n+1.from n (Γ , fst ∘→ A) , isOfHLevelRetractFromIso 2 (nestedΣᵣ-n+1.isom-from n (Γ , fst ∘→ A)) (isSetΣ (isSet-NestedΣᵣ-Γ) (snd ∘→ A)) 
  snd (isTypeCategory.cext isTypeCategory-CTX (n , Γ , _) A) = dropLastΣᵣ' Γ (fst ∘→ A)  
  isTypeCategory.reindex isTypeCategory-CTX F = _∘→ F 
  isTypeCategory.q⟨_,_⟩ isTypeCategory-CTX {(n , Γ , _)} {(n' , Γ' , _)} f A =
        (Iso.inv (nestedΣᵣ-n+1.isom-from n' _))
        ∘→  (_ ,_ ) ∘→  snd
        ∘→
        (Iso.fun (nestedΣᵣ-n+1.isom-from n _))
  isTypeCategory.sq isTypeCategory-CTX {_} {(n' , _ , _)} _ _ =
        funExt λ _ → cong fst (sym ((Iso.rightInv (nestedΣᵣ-n+1.isom-from n' _)) _))
  fst (isTypeCategory.isPB isTypeCategory-CTX {(n , Γ , _)} {(n' , Γ' , _)} f A {(n* , Γ* , _)} h k H') = 
     (w , funExt w' , funExt w'')

    where
      w : NestedΣᵣ Γ* → NestedΣᵣ (sig-n+1.from n (Γ , (λ x → fst (A (f x)))))
      w x = Iso.inv (nestedΣᵣ-n+1.isom-from n _)
             (h x , subst (fst ∘→ A ) (funExt⁻ (sym H') x) (snd (Iso.fun (nestedΣᵣ-n+1.isom-from n' _) (k x)))) 

      w' : _
      w' _ = cong fst (sym (Iso.rightInv (nestedΣᵣ-n+1.isom-from n (Γ , (λ x₁ → fst (A (f x₁))))) _))

      w'' : _
      w'' x =          
          (invEq (equivAdjointEquiv (isoToEquiv (nestedΣᵣ-n+1.isom-from n' (Γ' , fst ∘→ A)))) (ΣPathP ((sym (funExt⁻ H' x)) , transport-filler _ _)))
         ∙  cong  ((Iso.inv (nestedΣᵣ-n+1.isom-from n' (Γ' , fst ∘→ A))) ∘→ λ a → f (fst a) , (snd a)) ((sym (Iso.rightInv (nestedΣᵣ-n+1.isom-from n (Γ , fst ∘→ A ∘→ f)) _)))

  snd (isTypeCategory.isPB isTypeCategory-CTX {n , Γ , isSet-NestedΣᵣ-Γ} {n' , Γ'} f A {n* , Γ*} h k H') (ww , ww' , ww''') = 
     Σ≡Prop (λ _ → isProp× (isSet→ isSet-NestedΣᵣ-Γ _ _) (isSet→ ((snd
        (snd (fst (isTypeCategory.cext isTypeCategory-CTX (n' , Γ') A))))) _ _)) {!!}
