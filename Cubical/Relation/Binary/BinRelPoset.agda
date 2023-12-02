{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.BinRelPoset where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Binary.Order.Poset.Base


private
  variable
    ℓA ℓ≅A ℓA' ℓ≅A' : Level
    A : Type ℓA
    A' : Type ℓA'

BinRel⊆ : ∀ (A : Type ℓA) ℓ≅A →
  Rel (Rel A A ℓ≅A) (Rel A A ℓ≅A) (ℓ-max ℓA ℓ≅A) 
BinRel⊆ A ℓ≅A _r_ _r'_ = ∀ x y → x r y  → x r' y

open PosetStr
open IsPoset

BinRelPoset : ∀ (A : Type ℓA) ℓ≅A →
                Poset (ℓ-max ℓA (ℓ-suc ℓ≅A)) (ℓ-max ℓA ℓ≅A) 
fst (BinRelPoset A ℓ≅A) = PropRel A A ℓ≅A
_≤_ (snd (BinRelPoset A ℓ≅A)) = pulledbackRel (BinRel⊆ A ℓ≅A) fst
is-set (isPoset (snd (BinRelPoset A ℓ≅A))) = isSetPropRel
is-prop-valued (isPoset (snd (BinRelPoset A ℓ≅A))) _ (_ , pr) =
 isPropΠ3 λ _ _ _ → pr _ _ 
is-refl (isPoset (snd (BinRelPoset A ℓ≅A))) _ _ _ x = x
is-trans (isPoset (snd (BinRelPoset A ℓ≅A))) _ _ _ f g _ _ =
  g _ _ ∘ f _ _
is-antisym (isPoset (snd (BinRelPoset A ℓ≅A))) _ _ p q =
  PropRel≡ ((p _ _) , q _ _) 

