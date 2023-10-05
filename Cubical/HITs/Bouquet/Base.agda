{-

This file contains:

- Definition of the Bouquet of circles of a type aka wedge of A circles

-}
{-# OPTIONS --safe #-}

module Cubical.HITs.Bouquet.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

private
  variable
    ℓ : Level

data Bouquet (A : Type ℓ) : Type ℓ where
  base : Bouquet A
  loop : A → base ≡ base

Bouquet∙ : Type ℓ → Pointed ℓ
Bouquet∙ A = Bouquet A , base

elimProp : ∀ {A : Type ℓ} {ℓ'} {B : Bouquet A → Type ℓ'}
       → (∀ x → isProp (B x))
       → B base
       → ∀ x → B x
elimProp _ Bbase base = Bbase
elimProp isPropB Bbase (loop x i) =
  isProp→PathP (λ i → isPropB (loop x i)) Bbase Bbase i
