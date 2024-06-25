{-

Groupoid quotients:

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.GroupoidQuotients.Properties where

open import Cubical.HITs.GroupoidQuotients.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function

open import Cubical.Functions.Surjection

open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.HITs.PropositionalTruncation as PropTrunc using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.HITs.SetTruncation as SetTrunc using (∥_∥₂; ∣_∣₂; squash₂)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.Algebra.AbGroup.Base

import Cubical.HITs.EilenbergMacLane1 as EM

-- Type quotients

private
  variable
    ℓA ℓR ℓ : Level
    A : Type ℓA
    R : A → A → Type ℓR

elimSet : (Rt : BinaryRelation.isTrans R)
     → {B : A // Rt → Type ℓ}
     → ((x : A // Rt) → isSet (B x))
     → (f : (a : A) → B [ a ])
     → ({a b : A} (r : R a b) → PathP (λ i → B (eq// r i)) (f a) (f b))
     → (x : A // Rt)
     → B x
elimSet Rt Bset f feq [ a ] = f a
elimSet Rt Bset f feq (eq// r i) = feq r i
elimSet Rt Bset f feq (comp// {a} {b} {c} r s i j) =
  isSet→SquareP (λ i j → Bset (comp// r s i j))
    (λ j → feq r j) (λ j → feq (Rt a b c r s) j)
    (λ i → f a) (λ i → feq s i) i j
elimSet Rt Bset f feq (squash// x y p q r s i j k) =
  isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (Bset x))
    _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (squash// x y p q r s) i j k
  where
    g = elimSet Rt Bset f feq

elimProp : (Rt : BinaryRelation.isTrans R)
         → {B : A // Rt → Type ℓ}
         → ((x : A // Rt) → isProp (B x))
         → ((a : A) → B [ a ])
         → (x : A // Rt)
         → B x
elimProp Rt Brop f x =
  elimSet Rt (λ x → isProp→isSet (Brop x)) f (λ r → isProp→PathP (λ i → Brop (eq// r i)) (f _) (f _)) x

elimProp2 : (Rt : BinaryRelation.isTrans R)
          → {C : A // Rt → A // Rt → Type ℓ}
         → ((x y : A // Rt) → isProp (C x y))
         → ((a b : A) → C [ a ] [ b ])
         → (x y : A // Rt)
         → C x y
elimProp2 Rt Cprop f = elimProp Rt (λ x → isPropΠ (λ y → Cprop x y))
                                   (λ x → elimProp Rt (λ y → Cprop [ x ] y) (f x))

isSurjective[] : (Rt : BinaryRelation.isTrans R)
               → isSurjection (λ a → [ a ])
isSurjective[] Rt = elimProp Rt (λ x → squash₁) (λ a → ∣ a , refl ∣₁)

elim : (Rt : BinaryRelation.isTrans R)
     → {B : A // Rt → Type ℓ}
     → ((x : A // Rt) → isGroupoid (B x))
     → (f : (a : A) → B [ a ])
     → (feq : {a b : A} (r : R a b) → PathP (λ i → B (eq// r i)) (f a) (f b))
     → ({a b c : A} (r : R a b) (s : R b c)
           → SquareP (λ i j → B (comp// r s i j))
           (feq r) (feq (Rt a b c r s)) (λ j → f a) (feq s))
     → (x : A // Rt)
     → B x
elim Rt Bgpd f feq fcomp [ a ] = f a
elim Rt Bgpd f feq fcomp (eq// r i) = feq r i
elim Rt Bgpd f feq fcomp (comp// r s i j) = fcomp r s i j
elim Rt Bgpd f feq fcomp (squash// x y p q r s i j k) =
  isOfHLevel→isOfHLevelDep 3 Bgpd
    _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (squash// x y p q r s) i j k
  where
    g = elim Rt Bgpd f feq fcomp

rec : (Rt : BinaryRelation.isTrans R)
    → {B : Type ℓ}
    → isGroupoid B
    → (f : A → B)
    → (feq : {a b : A} (r : R a b) → f a ≡ f b)
    → ({a b c : A} (r : R a b) (s : R b c)
          → Square (feq r) (feq (Rt a b c r s)) refl (feq s))
    → (x : A // Rt)
    → B
rec Rt Bgpd = elim Rt (λ _ → Bgpd)



module _ {ℓ ℓ'} (A : Type ℓ) (abase : A) (isGroupoidA : isGroupoid A)
                (C : A → Type ℓ') (isGroupoidC : ∀ a → isGroupoid (C a)) where
 L : Group ℓ
 L = makeGroup (refl {_} {A} {abase})
       _∙_ sym (isGroupoidA _ _)
         assoc (sym ∘ rUnit) (sym ∘ lUnit)
         rCancel lCancel

 LR : Rel (C abase) (C abase) (ℓ-max ℓ ℓ')
 LR x y  = Σ (fst L) λ l → PathP (λ i → C (l i)) x y

 LRT : BinaryRelation.isTrans LR
 fst (LRT x y z (p , P) (q , Q)) = p ∙ q
 snd (LRT x y z (p , P) (q , Q)) = compPathP' {B = C} P Q

 /L : Type (ℓ-max ℓ ℓ')
 /L = (C abase) // LRT

 ΣC : Type (ℓ-max ℓ ℓ')
 ΣC = Σ _ C

 toΣ : /L → ΣC
 toΣ = rec
   LRT
   (isGroupoidΣ isGroupoidA isGroupoidC)
   (abase ,_)
    ΣPathP
   zz
  where
   zz : {a b c : C abase} (r : LR a b) (s : LR b c) →
      Square (ΣPathP r) (ΣPathP (LRT a b c r s)) refl (ΣPathP s)
   fst (zz (p , P) (q , Q) i j) = compPath-filler p q i j
   snd (zz (p , P) (q , Q) i j) = compPathP'-filler {B = C} P Q i j 

