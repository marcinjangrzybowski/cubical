{-# OPTIONS --safe #-}

module Cubical.HITs.Bouquet.Discrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li
open import Cubical.Data.Sum

open import Cubical.HITs.Bouquet.Base
open import Cubical.Algebra.Group.Free


private
  variable
    ℓ : Level

module _ {A : Type ℓ} (_≟_ : Discrete A) where

  open NormalForm A

  open Discrete _≟_


  CodeBouquet : Bouquet A → Type ℓ
  CodeBouquet base = Σ _ IsNormalised
  CodeBouquet (loop a i) = ua (η·≃ (true , a)) i

  co→ : ∀ x → base ≡ x → CodeBouquet x
  co→ x p = subst CodeBouquet p ([] , lower)

  co←base-step : Bool × A → Path (Bouquet A) base base

  co←base-step (b , a) = if b then (idfun _) else sym $ loop a

  co←base : [𝟚× A ] → Path (Bouquet A) base base
  co←base = Li.rec refl (flip _∙_ ∘ co←base-step)

  co←Sq' : (a : A) → (x : [𝟚× A ]) (y : IsNormalised x) →
      ∀ u → PathP (λ i → base ≡ loop a i)
      (λ i → Li.rec (λ _ → base) (flip _∙_ ∘ co←base-step) x i)
      (λ i → Li.rec (λ _ → base) (flip _∙_ ∘ co←base-step) (preη· (true , a) x u )
       i)
  co←Sq' a ((false , snd₁) ∷ xs) y (yes p) =
    cong (λ x' → co←base ((false , x') ∷ xs)) (cong snd (sym p))
      ◁ symP (compPath-filler (co←base xs) (sym (loop a)))
  co←Sq' a xs y (no ¬p) = compPath-filler _ _
  co←Sq' a ((true , snd₁) ∷ xs) y (yes p) = ⊥.rec (true≢false (cong fst p))

  co←Sq : (a : A) → SquareP (λ i j →  ua (η·≃ (true , a)) i → Bouquet A)
                       (λ j x → co←base (fst x) j)
                       (λ j x → co←base (fst x) j)
                       (λ i _ → base)
                       (λ i _ → loop a i)
  co←Sq a = congP (λ _ → funExt) (ua→ (uncurry
     (λ xs y → co←Sq' a xs y (HeadIsRedex? ((true , a) ∷ xs)))))

  co← : ∀ x → CodeBouquet x → base ≡ x
  co← base = co←base ∘ fst
  co← (loop a i) x j = co←Sq a i j x

  coSec : ∀ x → section (co← x) (co→ x)
  coSec _ = J (λ x b → co← x (co→ x b) ≡ b) refl

  coRet : (x : [𝟚× A ]) (y : IsNormalised x) →
            fst (subst CodeBouquet (co← base (x , y)) ([] , lower))
                  ≡ x
  coRet [] y = refl
  coRet (x@(b , a) ∷ xs) y =
    cong fst (substComposite CodeBouquet (co← base (xs , y ∘ inr))
      (co←base-step x) _)
      ∙∙
      cong (fst ∘ subst CodeBouquet (co←base-step x))
         (Σ≡Prop isPropIsNormalised (coRet xs (y ∘ inr))) ∙∙
      lem b xs (y ∘ inr) ∙ η·∷ x xs (y ∘ inl)

   where
   lem : ∀ b xs y → fst
      (subst CodeBouquet (co←base-step (b , a)) (xs , y))
      ≡ η· (b , a) xs
   lem false xs y = cong fst (~uaβ (η·≃ (true , a)) (xs , y ))
   lem true xs y = cong fst (uaβ (η·≃ (true , a)) (xs , y ))


  codeDecode : Iso (Path (Bouquet A) base base)
                   (Σ _ IsNormalised)
  Iso.fun codeDecode p = subst CodeBouquet p ([] , lower)
  Iso.inv codeDecode = co← base
  Iso.rightInv codeDecode = Σ≡Prop isPropIsNormalised ∘ uncurry coRet
  Iso.leftInv codeDecode = coSec base

  isSetΩBouquet : isSet (Path (Bouquet A) base base)
  isSetΩBouquet = isOfHLevelRetractFromIso 2 codeDecode
                     (isSetΣ isSet[𝟚×] (isProp→isSet ∘ isPropIsNormalised))
