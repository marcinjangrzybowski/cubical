-- https://homotopytypetheory.org/2016/02/24/parametricity-and-excluded-middle/
{-# OPTIONS --safe #-}
module Cubical.Experiments.Lemtest where

open import Cubical.Foundations.Everything

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Maybe
open import Cubical.Functions.Logic as L

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT


-- private
--   variable
--     ℓ : Level
--     A : hProp ℓ


module _ {ℓ} where

 LEM : hProp (ℓ-suc ℓ)
 LEM = ((A : hProp ℓ) → Dec ⟨ A ⟩) , isPropΠ (isPropDec ∘ snd) 


 T : hProp (ℓ-suc ℓ)
 T = ∃[ f ∶ ({A : Type ℓ} → A → A) ] (lower ∘ f {Lift Bool} ∘ lift ≡ not) ,
                   isSet→ isSetBool _ _


 LEM→T : ⟨ LEM ⇒ T ⟩
 LEM→T ？ = {!!}


 T→LEM' : (f : {A : Type ℓ} → A → A) → lower ∘ f {Lift Bool} ∘ lift ≡ not → ⟨ LEM ⟩
 T→LEM' f p A =
  {!!}
  where
   ~H : Maybe Bool → Maybe Bool → hProp ℓ
   ~H nothing nothing = ⊥* , isProp⊥*
   ~H nothing (just x) = ⊥* , isProp⊥*
   ~H (just x) nothing = ⊥* , isProp⊥*
   ~H (just _) (just _) = A
   
   H : Type ℓ
   H = Maybe Bool / λ x y → ⟨ ~H x y ⟩

   z : f {H} [ nothing ] ≡ [ nothing ] → ⟨ L.¬ A ⟩ 
   z = {!!}

 T→LEM : ⟨ T ⇒ LEM ⟩ 
 T→LEM = PT.rec (snd LEM) (uncurry T→LEM')
 

