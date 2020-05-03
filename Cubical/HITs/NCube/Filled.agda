{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.Filled where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
-- open import Cubical.Data.Prod
open import Cubical.Data.List
open import Cubical.Data.Sigma

open import Cubical.HITs.Interval
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.Base



data Filled {n} {X : Type₀} {X₀ X₁ : X} {X= : X₀ ≡ X₁} (injX : X → NCube (n)) : Type₀ where
   lidF : Bool → NCube (n) → Filled injX
   cylF : ∀ x → lidF false (injX x) ≡ lidF true (injX x)
   insF : Square (cylF X₀) (cylF X₁)
              (cong (lidF {X= = X=} false ∘ injX) X=)
              (cong (lidF {X= = X=} true ∘ injX) X=)


-- -- NBoundary and boundaryInj are recursively defined

NFilled : ℕ → Type₀
filledInj : ∀ {n} → NFilled n → NCube n
nfilled0 : ∀ n → NFilled n
nfilled1 : ∀ n → NFilled n
nfilled0=1 : ∀ n → nfilled0 n ≡ nfilled1 n


NFilled zero = Unit
NFilled (suc n) = Filled {n} {X₀ = nfilled0 n} {X₁ = nfilled1 n} {X= = nfilled0=1 n} (filledInj)

nfilled0 zero = _
nfilled0 (suc n) = lidF false corner0

nfilled1 zero = _
nfilled1 (suc n) = lidF true corner1


filledInj {zero} x = _
filledInj {suc n} (lidF x x₁) = (end x , x₁)
filledInj {suc n} (cylF x i) = inside i ,  filledInj x
filledInj {suc n} (insF i i₁) = inside i₁ , filledInj (nfilled0=1 n i)

nfilled0=1 zero i = _
nfilled0=1 (suc zero) i = cylF _ i
nfilled0=1 (suc (suc n)) i = insF i i



-- boundaryInj {zero} ()
-- boundaryInj {suc _} (lid x₁ x) = (end x₁) , x
-- boundaryInj {suc _} (cyl x i) = inside i ,  boundaryInj x
