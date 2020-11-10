{-# OPTIONS --cubical --safe  #-}
module Cubical.HITs.NCube.CubesZoo.VanillaBoundaryDep where


import Agda.Primitive.Cubical

open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat renaming (elim to ℕ-elim)
open import Cubical.Data.Nat.Order

open import Cubical.Data.Vec
open import Cubical.Data.Fin renaming (elim to Fin-elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.HITs.Interval
open import Cubical.HITs.PropositionalTruncation renaming (map to mapₚ)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 hiding (_*_)
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
import Cubical.Functions.Logic as Lo

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.IntervalPrim


open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying
open import Cubical.Data.Sigma.Nested.Path

Boundary : ∀ {ℓ} → ∀ {n} → ∀ (A : NCube n → Type ℓ) → Type ℓ

getBd : ∀ {ℓ} → ∀ {n} → ∀ {A : NCube n → Type ℓ} → (Π A) → Boundary A 

Boundary {n = zero} A = Unit*
Boundary {n = (suc zero)} A = ((A b∷ false) []) × ((A b∷ true) [])
Boundary {n = (suc (suc n))} A = Σ[ sides ∈ _ × _  ]
                              PathP (λ i → Boundary (A i∷ i))
                              (getBd (fst sides))
                              (getBd (snd sides))

getBd {n = zero} x = _
getBd {n = suc zero} x = ((x b∷ false) []) , ((x b∷ true) [])
getBd {n = suc (suc n)} x = ( x b∷ false , x b∷ true ) , λ i →  getBd (x i∷ i)

InsideOf : ∀ {ℓ} → ∀ {n} → ∀ {A : NCube n → Type ℓ} → Boundary A → Type ℓ

insideOf : ∀ {ℓ} → ∀ {n} → ∀ {A : NCube n → Type ℓ} → (c : Π A)
                      → InsideOf (getBd c) 

InsideOf {n = zero} {A = A} _ = A []
InsideOf {n = suc zero} {A = A} (x₀ , x₁) = PathP (λ i → (A i∷ i) []) x₀ x₁ 
InsideOf {n = suc (suc n)} ((x₀ , x₁) , p) =
    PathP (λ i → InsideOf (p i))
     (insideOf x₀)
     (insideOf x₁)


insideOf {n = zero} c = c []
insideOf {n = suc zero} c i = (c i∷ i) []
insideOf {n = suc (suc n)} c i = insideOf (c i∷ i)



Boundary-split : ∀ {ℓ} → ∀ n k → (A : NCube (n + k) → Type ℓ)
                      → (bdc : (c : NCube k) → Boundary {n = n} (A ∘ (_++ c)))
                         → Type ℓ                                                
Boundary-split n k A bdc = Boundary (InsideOf ∘ bdc)




split-++-lem : ∀ n k → Iso (NCube ((suc n) + k)) (NCube (n + suc k))
split-++-lem = {!!}

Boundary-Iso-split : ∀ {ℓ} → ∀ n k → (A : NCube ((suc n) + k) → Type ℓ)
                        → Iso (Σ _ (Boundary-split (suc n) k A))
                              (Σ _ (Boundary-split n (suc k) ( A ∘ (Iso.inv (split-++-lem n k)))))
Boundary-Iso-split n k A = {!!}


-- -- Boundaryω-↓ : ∀ {ℓ} → ∀ n k → (A : NCube (n + k) → Type ℓ) → Typeω
-- -- Boundaryω-↓ zero k A = T[ Boundaryω k Ct[ k , A ] ]
-- -- Boundaryω-↓ (suc n) zero A = Liftω (Boundary A)
-- -- Boundaryω-↓ (suc n) (suc k) A = T[ {!Boundaryω!} ]

-- Boundary-splitω : ∀ {ℓ} → ∀ n k → (A : NCube (n + k) → Type ℓ)
--                       → (bdc : (c : NCube k) → Boundary {n = n} (A ∘ (_++ c)))
--                          → ωType                                                
-- Boundary-splitω n k A bdc = Boundaryω k Ct[ k , InsideOf ∘ bdc ]
