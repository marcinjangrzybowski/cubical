{-# OPTIONS --cubical --safe  #-}
module Cubical.HITs.NCube.CubesZoo.VanillaBoundaryOmega where


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


Boundary : ∀ {ℓ} → ∀ n → ∀ (A : T[ CType ℓ n ]) → Type ℓ

getBd : ∀ {ℓ} → ∀ n → ∀ (A : T[ CType ℓ n ]) → (T[ cu n A ]) → Boundary n A 

Boundary zero A = Unit*
Boundary (suc zero) A = A i0 1=1 × A i1 1=1
Boundary (suc (suc n)) A = Σ[ sides ∈ {!!} × {!!}  ]
                              getBd (suc n) (A i0) {!!} ≡ getBd (suc n) {!!} {!!}


-- Boundary A zero = Unit*
-- Boundary A (suc zero) = A × A
-- Boundary A (suc (suc n)) =
--  Σ[ sides ∈ (NCube (suc n) → A) × (NCube (suc n) → A)  ]
--     getBd A (suc n) (fst sides) ≡ getBd A (suc n) (snd sides)

getBd = {!!}

-- getBd A (zero) x = _
-- getBd A (suc zero) x = x (end false ∷ []) , x (end true ∷ [])
-- getBd A (suc (suc n)) x = ( x b∷ false , x b∷ true ) , cong (getBd A (suc n)) (x i∷_ )

InsideOf : ∀ {ℓ} → ∀ n → ∀ (A : T[ CType ℓ n ]) → Boundary n A → Type ℓ

insideOf : ∀ {ℓ} → ∀ n → ∀ (A : T[ CType ℓ n ]) → (c : T[ cu n A ])
                      → InsideOf n A (getBd n A c) 

InsideOf = {!!}

-- InsideOf A zero x = A
-- InsideOf A (suc zero) (x₀ , x₁) = x₀ ≡ x₁
-- InsideOf A (suc (suc n)) ((x₀ , x₁) , p) =
--    PathP (λ i → InsideOf A (suc n) (p i))
--      (insideOf _ _ x₀)
--      (insideOf _ _ x₁)

insideOf = {!!}

-- insideOf A zero c = c []
-- insideOf A (suc zero) c i = (c i∷ i) [] 
-- insideOf A (suc (suc n)) c i = insideOf A (suc n) (c i∷ i)



