{-# OPTIONS --cubical --safe  #-}
module Cubical.HITs.NCube.CubesZoo.BoundarySigmaWithoutNestedOmega where


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

Partialⁿ-mk-Ends :  ∀ {ℓ} → ∀ n → {A : T[ CType ℓ (suc n) ]}
                      → (end0 : T[ cu n (A i0) ])
                      → (end1 : T[ cu n (A i1) ])
                      → T[ Partialⁿ (suc n)
                                 (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) 
                                 A ]
Partialⁿ-mk-Ends {ℓ} zero {A} end0 end1 i = zz
  where
    zz : _
    zz (i = i0) = end0 1=1
    zz (i = i1) = end1 1=1
    
Partialⁿ-mk-Ends {ℓ} (suc n) {A} end0 end1 i i₁ =
  Partialⁿ-mk-Ends {ℓ} (n) {λ j → A j i₁} (end0 i₁) (end1 i₁) i

Boundary : ∀ {ℓ} → ∀ n → ∀ (A : T[ CType ℓ n ]) → ωType

getBd : ∀ {ℓ} → ∀ n → (A : T[ CType ℓ n ]) → Morω (cu n A) (Boundary n A) 

T[ Boundary zero A ] = Liftω Unit
T[ Boundary (suc zero) A ] = Liftω ((A i0 1=1 × A i1 1=1))
T[ Boundary (suc (suc n)) A ] =
  Σω ((T[ cu (suc n) (A i0) ] ×ω T[ cu (suc n) (A i1) ]))
   λ x → ωType._≡ω_ {!!} ((Morω.f (getBd (suc n) (A i0)) (proj₁ω x))) {!!}


ωType._≡ω_ (Boundary n A) = {!!}
ωType.symω (Boundary n A) = {!!}
ωType._transω_ (Boundary n A) = {!!}
-- Boundary {ℓ} zero A = Liftω Unit
-- Boundary {ℓ} (suc zero) A = Liftω ((A i0 1=1 × A i1 1=1))
-- Boundary {ℓ} (suc (suc n)) A =
--   Σω ((T[ cu (suc n) (A i0) ] ×ω T[ cu (suc n) (A i1) ]))
--    λ x → {!!}


getBd = {!!}
-- getBd zero A x = λ _ → tt
-- getBd (suc zero) A x x₁ = (x i0 1=1) , (x i1 1=1)
-- getBd (suc (suc n)) A x =
--  pairω (x i0) (x i1) ,ω {!!}

--   where
--     -- zz : T[ Partialⁿ-Sub (suc (suc n)) (⊆'1-∧ {!!} {!!} (paⁿ (suc (suc n)) x)) ]
    -- zz = inPartialⁿ-Sub (suc (suc n)) (paⁿ (suc (suc n)) x)

    -- zz2 : T[
    --         Partialⁿ-Sub (suc (suc n))
    --         (⊆'2-∧ (↑Expr 1 (boundaryExpr (suc n)))
    --          (λ z → [ z ]Iexpr ∨ⁿ [ ~ z ]Iexpr)
    --          (Partialⁿ-mk-Ends (suc n) (x i0) (x i1)))
    --         ]
    -- zz2 = {!!}

InsideOf : ∀ {ℓ} → ∀ n → (A : T[ CType ℓ n ]) →  T[ Boundary n A ] → ωType

insideOf :  ∀ {ℓ} → ∀ n → (A : T[ CType ℓ n ]) → (c : T[ cu n A ])
                      → T[ InsideOf n A (Morω.f (getBd n A) c) ]

InsideOf = {!!}

-- InsideOf zero A x = T[ cu 0 A ]
-- InsideOf (suc zero) A x = {!!}
-- InsideOf (suc (suc n)) A x = {!!}
-- -- InsideOf A zero x = A
-- -- InsideOf A (suc zero) (x₀ , x₁) = x₀ ≡ x₁
-- -- InsideOf A (suc (suc n)) ((x₀ , x₁) , p) =
-- --    PathP (λ i → InsideOf A (suc n) (p i))
-- --      (insideOf _ _ x₀)
-- --      (insideOf _ _ x₁)


insideOf zero A c = {!!}
insideOf (suc zero) A c = {!!}
insideOf (suc (suc n)) A c = {!!}
-- insideOf A zero c = c []
-- insideOf A (suc zero) c i = (c i∷ i) [] 
-- insideOf A (suc (suc n)) c i = insideOf A (suc n) (c i∷ i)
