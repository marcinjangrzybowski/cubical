{-# OPTIONS --cubical --safe  #-}
module Cubical.HITs.NCube.SigmaSkelet where


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
open import Cubical.HITs.NCube.SigmaDone
open import Cubical.HITs.NCube.BaseVec

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying
open import Cubical.Data.Sigma.Nested.Path


Faces : ∀ {ℓ} → ∀ (A : Type ℓ) → ℕ → Type ℓ
Faces A n = Vec ((Cubeⁿ' (predℕ n) A) × (Cubeⁿ' (predℕ n) A)) n 


mapI : ∀ {ℓ} → ∀ {A B : Type ℓ} → ∀ {n} → ((I → A) → B) → 
              (I → Vec (A) n) → Vec (B) n
mapI {n = zero} x x₁ = []
mapI {n = (suc n)} x x₁ = x (λ i → head (x₁ i)) ∷ mapI {n = n} x λ i → tail (x₁ i)

fcsDbl : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → ∀ {m} →
              (I → Vec (Cubeⁿ' m A × Cubeⁿ' m A) n) →
                 Vec (Cubeⁿ' (suc m) A × Cubeⁿ' (suc m) A) n
fcsDbl {m = m} = mapI
  (λ x → (Iso.inv (Cube'-elim-iso m) (_ , λ i → (fst (x i)))
          , Iso.inv (Cube'-elim-iso m) (_ , λ i → (snd (x i)))))



extract-faces : ∀ {ℓ} → ∀ (A : Type ℓ) → ∀ n → Boundaryⁿ' n A → Faces A n
extract-faces A zero _ = []
extract-faces A (suc zero) (x0 , x1) = ((x0 , x1)) ∷ []
extract-faces A (suc n@(suc nn)) x =
    ends ∷
      fcsDbl {A = A} {m = nn}
        λ i → (cong (extract-faces A (suc nn)) cyli ) i

  where
    module cei = Iso (Boundary'-elim-iso {A = A} n)

    ends = fst (cei.fun x)

    cyli = snd (cei.fun x) 


Boundary : ∀ {ℓ} → ∀ (A : Type ℓ) → ℕ → Type ℓ

getBd : ∀ {ℓ} → ∀ (A : Type ℓ) → ∀ n → (NCube n → A) → Boundary A n 


-- TODO : omega version of this!

Boundary A zero = Unit*
Boundary A (suc zero) = A × A
Boundary A (suc (suc n)) =
 Σ[ sides ∈ (NCube (suc n) → A) × (NCube (suc n) → A)  ]
    getBd A (suc n) (fst sides) ≡ getBd A (suc n) (snd sides)

getBd A (zero) x = _
getBd A (suc zero) x = x (end false ∷ []) , x (end true ∷ [])
getBd A (suc (suc n)) x = ( x b∷ false , x b∷ true ) , cong (getBd A (suc n)) (x i∷_ )

InsideOfB : ∀ {ℓ} → ∀ (A : Type ℓ) → ∀ n → Boundary A n → Type ℓ

insideOfB :  ∀ {ℓ} → ∀ (A : Type ℓ) → ∀ n → (c : NCube n → A)
                      → InsideOfB A n (getBd A n c) 

InsideOfB A zero x = A
InsideOfB A (suc zero) (x₀ , x₁) = x₀ ≡ x₁
InsideOfB A (suc (suc n)) ((x₀ , x₁) , p) =
   PathP (λ i → InsideOfB A (suc n) (p i))
     (insideOfB _ _ x₀)
     (insideOfB _ _ x₁)

insideOfB A zero c = c []
insideOfB A (suc zero) c i = (c i∷ i) [] 
insideOfB A (suc (suc n)) c i = insideOfB A (suc n) (c i∷ i)
