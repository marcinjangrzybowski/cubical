{-# OPTIONS --cubical  #-}
module Cubical.HITs.NCube.ReflN where


open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≟_ to _≟Nat_)
open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum as Sum

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

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint


open import Cubical.HITs.NCube.IntervalPrim

open import Cubical.HITs.NCube.Cub

open import Cubical.HITs.NCube.BaseVec
open import Cubical.HITs.NCube.CompN

open import Cubical.HITs.NCube.Refl




maxNRefl : ℕ
maxNRefl = 10

-- fillReflMaxN :  ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
--             → (sides : (Bool × (Fin maxN)) → InsConst a maxN)
--             → (center : InsConst a maxN)
--             → Iⁿ→ A maxN
-- fillReflMaxN {A = A} a sides center i i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ i₉ =
--            let z : I → Bool → ℕ → A
--                z = λ j b k → toCubical {bd = const a} (sides (b , trimFin k))
--                    (replaceAt k (inside j) (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
--                     ∷ inside i₄ ∷ inside i₅ ∷ inside i₆ ∷ inside i₇ ∷ inside i₈ ∷ inside i₉ ∷ [])) 
--        in 
--                hfill
--                (λ j → λ {
--                   (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
--                   (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
--                   (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
--                   (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
--                   (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
--                   (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 ;
--                   (i₆ = i0) → z j false 6 ; (i₆ = i1) → z j true 6 ;
--                   (i₇ = i0) → z j false 7 ; (i₇ = i1) → z j true 7 ;
--                   (i₈ = i0) → z j false 8 ; (i₈ = i1) → z j true 8 ;
--                   (i₉ = i0) → z j false 9 ; (i₉ = i1) → z j true 9 
                  
--               })
--               (inS (center i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ i₉)) i

boxBd :  ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
         → ∀ n → Ins a n
         → NCube (suc n) → A
boxBd a n x (end x₁ ∷ x₂) = insToCub a n (snd x (Bool→I x₁)) x₂
boxBd a n x (inside i ∷ x₂) = insToCub a n (snd x i) x₂

-- boxBd-test : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A) →
--                      (Ins a 0) → I → {!!}
-- boxBd-test a x i = {!boxBd a 0 x (inside i ∷ []) !}
-- -- {!boxBd a 0 x (inside i ∷ [])!}


fillReflMaxN-bdAsm :  ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
            → (sides : (Bool × (Fin maxNRefl)) → Ins a (predℕ maxNRefl))
            → (center : InsConst a maxNRefl)
            → Iⁿ→ A maxNRefl
fillReflMaxN-bdAsm {A = A} a sides center i i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ i₉ =
           let z : I → Bool → ℕ → A
               z = λ j b k → boxBd a (predℕ maxNRefl) (sides (b , trimFin k))
                   ((inside j) ∷ removeAt k (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                    ∷ inside i₄ ∷ inside i₅ ∷ inside i₆ ∷ inside i₇ ∷ inside i₈ ∷ inside i₉ ∷ [])) 
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 ;
                  (i₆ = i0) → z j false 6 ; (i₆ = i1) → z j true 6 ;
                  (i₇ = i0) → z j false 7 ; (i₇ = i1) → z j true 7 ;
                  (i₈ = i0) → z j false 8 ; (i₈ = i1) → z j true 8 ;
                  (i₉ = i0) → z j false 9 ; (i₉ = i1) → z j true 9 
                  
              })
              (inS (center i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ i₉)) i



-- makeBdMaxN :  ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
--             → (Bool × Fin maxNRefl → Ins a (predℕ maxNRefl))
--             → NBoundary (maxNRefl) → A 
-- makeBdMaxN a x = Cu←I (predℕ maxNRefl) (fillReflMaxN-bdAsm a x (reflⁿ (maxNRefl) a ) i1)
--                    ∘ boundaryInj


----------------------------------

frbc-hlp : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → (a : A)
            → (sides : (Bool × (Fin (suc n))) → Ins a n)
             → NCube (suc n)
            → I → Bool → ℕ → A
frbc-hlp a sides cu i b k =
   boxBd a _ (sides (b , trimFin k))
                   ((inside i) ∷ removeAt k cu) 

fillReflBdCut :  ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ n → (a : A)
            → (sides : (Bool × (Fin n)) → Ins a (predℕ n))
            → (center : InsConst a n)
            → Iⁿ→ A n

fillReflBdCut {A = A} 0 a sides center i  =
               hfill {φ = i0}
               (λ j → λ ())
              (inS (center)) i

fillReflBdCut {A = A} 1 a sides center i i₀  =
           let z = frbc-hlp a sides 
                     (inside i₀ ∷ []) 
       in 
              hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 
              })
              (inS (center i₀)) i


fillReflBdCut {A = A} 2 a sides center i i₀ i₁ =
       let z =  frbc-hlp a sides
                     (inside i₀ ∷ inside i₁
                    ∷  [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 
              })
              (inS (center i₀ i₁)) i


fillReflBdCut {A = A} 3 a sides center i i₀ i₁ i₂ =
       let z =  frbc-hlp a sides
                     (inside i₀ ∷ inside i₁ ∷ inside i₂
                    ∷  [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 
              })
              (inS (center i₀ i₁ i₂)) i

fillReflBdCut {A = A} 4 a sides center i i₀ i₁ i₂ i₃ =
       let z =  frbc-hlp a sides
                     (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                    ∷  [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 
              })
              (inS (center i₀ i₁ i₂ i₃)) i

fillReflBdCut {A = A} 5 a sides center i i₀ i₁ i₂ i₃ i₄ =
       let z =  frbc-hlp a sides
                     (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                    ∷ inside i₄ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 
              })
              (inS (center i₀ i₁ i₂ i₃ i₄)) i


fillReflBdCut {A = A} 6 a sides center i i₀ i₁ i₂ i₃ i₄ i₅ =
           let z =  frbc-hlp a sides
                     (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                    ∷ inside i₄ ∷ inside i₅ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 
              })
              (inS (center i₀ i₁ i₂ i₃ i₄ i₅)) i


fillReflBdCut {A = A} 7 a sides center i i₀ i₁ i₂ i₃ i₄ i₅ i₆ =
           let z =  frbc-hlp a sides
                     (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                    ∷ inside i₄ ∷ inside i₅ ∷ inside i₆ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 ;
                  (i₆ = i0) → z j false 6 ; (i₆ = i1) → z j true 6 
              })
              (inS (center i₀ i₁ i₂ i₃ i₄ i₅ i₆)) i


fillReflBdCut {A = A} 8 a sides center i i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ =
           let z =  frbc-hlp a sides
                     (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                    ∷ inside i₄ ∷ inside i₅ ∷ inside i₆ ∷ inside i₇ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 ;
                  (i₆ = i0) → z j false 6 ; (i₆ = i1) → z j true 6 ;
                  (i₇ = i0) → z j false 7 ; (i₇ = i1) → z j true 7 
              })
              (inS (center i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇)) i


fillReflBdCut {A = A} 9 a sides center i i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ =
           let z =  frbc-hlp a sides
                     (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                    ∷ inside i₄ ∷ inside i₅ ∷ inside i₆ ∷ inside i₇ ∷ inside i₈ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 ;
                  (i₆ = i0) → z j false 6 ; (i₆ = i1) → z j true 6 ;
                  (i₇ = i0) → z j false 7 ; (i₇ = i1) → z j true 7 ;
                  (i₈ = i0) → z j false 8 ; (i₈ = i1) → z j true 8 
              })
              (inS (center i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈)) i


fillReflBdCut {A = A} 10 a sides center i i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ i₉ =
           let z =  frbc-hlp a sides
                     (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                    ∷ inside i₄ ∷ inside i₅ ∷ inside i₆ ∷ inside i₇ ∷ inside i₈ ∷ inside i₉ ∷ []) 
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 ;
                  (i₆ = i0) → z j false 6 ; (i₆ = i1) → z j true 6 ;
                  (i₇ = i0) → z j false 7 ; (i₇ = i1) → z j true 7 ;
                  (i₈ = i0) → z j false 8 ; (i₈ = i1) → z j true 8 ;
                  (i₉ = i0) → z j false 9 ; (i₉ = i1) → z j true 9 
                  
              })
              (inS (center i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ i₉)) i



fillReflBdCut {A = A} n a sides center = Cu→I _ (const a)

makeBdCut :  ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ n → (a : A)
            → (Bool × Fin n → Ins a (predℕ n))
            → NBoundary (n) → A 
makeBdCut (suc n) a x = (Cu←I n (fillReflBdCut (suc n) a x refl i1))
                                       ∘ boundaryInj


makeCylCut :  ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ n → (a : A)
            → (Bool × Fin n → InsConst a n)
            → I → NBoundary (n) → A 
makeCylCut (suc n) a x i = makeBdCut (suc n) a λ x₁ →  x x₁ i , λ i₁ → x x₁ (i ∧ i₁)

-- makeCylCut-test : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
--                     → ((Bool → InsConst a 1)) → I → {!!}
-- makeCylCut-test a x i = {!makeCylCut 1 a (x ∘ (fst)) i (lid true []) !}

-- makeCylCut-test2 : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
--                     → ((Bool → Ins a 0)) → I → {!!}
-- makeCylCut-test2 a x i = {!boxBd a zero (x false) !}
--{!fillReflBdCut 1 a (x ∘ fst) refl i !}


---------

hfillReflCut : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
            → ∀ {n}
            → (sides : (Bool × (Fin n)) → InsConst a n)
            → (center : InsConst a n)
            → (i : I) → InsideOf ((makeCylCut _ a sides) i)
hfillReflCut a {zero} sides center i = (hfillCut (makeCylCut _ a sides) center ) i            
hfillReflCut a {1} sides center i = (hfillCut (makeCylCut _ a sides) center ) i
hfillReflCut a {2} sides center i = (hfillCut (makeCylCut _ a sides) center ) i
hfillReflCut a {3} sides center i = (hfillCut (makeCylCut _ a sides) center ) i
hfillReflCut a {4} sides center i = (hfillCut (makeCylCut _ a sides) center ) i
hfillReflCut a {5} sides center i = (hfillCut (makeCylCut _ a sides) center ) i
hfillReflCut a {6} sides center i = (hfillCut (makeCylCut _ a sides) center ) i
hfillReflCut a {7} sides center i = (hfillCut (makeCylCut _ a sides) center ) i
hfillReflCut a {8} sides center i = (hfillCut (makeCylCut _ a sides) center ) i
hfillReflCut a {9} sides center i = (hfillCut (makeCylCut _ a sides) center ) i
hfillReflCut a {10} sides center i = (hfillCut (makeCylCut _ a sides) center ) i
hfillReflCut a {suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))} sides center i =
  refl


hcompReflCut : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
            → ∀ {n}
            → (sides : (Bool × (Fin n)) → InsConst a n)
            → (center : InsConst a n)
            → InsConst a n
hcompReflCut a {zero} sides center = (hcompCut (makeCylCut _ a sides) center )            
hcompReflCut a {1} sides center = (hcompCut (makeCylCut _ a sides) center )
hcompReflCut a {2} sides center = (hcompCut (makeCylCut _ a sides) center )
hcompReflCut a {3} sides center = (hcompCut (makeCylCut _ a sides) center )
hcompReflCut a {4} sides center = (hcompCut (makeCylCut _ a sides) center )
hcompReflCut a {5} sides center = (hcompCut (makeCylCut _ a sides) center )
hcompReflCut a {6} sides center = (hcompCut (makeCylCut _ a sides) center )
hcompReflCut a {7} sides center = (hcompCut (makeCylCut _ a sides) center )
hcompReflCut a {8} sides center = (hcompCut (makeCylCut _ a sides) center )
hcompReflCut a {9} sides center = (hcompCut (makeCylCut _ a sides) center )
hcompReflCut a {10} sides center = (hcompCut (makeCylCut _ a sides) center )
hcompReflCut a {n} sides center = center



reflFill :  ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
            → ∀ {n}
            → insRefl a n ≡ hcompReflCut a {n = n} (λ x₂ → insRefl a n) (insRefl a n)
reflFill a {0} i = hfillReflCut a (const (insRefl a 0)) (insRefl a 0) i
reflFill a {1} i = hfillReflCut a (const (insRefl a 1)) (insRefl a 1) i
reflFill a {2} i = hfillReflCut a (const (insRefl a 2)) (insRefl a 2) i
reflFill a {3} i = hfillReflCut a (const (insRefl a 3)) (insRefl a 3) i
reflFill a {4} i = hfillReflCut a (const (insRefl a 4)) (insRefl a 4) i
reflFill a {5} i = hfillReflCut a (const (insRefl a 5)) (insRefl a 5) i
reflFill a {6} i = hfillReflCut a (const (insRefl a 6)) (insRefl a 6) i
reflFill a {7} i = hfillReflCut a (const (insRefl a 7)) (insRefl a 7) i
reflFill a {8} i = hfillReflCut a (const (insRefl a 8)) (insRefl a 8) i
reflFill a {9} i = hfillReflCut a (const (insRefl a 9)) (insRefl a 9) i
reflFill a {10} i = hfillReflCut a (const (insRefl a 10)) (insRefl a 10) i
reflFill a {suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))} i
       = refl



hf2 :  ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ n → (a : A)
            → (skel : Σ (NCube (suc n) → A) (const a ≡_ ))
            → (sides : (b : Bool) → (k : Fin (suc n)) →
                        Σ _ (PathP (λ i →  InsideOf ((snd skel) i ∘ faceMap (fst k) b ∘ boundaryInj))
                         (reflⁿ n a)))
            → Iⁿ→ A (suc n)
hf2 {A = A} 0 a skel sides i i₀ =
       let z : (j : I) → Bool → ℕ → A
           z = λ j b k → (toCubical {bd = (snd skel) j ∘ faceMap (fst (trimFin {n = 1} k)) b ∘ boundaryInj}
                                 (snd (sides b (trimFin k)) j) ∘ (removeAt k))                     
               ( (inside i₀ ∷  []))
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 
              })
              (inS (a)) i  

hf2 {A = A} 1 a skel sides i i₀ i₁ =
       let z : (j : I) → Bool → ℕ → A
           z = λ j b k → (toCubical {bd = (snd skel) j ∘ faceMap (fst (trimFin {n = 1} k)) b ∘ boundaryInj}
                                 (snd (sides b (trimFin k)) j) ∘ (removeAt k))                     
               ( (inside i₀ ∷ inside i₁ ∷ []))
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 
              })
              (inS (a)) i                   
hf2 {A = A} 2 a skel sides i i₀ i₁ i₂ =
       let z : (j : I) → Bool → ℕ → A
           z = λ j b k → (toCubical {bd = (snd skel) j ∘ faceMap (fst (trimFin {n = 2} k)) b ∘ boundaryInj}
                                 (snd (sides b (trimFin k)) j) ∘ (removeAt k))                     
               ( (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ []))
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 
              })
              (inS (a)) i                        
hf2 {A = A} 3 a skel sides i i₀ i₁ i₂ i₃ =
       let z : (j : I) → Bool → ℕ → A
           z = λ j b k → (toCubical {bd = (snd skel) j ∘ faceMap (fst (trimFin {n = 3} k)) b ∘ boundaryInj}
                                 (snd (sides b (trimFin k)) j) ∘ (removeAt k))                     
               ( (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃ ∷ []))
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 
              })
              (inS (a)) i            
hf2 {A = A} 4 a skel sides i i₀ i₁ i₂ i₃ i₄ =
       let z : (j : I) → Bool → ℕ → A
           z = λ j b k → (toCubical {bd = (snd skel) j ∘ faceMap (fst (trimFin {n = 4} k)) b ∘ boundaryInj}
                                 (snd (sides b (trimFin k)) j) ∘ (removeAt k))                     
               ( (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃ ∷ inside i₄ ∷ []))
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 
              })
              (inS (a)) i
hf2 {A = A} 5 a skel sides i i₀ i₁ i₂ i₃ i₄ i₅ =
       let z : (j : I) → Bool → ℕ → A
           z = λ j b k → (toCubical {bd = (snd skel) j ∘ faceMap (fst (trimFin {n = 5} k)) b ∘ boundaryInj}
                                 (snd (sides b (trimFin k)) j) ∘ (removeAt k))                     
               ( (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃ ∷ inside i₄ ∷ inside i₅ ∷ []))
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 
              })
              (inS (a)) i


hf2 n a skel sides x = Cu→I n (const a)



-- mkBnd : ∀ {ℓ} → {A : Type ℓ} → (a : A) → ∀ n → ∀ k
--          → PartialBoundaryₖ n k
--          → Iⁿ→ A n
-- mkBnd a n zero pb = Cu→I n {!!}
-- mkBnd a n (suc k) pb = {!!}



-- test : {!!}
-- test = {!IFaceE (just false ∷ nothing ∷ just true ∷ nothing ∷ [])!}
