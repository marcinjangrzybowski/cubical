{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.ExponentiationDer where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos; ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Bisect
open import Cubical.HITs.CauchyReals.NthRoot

open import Cubical.HITs.CauchyReals.Exponentiation

import Cubical.Algebra.CommRing.Instances.Int as ℤCRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties 
import Cubical.Algebra.CommRing as CR

module L𝐙 = Lems ℤCRing.ℤCommRing
module 𝐙' = RingTheory (CR.CommRing→Ring ℤCRing.ℤCommRing ) 


bernoulli's-ineq-^ℚⁿ : ∀ x n → 1 ℚ.< x
 → 
  ((fromNat (suc (suc n))) ℚ.· (x ℚ.- 1)) ℚ.+ 1  ℚ.< (x ℚ^ⁿ (suc (suc n))) 
bernoulli's-ineq-^ℚⁿ x n 1<x =
 <ᵣ→<ℚ _ _
   (subst2 _<ᵣ_
     (cong (1 +ᵣ_) (sym (rat·ᵣrat _ _)) ∙  +ᵣComm _ _) (^ⁿ-ℚ^ⁿ _ _)
     (bernoulli's-ineq-^ℚ (ℚ₊→ℝ₊ (x ,
       ℚ.<→0< _ (ℚ.isTrans< 0 1 _ (ℚ.0<pos  _ _) 1<x)))
       (fromNat (suc (suc n))) (<ℚ→<ᵣ _ _ 1<x)
          (ℚ.<ℤ→<ℚ _ _ (invEq (ℤ.pos-<-pos≃ℕ< _ _)
            (ℕ.suc-≤-suc (ℕ.zero-<-suc {n}))))))


x^→∞ : ∀ m (ε : ℚ₊) →
         Σ[ N ∈ ℕ ]
           (∀ n → N ℕ.< n → fromNat m ℚ.< (((fst ε) ℚ.+ 1) ℚ^ⁿ n))
x^→∞ m ε =
 let (1+ N , X) = ℚ.ceilℚ₊
         (fromNat (suc m) ℚ₊· invℚ₊ ε )
 in   suc N
    , λ { zero 0< → ⊥.rec (ℕ.¬-<-zero 0<) 
      ; (suc zero) <1 → ⊥.rec (ℕ.¬-<-zero (ℕ.predℕ-≤-predℕ <1)) 
      ; (suc (suc n)) <ssn →
       ℚ.isTrans< (fromNat m) _ _
         (subst (fromNat m ℚ.<_)
           (ℚ.·Comm _ _)
           (ℚ.isTrans< _ (fromNat (suc m)) _
             (ℚ.<ℤ→<ℚ _ _ ((ℤ.isRefl≤ {pos (suc m)})))
              (ℚ.x·invℚ₊y<z→x<y·z _ _ _ X)))
         (ℚ.isTrans< _ _ _ (ℚ.<-·o
           (fromNat (suc N))
           (fromNat (suc (suc n))) _ (ℚ.0<ℚ₊ ε)
           (ℚ.<ℤ→<ℚ _ _  (invEq (ℤ.pos-<-pos≃ℕ< (suc N) (suc (suc n))) <ssn)))
          (ℚ.isTrans< _ _ _ (
           ℚ.isTrans≤< _ _ _
            (ℚ.≡Weaken≤ _ _
             (cong ((fromNat (suc (suc n))) ℚ.·_)
              lem--034))
            (ℚ.<+ℚ₊' _ _ 1 (ℚ.isRefl≤ _)))
          (bernoulli's-ineq-^ℚⁿ ((fst ε) ℚ.+ 1) n
           (subst (1 ℚ.<_) (ℚ.+Comm _ _)
            (ℚ.<+ℚ₊' 1 1 ε (ℚ.isRefl≤ 1))))))
      }

x+1/x-bound : ∀ (x : ℝ₊) → rat [ 1 / 2 ] <ᵣ fst x →
   (fst x -ᵣ 1) -ᵣ (1 -ᵣ fst (invℝ₊ x))  ≤ᵣ (2 ·ᵣ (fst x -ᵣ 1)) ·ᵣ (fst x -ᵣ 1)  
x+1/x-bound x 1/2<x =
  {!!}

 where
 h : ?
 h = ?
-- module _ (Z : ℕ) (z : ℝ₊) (z<Z : fst z <ᵣ fromNat (suc (suc Z))) (1<z : 1 <ᵣ fst z) where

--  lnSeq : ℕ → ℝ
--  lnSeq n =  (fst (z ^ℚ [ 1 / 2+ n ]) -ᵣ 1)  ·ᵣ fromNat (suc (suc n))

--  lnSeq< : ∀ n → lnSeq n <ᵣ fst z -ᵣ 1 
--  lnSeq< n = {!!}



--  lnSeq' : ℕ → ℝ
--  lnSeq' n = (1 -ᵣ fst (z ^ℚ (ℚ.- [ 1 / 2+ n ])))  ·ᵣ fromNat (suc (suc n))

--  lnSeq'<lnSeq : ∀ n m → lnSeq' n <ᵣ lnSeq m
--  lnSeq'<lnSeq n m = {!!}
--  -- <ᵣ-·ᵣo _ _ (fromNat (suc (suc n)))
--  --      (subst2 _<ᵣ_
--  --        {!!}
--  --        {!!}
--  --        (slope-monotone-strict z 1<z (ℚ.- [ 1 / 2+ n ]) 1 1 [ 1 / 2+ n ]
--  --          {!!} {!!} {!!} {!!}  ))

--  seqΔ :   ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ]
--     (∀ n → N ℕ.< n →
--        lnSeq n -ᵣ lnSeq' n <ᵣ (rat (fst ε)))

--  seqΔ ε =
--      {!!}
--    , λ n N>n →
--      let h = {!!}
--      in isTrans≡<ᵣ _ _ _
--        (cong (λ y → lnSeq n -ᵣ  (1 -ᵣ y) ·ᵣ fromNat (suc (suc n)) )
--          (cong fst (^ℚ-minus' z _) ∙
--            cong fst (invℝ₊^ℚ _ _))
--         ∙ sym (𝐑'.·DistL- _ _ _))
--        (isTrans≤<ᵣ _ _ _
--          (isTrans≤≡ᵣ _ _ _ (≤ᵣ-·ᵣo _ _ (fromNat (suc (suc n)))
--           {!!}
--           ((x+1/x-bound _ {!!})))
--           (sym (·ᵣAssoc _ _ _)))
--           (isTrans<ᵣ _ _ _
--            (<ᵣ₊Monotone·ᵣ _ _ _ _
--            {!!} {!!}
--              (<ᵣ-o·ᵣ _ _ 2
--               (<ᵣ-+o _ _ -1
--                (^ℚ-StrictMonotone {y = fromNat (suc (suc Z))} ([ 1 / 2+ n ] , _) z<Z)))
--              (isTrans<ᵣ _ _ _ (lnSeq< n)
--                (<ᵣ-+o _ _ -1 z<Z)))
--            (isTrans≡<ᵣ _ _ _ (·ᵣComm _ _ ∙  (·ᵣAssoc _ _ _) ∙
--             cong (_·ᵣ (fst (fromNat (suc (suc Z)) ^ℚ [ 1 / 2+ n ]) +ᵣ -1))
--              (sym (rat·ᵣrat _ _)) )
--                {!!})))

--  ca-lnSeq : IsCauchySequence' lnSeq
--  ca-lnSeq ε =
--   let (N , X) = seqΔ ε
--   in N , ℕ.elimBy≤
--     (λ x y X u v → isTrans≡<ᵣ _ _ _
--       (minusComm-absᵣ _ _) (X v u) )
--     λ x y x<y <y <x → 
--       ⊎.rec
--        (λ x<y →
--          isTrans<ᵣ _ _ _
--           (isTrans≡<ᵣ _ _ _
--            (absᵣNonPos (lnSeq y +ᵣ -ᵣ lnSeq x) {!!}
--              ∙ -[x-y]≡y-x _ _)
--            (<ᵣ-o+ _ _ _ (-ᵣ<ᵣ _ _ (lnSeq'<lnSeq x y))))
--           (X _ <x))
--        (λ x≡y → isTrans≡<ᵣ _ _ _
--          (cong absᵣ (𝐑'.+InvR' _ _ (cong lnSeq (sym x≡y)))) (snd (ℚ₊→ℝ₊ ε)))
--        (ℕ.≤-split {x} {y} x<y) 
--  -- bdSeq : {!!}
--  -- bdSeq = {!!}
