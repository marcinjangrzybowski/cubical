{-# OPTIONS --safe --lossy-unification  #-}


module Cubical.HITs.CauchyReals.NthRootSlow where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos;ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ

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




-- test0 : _
-- test0 = PT.map fst (∃rationalApprox≤ 1 ([ 1 / 3 ] , _))

-- test0' : _
-- test0' = PT.map fst (∃rationalApprox≤ 3 ([ 1 / 4 ] , _))

-- -- test0 = PT.map fst (∃rationalApprox≤ 2 ([ 1 / 5 ] , _))


-- bndsTest : ℚ₊ → ∥ ℕ ∥₁
-- bndsTest q = PT.map fst (NthRoot.ℝ₊⊆rootSeq 0 (rat (fst q))
--          (snd (ℚ₊→ℝ₊ q)))

-- bndsTest1 : ∥ ℕ ∥₁
-- bndsTest1 = bndsTest (2 , _)


-- -- inBds : {!!}
-- -- inBds = {!PT.map fst (NthRoot.ℝ₊⊆rootSeq 0 2 (decℚ<ᵣ? {0} {2})) !}

-- testX : ∥ ℚ ∥₁
-- testX =
--  PT.map fst $
--    ∃rationalApprox≤
--      ((NthRoot.rootSeq⊆→ 0).Seq⊆→.fun 2 2 (decℚ≤ᵣ? , decℚ≤ᵣ?)) 1 


-- testX' : ∥ ℚ ∥₁
-- testX' =
--  PT.map fst $
--    ∃rationalApprox≤
--      (IsBilipschitz.f⁻¹ (NthRoot.rootRest 0 2) 2 (decℚ≤ᵣ? , decℚ≤ᵣ?)) 1 


-- ℚ→∣ℤ×ℕ∣₁ : ℚ → ∥ ℤ × ℕ  ∥₁
-- ℚ→∣ℤ×ℕ∣₁ SQ.[ z , (1+ n) ] = ∣ z , suc n ∣₁
-- ℚ→∣ℤ×ℕ∣₁ (SQ.eq/ a b r i) =
--  squash₁ ∣ a .fst , suc (a .snd .ℕ₊₁.n) ∣₁
--          ∣ b .fst , suc (b .snd .ℕ₊₁.n) ∣₁ i

-- ℚ→∣ℤ×ℕ∣₁ (SQ.squash/ x x₁ p q i i₁) =
--   isProp→isSet' squash₁ (cong ℚ→∣ℤ×ℕ∣₁ p) (cong ℚ→∣ℤ×ℕ∣₁ q) refl refl
--      i i₁

-- module _ where

--  open IsBilipschitz (NthRoot.rootRest 0 2) 

--  s₁ : ∥ ℤ × ℕ  ∥₁
--  s₁ = ℚ→∣ℤ×ℕ∣₁
--         (IsBilipschitz.s (NthRoot.rootRest 0 2) 2 (decℚ≤ᵣ? , decℚ≤ᵣ?) 2)


--  invℝtest = invℝ₊ 1

--  -- s₁≡ : s₁ ≡ ∣ _ , _ ∣₁
--  -- s₁≡ = refl

-- --  -- ℚ.[
-- --  --        transp (λ i → Σ ℤ.ℤ (λ _ → ℕ₊₁)) i0
-- --  --        (transp (λ i → Σ ℤ.ℤ (λ _ → ℕ₊₁)) i0 (pos 1 , (1+ 3)))
-- --  --        ]

-- -- -- testS' : ℚ
-- -- -- testS' =
-- -- --  ({!IsBilipschitz.s (NthRoot.rootRest 0 2) 2 !})


-- -- -- -- 

-- -- -- -- testSqrt1 : _
-- -- -- -- testSqrt1 = PT.map fst (∃rationalApprox≤ (nth-root 0 2) 1)

