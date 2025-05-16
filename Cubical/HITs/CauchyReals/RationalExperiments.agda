{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.RationalExperiments where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.IntAlt as ℤ using (pos; ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

import Cubical.Data.Rationals as ℚ
-- import Cubical.Data.Rationals.Order.Properties as ℚ

open import Cubical.Data.BinNat.BinNat


a : ℕ
a = 12333212

b : ℕ
b = 32444391

-- a·b : ℕ
-- a·b = {!a ℕ.+ b!}

-- a·b' : ℤ
-- a·b' = {!pos a ℤ.+f pos b!}



expSeqℕ×ℕ : ℕ → ℕ × ℕ
expSeqℕ×ℕ n = suc n ^ n , (n ^ n) 

-- -- a+b' : ℕ₊₁
-- -- a+b' = {!(1+ a) ·₊₁ (1+ b)!}


-- _+r_  : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
-- x +r y = ℚ.reduce (x ℚ.+ y)

-- _·r_  : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
-- x ·r y = ℚ.reduce (x ℚ.· y)


-- _ℚ^ⁿr_ : ℚ.ℚ → ℕ → ℚ.ℚ
-- x ℚ^ⁿr zero = 1
-- x ℚ^ⁿr suc n = (x ℚ^ⁿr n) ·r x


expSeq : ℕ → ℚ.ℚ
expSeq n = (ℚ.[ pos n / 1+ n ]) ℚ.ℚ^ⁿ n

-- -- expSeq-r : ℕ → ℚ.ℚ
-- -- expSeq-r n = (1 +r ℚ.[ 1 / 1+ n ]) ℚ^ⁿr n


-- -- -- bn123 : Binℕ
-- -- -- bn123 = ℕ→Binℕ 1230121

-- -- -- bn123' : {!!}
-- -- -- bn123' = {!Binℕ→ℕ bn123!}


