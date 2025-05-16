-- This is the preferred version of the integers in the library. Other
-- versions can be found in the MoreInts directory.
{-# OPTIONS --safe #-}
module Cubical.Data.IntAlt where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.Base as ℤ hiding (_+_ ; _·_; _-_ )
 renaming (_+f_ to _+_ ; _·f_ to _·_;_-f_ to _-_) public
open import Cubical.Data.Int.PropertiesAlt public
-- open import Cubical.Data.Int.Properties public
--   hiding (·lCancel ; ·rCancel; +Assoc ;+Comm;-DistL·;-DistR·;minusPlus;plusMinus
--    ;·Assoc;·Comm;·DistL+;·DistR+;·IdL;·IdR;·DistPosRMin;·DistPosRMax;·DistPosLMin)

-- open import Cubical.Algebra.CommRing
-- open import Cubical.Algebra.Ring.Properties
-- open import Cubical.Algebra.Ring

-- ℤCommRing : CommRing ℓ-zero
-- ℤCommRing .fst = ℤ
-- ℤCommRing .snd .CommRingStr.0r = 0
-- ℤCommRing .snd .CommRingStr.1r = 1
-- ℤCommRing .snd .CommRingStr._+_ = _+_
-- ℤCommRing .snd .CommRingStr._·_ = _·_
-- CommRingStr.- ℤCommRing .snd = -_
-- ℤCommRing .snd .CommRingStr.isCommRing = isCommRingℤ'
--   where
--   abstract
--     isCommRingℤ : IsCommRing (pos 0) (pos 1) ℤ._+_ ℤ._·_ (-_)
--     isCommRingℤ =
--       makeIsCommRing isSetℤ +Assoc (λ _ → refl)
--                                  -Cancel +Comm ·Assoc
--                                  ·IdR ·DistR+ ·Comm

--     isCommRingℤ' : IsCommRing (pos 0) (pos 1) _+_ _·_ (-_)
--     isCommRingℤ' =
--      subst2 (λ _+_ _·_ → IsCommRing (pos 0) (pos 1) _+_ _·_ (-_))
--        (λ i x y → +≡+f x y i) (λ i x y → ·≡·f x y i) isCommRingℤ

-- module 𝐙 where
--  open RingTheory (CommRing→Ring ℤCommRing) public
--  open CommRingTheory (ℤCommRing) public
--  open RingStr (snd (CommRing→Ring ℤCommRing)) public

-- ·lCancel : (c m n : ℤ) → c · m ≡ c · n → ¬ c ≡ 0 → m ≡ n
-- ·lCancel c m n p h = -≡0 _ _ (isIntegralℤ c (m - n) (·lCancel-helper c m n p) h)

-- ·rCancel : (c m n : ℤ) → m · c ≡ n · c → ¬ c ≡ 0 → m ≡ n
-- ·rCancel c m n p h = ·lCancel c m n (·Comm c m ∙ p ∙ ·Comm n c) h
