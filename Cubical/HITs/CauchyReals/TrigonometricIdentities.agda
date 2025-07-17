{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.TrigonometricIdentities where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

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
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.Uniform
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot

x²=1→∣x∣=1 : ∀ x → x ·ᵣ x ≡ 1 → absᵣ x ≡ 1
x²=1→∣x∣=1 x x²=1 = {!cong (x ·ᵣ_) !}

-- sin[π/2]≡1 : sin π-number/2 ≡ 1
-- sin[π/2]≡1 =
--  let z = sym (𝐑'.+IdR' _ _
--                    (𝐑'.0RightAnnihilates' _ _ cos[π/2]≡0))
--              ∙ sin²+cos²=1 π-number/2

--  in {!!}
--   -- cong fst (
--   --      sym (Iso.leftInv (nth-pow-root-iso 2) (sin π-number/2 ,
--   --         {!!}))
--   --       ∙ cong (Iso.inv (nth-pow-root-iso 2)) (ℝ₊≡ {_} {ℚ₊→ℝ₊ 1} z))
--   --        ∙ {!!}
  
-- cos[x]=sin[x+π/2] : ∀ x → cos x ≡ sin (x +ᵣ π-number/2)
-- cos[x]=sin[x+π/2] x = sym (𝐑'.·IdR' _ _ sin[π/2]≡1)
--    ∙∙ sym (𝐑'.+IdL' _ _ (𝐑'.0RightAnnihilates' _ _ cos[π/2]≡0 ))
--    ∙∙ sym (sinOfSum x π-number/2)

-- sin[x]=-cos[x+π/2] : ∀ x → sin x ≡ -ᵣ cos (x +ᵣ π-number/2)
-- sin[x]=-cos[x+π/2] x = sym (𝐑'.·IdR' _ _ sin[π/2]≡1)
--    ∙∙ sym (𝐑'.+IdR' _ _ (cong -ᵣ_ ((𝐑'.0RightAnnihilates' _ _ cos[π/2]≡0 ))
--       ∙ -ᵣ-rat 0))
--    ∙∙ sym (-[x-y]≡y-x _ _) ∙ cong -ᵣ_ (sym (cosOfSum x π-number/2))


-- -- sin-period : ∀ x → sin x ≡ sin (x +ᵣ 2 ·ᵣ π-number) 
-- -- sin-period x =
-- --     {!!}
-- --   ∙ cong sin (cong (x +ᵣ_) (x+x≡2x _))
