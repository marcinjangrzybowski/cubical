{-# OPTIONS --safe #-}

module Cubical.Data.List.HITs.Groupoid.Comm2Quot where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Empty renaming (elim to ⊥elim ; rec to ⊥rec)

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Nat.Order

open import Cubical.HITs.GroupoidTruncation


import Cubical.Data.List.Base as B
import Cubical.Data.List.Properties as BP

import Cubical.Functions.Logic as L

open import Cubical.Data.List.HITs.Groupoid.Base
open import Cubical.Data.List.HITs.Groupoid.BaseMore

open import Cubical.Data.List.HITs.Groupoid.Comm2

open import Cubical.HITs.GroupoidQuotients

open import Cubical.Relation.Binary

private
  variable
    ℓ : Level
    A : Type ℓ

-- module Ωℙ (A : Type ℓ) where

--  Code : (a b : List A) → Type ℓ
--  Code a b = {!Σ ? ?!}
 
--  code : (a b : List A) → 𝕡base a ≡ 𝕡base b → Code a b
--  code = {!!}

--  decode : (a b : List A) → Code a b → 𝕡base a ≡ 𝕡base b 
--  decode = {!!}


-- module ⇎ (A : Type ℓ) where

--  _⇎_ : Rel (List A) (List A) ℓ
--  x ⇎ y = 𝕡base x ≡ 𝕡base y

--  isTrans⇎ : BinaryRelation.isTrans _⇎_
--  isTrans⇎ _ _ _ = _∙_

--  ℙ// : Type ℓ
--  ℙ// = List A // isTrans⇎

-- module _ (A : Type ℓ) where

--  open ⇎ A

--  Rfun : Rrec {R = _⇎_} {isTrans⇎} (ℙ A)
--  Rrec.Bgpd Rfun = 𝕡trunc
--  Rrec.fb Rfun = 𝕡base
--  Rrec.feq Rfun x = x
--  Rrec.fsq Rfun r q = compPath-filler r q

--  Rinv'' : Recℙ.H1 {A = A} ℙ//
--  Recℙ.bbase Rinv'' = [_]


--  Rinv' : Recℙ.H2 Rinv''
--  Recℙ.bloop Rinv' xs ys zs ws = eq// (𝕡loop _ _ _ _)
--  Recℙ.bhexDiag Rinv' ls xs ys zs rs = eq// (𝕡hexDiag _ _ _ _ _)
--  Recℙ.bcommDiag Rinv' xs ys zs ws++xs' ys' zs' ws' =
--    eq// (𝕡commDiag _ _ _ _ _ _ _)
--  Recℙ.bcommDiag' Rinv' xs ys zs ws++xs' ys' zs' ws' =
--    eq// (𝕡commDiag' _ _ _ _ _ _ _)
 
--  Rinv : Recℙ.H3 Rinv'
--  Recℙ.binvol Rinv xs ys zs ws =
--    (λ i i₁ → eq// (𝕡invol xs ys zs ws i) i₁)
--      ▷ {!!}
--  Recℙ.bhexU Rinv ls xs ys zs rs i i₁ =
--    eq// (𝕡hexU ls xs ys zs rs i) i₁
--  Recℙ.bhexD Rinv ls xs ys zs rs i i₁ = {!comp// ? ? i₁ i!}
--  Recℙ.bcommA Rinv = {!!}
--  Recℙ.bcommB Rinv = {!!}
--  Recℙ.bcomm Rinv = {!!}

--  Rri' : Elimℙ.H1 λ (b : ℙ A) → Rrec.f Rfun (Recℙ.f₃ Rinv squash// b) ≡ b
--  Elimℙ.bbase Rri' _ = refl

--  Rri : Elimℙ.H2 Rri'
--  Elimℙ.bloop Rri xs ys zs ws i _ = 𝕡loop xs ys zs ws i
--  Elimℙ.bhexDiag Rri ls xs ys zs rs i _ = 𝕡hexDiag ls xs ys zs rs i
--  Elimℙ.bcommDiag Rri xs ys zs ws++xs' ys' zs' ws' i _ =
--    𝕡commDiag xs ys zs ws++xs' ys' zs' ws' i
--  Elimℙ.bcommDiag' Rri xs ys zs ws++xs' ys' zs' ws' i _ =
--    𝕡commDiag' xs ys zs ws++xs' ys' zs' ws' i



--  Rli : RelimSet (λ z → Recℙ.f₃ Rinv squash// (Rrec.f Rfun z) ≡ z)
--  RelimSet.truncB Rli _ = squash// _ _
--  RelimSet.fb Rli _ = refl
--  RelimSet.fbEq Rli r i j = {!!}

--  isoℙ// : Iso ℙ// (ℙ A)
--  Iso.fun isoℙ// = Rrec.f Rfun
--  Iso.inv isoℙ// = Recℙ.f₃ Rinv squash//
--  Iso.rightInv isoℙ// = Elimℙ.f₂ Rri λ _ → 𝕡trunc _ _
--  Iso.leftInv isoℙ// = RelimSet.f Rli
