{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Free where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Bool as 𝟚
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Bool using (false ; true) renaming (Bool to 𝟚) 
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum  as ⊎

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.HITs.GroupoidTruncation as GT
import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.S1

open import Cubical.Algebra.Group.Presentation.RelIndex
 using (Sq ; sq ; cns ; fc)

import Cubical.Algebra.Group.Presentation.RelIndex

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Subgroup

open import Cubical.Algebra.Group.Abelianization.Properties renaming (rec to recAb ; elimProp to  elimPropAb ; elimProp2 to  elimProp2Ab)


open import Cubical.HITs.Bouquet
open import Cubical.HITs.FreeGroup


open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.Data.Int hiding (_·_)

private
 variable
  ℓ ℓ' : Level

module Free (IxG : Type ℓ)  where

 open Cubical.Algebra.Group.Presentation.RelIndex.Pres
              IxG ⊥.rec

 IsoFree𝔹 : Iso 𝔹T (∥ Bouquet IxG ∥₃)
 Iso.fun IsoFree𝔹 = Rec𝔹T.f w
  where
  open Rec𝔹T
  w : Rec𝔹T ∥ Bouquet IxG ∥₃
  isGroupoidA w = squash₃
  baseA w = ∣ base ∣₃
  loopA w = cong ∣_∣₃ ∘ loop
  
 Iso.inv IsoFree𝔹 = GT.rec trunc
     λ { base → base ; (loop a i) → loop a i }
 Iso.rightInv IsoFree𝔹 =
   GT.elim (λ _ → isSet→isGroupoid (squash₃ _ _))
    λ { base → refl ; (loop a i) j → ∣ loop a i ∣₃ } 
 Iso.leftInv IsoFree𝔹 = ElimSet𝔹T.f w
  where
  open ElimSet𝔹T
  w : ElimSet𝔹T _
  isSetA w _ = trunc _ _
  baseA w = refl
  loopA w a i j = loop a i


 -- IsoFree : Iso T (FreeGroup IxG)
 -- IsoFree = compIso {!!} (compIso {!!} {!!})


 -- module N = Cubical.Algebra.Group.Presentation.RelIndex.Pres
 --              (F.T × IxR) ⊥.rec


 -- F→FR : GroupHom N.GroupT F.GroupT
 -- fst F→FR = N.RecT.f w
 --  where
 --  open N.RecT
 --  w : N.RecT _
 --  isSetA w = F.trunc
 --  εA w = F.ε
 --  ∷A w b (x , ixR) = ((b , ((F.inv x)  F.· ((F.sq→T (rels ixR)) F.· x)))) F.·∷_
 --  inv∷A w false ixG a = {!!}
 --  inv∷A w true ixG a = {!!}
 
 -- IsGroupHom.pres· (snd F→FR) = {!!}
 -- IsGroupHom.pres1 (snd F→FR) = {!!}
 -- IsGroupHom.presinv (snd F→FR) = {!!}
 
 -- -- H : Subgroup F.GroupT
 -- -- fst H = {!!}
 -- -- snd H = {!!}

 
 -- open Cubical.Algebra.Group.Presentation.RelIndex.Pres IxG rels
 --  renaming (_·_ to _·*_ ; η to η')

 -- isNormal-imSubgroup-N→FR : isNormal (imSubgroup F→FR)
 -- isNormal-imSubgroup-N→FR g h = PT.map
 --   λ (h' , h'∈) → {!!} , {!!} 
 --   -- PT.∣ {!!} , {!!} ∣₁

 -- QIso : Iso T ⟨ F.GroupT /
 --           (imSubgroup F→FR ,
 --             isNormal-imSubgroup-N→FR) ⟩
 -- QIso = {!!}


 
