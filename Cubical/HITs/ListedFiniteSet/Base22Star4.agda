{-# OPTIONS --safe    #-} 
module Cubical.HITs.ListedFiniteSet.Base22Star4 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sigma

open import Cubical.Data.FinData.Transpositions

import Cubical.Functions.Logic as Lo
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.Function
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Foundations.Univalence


open import Cubical.HITs.EilenbergMacLane1

-- open import Cubical.Data.FinData

open import Cubical.Data.Nat.Order.Recursive

import Cubical.Data.SumFin as F


open import Cubical.HITs.ListedFiniteSet.Base3

-- open import Cubical.Data.FinData.GTrun

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.GroupoidTruncation as GT
open import Cubical.HITs.SetTruncation as ST


open import Cubical.Functions.Involution

open import Cubical.Homotopy.EilenbergMacLane.Properties

open import Cubical.Data.FinSet


open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.SymmetricGroup
open import Cubical.Algebra.Group.Generators

open import Cubical.HITs.ListedFiniteSet.Base22Star2
open import Cubical.HITs.ListedFiniteSet.Base22Star3


 -- look-tab-Iso : Iso (FMSet2 A) (Σ𝔽→ A) --(Σ (FMSet2 Unit) λ xs → 𝔽in xs → A)
 -- Iso.fun look-tab-Iso xs = fm⊤ xs , FM2look' xs
 -- Iso.inv look-tab-Iso = uncurry fm2tab
 -- Iso.rightInv look-tab-Iso =
 --    uncurry λ xs f → ΣPathP
 --     (RElimSet'.f lt-sec-fst xs f ,
 --      λ i → RElimSet'.f lt-sec-snd xs i f)
 -- Iso.leftInv look-tab-Iso = RElimSet'.f lt-ret

private
  variable
    ℓ : Level
    A : Type ℓ

GroupoidLoop : isGroupoid A → A → Group _
GroupoidLoop {A = A} isGroupoidA a =
  makeGroup {G = (a ≡ a)}
    refl _∙_ sym
    (isGroupoidA _ _) assoc
     (sym ∘ rUnit) (sym ∘ lUnit)
      rCancel lCancel

FMℙermG : ∀ n → Group (ℓ-suc ℓ-zero)
FMℙermG n = GroupoidLoop trunc (rep Unit n)

FMℙerm : ∀ n → Type₁
FMℙerm n = EM₁ (FMℙermG n)

sucFMℙerm : ∀ {n} → FMℙerm n → FMℙerm (suc n)
sucFMℙerm {n} = EMrec.f {B = FMℙerm (suc n)} {emsquash}
 w
 where
 w : EMrec (FMℙermG n) emsquash
 EMrec.b w = embase
 EMrec.bloop w = emloop ∘ cong (_ ∷2_)
 EMrec.bComp w g h =
  emcomp _ _ ▷ cong emloop
    (sym (congFunct (_ ∷2_) _ _)) 

-- 𝕃ist : ?
-- 𝕃ist : ? 



[_]_↔_ : ∀ n → (Fin n → A) → (Fin n → A) → Type _
[ n ] x ↔ y = {!Σ ? ?!}

-- _↔_ : {!∀ n → ? !}
-- _↔_ = {!!}

-- -- commFMℙerm : ∀ n (b : FMℙerm n) →       
-- --       sucFMℙerm (sucFMℙerm b) ≡
-- --       sucFMℙerm (sucFMℙerm b)
-- -- commFMℙerm n = EMelimSet.f w
-- --  where
-- --  w : EMelimSet (FMℙermG n)
-- --        (λ z → sucFMℙerm (sucFMℙerm z) ≡ sucFMℙerm (sucFMℙerm z))
-- --  EMelimSet.isSetB w _ = emsquash _ _
-- --  EMelimSet.b w = emloop (comm _ _ _)
-- --  EMelimSet.bPathP w g = {!!}
-- --    -- hcomp
-- --    --  (λ l → λ {
-- --    --     (i = i0) → {!!}
-- --    --    ;(i = i1) → {!!}
-- --    --    ;(j = i0) → {!!}
-- --    --    ;(j = i1) → {!!} })
-- --    --     (emloop (λ i₁ → comm _ _ (g i₁) i₁) j) 
    

-- -- -- i = i0 ⊢ emloop (comm Unit Unit (rep Unit n)) j
-- -- -- i = i1 ⊢ emloop (comm Unit Unit (rep Unit n)) j
-- -- -- j = i0 ⊢ emloop (λ i₁ → Unit ∷2 Unit ∷2 g i₁) i
-- -- -- j = i1 ⊢ emloop (λ i₁ → Unit ∷2 Unit ∷2 g i₁) i


-- --  -- w
-- --  -- where
-- --  -- w : EMrec (FMℙermG n) emsquash
-- --  -- EMrec.b w = embase
-- --  -- EMrec.bloop w = emloop ∘ cong (_ ∷2_)
-- --  -- EMrec.bComp w _ _ =
-- --  --   emcomp _ _ ▷ cong emloop (sym (cong-∙ (_ ∷2_) _ _)) 


-- -- FMSet2⊤→ΣFMℙerm : FMSet2 Unit → Σ ℕ FMℙerm
-- -- FMSet2⊤→ΣFMℙerm = RRec.f w
-- --  where
-- --  w : RRec {B = Σ ℕ FMℙerm}
-- --    (isGroupoidΣ (isSet→isGroupoid isSetℕ) (λ _ → emsquash))
-- --  RRec.[]* w = zero , embase
-- --  (w RRec.∷* _) (n , x) = suc n , sucFMℙerm x
-- --  RRec.comm* w = {!!}
-- --  RRec.comm-inv* w = {!!}
-- --  RRec.commmL* w = {!!}
-- --  RRec.commmR* w = {!!}
-- --  RRec.commpL* w = {!!}
-- --  RRec.commpR* w = {!!}
-- --  RRec.hex* w = {!!}

-- -- zz : {!!}
-- -- zz = {!!}


-- -- -- IsomFMSet⊤ΣFMℙerm : Iso (FMSet2 Unit) (Σ  _ FMℙerm)
-- -- -- Iso.fun IsomFMSet⊤ΣFMℙerm = FMSet2⊤→ΣFMℙerm
-- -- -- Iso.inv IsomFMSet⊤ΣFMℙerm = {!!}
-- -- -- Iso.rightInv IsomFMSet⊤ΣFMℙerm = {!!}
-- -- -- Iso.leftInv IsomFMSet⊤ΣFMℙerm = {!!}

-- -- -- iso-fmset-Σem : {!!}
-- -- -- iso-fmset-Σem = {!!}


