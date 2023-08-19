{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Quotient where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Powerset

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
open import Cubical.HITs.SetQuotients as SQ

open import Cubical.Algebra.Group.Presentation.RelIndex
 using (Sq ; sq ; cns ; fc)

import Cubical.Algebra.Group.Presentation.RelIndex

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup

open import Cubical.Algebra.Group.Abelianization.Properties renaming (rec to recAb ; elimProp to  elimPropAb ; elimProp2 to  elimProp2Ab)


open import Cubical.Algebra.Group.QuotientGroup renaming (_/_ to _/ᵍ_)

open import Cubical.Data.Int hiding (_·_)

private
 variable
  ℓ ℓ' : Level

module _ {IxG : Type ℓ} {IxR : Type ℓ} (rels : IxR → Sq IxG) where

 module F = Cubical.Algebra.Group.Presentation.RelIndex.Pres
              IxG ⊥.rec

 module N = Cubical.Algebra.Group.Presentation.RelIndex.Pres
              (F.T × IxR) ⊥.rec

 open Cubical.Algebra.Group.Presentation.RelIndex.Pres IxG rels
   renaming (η to η')


 F→T : GroupHom F.GroupT GroupT
 fst F→T = F.RecT.f w
  where
  open F.RecT

  w : F.RecT _
  isSetA w = trunc
  εA w = ε
  ∷A w b x = (b , x) ∷_
  inv∷A w = inv∷  
 IsGroupHom.pres· (snd F→T) = {!!}
 IsGroupHom.pres1 (snd F→T) = refl
 IsGroupHom.presinv (snd F→T) =
   F.ElimPropT.f w
  where
  open F.ElimPropT
  w : F.ElimPropT _ 
  isPropA w _ = trunc _ _
  εA w = refl
  ∷A w = {!!}


 F→FR : GroupHom N.GroupT F.GroupT
 fst F→FR = N.RecT.f w
  where
  open N.RecT
  w : N.RecT _
  isSetA w = F.trunc
  εA w = F.ε
  ∷A w b (x , ixR) = ((b , ((F.inv x)  F.· ((F.sq→T (rels ixR)) F.· x)))) F.·∷_
  inv∷A w false ixG a = {!!}
  inv∷A w true ixG a = {!!}
 
 IsGroupHom.pres· (snd F→FR) = {!!}
 IsGroupHom.pres1 (snd F→FR) = {!!}
 IsGroupHom.presinv (snd F→FR) = {!!}
 
 -- H : Subgroup F.GroupT
 -- fst H = {!!}
 -- snd H = {!!}

 
 
 isNormal-imSubgroup-N→FR : isNormal (imSubgroup F→FR)
 isNormal-imSubgroup-N→FR g h = PT.rec
   PT.squash₁ (uncurry
              λ x y →
               subst-∈ ⟪ imSubgroup F→FR ⟫
                   (cong (λ x' → g F.· (x' F.·  F.inv g))
                       y)
                (F.ElimPropT.f w g x) )
  where

  open ElimPropT
  w : F.ElimPropT λ g → ∀ x →
            (g F.· (fst F→FR x F.· F.inv g)) ∈ ⟪ imSubgroup F→FR ⟫
  isPropA w = {!!}
  εA w x = PT.∣ x , sym (F.·IdR _) ∣₁
  ∷A w b x p h = {!rec!}
  
 --  open ElimPropT
 --  w : N.ElimPropT λ x → ∀ g →
 --          (g F.· (fst F→FR x F.· F.inv g)) ∈ ⟪ imSubgroup F→FR ⟫
 --  isPropA w _ = isPropΠ λ _ → PT.squash₁
 --  εA w g = PT.∣ N.ε , sym (F.·InvR g) ∣₁
 --  ∷A w {xs} = flip (uncurry
 --     (F.ElimPropT.f ww))
 --    where
 --    ww : F.ElimPropT _
 --    isPropA ww _ = isPropΠ4 λ _ _ _ _ → PT.squash₁
 --    εA ww x y z = F.ElimPropT.f www
 --     where
 --     www : F.ElimPropT _
 --     isPropA www _ = PT.squash₁
 --     εA www = {!!}
 --      --   PT.map
 --      -- (λ (a , b) →
 --      --   {!!} ,
 --      --     {!b!})
 --      --  (z (F.sq→T (rels x)))
 --     ∷A www = {!!}
 --      -- PT.map (λ (q , qq) →
 --      --     ({!!}) ,
 --      --         {!qq!}
 --      --       -- {!!} ∙∙ cong (F._· ((y , F.sq→T (rels x)) F.·∷ F.ε)) qq
 --      --       --    ∙∙ {!!}
            
 --      --          )
 --      --     (z (w₁ F.· ((y , F.sq→T (rels x)) F.·∷ F.ε)))
 --     -- let (q , qq) = z w₁
 --     -- in PT.∣ {!z w₁!} ∣₁
 --    ∷A ww = {!!}
 --    -- PT.map λ (h , p) →
 --    --   {!!} , {!!}
 --  -- ∷A w true x _ = {!!}
   
 --   -- λ (h' , h'∈) → {!!} , {!!} 
 --   -- PT.∣ {!!} , {!!} ∣₁


 GroupT' = F.GroupT /ᵍ
           (imSubgroup F→FR ,
             isNormal-imSubgroup-N→FR)

 T→T' : T → ⟨ GroupT' ⟩
 T→T' = RecT.f w
  where
  open RecT
  w : RecT ⟨ GroupT' ⟩
  isSetA w = squash/
  εA w = [ F.ε ]
  ∷A w b ixG =
    SQ.setQuotUnaryOp
     (((b , ixG)) F.∷_)
      λ a a' → PT.map
        {!IsGroupHom.pres· (snd F→T)!}
  inv∷A w = {!!}
  relA w = {!!}


 kerN→T' : ∀ x → fst F→T (fst F→FR x) ≡ ε
 kerN→T' = N.ElimPropT.f
   w
  where
  open N.ElimPropT
  w : N.ElimPropT _
  isPropA w _ = trunc _ _
  εA w = refl
  ∷A w b (x , ixR) =
    let p : fst F→T (F.inv x F.· (F.sq→T (rels ixR) F.· x)) ≡ ε
        p = pres· _ _
              ∙∙ cong₂ (_·_) {!!} (pres· _ _)
              ∙∙
               (cong (inv (fst F→T x) ·_)
                  (cong (_· fst F→T x)
                   {!!}) ∙∙ {!!} ∙∙ {!!})
             -- cong (F.inv x F.·_)
             --     (cong (F._· x) {!ixG→T≡ε ?!} ∙ F.·IdL x) ∙ F.·InvL x
    in ({!!} ∙ {!!}) ∙_ 
   where
   open IsGroupHom (snd F→T)
 T'→T : ⟨ GroupT' ⟩ → T
 T'→T = SQ.rec trunc
   (fst F→T)
   λ a b → PT.elim (λ _ → trunc _ _)
     (λ (h , p) →
        invUniqueL (
             (sym (IsGroupHom.pres· (snd F→T) a (F.inv b)))
             
          ∙∙ cong (fst F→T) (sym p)
          ∙∙ kerN→T' h ) ∙
            invHomInv (snd (F.GroupT)) (fst F→T) (snd (GroupT))
              (IsGroupHom.pres· (snd F→T)) _)
  where
  open GroupTheory GroupT

 QIso : Iso T ⟨ GroupT' ⟩
 Iso.fun QIso = T→T'
 Iso.inv QIso = T'→T
 Iso.rightInv QIso = SQ.elimProp (λ _ → squash/ _ _)
   (F.ElimPropT.f w)
  where
  open F.ElimPropT
  w : F.ElimPropT _
  isPropA w _ = squash/ _ _
  εA w = refl
  ∷A w b x = {!!}
 Iso.leftInv QIso = ElimPropT.f w
  where
  open ElimPropT
  w : ElimPropT _
  isPropA w _ = trunc _ _
  εA w = refl
  ∷A w b xs =
    {!!}

 
