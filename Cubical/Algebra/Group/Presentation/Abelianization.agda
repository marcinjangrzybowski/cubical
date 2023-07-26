{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Abelianization where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
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

open import Cubical.HITs.S1

open import Cubical.Algebra.Group.Presentation.RelIndex
 using (Sq ; sq ; cns ; fc)

import Cubical.Algebra.Group.Presentation.RelIndex

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Algebra.Group.Abelianization.Properties renaming (rec to recAb ; elimProp to  elimPropAb ; elimProp2 to  elimProp2Ab)


open import Cubical.Data.Int hiding (_·_)

private
 variable
  ℓ ℓ' : Level

module _ {IxG : Type ℓ} {IxR : Type ℓ'} where

 open Cubical.Algebra.Group.Presentation.RelIndex.Pres IxG
  renaming (_·_ to _·*_ ; η to η')

 module PresentationAbelianization (rels : IxR → Sq IxG) where
  
  relsAb = (⊎.rec {A = IxG × IxG}
      (λ (x , y) →
       sq (fc true x) (fc true x) (fc true y) (fc true y))
        rels)

  _·'_ = _·*_ rels
  _·''_ = _·*_ relsAb


  head-comm-false : ∀ x y (xs : T relsAb) → 
    (false , y) ∷ (true , x) ∷ xs ≡ ((true , x) ∷ (false , y) ∷ xs)
  head-comm-false x y xs = 
     let z = cong ((false , y) ∷_)
            (rel (inl (y , x)) (((false , y)) ∷ xs))
     in sym (cong (λ xs → _ ∷ _ ∷ xs) (inv∷ false y xs))
          ∙∙ z ∙∙ inv∷ true y _
     
  head-comm-η : ∀ x y (xs : T relsAb) →
     x ∷ y ∷ xs ≡ (y ∷ x ∷ xs)
  head-comm-η (false , x) (false , y) = relInv relsAb (inl (x , y)) 
  head-comm-η (false , x) (true , y) xs = head-comm-false _ _ _
  head-comm-η (true , x) (false , y) xs = sym (head-comm-false _ _ _)
  head-comm-η (true , x) (true , y) = rel (inl (y , x))
  
 
  
  comm·η : ∀ b x y → (b , x) ∷ y ≡ y ·'' ((b , x) ∷ ε)
  comm·η b x = ElimPropT.f relsAb w
   where
   
   open ElimPropT relsAb
   w : ElimPropT _ λ z → (b , x) ∷ z ≡ (z ·'' ((b , x) ∷ ε))
   isPropA w _ = trunc _ _
   εA w = refl
   ∷A w {xs} b x' p = head-comm-η _ _ _ ∙ cong (_ ∷_) p     
   
  comm·'' : ∀ x y → x ·'' y ≡ y ·'' x
  comm·'' = ElimPropT.f relsAb w
   where
   
   open ElimPropT relsAb
   w : ElimPropT _ _
   isPropA w _ = isPropΠ λ _ → trunc _ _
   εA w p = sym (·IdR relsAb p) 
   ∷A w {xs} b x p y =
     (·assoc relsAb ((b , x) ∷ ε) _ _)
      ∙∙ cong ((b , x) ∷_) (p y) ∙∙
      (cong (_·'' xs) (comm·η b x y) ∙ sym (·assoc relsAb y ((b , x) ∷ ε) xs)) 


  invAbR : RecT relsAb (T relsAb)
  RecT.isSetA invAbR = trunc
  RecT.εA invAbR = ε
  RecT.∷A invAbR b x = (𝟚.not b , x) ∷_
  RecT.inv∷A invAbR b x xs = inv∷ (𝟚.not b) x xs
  RecT.relA invAbR ixR xs =
    lem∷fc _ _ ∙∙ relInv relsAb ixR xs ∙∙ sym (lem∷fc _ _)
   where
   open Cubical.Algebra.Group.Presentation.RelIndex.FcCons
   lem∷fc : ∀ f₀ f₁ → fcCons IxG
      (uncurry (λ b x → _∷_ (𝟚.not b , x))) f₁
      (fcCons IxG
       (uncurry (λ b x → _∷_ (𝟚.not b , x))) f₀ xs)
      ≡
      (_fc∷_ relsAb)
      (notFC relsAb f₀)
      ((_fc∷_ relsAb)
       (notFC relsAb f₁)
       xs)
       -- 
   lem∷fc (fc x x₁) (fc x₂ x₃) = head-comm-η _ _ _ 
   lem∷fc (fc x x₁) cns = refl
   lem∷fc cns (fc x x₁) = refl
   lem∷fc cns cns = refl

  invAb : T relsAb → T relsAb
  invAb = RecT.f _ invAbR
  
  invAb≡inv : ∀ x → invAb x ≡ inv _ x
  invAb≡inv = ElimPropT.f _ w
   where
   w : ElimPropT _ _
   ElimPropT.isPropA w _ = trunc _ _
   ElimPropT.εA w = refl
   ElimPropT.∷A w {xs} b x p =
    cong ((𝟚.not b , x) ∷_) p ∙ comm·'' _ _

  AbGroupT : AbGroup _
  fst AbGroupT = _
  AbGroupStr.0g (snd AbGroupT) = ε
  AbGroupStr._+_ (snd AbGroupT) = _
  AbGroupStr.- snd AbGroupT = invAb
  IsAbGroup.isGroup (AbGroupStr.isAbGroup (snd AbGroupT)) =
    makeIsGroup
      trunc
      (·assoc _)
      (·IdR _) (·IdL _)
      (λ x → cong (x ·''_) (invAb≡inv x) ∙ ·InvR _ x)
      (λ x → cong (_·'' x) (invAb≡inv x) ∙ ·InvL _ x)

  IsAbGroup.+Comm (AbGroupStr.isAbGroup (snd AbGroupT)) = comm·''

  T→AbT : T rels → T relsAb 
  T→AbT = RecT.f _ Ab→Ab'r
   where
   open RecT
   Ab→Ab'r : RecT _ (T relsAb)
   isSetA Ab→Ab'r = trunc
   εA Ab→Ab'r = ε
   ∷A Ab→Ab'r b x = (b , x) ∷_
   inv∷A Ab→Ab'r = inv∷
   relA Ab→Ab'r ixR a = rel (inr ixR) a

  pres· : (x y : fst (GroupT rels)) →
      T→AbT ((snd (GroupT rels) GroupStr.· x) y) ≡
      (snd (GroupT relsAb) GroupStr.· T→AbT x) (T→AbT y)
  pres· = ElimPropT.f rels w
   where
   
   open ElimPropT rels
   w : ElimPropT _ _
   isPropA w _ = isPropΠ λ _ → trunc _ _
   εA w _ = refl
   ∷A w b x p y = cong (_ ∷_) (p y)


   
  T→AbT-Mor : IsGroupHom (snd (GroupT rels)) T→AbT
    (AbGroupStr→GroupStr (snd (AbGroupT)))
  IsGroupHom.pres· T→AbT-Mor = pres·

  IsGroupHom.pres1 T→AbT-Mor = refl
  IsGroupHom.presinv T→AbT-Mor = ElimPropT.f rels w
   where

   open ElimPropT relsAb
   w : ElimPropT _ _
   isPropA w _ = trunc _ _
   εA w = refl
   ∷A w {xs} b x p =
     pres· _ _ ∙∙
    comm·'' _ _ ∙∙ cong ((𝟚.not b , x) ∷_) p
 
  Ab→Ab' : Abelianization (GroupT rels) → T relsAb
  Ab→Ab' = recAb
   _
   trunc
    T→AbT
    λ a b c →
      pres· _ _
       ∙∙ cong (snd (GroupT relsAb) GroupStr.· T→AbT a)
           (pres· _ _ ∙∙ comm·'' _ _ ∙∙ sym (pres· _ _) )
       ∙∙ sym (pres· _ _)

  open AbelianizationGroupStructure (GroupT rels)

  Ab'→Ab : T relsAb → Abelianization (GroupT rels)    
  Ab'→Ab = RecT.f _ w
   where
   open RecT
   w : RecT _ _
   isSetA w = isset
   εA w = η ε
   ∷A w b x = η ((b , x) ∷ ε ) ·Ab_ 
    
   inv∷A w b ixG = elimPropAb
     _
     (λ _ → isset _ _)
     λ _ → cong η
           (inv∷ _ _ _)  
   relA w (inl (x , y)) =
     elimPropAb
     _
     (λ _ → isset _ _)
     (λ a → 
        cong (_·Ab (η a))
           (commAb (η ((true , y) ∷ ε))
            (η ((true , x) ∷ ε))))
   relA w (inr ixR) =
     elimPropAb
     _
     (λ _ → isset _ _)
     λ xs → sym (lem xs _ _) ∙∙ cong η
            (rel ixR xs ) ∙∙ lem xs _ _
    where
     lem : ∀ xs f0 f1 →
         η
      ((IxG Cubical.Algebra.Group.Presentation.RelIndex.Pres.fc∷ rels)
       (f1)
       ((IxG Cubical.Algebra.Group.Presentation.RelIndex.Pres.fc∷ rels)
        (f0) xs))
      ≡
      Cubical.Algebra.Group.Presentation.RelIndex.FcCons.fcCons IxG
      (uncurry (λ b x → _·Ab_ (η ((b , x) ∷ ε))))
      (f1)
      (Cubical.Algebra.Group.Presentation.RelIndex.FcCons.fcCons IxG
       (uncurry (λ b x → _·Ab_ (η ((b , x) ∷ ε))))
       (f0) (η xs))
     lem xs (fc x x₁) (fc x₂ x₃) = refl
     lem xs (fc x x₁) cns = refl
     lem xs cns (fc x x₁) = refl
     lem xs cns cns = refl



  retAb'→Ab : retract Ab'→Ab Ab→Ab'
  retAb'→Ab = ElimPropT.f _ w
   where
   open ElimPropT rels

   lem : ∀ b x xs → Ab→Ab'
      (η ((b , x) ∷ ε) ·Ab xs)
      ≡ (b , x) ∷ (Ab→Ab' xs)
   lem b x = 
    elimPropAb
     _
     (λ _ → trunc _ _)
     λ _ → refl
   
   w : ElimPropT _ _
   isPropA w _ = trunc _ _
   εA w = refl
   ∷A w {xs} b x p = (lem b x (Ab'→Ab xs )) ∙ cong ((b , x) ∷_) p
                

  secAb'→Ab : section Ab'→Ab Ab→Ab'
  secAb'→Ab = elimPropAb
    _ (λ _ → isset _ _)
    (ElimPropT.f _ w)
   where
   open ElimPropT rels
   w : ElimPropT rels _
   isPropA w _ = isset _  _
   εA w = refl
   ∷A w {xs} b x p = cong (η ((b , x) ∷ ε) ·Ab_) p


  
  IsoAbAb' : Iso (Abelianization (GroupT rels)) (T relsAb)
  Iso.fun IsoAbAb' = Ab→Ab'
  Iso.inv IsoAbAb' = Ab'→Ab
  Iso.rightInv IsoAbAb' = retAb'→Ab
  Iso.leftInv IsoAbAb' = secAb'→Ab

  Ab'→Ab-hom : IsGroupHom (snd (AbGroup→Group (asAbelianGroup))) Ab→Ab'
    (AbGroupStr→GroupStr (snd (AbGroupT)))
  IsGroupHom.pres· Ab'→Ab-hom =
    elimProp2Ab _ (λ _ _ → trunc _ _) pres·
  IsGroupHom.pres1 Ab'→Ab-hom = refl
  IsGroupHom.presinv Ab'→Ab-hom = 
    elimPropAb _ (λ _ → trunc _ _) (IsGroupHom.presinv T→AbT-Mor)

  -- AbGroupIsoAb'Ab : AbGroupIso asAbelianGroup AbGroupT
  -- fst AbGroupIsoAb'Ab = IsoAbAb'
  -- snd AbGroupIsoAb'Ab = Ab'→Ab-hom
