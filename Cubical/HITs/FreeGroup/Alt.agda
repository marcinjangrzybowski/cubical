{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.Alt where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Properties

import Cubical.HITs.FreeGroup.Base as B
import Cubical.HITs.FreeGroup.Properties as P

import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

module _ (A : Type ℓ) where

 infixr 5 _∷_ 

 data FreeGroup : Type ℓ where
  ε : FreeGroup
  _∷_ : (Bool × A) → FreeGroup → FreeGroup
  inv∷ : ∀ b A xs → ((not b) , A) ∷ (b , A) ∷ xs ≡ xs
  trunc : isSet FreeGroup


η : A → FreeGroup A
η = (_∷ ε) ∘ (true ,_)

record Rec {A : Type ℓ} (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
 no-eta-equality
 field
  isSetB : isSet B
  εB : B
  ∷B : Bool → A → B → B
  inv∷B : ∀ b a x → ∷B (𝟚.not b) a (∷B b a x) ≡ x

 go : FreeGroup A → B
 go ε = εB
 go ((b , a) ∷ xs) = ∷B b a (go xs)
 go (inv∷ b a xs i) = inv∷B b a (go xs) i
 go (trunc _ _ p q i j) =
    isSetB _ _ (cong go p) (cong go q) i j

module _ {A : Type ℓ} (B : FreeGroup A → Type ℓ') where

 record Elim₁  : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
   εB : B ε
   ∷B : ∀ b a {xs} → B xs → B ((b , a) ∷ xs)


 record Elim : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
   elim₁ : Elim₁
  open Elim₁ elim₁
  field
   isSetB : ∀ xs → isSet (B xs)
   inv∷B : ∀ b a {xs} x → 
     PathP (λ i → B (inv∷ b a xs i))
       (∷B (𝟚.not b) a (∷B b a x)) x

  go : ∀ x → B x 
  go ε = εB
  go ((b , a) ∷ xs) = ∷B b a (go xs)
  go (inv∷ b a xs i) = inv∷B b a (go xs) i
  go (trunc _ _ p q i j) =
    isSet→SquareP (λ i j → isSetB (trunc _ _ p q i j))
       (cong go p) (cong go q) refl refl i j 


 record ElimProp : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
   elim₁ : Elim₁
   isPropB : ∀ xs → isProp (B xs)

  private
   r : Elim
   Elim.elim₁ r = elim₁
   Elim.isSetB r = isProp→isSet ∘ isPropB
   Elim.inv∷B r b a x =
     isProp→PathP (λ _ → isPropB _) _ _

  open Elim r public using (go)

open Elim₁ public
open Elim public hiding (go)
open ElimProp public hiding (go)

_·_ : FreeGroup A → FreeGroup A → FreeGroup A
ε · y = y
(x ∷ xs) · y = x ∷ (xs · y)
inv∷ b A x i · y = inv∷ b A (x · y) i
trunc _ _ p q i j · y =
    trunc _ _ (cong (_· y) p) (cong (_· y) q) i j

idr : ∀ (x : FreeGroup A) → x · ε ≡ x
idr = ElimProp.go r
 where
 r : ElimProp _
 εB (elim₁ r) = refl
 ∷B (elim₁ r) b a x = cong ((b , a) ∷_) x
 isPropB r _ = trunc _ _

·assoc : ∀ (x y z : FreeGroup A) → x · (y · z) ≡ (x · y) · z
·assoc = ElimProp.go r
 where

 r : ElimProp _
 εB (elim₁ r) _ _ = refl
 ∷B (elim₁ r) b a x _ _ = cong ((b , a) ∷_) (x _ _)
 isPropB r _ = isPropΠ2 λ _ _ → trunc _ _


inv : FreeGroup A  → FreeGroup A
inv = Rec.go r
 where
 open Rec
 r : Rec _
 isSetB r = trunc
 εB r = ε
 ∷B r b a x = x · (((not b) , a) ∷ ε)
 inv∷B r b a x =
    (λ i → ·assoc  x ((not b , a) ∷ ε)
                 ((notnot b i , a) ∷ ε) (~ i))
    ∙∙ cong (x ·_) (inv∷ b a ε) ∙∙ idr _


invr  : ∀ (x : FreeGroup A) → x · (inv x) ≡ ε
invr = ElimProp.go r
 where
 r : ElimProp _
 εB (elim₁ r) = refl
 ∷B (elim₁ r) b a {xs} x = 
   cong ((b , a) ∷_) (·assoc xs (inv xs) ((not b , a) ∷ ε))
    ∙∙ congP (λ i → ((notnot b (~ i) , a) ∷_) ∘ (_· ((not b , a) ∷ ε))) x
    ∙∙ inv∷ _ _ _
 isPropB r _ = trunc _ _

invl  : ∀ (x : FreeGroup A) → (inv x) · x ≡ ε
invl = ElimProp.go r
 where
 r : ElimProp _
 εB (elim₁ r) = refl
 ∷B (elim₁ r) b a {xs} =
   sym (·assoc (inv xs) _ _) ∙∙
     cong (inv xs ·_) (inv∷ _ _ _) ∙∙_  
 isPropB r _ = trunc _ _


freeGroupGroup : (A : Type ℓ) → Group ℓ
freeGroupGroup A = makeGroup {G = FreeGroup A}
  ε _·_ inv trunc
  ·assoc idr (λ _ → refl) invr invl

module _ {Group : Group ℓ'}  where


 module GS = GroupStr (snd Group) 
 open IsGroupHom

 module _ (ηG : A → Group .fst) where

  f : FreeGroup A → fst Group
  f = Rec.go w
   where
   open Rec
   w : Rec _
   isSetB w = GS.is-set 
   εB w = GS.1g
   ∷B w b a = (if b then (idfun _) else GS.inv) (ηG a) GS.·_
   inv∷B w false a x =
     GS.·Assoc _ _ _ ∙∙
      cong (GS._· x) (GS.·InvR _) ∙∙
      GS.·IdL x
   inv∷B w true a x =
     GS.·Assoc _ _ _ ∙∙
      cong (GS._· x) (GS.·InvL _) ∙∙
      GS.·IdL x

  f-pres· = ElimProp.go r
   where
   r : ElimProp λ x → ∀ y → f (x · y) ≡ f x GS.· f y
   εB (elim₁ r) _ = sym (GS.·IdL _)
   ∷B (elim₁ r) b a x y =
     cong (_ GS.·_) (x _)
      ∙ GS.·Assoc _ _ _
   isPropB r _ = isPropΠ λ _ → GS.is-set _ _

  isHomF : IsGroupHom (snd (freeGroupGroup A)) f (snd Group)
  pres· isHomF = f-pres·
  pres1 isHomF = refl
  presinv isHomF = ElimProp.go r
   where
   r : ElimProp _
   εB (elim₁ r) = sym (GroupTheory.inv1g Group)
   ∷B (elim₁ r) b a {xs} x =
        (f-pres· (inv xs) _ 
        ∙ cong (f (inv xs) GS.·_) (GS.·IdR _ ∙ h b))
     ∙∙ cong (GS._· GS.inv ((if b then (idfun _) else GS.inv) (ηG a))) x
     ∙∙ sym (GroupTheory.invDistr Group _ _)
     where
     h : ∀ b → (if not b then idfun (fst Group) else GS.inv) (ηG a) ≡
           GS.inv ((if b then idfun (fst Group) else GS.inv) (ηG a))
     h false = sym (GroupTheory.invInv Group _)
     h true = refl
   isPropB r _ = GS.is-set _ _ 

  rec : GroupHom (freeGroupGroup A) Group
  fst rec = f
  snd rec = isHomF




 freeGroupHom≡ : {f g : GroupHom (freeGroupGroup A) Group}
                → (∀ a → (fst f) (η a) ≡ (fst g) (η a)) → f ≡ g
 freeGroupHom≡  {f = f} {g} eqOnA =
   Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt (ElimProp.go
     w))
   where
   eqOnA' : ∀ b a → fst f ((b , a) ∷ ε) ≡ fst g ((b , a) ∷ ε)
   eqOnA' false a =
      presinv (snd f) (η a) ∙∙
       cong GS.inv (eqOnA a)
       ∙∙ sym (presinv (snd g) (η a))
   eqOnA' true a = eqOnA a

   w : ElimProp _
   εB (elim₁ w) =
     pres1 (snd f) ∙ sym (pres1 (snd g))
   ∷B (elim₁ w) b a {xs} x =
     pres· (snd f) ((b , a) ∷ ε) _ ∙∙
      cong₂ (GS._·_) (eqOnA' b a) x 
     ∙∙ sym (pres· (snd g) (((b , a) ∷ ε)) _)
   isPropB w _ = GS.is-set _ _


 A→Group≃GroupHom : (A → Group .fst) ≃ GroupHom (freeGroupGroup A) Group
 A→Group≃GroupHom = biInvEquiv→Equiv-right biInv where
   biInv : BiInvEquiv (A → Group .fst) (GroupHom (freeGroupGroup _) Group)
   BiInvEquiv.fun  biInv              = rec
   BiInvEquiv.invr biInv (hom , _) a  = hom (η a)
   BiInvEquiv.invr-rightInv biInv hom = freeGroupHom≡ (λ a → GS.·IdR _)
   BiInvEquiv.invl biInv (hom ,  _) a = hom (η a)
   BiInvEquiv.invl-leftInv biInv f    = funExt (λ a → GS.·IdR _)


IsoFreeGroupAlt : GroupIso (P.freeGroupGroup A) (freeGroupGroup A)
fst (IsoFreeGroupAlt {A = A}) = w
 where
 w : Iso _ _
 Iso.fun w = fst (P.rec η)
 Iso.inv w = fst (rec {Group = P.freeGroupGroup A} B.η)
 Iso.rightInv w = ElimProp.go ww
  where
  ww : ElimProp _
  εB (elim₁ ww) = refl
  ∷B (elim₁ ww) false a {xs} p = cong ((false , a) ∷_) p
  ∷B (elim₁ ww) true a {xs} p = cong ((true , a) ∷_) p
  isPropB ww _ = trunc _ _
 Iso.leftInv w = funExt⁻
  (cong fst (P.freeGroupHom≡ {Group = P.freeGroupGroup A}
     {f = compGroupHom (P.rec η) (rec {Group = P.freeGroupGroup A} B.η)}
     {idGroupHom}
     λ _ → sym (B.idr _)))
snd IsoFreeGroupAlt = snd (P.rec η)

