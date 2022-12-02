{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Setoids where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Relation.Binary

open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Limits

open import Cubical.HITs.SetQuotients renaming ([_] to [_]/)

import Cubical.HITs.PropositionalTruncation as PT


open import Cubical.Categories.Adjoint

open import Cubical.Data.Unit

open import Cubical.Categories.NaturalTransformation

open Category

record Setoid (ℓ ℓR : Level) : Type (ℓ-suc (ℓ-max ℓ ℓR)) where
  constructor st
  field
    Carrier : Type ℓ
    rel : EquivSetRel Carrier ℓR
    is-set : isSet Carrier
    

open Setoid

record SetoidMor {ℓ ℓR ℓ' ℓR' : Level} (A : Setoid ℓ ℓR) (B : Setoid ℓ' ℓR') :
          Type (ℓ-max (ℓ-max ℓ ℓR) (ℓ-max ℓ' ℓR')) where
  constructor sm
  field
    f : Carrier A → Carrier B
    r : ∀ a a' → fst (fst (rel A)) a a' → fst (fst (rel B)) (f a) (f a') 

compSetoidMor : {ℓ ℓR ℓ' ℓR' ℓ'' ℓR'' : Level} {A : Setoid ℓ ℓR} {B : Setoid ℓ' ℓR'}
                     {C : Setoid ℓ'' ℓR''} →
                      SetoidMor  A B → SetoidMor B C → SetoidMor A C
SetoidMor.f (compSetoidMor (sm f r) (sm f₁ r₁)) = f₁ ∘f f
SetoidMor.r (compSetoidMor (sm f r) (sm f₁ r₁)) _ _ = (r₁ _ _) ∘f (r _ _)

module _ {ℓ : Level} where
  SETOID : Category (ℓ-suc ℓ) ℓ
  ob SETOID = Setoid ℓ ℓ
  Hom[_,_] SETOID = SetoidMor
  id SETOID = sm (idfun _) (λ _ _ → idfun _)
  _⋆_ SETOID = compSetoidMor
  ⋆IdL SETOID f = refl 
  ⋆IdR SETOID f = refl
  ⋆Assoc SETOID f g h = refl
  isSetHom SETOID = {!!}


-- record Setoid' (ℓV ℓE : Level) : Type (ℓ-suc (ℓ-max ℓV ℓE)) where
--   constructor st
--   field
--     V : hSet ℓV
--     E : hSet ℓE
--     s t : fst E → fst V
--     reflE : fst V → fst E
--     symE : fst E → fst E
--     reflS : ∀ a → s (reflE a) ≡ a
--     reflT : ∀ a → t (reflE a) ≡ a
--     symST : ∀ e → (s e) ≡ t (symE e)
--     symTS : ∀ e → (s e) ≡ t (symE e)
--     -- z : 
--     -- rel : EquivSetRel Carrier ℓR
--     -- is-set : isSet Carrier
    






-- private
--   variable
--     ℓ ℓ' : Level

  open Functor

  
  idRel : ((A , _) : hSet ℓ) → EquivSetRel A ℓ
  fst (fst (idRel A)) = _≡_
  snd (fst (idRel A)) a b = isProp→isSet (snd A _ _)
  BinaryRelation.isEquivRel.reflexive (snd (idRel A)) a = refl
  BinaryRelation.isEquivRel.symmetric (snd (idRel A)) a b = sym
  BinaryRelation.isEquivRel.transitive (snd (idRel A)) a b c = _∙_

  fullRel : ((A , _) : hSet ℓ) → EquivSetRel A ℓ
  fst (fst (fullRel _)) = λ _ _ → Unit*
  snd (fst (fullRel _)) = λ _ _ → isSetUnit*
  snd (fullRel _) = BinaryRelation.equivRel
   (λ a → tt*) (λ a b _ → tt*) (λ a b c _ _ → tt*)

  -- fullRel' : (A : hSet ℓ) → EquivSetRel (Unit* {ℓ = ℓ}) ℓ
  -- fst (fst (fullRel' A)) = λ _ _ → fst A
  -- snd (fst (fullRel' A)) = λ _ _ → snd A
  -- BinaryRelation.isEquivRel.reflexive (snd (fullRel' A)) = {!!}
  -- BinaryRelation.isEquivRel.symmetric (snd (fullRel' A)) = {!!}
  -- BinaryRelation.isEquivRel.transitive (snd (fullRel' A)) = {!!}

  Disc : Functor (SET ℓ) SETOID
  F-ob Disc x = st (fst x) (idRel x) (snd x)
  F-hom Disc x = sm x λ _ _ → cong _
  F-id Disc = refl
  F-seq Disc f g = refl

  Codisc : Functor (SET ℓ) SETOID
  F-ob Codisc x = st (fst x) (fullRel x) (snd x)
  F-hom Codisc x = sm x (λ a a' _ → tt*)
  F-id Codisc = refl
  F-seq Codisc f g = cong₂ sm refl λ _ _ _ _ → tt* 

  -- Codisc' : Functor (SET ℓ) SETOID
  -- F-ob Codisc' x = st ({!!} → fst x) ((fullRel ((_ → fst x) , {!!}))) {!!}
  -- F-hom Codisc' = {!!}
  -- F-id Codisc' = {!!}
  -- F-seq Codisc' = {!!}

  Π : Functor SETOID (SET ℓ) 
  F-ob Π x = ( Carrier x / fst (fst (rel x))) , squash/
  F-hom Π (sm f r) = rec squash/ ([_]/ ∘f f) λ _ _ → eq/ _ _ ∘f r _ _
  F-id Π {x = x} = funExt (elimProp (λ _ → squash/ _ _) λ _ → refl)
  F-seq Π {x} {y} {z} f g = funExt (elimProp (λ _ → squash/ _ _) λ _ → refl)

  Γ : Functor SETOID (SET ℓ) 
  F-ob Γ x = Carrier x , is-set x
  F-hom Γ (sm f _) = f
  F-id Γ = refl
  F-seq Γ _ _ = refl

  Γ' : Functor SETOID (SET ℓ) 
  F-ob Γ' x = Σ (Carrier x) (λ c → fst (fst (rel x)) c c ) , isSetΣ (is-set x) λ _ → snd (fst (rel x)) _ _
  F-hom Γ' (sm f r) (c , e) = (f c) , r c c e
  F-id Γ' = refl
  F-seq Γ' _ _ = refl


  open Cubical.Categories.Adjoint.NaturalBijection --UnitCounit

  module _ (C : Setoid ℓ ℓ) (D : hSet ℓ) where
    aI : Iso (SET ℓ [ Π ⟅ C ⟆ , D ]) ( SETOID [ C , Disc ⟅ D ⟆ ])
    Iso.fun aI f = sm _ λ _ _ → cong f ∘f eq/ _ _
    Iso.inv aI _ = rec (snd D) _ _
    Iso.rightInv aI b = refl
    Iso.leftInv aI a = funExt (elimProp (λ _ → snd D _ _) λ _ → refl)
    
  Π⊣Disc : Π ⊣ Disc
  _⊣_.adjIso Π⊣Disc {c} {d} = aI c d
  _⊣_.adjNatInD Π⊣Disc f k = refl
  _⊣_.adjNatInC Π⊣Disc {d = d} g h = funExt (elimProp (λ _ → snd d _ _) λ _ → refl)


  module _ (C : hSet ℓ) (D : Setoid ℓ ℓ)  where
    open BinaryRelation.isEquivRel ((snd (D .rel)))
    
    aI'' : Iso (SETOID [ Disc ⟅ C ⟆ , D ]) (SET ℓ [ C , Γ' ⟅ D ⟆ ])
    Iso.fun aI'' (sm f r) c = (f c) , r c c refl
    Iso.inv aI'' x = sm ( fst ∘f x) λ a a' x₁ →  subst (fst (D .rel) .fst (fst (x a))) (cong (fst ∘f x) x₁) (snd (x a)) 
    Iso.rightInv aI'' _ = funExt λ _ → ΣPathP (refl , (transportRefl _))
    Iso.leftInv aI'' (sm f r) = congP₂ (λ _ → sm) refl
     (funExt λ a  → funExt λ a' → funExt
       (J (λ a' (x : a ≡ a') →
      subst (λ zz → fst (D .rel) .fst (f a) (f zz)) x
      (r a a (λ _ → a))
      ≡ r a a' x) (transportRefl _))) 
     

  Disc⊣Γ' : Disc ⊣ Γ'
  _⊣_.adjIso Disc⊣Γ' {c} {d} = aI'' c d
  _⊣_.adjNatInD Disc⊣Γ' f k = refl
  _⊣_.adjNatInC Disc⊣Γ' g h = refl


  module _ (C : Setoid ℓ ℓ) (D : hSet ℓ)  where
    open BinaryRelation.isEquivRel ((snd (C .rel)))
    
    aI''' : Iso (SET ℓ [ Γ ⟅ C ⟆ , D ]) (SETOID [ C , Codisc ⟅ D ⟆ ])
    Iso.fun aI''' x = sm x (λ a a' x₁ → tt*)
    Iso.inv aI''' (sm f r) = f
    Iso.rightInv aI''' b = refl
    Iso.leftInv aI''' a = refl

  Γ⊣Codisc : Γ ⊣ Codisc 
  _⊣_.adjIso Γ⊣Codisc {c} {d} = aI''' c d 
  _⊣_.adjNatInD Γ⊣Codisc _ _ = refl
  _⊣_.adjNatInC Γ⊣Codisc _ _ = refl


--   module _ (C : hSet ℓ) (D : Setoid ℓ ℓ)  where
--     open BinaryRelation.isEquivRel ((snd (D .rel)))
    
--     aI' : Iso (SETOID [ Disc ⟅ C ⟆ , D ]) (SET ℓ [ C , Γ ⟅ D ⟆ ])
--     Iso.fun aI' (sm f r) = f
--     Iso.inv aI' x = sm x λ a a' x₁ → subst (fst (D .rel) .fst (x a)) (cong x x₁) (reflexive (x a))
--     Iso.rightInv aI' _ = refl
--     Iso.leftInv aI' (sm f r) = 
--      congP₂ (λ _ → sm) refl
--       (funExt λ a  → funExt λ a' → funExt 
--         (J (λ a' x →
--                 subst (fst (D .rel) .fst (f a))
--                (cong f x) (reflexive (f a))
--                ≡ r a a' x)
--           (transportRefl _ ∙ {!!})))

--   Disc⊣Γ : Disc ⊣ Γ
--   _⊣_.adjIso Disc⊣Γ {c} {d} = {!!}
--   _⊣_.adjNatInD Disc⊣Γ = {!!}
--   _⊣_.adjNatInC Disc⊣Γ = {!!}


--   -- l1 : NatTrans 𝟙⟨ SETOID ⟩ (funcComp Disc Π)
--   -- SetoidMor.f (NatTrans.N-ob l1 x) = [_]
--   -- SetoidMor.r (NatTrans.N-ob l1 x) a a'  = eq/ _ _
--   -- NatTrans.N-hom l1 f = cong₂ sm refl refl

--   -- Π⊣Disc : Π ⊣ Disc
--   -- _⊣_.η Π⊣Disc = natTrans (λ _ → sm [_] eq/) λ _ → refl
--   -- _⊣_.ε Π⊣Disc =
--   --   natTrans (λ x → rec (snd x) (idfun _) λ _ _ → idfun _ )
--   --             λ {_} {y} _ → funExt (elimProp (λ _ → snd y _ _) λ _ → refl )
--   -- NatTrans.N-ob (_⊣_.Δ₁ Π⊣Disc i) = {!!}
--   -- NatTrans.N-hom (_⊣_.Δ₁ Π⊣Disc i) = {!!}
--   --   -- cong₂ natTrans (funExt (λ x → funExt λ y → {!!})) {!!}
--   -- _⊣_.Δ₂ Π⊣Disc = {!!}
    


-- -- -- -- Hom functors
-- -- -- _[-,_] : (C : Category ℓ ℓ') → (c : C .ob) → Functor (C ^op) (SET ℓ')
-- -- -- (C [-, c ]) .F-ob x    = (C [ x , c ]) , C .isSetHom
-- -- -- (C [-, c ]) .F-hom f k = f ⋆⟨ C ⟩ k
-- -- -- (C [-, c ]) .F-id      = funExt λ _ → C .⋆IdL _
-- -- -- (C [-, c ]) .F-seq _ _ = funExt λ _ → C .⋆Assoc _ _ _

-- -- -- _[_,-] : (C : Category ℓ ℓ') → (c : C .ob)→ Functor C (SET ℓ')
-- -- -- (C [ c ,-]) .F-ob x    = (C [ c , x ]) , C .isSetHom
-- -- -- (C [ c ,-]) .F-hom f k = k ⋆⟨ C ⟩ f
-- -- -- (C [ c ,-]) .F-id      = funExt λ _ → C .⋆IdR _
-- -- -- (C [ c ,-]) .F-seq _ _ = funExt λ _ → sym (C .⋆Assoc _ _ _)

-- -- -- module _ {C : Category ℓ ℓ'} {F : Functor C (SET ℓ')} where
-- -- --   open NatTrans

-- -- --   -- natural transformations by pre/post composition
-- -- --   preComp : {x y : C .ob}
-- -- --           → (f : C [ x , y ])
-- -- --           → C [ x ,-] ⇒ F
-- -- --           → C [ y ,-] ⇒ F
-- -- --   preComp f α .N-ob c k = (α ⟦ c ⟧) (f ⋆⟨ C ⟩ k)
-- -- --   preComp f α .N-hom {x = c} {d} k
-- -- --     = (λ l → (α ⟦ d ⟧) (f ⋆⟨ C ⟩ (l ⋆⟨ C ⟩ k)))
-- -- --     ≡[ i ]⟨ (λ l → (α ⟦ d ⟧) (⋆Assoc C f l k (~ i))) ⟩
-- -- --       (λ l → (α ⟦ d ⟧) (f ⋆⟨ C ⟩ l ⋆⟨ C ⟩ k))
-- -- --     ≡[ i ]⟨ (λ l → (α .N-hom k) i (f ⋆⟨ C ⟩ l)) ⟩
-- -- --       (λ l → (F ⟪ k ⟫) ((α ⟦ c ⟧) (f ⋆⟨ C ⟩ l)))
-- -- --     ∎

-- -- -- -- properties
-- -- -- -- TODO: move to own file
-- -- -- open isIso renaming (inv to cInv)
-- -- -- open Iso

-- -- -- module _ {A B : (SET ℓ) .ob } where

-- -- --   Iso→CatIso : Iso (fst A) (fst B)
-- -- --              → CatIso (SET ℓ) A B
-- -- --   Iso→CatIso is .fst = is .fun
-- -- --   Iso→CatIso is .snd .cInv = is .inv
-- -- --   Iso→CatIso is .snd .sec = funExt λ b → is .rightInv b -- is .rightInv
-- -- --   Iso→CatIso is .snd .ret = funExt λ b → is .leftInv b -- is .rightInv

-- -- --   CatIso→Iso : CatIso (SET ℓ) A B
-- -- --              → Iso (fst A) (fst B)
-- -- --   CatIso→Iso cis .fun = cis .fst
-- -- --   CatIso→Iso cis .inv = cis .snd .cInv
-- -- --   CatIso→Iso cis .rightInv = funExt⁻ λ b → cis .snd .sec b
-- -- --   CatIso→Iso cis .leftInv  = funExt⁻ λ b → cis .snd .ret b


-- -- --   Iso-Iso-CatIso : Iso (Iso (fst A) (fst B)) (CatIso (SET ℓ) A B)
-- -- --   fun Iso-Iso-CatIso = Iso→CatIso
-- -- --   inv Iso-Iso-CatIso = CatIso→Iso
-- -- --   rightInv Iso-Iso-CatIso b = refl
-- -- --   fun (leftInv Iso-Iso-CatIso a i) = fun a
-- -- --   inv (leftInv Iso-Iso-CatIso a i) = inv a
-- -- --   rightInv (leftInv Iso-Iso-CatIso a i) = rightInv a
-- -- --   leftInv (leftInv Iso-Iso-CatIso a i) = leftInv a

-- -- --   Iso-CatIso-≡ : Iso (CatIso (SET ℓ) A B) (A ≡ B)
-- -- --   Iso-CatIso-≡ = compIso (invIso Iso-Iso-CatIso) (hSet-Iso-Iso-≡ _ _)

-- -- -- -- SET is univalent

-- -- -- isUnivalentSET : isUnivalent {ℓ' = ℓ} (SET _)
-- -- -- isUnivalent.univ isUnivalentSET (A , isSet-A) (B , isSet-B)  =
-- -- --    precomposesToId→Equiv
-- -- --       pathToIso _ (funExt w) (isoToIsEquiv Iso-CatIso-≡)
-- -- --    where
-- -- --      w : _
-- -- --      w ci =
-- -- --        invEq
-- -- --          (congEquiv (isoToEquiv (invIso Iso-Iso-CatIso)))
-- -- --          (SetsIso≡-ext isSet-A isSet-B
-- -- --             (λ x i → transp (λ _ → B) i (ci .fst (transp (λ _ → A) i x)))
-- -- --             (λ x i → transp (λ _ → A) i (ci .snd .cInv (transp (λ _ → B) i x))))

-- -- -- -- SET is complete

-- -- -- open LimCone
-- -- -- open Cone

-- -- -- completeSET : ∀ {ℓJ ℓJ'} → Limits {ℓJ} {ℓJ'} (SET (ℓ-max ℓJ ℓJ'))
-- -- -- lim (completeSET J D) = Cone D (Unit* , isOfHLevelLift 2 isSetUnit) , isSetCone D _
-- -- -- coneOut (limCone (completeSET J D)) j e = coneOut e j tt*
-- -- -- coneOutCommutes (limCone (completeSET J D)) j i e = coneOutCommutes e j i tt*
-- -- -- univProp (completeSET J D) c cc =
-- -- --   uniqueExists
-- -- --     (λ x → cone (λ v _ → coneOut cc v x) (λ e i _ → coneOutCommutes cc e i x))
-- -- --     (λ _ → funExt (λ _ → refl))
-- -- --     (λ x → isPropIsConeMor cc (limCone (completeSET J D)) x)
-- -- --     (λ x hx → funExt (λ d → cone≡ λ u → funExt (λ _ → sym (funExt⁻ (hx u) d))))
