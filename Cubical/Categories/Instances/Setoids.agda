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
    rel : EquivPropRel Carrier ℓR
    is-set : isSet Carrier
    
open Setoid

record SetoidMor {ℓ ℓR ℓ' ℓR' : Level} (A : Setoid ℓ ℓR) (B : Setoid ℓ' ℓR') :
          Type (ℓ-max (ℓ-max ℓ ℓR) (ℓ-max ℓ' ℓR')) where
  constructor sm
  field
    f : Carrier A → Carrier B
    r : ∀ a a' → fst (fst (rel A)) a a' → fst (fst (rel B)) (f a) (f a') 

private
 variable
  ℓ ℓ' ℓR ℓR' : Level
  A : Setoid ℓ ℓR
  B : Setoid ℓ' ℓR'

isSetSetoidMor : isSet (SetoidMor A B) 
isSetSetoidMor {B = B} =
 isOfHLevelRetract 2 _ (uncurry sm) (λ _ → refl) (isSetΣ (isSet→ (is-set B) )
   (λ _ → isSetΠ2 λ _ _ → isSet→ (isProp→isSet (snd (fst (rel B)) _ _))))

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
  isSetHom SETOID = isSetSetoidMor


  isUnivalentSETOID : isUnivalent SETOID
  isUnivalent.univ isUnivalentSETOID x y = isoToIsEquiv w
   where
   w : Iso (x ≡ y) (CatIso SETOID x y)
   Iso.fun w = λ z → subst (CatIso SETOID x) z idCatIso
   Iso.inv w z = cong (uncurry (uncurry st))
     (Σ≡Prop {!!} (ΣPathP ((isoToPath {!!}) , {!!})))
   Iso.rightInv w = {!!}
   Iso.leftInv w = {!!}

  -- open Functor
  
  -- idRel : ((A , _) : hSet ℓ) → EquivPropRel A ℓ
  -- fst (fst (idRel A)) = _≡_
  -- snd (fst (idRel A)) a b = (snd A _ _)
  -- BinaryRelation.isEquivRel.reflexive (snd (idRel A)) a = refl
  -- BinaryRelation.isEquivRel.symmetric (snd (idRel A)) a b = sym
  -- BinaryRelation.isEquivRel.transitive (snd (idRel A)) a b c = _∙_

  -- fullRel : ((A , _) : hSet ℓ) → EquivPropRel A ℓ
  -- fst (fst (fullRel _)) = λ _ _ → Unit*
  -- snd (fst (fullRel _)) = λ _ _ → isPropUnit*
  -- snd (fullRel _) = BinaryRelation.equivRel
  --  (λ a → tt*) (λ a b _ → tt*) (λ a b c _ _ → tt*)

  -- Codisc Disc : Functor (SET ℓ) SETOID
  -- Γ Π         : Functor SETOID (SET ℓ)
    
  -- F-ob Disc x = st (fst x) (idRel x) (snd x)
  -- F-hom Disc x = sm x λ _ _ → cong _
  -- F-id Disc = refl
  -- F-seq Disc f g = refl

  -- F-ob Codisc x = st (fst x) (fullRel x) (snd x)
  -- F-hom Codisc x = sm x (λ a a' _ → tt*)
  -- F-id Codisc = refl
  -- F-seq Codisc f g = refl

  -- F-ob Π x = ( Carrier x / fst (fst (rel x))) , squash/
  -- F-hom Π (sm f r) = rec squash/ ([_]/ ∘f f) λ _ _ → eq/ _ _ ∘f r _ _
  -- F-id Π = funExt (elimProp (λ _ → squash/ _ _) λ _ → refl)
  -- F-seq Π f g = funExt (elimProp (λ _ → squash/ _ _) λ _ → refl)

  -- F-ob Γ x = Carrier x , is-set x
  -- F-hom Γ (sm f _) = f
  -- F-id Γ = refl
  -- F-seq Γ _ _ = refl


  -- open Cubical.Categories.Adjoint.NaturalBijection

  -- module _ (C : Setoid ℓ ℓ) (D : hSet ℓ) where
  --   aI : Iso (SET ℓ [ Π ⟅ C ⟆ , D ]) ( SETOID [ C , Disc ⟅ D ⟆ ])
  --   Iso.fun aI f = sm _ λ _ _ → cong f ∘f eq/ _ _
  --   Iso.inv aI _ = rec (snd D) _ _
  --   Iso.rightInv aI b = refl
  --   Iso.leftInv aI a = funExt (elimProp (λ _ → snd D _ _) λ _ → refl)
    
  -- Π⊣Disc : Π ⊣ Disc
  -- _⊣_.adjIso Π⊣Disc {c} {d} = aI c d
  -- _⊣_.adjNatInD Π⊣Disc f k = refl
  -- _⊣_.adjNatInC Π⊣Disc {d = d} g h = funExt (elimProp (λ _ → snd d _ _) λ _ → refl)


  -- module _ (C : hSet ℓ) (D : Setoid ℓ ℓ)  where
  --   open BinaryRelation.isEquivRel ((snd (D .rel)))
    
  --   aI' : Iso (SETOID [ Disc ⟅ C ⟆ , D ]) (SET ℓ [ C , Γ ⟅ D ⟆ ])
  --   Iso.fun aI' (sm f r) = f
  --   Iso.inv aI' x = sm x λ a a' x₁ → subst (fst (D .rel) .fst (x a)) (cong x x₁) (reflexive (x a))
  --   Iso.rightInv aI' _ = refl
  --   Iso.leftInv aI' (sm f r) = cong (sm f)
  --     (isPropΠ3 (λ _ _ _ → snd (fst (D .rel)) _ _) _ _)
      
  -- Disc⊣Γ : Disc ⊣ Γ
  -- _⊣_.adjIso Disc⊣Γ {c} {d} = aI' _ _
  -- _⊣_.adjNatInD Disc⊣Γ _ _ = refl
  -- _⊣_.adjNatInC Disc⊣Γ {d = d} f g = refl



  -- module _ (C : Setoid ℓ ℓ) (D : hSet ℓ)  where
  --   open BinaryRelation.isEquivRel ((snd (C .rel)))
    
  --   aI''' : Iso (SET ℓ [ Γ ⟅ C ⟆ , D ]) (SETOID [ C , Codisc ⟅ D ⟆ ])
  --   Iso.fun aI''' x = sm x (λ a a' x₁ → tt*)
  --   Iso.inv aI''' (sm f r) = f
  --   Iso.rightInv aI''' b = refl
  --   Iso.leftInv aI''' a = refl

  -- Γ⊣Codisc : Γ ⊣ Codisc 
  -- _⊣_.adjIso Γ⊣Codisc {c} {d} = aI''' c d 
  -- _⊣_.adjNatInD Γ⊣Codisc _ _ = refl
  -- _⊣_.adjNatInC Γ⊣Codisc _ _ = refl


 
