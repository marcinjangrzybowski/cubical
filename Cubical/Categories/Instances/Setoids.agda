{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Setoids where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Logic
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Instances.Sets

open import Cubical.Relation.Binary

open import Cubical.HITs.SetQuotients as /

open Category hiding (_∘_)
open Functor

module _ ℓ where
  SETOID : Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ)) (ℓ-max ℓ ℓ)
  ob SETOID = Setoid ℓ ℓ
  Hom[_,_] SETOID = SetoidMor 
  fst (id SETOID) _ = _
  snd (id SETOID) _ _ r = r
  fst ((SETOID ⋆ _) _) = _
  snd ((SETOID ⋆ (_ , f)) (_ , g)) _ _ = g _ _ ∘ f _ _ 
  ⋆IdL SETOID _ = refl
  ⋆IdR SETOID _ = refl
  ⋆Assoc SETOID _ _ _ = refl
  isSetHom SETOID {y = (_ , isSetB) , ((_ , isPropR) , _)} =
   isSetΣ (isSet→ isSetB) (isProp→isSet ∘ isPropRespects isPropR )

  open Iso
  
  IsoPathCatIsoSETOID : ∀ {x y} → Iso (x ≡ y) (CatIso SETOID x y)
  fun (IsoPathCatIsoSETOID) = pathToIso
  inv (IsoPathCatIsoSETOID {y = _ , ((y , _) , _) }) ((_ , r) , ci) =
    cong₂ _,_
     (TypeOfHLevel≡ 2 (isoToPath i))
     (toPathP (EquivPropRel≡ λ _ _ →
         substRel y ((cong fst c.sec ≡$ _) ∙_ ∘ transportRefl) ∘ r _ _
       , snd c.inv _ _ ∘ substRel y (sym ∘ transportRefl)))
   where
   module c = isIso ci
   i : Iso _ _
   fun i = _ ; inv i = fst c.inv
   rightInv i = cong fst c.sec ≡$_ ; leftInv i = cong fst c.ret ≡$_
        
  rightInv (IsoPathCatIsoSETOID {x = x} {y = y}) ((f , _) , _) =
    CatIso≡ _ _ (SetoidMor≡ x y
       (funExt λ _ → transportRefl _ ∙ cong f (transportRefl _)))
  leftInv (IsoPathCatIsoSETOID) a =
    ΣSquareSet (λ _ → isSetEquivPropRel)
      (TypeOfHLevel≡Path 2 (λ _ →
       transportRefl _ ∙ cong (subst (fst ∘ fst) a) (transportRefl _)))
  
  isUnivalentSETOID : isUnivalent SETOID
  isUnivalent.univ isUnivalentSETOID _ _ =
   isoToIsEquiv IsoPathCatIsoSETOID


  Π Γ         : Functor SETOID (SET ℓ)
  Disc coDisc : Functor (SET ℓ) SETOID

  
  F-ob Π (_ , ((R , _) , _)) = (_ / R) , squash/
  F-hom Π (f , r) = /.rec squash/ ([_] ∘  f) λ _ _ → eq/ _ _ ∘ r _ _
  F-id Π = funExt (/.elim (λ _ → isProp→isSet (squash/ _ _))
    (λ _ → refl) λ _ _ _ _ → refl)
  F-seq Π _ _ = funExt (/.elim (λ _ → isProp→isSet (squash/ _ _))
    (λ _ → refl) λ _ _ _ _ → refl)
  
  F-ob Disc A = A , (_ , snd A) , isEquivRelIdRel
  F-hom Disc = _, λ _ _ → cong _
  F-id Disc = refl
  F-seq Disc _ _ = refl

  F-ob Γ = fst
  F-hom Γ = fst
  F-id Γ = refl
  F-seq Γ _ _ = refl

  F-ob coDisc = _, fullEquivPropRel
  F-hom coDisc = _, _
  F-id coDisc = refl
  F-seq coDisc _ _ = refl


  open Cubical.Categories.Adjoint.NaturalBijection
  open _⊣_
  
  Π⊣Disc : Π ⊣ Disc
  adjIso Π⊣Disc {d = (_ , isSetD)} = setQuotUniversalIso isSetD
  adjNatInD Π⊣Disc {c = c} {d' = d'} f k = SetoidMor≡ c (Disc ⟅ d' ⟆) refl 
  adjNatInC Π⊣Disc {d = d} g h = 
   funExt (/.elimProp (λ _ → snd d _ _) λ _ → refl)  

  Disc⊣Γ : Disc ⊣ Γ
  fun (adjIso Disc⊣Γ) = fst
  inv (adjIso Disc⊣Γ {d = d}) f = 
    f , λ _ _ → J (λ x' p → fst (fst (snd d)) (f _) (f x'))
      (BinaryRelation.isEquivRel.reflexive (snd (snd d)) (f _))
  rightInv (adjIso Disc⊣Γ) _ = refl
  leftInv (adjIso Disc⊣Γ {c = c} {d = d}) _ =
    SetoidMor≡ (Disc ⟅ c ⟆) d refl
  adjNatInD Disc⊣Γ _ _ = refl
  adjNatInC Disc⊣Γ _ _ = refl
  
  Γ⊣coDisc : Γ ⊣ coDisc
  fun (adjIso Γ⊣coDisc) = _
  inv (adjIso Γ⊣coDisc) = fst
  rightInv (adjIso Γ⊣coDisc) _ = refl
  leftInv (adjIso Γ⊣coDisc) _ = refl
  adjNatInD Γ⊣coDisc _ _ = refl
  adjNatInC Γ⊣coDisc _ _ = refl

  open Cubical.Categories.Adjoint.UnitCounit
  
--   pieces : Functor SETOID SETOID
--   pieces = Disc ∘F Π

--   points : Functor SETOID SETOID
--   points = Disc ∘F Γ

--   pieces⊣points : pieces ⊣ points
--   pieces⊣points = Compose.LF⊣GR Π⊣Disc Disc⊣Γ

--   pieces→≃→points : (A B : Setoid ℓ ℓ) →
--          SetoidMor (pieces ⟅ A ⟆) B
--        ≃ SetoidMor A (points ⟅ B ⟆)
--   pieces→≃→points A B = 
--      NaturalBijection._⊣_.adjEquiv
--        (adj→adj' _ _ pieces⊣points)
--        {c = A} {d = B}


--   decRels : Functor SETOID SETOID
--   decRels = {!HomFunctor!}


-- module _ ℓ where

--   Propsₛ : ob (SETOID (ℓ-suc ℓ))
--   Propsₛ = Disc _ ⟅ hProp ℓ , isSetHProp ⟆

-- module _ ℓ where

--   -- PropsₛF : Functor (SETOID (ℓ-suc ℓ) ^op) (SETOID (ℓ-suc ℓ))
--   -- F-ob PropsₛF (X , R) = {!!}
--   -- F-hom PropsₛF = {!!}
--   -- F-id PropsₛF = {!!}
--   -- F-seq PropsₛF = {!!}

--   PropsₛF : Functor (SET (ℓ-suc ℓ) ^op) (SET (ℓ-suc ℓ))
--   F-ob PropsₛF X = EquivPropRel (fst X) ℓ  , isSetEquivPropRel {A = fst X} 
--   fst (F-hom PropsₛF f ((_ , pr) , _)) = _ , λ _ _ → pr _ _
--   snd (F-hom PropsₛF f (r , er)) = isEquivRelPulledbackRel f _ er
--   F-id PropsₛF = funExt λ x → EquivPropRel≡ λ _ _ → idfun _ , idfun _
--   F-seq PropsₛF _ _ = funExt λ x → EquivPropRel≡ λ _ _ → idfun _ , idfun _

--   IdsSecs : {!!}
--   IdsSecs = {!!}
