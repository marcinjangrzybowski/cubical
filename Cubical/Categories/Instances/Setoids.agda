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
open import Cubical.Functions.Logic hiding (_⇒_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Setoid

open import Cubical.HITs.SetQuotients as /

open Category hiding (_∘_)
open Functor


module _ ℓ where
  SETOID : Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ)) (ℓ-max ℓ ℓ)
  ob SETOID = Setoid ℓ ℓ
  Hom[_,_] SETOID = SetoidMor 
  fst (id SETOID) _ = _
  snd (id SETOID) r = r
  fst ((SETOID ⋆ _) _) = _
  snd ((SETOID ⋆ (_ , f)) (_ , g)) = g ∘ f 
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
     (toPathP (EquivPropRel≡
       ( substRel y ((cong fst c.sec ≡$ _) ∙_ ∘ transportRefl) ∘ r
       , snd c.inv ∘ substRel y (sym ∘ transportRefl))
       ))
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


  Quot Forget         : Functor SETOID (SET ℓ)
  Disc coDisc : Functor (SET ℓ) SETOID

  
  F-ob Quot (_ , ((R , _) , _)) = (_ / R) , squash/
  F-hom Quot (f , r) = /.rec squash/ ([_] ∘  f) λ _ _ → eq/ _ _ ∘ r 
  F-id Quot = funExt (/.elim (λ _ → isProp→isSet (squash/ _ _))
    (λ _ → refl) λ _ _ _ _ → refl)
  F-seq Quot _ _ = funExt (/.elim (λ _ → isProp→isSet (squash/ _ _))
    (λ _ → refl) λ _ _ _ _ → refl)
  
  F-ob Disc A = A , (_ , snd A) , isEquivRelIdRel
  F-hom Disc = _, cong _
  F-id Disc = refl
  F-seq Disc _ _ = refl

  F-ob Forget = fst
  F-hom Forget = fst
  F-id Forget = refl
  F-seq Forget _ _ = refl

  F-ob coDisc = _, fullEquivPropRel
  F-hom coDisc = _, _
  F-id coDisc = refl
  F-seq coDisc _ _ = refl


  open Cubical.Categories.Adjoint.NaturalBijection
  open _⊣_
  
  Quot⊣Disc : Quot ⊣ Disc
  adjIso Quot⊣Disc {d = (_ , isSetD)} = setQuotUniversalIso isSetD
  adjNatInD Quot⊣Disc {c = c} {d' = d'} f k = SetoidMor≡ c (Disc ⟅ d' ⟆) refl 
  adjNatInC Quot⊣Disc {d = d} g h = 
   funExt (/.elimProp (λ _ → snd d _ _) λ _ → refl)  

  Disc⊣Forget : Disc ⊣ Forget
  fun (adjIso Disc⊣Forget) = fst
  inv (adjIso Disc⊣Forget {d = d}) f = 
    f , J (λ x' p → fst (fst (snd d)) (f _) (f x'))
      (BinaryRelation.isEquivRel.reflexive (snd (snd d)) (f _))
  rightInv (adjIso Disc⊣Forget) _ = refl
  leftInv (adjIso Disc⊣Forget {c = c} {d = d}) _ =
    SetoidMor≡ (Disc ⟅ c ⟆) d refl
  adjNatInD Disc⊣Forget _ _ = refl
  adjNatInC Disc⊣Forget _ _ = refl
  
  Forget⊣coDisc : Forget ⊣ coDisc
  fun (adjIso Forget⊣coDisc) = _
  inv (adjIso Forget⊣coDisc) = fst
  rightInv (adjIso Forget⊣coDisc) _ = refl
  leftInv (adjIso Forget⊣coDisc) _ = refl
  adjNatInD Forget⊣coDisc _ _ = refl
  adjNatInC Forget⊣coDisc _ _ = refl

  
  pieces : Functor SETOID SETOID
  pieces = Disc ∘F Quot

  points : Functor SETOID SETOID
  points = Disc ∘F Forget

  pieces⊣points : pieces ⊣ points
  pieces⊣points = Compose.LF⊣GR Quot⊣Disc Disc⊣Forget

  points→pieces : points ⇒ pieces
  points→pieces =  
      ε (adj'→adj _ _ Disc⊣Forget)
   ●ᵛ η (adj'→adj _ _ Quot⊣Disc)
   where open UnitCounit._⊣_

  piecesHavePoints : ∀ A →
    isEpic SETOID {points ⟅ A ⟆ } {pieces ⟅ A ⟆}
     (points→pieces ⟦ A ⟧)
  piecesHavePoints  A {z = z@((_ , isSetZ) , _) } =
    SetoidMor≡ (pieces ⟅ A ⟆) z ∘
      (funExt ∘ /.elimProp (λ _ → isSetZ _ _) ∘ funExt⁻ ∘ cong fst)
  
  pieces→≃→points : (A B : Setoid ℓ ℓ) →
         SetoidMor (pieces ⟅ A ⟆) B
       ≃ SetoidMor A (points ⟅ B ⟆)
  pieces→≃→points A B = 
     NaturalBijection._⊣_.adjEquiv
       (pieces⊣points)
       {c = A} {d = B}

  -⊗- : Functor (SETOID ×C SETOID) SETOID
  F-ob -⊗- = uncurry _⊗_
  fst (F-hom -⊗- _) = _
  snd (F-hom -⊗- (f , g)) (x , y) = snd f x , snd g y
  F-id -⊗- = refl
  F-seq -⊗- _ _ = refl

  InternalHomFunctor : Functor (SETOID ^op ×C SETOID) SETOID
  F-ob InternalHomFunctor = uncurry _⟶_
  fst (F-hom InternalHomFunctor (f , g )) (_ , y) = _ , snd g ∘ y ∘ (snd f)    
  snd (F-hom InternalHomFunctor (f , g)) q = snd g ∘ q ∘ fst f
  F-id InternalHomFunctor = refl
  F-seq InternalHomFunctor _ _ = refl

  -^_ : ∀ X → Functor SETOID SETOID
  -^_ X = (λF SETOID _ (SETOID ^op) InternalHomFunctor ⟅ X ⟆)

  -⊗_ : ∀ X → Functor SETOID SETOID
  -⊗_ X = (λF SETOID _ (SETOID) (-⊗- ∘F fst (Swap SETOID SETOID)) ⟅ X ⟆)
  
  ⊗⊣^ : ∀ X → (-⊗ X) ⊣ (-^ X)               
  adjIso (⊗⊣^ X) {A} {B} = setoidCurryIso X A B 
  adjNatInD (⊗⊣^ X) {A} {d' = C} _ _ = SetoidMor≡ A (X ⟶ C) refl
  adjNatInC (⊗⊣^ X) {A} {d = C} _ _ = SetoidMor≡ (A ⊗ X) C refl




-- module 

--   Propₛ : Setoid ℓ ℓ
--   Propₛ = Disc ⟅ hProp ℓ , isSetHProp {ℓ} ⟆
