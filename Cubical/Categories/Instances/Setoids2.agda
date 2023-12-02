{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Setoids2 where

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
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Poset
open import Cubical.Relation.Binary.Order.Poset

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Setoid

open import Cubical.HITs.SetQuotients as /

open Category hiding (_∘_)
open Functor


module SET,REL ℓ ℓ' where
  SET,REL : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob SET,REL = Σ (hSet ℓ) λ (X , _) → PropRel X X ℓ'
  Hom[_,_] SET,REL (_ , (R , _)) (_ , (R' , _)) = Σ _ (respects R R')
  fst (id SET,REL) _ = _
  snd (id SET,REL) r = r
  fst ((SET,REL ⋆ _) _) = _
  snd ((SET,REL ⋆ (_ , f)) (_ , g)) = g ∘ f 
  ⋆IdL SET,REL _ = refl
  ⋆IdR SET,REL _ = refl
  ⋆Assoc SET,REL _ _ _ = refl
  isSetHom SET,REL {y = (_ , isSetB) , (_ , isPropR)} =
   isSetΣ (isSet→ isSetB) (isProp→isSet ∘ isPropRespects isPropR )

  open Iso
  
  IsoPathCatIsoSET,REL : ∀ {x y} → Iso (x ≡ y) (CatIso SET,REL x y)
  fun (IsoPathCatIsoSET,REL) = pathToIso
  inv (IsoPathCatIsoSET,REL {y = _ , (y , _) }) ((_ , r) , ci) =
    cong₂ _,_
     (TypeOfHLevel≡ 2 (isoToPath i))
     (toPathP (PropRel≡
       ( substRel y ((cong fst c.sec ≡$ _) ∙_ ∘ transportRefl) ∘ r
       , snd c.inv ∘ substRel y (sym ∘ transportRefl))
       ))
   where
   module c = isIso ci
   i : Iso _ _
   fun i = _ ; inv i = fst c.inv
   rightInv i = cong fst c.sec ≡$_ ; leftInv i = cong fst c.ret ≡$_
        
  rightInv (IsoPathCatIsoSET,REL {x = x} {y = _ , (_ , pr)}) ((f , _) , _) =
    CatIso≡ _ _ (Σ≡Prop (isPropRespects pr)
     (funExt λ _ → transportRefl _ ∙ cong f (transportRefl _)) )
      
  leftInv (IsoPathCatIsoSET,REL) a =
    ΣSquareSet (λ _ → isSetPropRel)
      (TypeOfHLevel≡Path 2 (λ _ →
       transportRefl _ ∙ cong (subst (fst ∘ fst) a) (transportRefl _)))


-- module SETOID ℓ ℓ' where
--   SETOID : Category _ _
--   ob SETOID = Setoid ℓ ℓ'
--   Hom[_,_] SETOID = SetoidMor 
--   fst (id SETOID) _ = _
--   snd (id SETOID) r = r
--   fst ((SETOID ⋆ _) _) = _
--   snd ((SETOID ⋆ (_ , f)) (_ , g)) = g ∘ f 
--   ⋆IdL SETOID _ = refl
--   ⋆IdR SETOID _ = refl
--   ⋆Assoc SETOID _ _ _ = refl
--   isSetHom SETOID {y = (_ , isSetB) , ((_ , isPropR) , _)} =
--    isSetΣ (isSet→ isSetB) (isProp→isSet ∘ isPropRespects isPropR )
   
--   open Iso
  
--   IsoPathCatIsoSETOID : ∀ {x y} → Iso (x ≡ y) (CatIso SETOID x y)
--   fun (IsoPathCatIsoSETOID) = pathToIso
--   inv (IsoPathCatIsoSETOID {y = _ , ((y , _) , _) }) ((_ , r) , ci) =
--     cong₂ _,_
--      (TypeOfHLevel≡ 2 (isoToPath i))
--      (toPathP (EquivPropRel≡
--        ( substRel y ((cong fst c.sec ≡$ _) ∙_ ∘ transportRefl) ∘ r
--        , snd c.inv ∘ substRel y (sym ∘ transportRefl))
--        ))
--    where
--    module c = isIso ci
--    i : Iso _ _
--    fun i = _ ; inv i = fst c.inv
--    rightInv i = cong fst c.sec ≡$_ ; leftInv i = cong fst c.ret ≡$_
        
--   rightInv (IsoPathCatIsoSETOID {x = x} {y = y}) ((f , _) , _) =
--     CatIso≡ _ _ (SetoidMor≡ x y
--        (funExt λ _ → transportRefl _ ∙ cong f (transportRefl _)))
--   leftInv (IsoPathCatIsoSETOID) a =
--     ΣSquareSet (λ _ → isSetEquivPropRel)
--       (TypeOfHLevel≡Path 2 (λ _ →
--        transportRefl _ ∙ cong (subst (fst ∘ fst) a) (transportRefl _)))
  
--   isUnivalentSETOID : isUnivalent SETOID
--   isUnivalent.univ isUnivalentSETOID _ _ =
--    isoToIsEquiv IsoPathCatIsoSETOID

--   Forget : Functor SETOID (SET ℓ)

--   Quot : Functor SETOID (SET (ℓ-max ℓ ℓ'))

  
--   F-ob Quot (_ , ((R , _) , _)) = (_ / R) , squash/
--   F-hom Quot (f , r) = /.rec squash/ ([_] ∘  f) λ _ _ → eq/ _ _ ∘ r 
--   F-id Quot = funExt (/.elim (λ _ → isProp→isSet (squash/ _ _))
--     (λ _ → refl) λ _ _ _ _ → refl)
--   F-seq Quot _ _ = funExt (/.elim (λ _ → isProp→isSet (squash/ _ _))
--     (λ _ → refl) λ _ _ _ _ → refl)

--   F-ob Forget = fst
--   F-hom Forget = fst
--   F-id Forget = refl
--   F-seq Forget _ _ = refl

-- private
--   variable
--     ℓ ℓ' ℓ'' ℓ''' : Level

-- module _ where
--  open SETOID
--  coDisc : Functor (SET ℓ) (SETOID ℓ ℓ')
--  F-ob coDisc = _, fullEquivPropRel
--  F-hom coDisc = _, _
--  F-id coDisc = refl
--  F-seq coDisc _ _ = refl

--  Disc : Functor (SET ℓ) (SETOID ℓ ℓ)  
--  F-ob Disc A = A , (_ , snd A) , isEquivRelIdRel
--  F-hom Disc = _, cong _
--  F-id Disc = refl
--  F-seq Disc _ _ = refl

--  open Cubical.Categories.Adjoint.NaturalBijection
--  open _⊣_
  
--  Quot⊣Disc : Quot ℓ ℓ ⊣ Disc
--  adjIso Quot⊣Disc {d = (_ , isSetD)} = setQuotUniversalIso isSetD
--  adjNatInD Quot⊣Disc {c = c} {d' = d'} f k = SetoidMor≡ c (Disc ⟅ d' ⟆) refl 
--  adjNatInC Quot⊣Disc {d = d} g h = 
--   funExt (/.elimProp (λ _ → snd d _ _) λ _ → refl)
  
--  open Iso
--  Disc⊣Forget : Disc ⊣ Forget ℓ ℓ
--  fun (adjIso Disc⊣Forget) = fst
--  inv (adjIso Disc⊣Forget {d = d}) f = 
--    f , J (λ x' p → fst (fst (snd d)) (f _) (f x'))
--      (BinaryRelation.isEquivRel.reflexive (snd (snd d)) (f _))
--  rightInv (adjIso Disc⊣Forget) _ = refl
--  leftInv (adjIso Disc⊣Forget {c = c} {d = d}) _ =
--    SetoidMor≡ (Disc ⟅ c ⟆) d refl
--  adjNatInD Disc⊣Forget _ _ = refl
--  adjNatInC Disc⊣Forget _ _ = refl
  
--  Forget⊣coDisc : Forget ℓ ℓ ⊣ coDisc
--  fun (adjIso Forget⊣coDisc) = _
--  inv (adjIso Forget⊣coDisc) = fst
--  rightInv (adjIso Forget⊣coDisc) _ = refl
--  leftInv (adjIso Forget⊣coDisc) _ = refl
--  adjNatInD Forget⊣coDisc _ _ = refl
--  adjNatInC Forget⊣coDisc _ _ = refl

  
--  pieces : Functor (SETOID ℓ ℓ) (SETOID ℓ ℓ)
--  pieces = Disc ∘F Quot _ _

--  points : Functor (SETOID ℓ ℓ) (SETOID ℓ ℓ)
--  points = Disc ∘F Forget _ _

--  pieces⊣points : pieces {ℓ} ⊣ points
--  pieces⊣points = Compose.LF⊣GR Quot⊣Disc Disc⊣Forget

--  points→pieces : points {ℓ} ⇒ pieces
--  points→pieces =  
--      ε (adj'→adj _ _ Disc⊣Forget)
--   ●ᵛ η (adj'→adj _ _ Quot⊣Disc)
--   where open UnitCounit._⊣_

--  piecesHavePoints : ∀ A →
--    isEpic (SETOID ℓ ℓ) {points ⟅ A ⟆ } {pieces ⟅ A ⟆}
--     (points→pieces ⟦ A ⟧)
--  piecesHavePoints  A {z = z@((_ , isSetZ) , _) } =
--    SetoidMor≡ (pieces ⟅ A ⟆) z ∘
--      (funExt ∘ /.elimProp (λ _ → isSetZ _ _) ∘ funExt⁻ ∘ cong fst)
  
--  pieces→≃→points : (A B : Setoid ℓ ℓ) →
--         SetoidMor (pieces ⟅ A ⟆) B
--       ≃ SetoidMor A (points ⟅ B ⟆)
--  pieces→≃→points A B = 
--     NaturalBijection._⊣_.adjEquiv
--       (pieces⊣points)
--       {c = A} {d = B}

--  -⊗- : Functor (SETOID ℓ ℓ' ×C SETOID ℓ'' ℓ''')
--                   (SETOID (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ'''))
--  F-ob -⊗- = uncurry _⊗_
--  fst (F-hom -⊗- _) = _
--  snd (F-hom -⊗- (f , g)) (x , y) = snd f x , snd g y
--  F-id -⊗- = refl
--  F-seq -⊗- _ _ = refl

--  InternalHomFunctor : Functor ((SETOID ℓ ℓ) ^op ×C (SETOID ℓ ℓ)) (SETOID _ _)
--  F-ob InternalHomFunctor = uncurry _⟶_
--  fst (F-hom InternalHomFunctor (f , g )) (_ , y) = _ , snd g ∘ y ∘ (snd f)    
--  snd (F-hom InternalHomFunctor (f , g)) q = snd g ∘ q ∘ fst f
--  F-id InternalHomFunctor = refl
--  F-seq InternalHomFunctor _ _ = refl

--  -^_ : ∀ X → Functor (SETOID ℓ ℓ) (SETOID _ _)
--  -^_ X = (λF (SETOID _ _) _ ((SETOID _ _) ^op) InternalHomFunctor ⟅ X ⟆)

--  -⊗_ : ∀ X → Functor (SETOID ℓ ℓ) (SETOID ℓ ℓ)
--  -⊗_ {ℓ} X = (λF (SETOID _ _) _ (SETOID ℓ ℓ)
--      (-⊗- ∘F fst (Swap (SETOID _ _) (SETOID _ _))) ⟅ X ⟆)
  
--  ⊗⊣^ : (X : Setoid ℓ ℓ) → (-⊗ X) ⊣ (-^ X)               
--  adjIso (⊗⊣^ {ℓ} X) {A} {B} = setoidCurryIso X A B 
--  adjNatInD (⊗⊣^ X) {A} {d' = C} _ _ = SetoidMor≡ A (X ⟶ C) refl
--  adjNatInC (⊗⊣^ X) {A} {d = C} _ _ = SetoidMor≡ (A ⊗ X) C refl




-- module _ (ℓ : Level) where
--   open SETOID
--   open BinaryRelation
--   open isEquivRel

--   isEquivRel⇔ : isEquivRel {ℓ-suc ℓ} {ℓ} (λ z z₁ → fst (z ⇔ z₁))
--   reflexive isEquivRel⇔ _ = idfun _ , idfun _
--   symmetric isEquivRel⇔ _ _ (p , q) = q , p
--   transitive isEquivRel⇔ _ _ _ (p , q) (p' , q') = p' ∘ p , q ∘ q'
  
--   Propₛ : Setoid (ℓ-suc ℓ) ℓ
--   Propₛ = (hProp ℓ , isSetHProp) ,
--        (_ , λ p q → snd (p ⇔ q)) , isEquivRel⇔


--   equivPropRelOnSetFunctor : ∀ ℓ≅ → Functor (SET ℓ ^op) (SET (ℓ-max ℓ (ℓ-suc ℓ≅))) 
--   F-ob (equivPropRelOnSetFunctor ℓ≅) X =
--    _ , isSetEquivPropRel {A = fst X} {ℓ≅A = ℓ≅} 
--   F-hom (equivPropRelOnSetFunctor ℓ≅) f ((_ , pr) , eqr) =
--     ((_ , λ _ _ → pr _ _) , isEquivRelPulledbackRel eqr f)
--   F-id (equivPropRelOnSetFunctor ℓ≅) = refl
--   F-seq (equivPropRelOnSetFunctor ℓ≅) _ _ = refl

--   -- relPt : ∀ ℓ≅ → Constant _ _ (_ , isSetUnit*) ⇒
--   --    (equivPropRelOnSetFunctor ℓ≅ ∘F (Forget ℓ ℓ≅ ^opF)) 
--   -- NatTrans.N-ob (relPt ℓ≅) x _ = snd x
--   -- NatTrans.N-hom (relPt ℓ≅) f  =
--   --   funExt λ _ → EquivPropRel≡ (snd f , {!!})
--   -- -- toRel : Functor ((SETOID ℓ ℓ) ^op) (SET {!!}) 
--   -- -- F-ob toRel X = {!!}
--   -- -- F-hom toRel {x} {y} f = {!!}
--   -- -- F-id toRel = {!!}
--   -- -- F-seq toRel = {!!}
   
-- -- module _ (ℓ ℓ' : Level) where
-- --  open SETOID
 
-- --  POSET : Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
-- --  POSET = ΣPropCat (SETOID ℓ ℓ')
-- --            λ (_ , ((r , pr) , eqr)) →
-- --                Lift (IsPoset r) , isOfHLevelLift 1 (isPropIsPoset _) 
