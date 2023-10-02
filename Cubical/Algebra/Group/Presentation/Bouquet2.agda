{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Bouquet2 where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Powerset
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Empty as ⊥
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Bool using (false ; true) renaming (Bool to 𝟚) 



open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.HITs.EilenbergMacLane1


open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/₂_)

open import Cubical.HITs.GroupoidTruncation as GT
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.HITs.FreeGroup as FG renaming (assoc to ·assoc)

open import Cubical.HITs.TypeQuotients as TQ

open import Cubical.HITs.Bouquet
open import Cubical.Data.List as List
open import Cubical.Functions.Logic as L
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Data.Int hiding (_·_)

open import Cubical.Foundations.Pointed

open import Cubical.Homotopy.Loopspace

open import Cubical.Algebra.Group.Instances.SetsAutomorphism

-- open import Cubical.Algebra.Group.Presentation.Bouquet


-- module _ {ℓ} (A : Type ℓ) where


private
  variable
    ℓ ℓ' ℓ'' : Level

data 𝟜 : Type where
 ₀₋ ₁₋ ₋₀ ₋₁ : 𝟜


𝟜→Ω : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
𝟜→Ω A = 𝟜 → ⟨ Ω A ⟩




-- -- -- -- mapSq : ∀ {A : Pointed ℓ} {B : Pointed ℓ'} → (A →∙ B) → Sq A → Sq B
-- -- -- -- Sq.fc₀₋ (mapSq f x₁) = {!fst f!}
-- -- -- -- Sq.fc₁₋ (mapSq f x₁) = {!!}
-- -- -- -- Sq.fc₋₀ (mapSq f x₁) = {!!}
-- -- -- -- Sq.fc₋₁ (mapSq f x₁) = {!!}

module _ (A : Pointed ℓ) {B : Type ℓ'} (rels : B → 𝟜→Ω A) where



 data _≡/₃_ : Type (ℓ-max ℓ ℓ') 


 [_]' : ⟨ A ⟩ → _≡/₃_

 _≡/₃∙_ : Pointed (ℓ-max ℓ ℓ') 
 _≡/₃∙_ = _≡/₃_ , [ pt A ]'


 data _≡/₃_ where

  [_]≡/₃ : ⟨ A ⟩ → _≡/₃_
  □_ : (b : B) → Square {A = _≡/₃_}
                (cong [_]' (rels b ₀₋))
                (cong [_]' (rels b ₁₋))
                (cong [_]' (rels b ₋₀))
                (cong [_]' (rels b ₋₁))
  -- trunc : isGroupoid _≡/₃_

 [_]' = [_]≡/₃


 record Rec≡/₃ (X : Pointed ℓ'') : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
   -- isGroupoidX : isGroupoid ⟨ X ⟩ 
   a→x : A →∙ X 
   sq : (b : B) → Square {A = ⟨ X ⟩}
                (λ i → fst a→x (rels b ₀₋ i))
                (λ i → fst a→x (rels b ₁₋ i))
                (λ i → fst a→x (rels b ₋₀ i))
                (λ i → fst a→x (rels b ₋₁ i))
   

  f : _≡/₃_ → ⟨ X ⟩
  f [ x ]≡/₃ = fst a→x x
  f ((□ b) i i₁) = sq b i i₁
  -- f (trunc x y p q r s i i₁ i₂) =
  --   isGroupoidX _ _ _ _
  --     (λ i j → f (r i j)) (λ i j → f (s i j))
  --     i i₁ i₂ 
   

  f∙ : _≡/₃∙_ →∙ X
  f∙ = f , snd a→x

 record Elim≡/₃ (X : typ _≡/₃∙_ → Type ℓ'') : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
   -- isGroupoidX : ∀ x → isGroupoid ⟨ ∙X x ⟩ 
   a→x : ∀ a  → X [ a ]≡/₃
   sq : (b : B) → SquareP (λ i j → X ((□ b) i j))
                (λ i → a→x (rels b ₀₋ i))
                (λ i → a→x (rels b ₁₋ i))
                (λ i → a→x (rels b ₋₀ i))
                (λ i → a→x (rels b ₋₁ i))
   
  f : ∀ a → (X a)
  f [ x ]≡/₃ = a→x x
  f ((□ b) i j) = sq b i j 
  -- f (trunc x y p q r s i i₁ i₂) =
  --    isOfHLevel→isOfHLevelDep 3 isGroupoidX
  --      (f x) (f y) (cong f p) (cong f q)
  --        (λ i j → f (r i j)) (λ i j → f (s i j))
  --       (trunc x y p q r s)
  --       i i₁ i₂ 

--   -- f∙ : ⟨ Πᵖ∙ _≡/₃∙_ ∙X ⟩
--   -- fst f∙ = f
--   -- snd f∙ = snd a→x

module _ (A∙ : Pointed ℓ) where
 IsoTrunc⊥ : Iso ⟨ A∙ ⟩ (A∙ ≡/₃ ⊥.rec)
 Iso.fun IsoTrunc⊥ = [_]≡/₃ 
 Iso.inv IsoTrunc⊥ [ x ]≡/₃ = x
 Iso.rightInv IsoTrunc⊥ [ x ]≡/₃ = refl 
 Iso.leftInv IsoTrunc⊥ _ = refl

-- GT.elim (λ _ → {!!}) λ _ → refl

-- module X (A : Type ℓ) {B : Type ℓ'} (rels : B → □Ω (Bouquet∙ A)) where
--  ⟨_∣_⟩ : Type (ℓ-max ℓ ℓ') 
--  ⟨_∣_⟩ = Bouquet∙ A ≡/₃ rels

--  ⟨_∣_⟩∙ : Pointed (ℓ-max ℓ ℓ') 
--  ⟨_∣_⟩∙ = Bouquet∙ A ≡/₃∙ rels


--  record RecSet {ℓ''} (∙X : Pointed ℓ'') 
--                    : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
--   field
--    loopX : A → ⟨ Ω ∙X ⟩

--   bq : Bouquet∙ A →∙ ∙X
--   fst bq base = _
--   fst bq (loop x i) = loopX x i
--   snd bq = refl

--   record RecGpd : Type (ℓ-max ℓ' ℓ'') where
--    field
--     sqX : (b : B) → _
    
--    R : Rec≡/₃ (Bouquet∙ A) rels ∙X
--    Rec≡/₃.a→x R = bq
--    Rec≡/₃.sq R = sqX

--    f = Rec≡/₃.f R

--  record ElimSet {ℓ''} (∙X : typ ⟨_∣_⟩∙ → Pointed ℓ') 
--                    : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
--   field
--    loopX : ∀ a → PathP (λ i → typ (∙X [ loop a i ]≡/₃))
--                   (pt (∙X [ base ]≡/₃))
--                   (pt (∙X [ base ]≡/₃))


--   bq : ⟨ Πᵖ∙ (Bouquet∙ A) (∙X ∘ [_]≡/₃) ⟩
--   fst bq base = _
--   fst bq (loop x i) = loopX x i
--   snd bq = refl

--   record ElimGpd : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
--    field
--     sqX : (b : B) → SquareP _ _ _ _ _
    
--    R : Elim≡/₃ (Bouquet∙ A) rels (fst ∘ ∙X)
--    Elim≡/₃.a→x R = fst bq
--    Elim≡/₃.sq R = sqX

--    f = Elim≡/₃.f R

--    -- f∙ = Elim≡/₃.f∙ R


--    -- sqX : ∀ b → SquareP (λ i j → typ (∙X ((□ b) i j)))
--    --               {!!}
--    --               {!!}
--    --               {!λ i → fst f [ rels b ₋₀ i ]!}
--    --               {!!}

-- -- Goal: typ (∙X ((□ b) i i₁))
-- -- ———— Boundary (wanted) —————————————————————————————————————
-- -- i₁ = i0 ⊢ fst f [ rels b ₋₀ i ]
-- -- i₁ = i1 ⊢ fst f [ rels b ₋₁ i ]
-- -- i = i0 ⊢ fst f [ rels b ₀₋ i₁ ]
-- -- i = i1 ⊢ fst f [ rels b ₁₋ i₁ ]


-- --   bq : Bouquet∙ A →∙ ∙X
-- --   fst bq base = _
-- --   fst bq (loop x i) = loopX x i
-- --   snd bq = refl


-- module _ (IxG : Type ℓ) where

--  data Fc : Type ℓ where
--   fc : 𝟚 → IxG → Fc
--   cns : Fc

--  Fc∙ : Pointed ℓ
--  Fc∙ = Fc , cns

--  mkFc≡ : (IxG → ⟨ Ω A∙ ⟩) → Fc∙ →∙ Ω A∙ 
--  fst (mkFc≡ f) (fc b x) = 𝟚.if b then f x else sym (f x)
--  fst (mkFc≡ _) cns = _
--  snd (mkFc≡ _) = refl


-- module _ (A : Type ℓ) {B : Type ℓ} (rels : B → 𝟜 → Fc A) where
--  open X A (λ b → fst (mkFc≡ _ loop) ∘ rels b) public

--  module F𝔹 = X A ⊥.rec

--  F = freeGroupGroup A

--  fc→fg : Fc A → FreeGroup A
--  fc→fg (fc x a) = 𝟚.if x then η a else inv (η a)
--  fc→fg cns = ε

--  rels' : B → 𝟜 → FreeGroup A
--  rels' = λ b → fc→fg ∘' rels b 
 


--  relatorsF : B → FreeGroup A 
--  relatorsF b =
--   let r = rels' b
--   in inv (r ₁₋ · r ₋₀) · (r ₋₁ · r ₀₋)

--  FN = freeGroupGroup (FreeGroup A × B)

--  FN→F : GroupHom FN F
--  FN→F = fst A→Group≃GroupHom λ (g , b) → inv g · (relatorsF b · g) 

--  h→ : ⟨ F ⟩ → GroupHom FN FN
--  h→ a = fst A→Group≃GroupHom λ (g , b) → η (g · a , b) 



--  _∼ₚ_ :  (FreeGroup A) → (FreeGroup A) → Type ℓ 
--  g ∼ₚ g' = Σ B λ b →
--                    let r = rels' b
--                    in (r ₋₁ · (r ₀₋ · g)) ≡ (r ₁₋ · (r ₋₀ · g'))


--  open GroupTheory F

--  module FGS = GroupStr (snd F)
 

--  lemGen : ∀ a y → FN→F .fst (fst (h→ (inv a)) y) ≡
--       (a · (fst FN→F y · inv a) )
--  lemGen a = ElimProp.f w
--   where
--   w : ElimProp
--         (λ z → FN→F .fst (fst (h→ (inv a)) z) ≡ (a · (fst FN→F z · inv a)))
--   ElimProp.isPropB w _ = trunc _ _
--   ElimProp.εB w = sym (invr a) ∙ cong (a ·_) (idl (inv a))
--   ElimProp.ηB w (g , b) =
--    cong₂ _·_ (invDistr g (inv a) ∙ cong (_· (inv g)) (invInv a))
--      (FGS.·Assoc _ _ _)
--     ∙∙ sym (FGS.·Assoc _ _ _)
--     ∙∙ cong (a ·_) (FGS.·Assoc _ _ _)
--   ElimProp.invB w x p = cong inv p ∙
--      invDistr _ _ ∙
--        cong (_· inv a) (invDistr _ _) ∙
--         λ i → ·assoc (invInv a i) (IsGroupHom.presinv (snd FN→F) x i) (inv a)
--              (~ i)
         
--   ElimProp.·B w x y X Y =
--      cong₂ _·_ X Y ∙∙
--         (λ i → ·assoc a (fst FN→F x · inv a) (·assoc a (fst FN→F y) (inv a) i) (~ i))
--           ∙∙ cong (a ·_) (·assoc _ _ _ ∙ cong (_· inv a)
--             (·assoc _ _ _ ∙∙ cong (_· _)
--                (sym (·assoc _ _ _) ∙∙ cong ((fst FN→F x) ·_) (invl a)
--                 ∙∙ sym (idr _))
--                 ∙∙ sym (IsGroupHom.pres· (snd FN→F) _ _)))


--  isNormalN : isNormal (imSubgroup FN→F)
--  isNormalN x h = PT.map
--    λ (g , p) → _ , lemGen x g ∙ λ i → (x · (p i · inv x))
   
--  P : Group ℓ 
--  P = F / (imSubgroup FN→F , isNormalN)


-- --  𝔹P = {!!}

-- --  -- ℙ = ? / ?

-- -- --  3→2T : ∥ Bouquet A ∥₃ → hSet ℓ
-- -- --  3→2T = GT.rec isGroupoidHSet λ x → ∥ base ≡ x ∥₂ , squash₂ 
-- -- --    -- λ {base → ∥ Path (Bouquet A) base base ∥₂ , squash₂
-- -- --    --   ; (loop a i) → ∥ Path (Bouquet A) base (loop a i) ∥₂ , {!!} }

-- -- --  3→2 : ∀ x → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x) → 
-- -- --              ⟨ 3→2T x ⟩
-- -- --  3→2 x = J (λ x → λ v → ⟨ 3→2T x ⟩) ∣ refl ∣₂

-- -- --  -- 2→3 : ∀ x → Path (Bouquet A) base x 
-- -- --  --           → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ ∣ x ∣₃)
-- -- --  -- 2→3 x = cong ∣_∣₃
-- -- --  --  -- J (λ x _ → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ ∣ x ∣₃)) refl


-- -- --  2→3' : ∀ x → ⟨ 3→2T x ⟩ 
-- -- --            → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x) 
-- -- --  2→3' = GT.elim (λ _ → isGroupoidΠ λ _ → isSet→isGroupoid (squash₃ _ _))
-- -- --             λ x → ST.rec (squash₃ _ _) (cong ∣_∣₃)
 

-- -- --  sec2' : ∀ x → (p : Path (Bouquet A) base x) →
-- -- --                (3→2 (∣ x ∣₃) (2→3' ∣ x ∣₃ ∣ p ∣₂)) ≡ ∣ p ∣₂ 
-- -- --  sec2' x = J (λ x (p : Path (Bouquet A) base x) →
-- -- --                (3→2 (∣ x ∣₃) (2→3' ∣ x ∣₃ ∣ p ∣₂)) ≡ ∣ p ∣₂)
-- -- --                   (cong ∣_∣₂ (transportRefl _))
-- -- --                   -- (cong ∣_∣₂ (transportRefl _ ∙∙ transportRefl _ ∙∙ transportRefl _)
-- -- --                   -- )

-- -- --  sec3 : ∀ x → (p : Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x)  →
-- -- --                (2→3' (x) ((3→2 x p))) ≡ p 
-- -- --  sec3 x = J (λ x → λ (p : Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x)  →
-- -- --                (2→3' (x) ((3→2 x p))) ≡ p)
-- -- --                  λ j i → ∣ doubleCompPath-filler refl (λ _ → base) refl (~ j) i ∣₃
                   

-- -- --  Iso₂₃ : Iso (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ ∣ base ∣₃)
-- -- --              ∥ Path (Bouquet A) base base ∥₂
-- -- --  Iso.fun Iso₂₃ = 3→2 ∣ base ∣₃
-- -- --  Iso.inv Iso₂₃ = (2→3' ∣ base ∣₃)
-- -- --  Iso.rightInv Iso₂₃ = ST.elim (λ _ → isProp→isSet (squash₂ _ _)) (sec2' base)  
-- -- --  Iso.leftInv Iso₂₃ = sec3 ∣ base ∣₃


-- -- --  -- FF : F𝔹.⟨_∣_⟩∙ →∙ (Bouquet∙ A)
-- -- --  -- fst FF [ x ] = x
-- -- --  -- snd FF = {!!}
-- -- --  -- -- fst FF = F𝔹.RecSet.RecGpd.f  w
-- -- --  -- --  where
-- -- --  -- --  w' : F𝔹.RecSet (∥ Bouquet A ∥₃ , ∣ base ∣₃)
-- -- --  -- --  X.RecSet.loopX w' a = cong ∣_∣₃ (loop a)
  
-- -- --  --  w : F𝔹.RecSet.RecGpd w'
-- -- --  --  X.RecSet.RecGpd.isGroupoidX w _ _ = squash₃ _ _
-- -- --  -- snd FF = refl

-- -- --  -- GHF𝔹 : GroupIso {!F𝔹!} F
-- -- --  -- fst GHF𝔹 = {!compIso TruncatedFamiliesIso {A = ?} base !}
-- -- --  -- snd GHF𝔹 = {!!}
 

-- -- -- --  P𝔹 = πGr 1 (Bouquet∙ A ) / (imSubgroup {!!} , {!!})

-- -- -- --   -- X = ⟨ ∙X ⟩
-- -- -- -- --   field
-- -- -- -- --    isGroupoidX : isGroupoid X
-- -- -- -- --    bq : Bouquet A → X

-- -- -- -- --    □X : ∀ b → Square
-- -- -- -- --                (cong bq (Sq'.fc₀₋ (rels b)))
-- -- -- -- --                (cong bq (Sq'.fc₁₋ (rels b)))
-- -- -- -- --                (cong bq (Sq'.fc₋₀ (rels b)))
-- -- -- -- --                (cong bq (Sq'.fc₋₁ (rels b)))

-- -- -- -- --   f : ⟨_∣_⟩ → X
-- -- -- -- --   f [ x ] = bq x
-- -- -- -- --   f ((□ b) i i₁) =  □X b i i₁
-- -- -- -- --   f (trunc x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) = {!!}




-- -- -- -- --  Sq = Sq' Fc

-- -- -- -- --  Sq→SqΩ : ∀ {ℓa} {A : Type ℓa} {base : A} → (loop : IxG → base ≡ base)
-- -- -- -- --               → Sq → SqΩ (A , base)
-- -- -- -- --  Sq'.fc₀₋ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₀₋ x)
-- -- -- -- --  Sq'.fc₁₋ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₁₋ x)
-- -- -- -- --  Sq'.fc₋₀ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₋₀ x)
-- -- -- -- --  Sq'.fc₋₁ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₋₁ x)

-- -- -- -- -- -- module _ (A : Type ℓ) {B : Type ℓ'} (rels : B → Sq A) where
-- -- -- -- -- --  open X A (Sq→SqΩ _ loop ∘ rels)
   
  
-- -- -- -- -- -- private
-- -- -- -- -- --   variable
-- -- -- -- -- --     A : Type ℓ
-- -- -- -- -- --     B : Type ℓ'
-- -- -- -- -- --     rels : B → SqΩ (Bouquet∙ A)


-- -- -- -- -- -- -- zz : X.⟨ A ∣ rels ⟩ → A
-- -- -- -- -- -- -- zz [ base ] = {!!}
-- -- -- -- -- -- -- zz [ loop x i ] = {!!}
-- -- -- -- -- -- -- zz ((□ b) i i₁) = {!!}
-- -- -- -- -- -- -- zz (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) = {!!}
