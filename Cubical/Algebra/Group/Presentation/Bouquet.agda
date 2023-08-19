{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Bouquet where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool using (false ; true) renaming (Bool to 𝟚) 



open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.HITs.EilenbergMacLane1


open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.GroupoidTruncation as GT
open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.Bouquet

open import Cubical.Foundations.Pointed

open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    A∙ : Pointed ℓ


data 𝟜 : Type where
 ₀₋ ₁₋ ₋₀ ₋₁ : 𝟜


-- IT→ : ∥ ⟨ Ω A∙ ⟩ ∥₂ → ⟨ Ω (∥ ⟨ A∙ ⟩ ∥₃ , ∣ pt A∙ ∣₃) ⟩
-- IT→ = ST.rec (squash₃ _ _) (cong ∣_∣₃)

-- IT← : ⟨ Ω (∥ ⟨ A∙ ⟩ ∥₃ , ∣ pt A∙ ∣₃) ⟩ → ∥ ⟨ Ω A∙ ⟩ ∥₂ 
-- IT← = {!!}


-- IsoΩTrunc₂ : Iso {!Ω ?!} {!!}
-- IsoΩTrunc₂ = {!!}

-- record Sq' {ℓ} (A : Type ℓ) : Type ℓ where
--  constructor sq
--  field
--   fc₀₋ fc₁₋ fc₋₀ fc₋₁ : A  


□Ω : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
□Ω A = 𝟜 → ⟨ Ω A ⟩




-- -- -- mapSq : ∀ {A : Pointed ℓ} {B : Pointed ℓ'} → (A →∙ B) → Sq A → Sq B
-- -- -- Sq.fc₀₋ (mapSq f x₁) = {!fst f!}
-- -- -- Sq.fc₁₋ (mapSq f x₁) = {!!}
-- -- -- Sq.fc₋₀ (mapSq f x₁) = {!!}
-- -- -- Sq.fc₋₁ (mapSq f x₁) = {!!}

module _ (A : Pointed ℓ) {B : Type ℓ'} (rels : B → □Ω A) where



 data _≡/₃_ : Type (ℓ-max ℓ ℓ') 


 [_]' : ⟨ A ⟩ → _≡/₃_

 _≡/₃∙_ : Pointed (ℓ-max ℓ ℓ') 
 _≡/₃∙_ = _≡/₃_ , [ pt A ]'


 data _≡/₃_ where

  [_] : ⟨ A ⟩ → _≡/₃_
  □_ : (b : B) → Square {A = _≡/₃_}
                (cong [_]' (rels b ₀₋))
                (cong [_]' (rels b ₁₋))
                (cong [_]' (rels b ₋₀))
                (cong [_]' (rels b ₋₁))
  trunc : isGroupoid _≡/₃_

 [_]' = [_]


 record Rec≡/₃ (X : Pointed ℓ'') : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
   isGroupoidX : isGroupoid ⟨ X ⟩ 
   a→x : A →∙ X 
   sq : (b : B) → Square {A = ⟨ X ⟩}
                (λ i → fst a→x (rels b ₀₋ i))
                (λ i → fst a→x (rels b ₁₋ i))
                (λ i → fst a→x (rels b ₋₀ i))
                (λ i → fst a→x (rels b ₋₁ i))
   

  f : _≡/₃_ → ⟨ X ⟩
  f [ x ] = fst a→x x
  f ((□ b) i i₁) = sq b i i₁
  f (trunc x y p q r s i i₁ i₂) =
    isGroupoidX _ _ _ _
      (λ i j → f (r i j)) (λ i j → f (s i j))
      i i₁ i₂ 
   

  f∙ : _≡/₃∙_ →∙ X
  f∙ = f , snd a→x

 record Elim≡/₃ (∙X : typ _≡/₃∙_ → Pointed ℓ'') : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
   isGroupoidX : ∀ x → isGroupoid ⟨ ∙X x ⟩ 
   a→x : ⟨ Πᵖ∙ A (∙X ∘ [_]) ⟩
   sq : (b : B) → SquareP (λ i j → ⟨ ∙X ((□ b) i j) ⟩)
                (λ i → fst a→x (rels b ₀₋ i))
                (λ i → fst a→x (rels b ₁₋ i))
                (λ i → fst a→x (rels b ₋₀ i))
                (λ i → fst a→x (rels b ₋₁ i))
   
  f : ∀ a → typ (∙X a)
  f [ x ] = fst a→x x
  f ((□ b) i j) = sq b i j 
  f (trunc x y p q r s i i₁ i₂) =
     isOfHLevel→isOfHLevelDep 3 isGroupoidX
       (f x) (f y) (cong f p) (cong f q)
         (λ i j → f (r i j)) (λ i j → f (s i j))
        (trunc x y p q r s)
        i i₁ i₂ 

  f∙ : ⟨ Πᵖ∙ _≡/₃∙_ ∙X ⟩
  fst f∙ = f
  snd f∙ = snd a→x

IsoTrunc₃← : Rec≡/₃ A∙ (⊥.rec) (∥ ⟨ A∙ ⟩ ∥₃ , ∣ pt A∙ ∣₃)
Rec≡/₃.isGroupoidX IsoTrunc₃← = squash₃
Rec≡/₃.a→x IsoTrunc₃← = ∣_∣₃ , refl

IsoTrunc₃ : Iso ∥ ⟨ A∙ ⟩ ∥₃ (A∙ ≡/₃ ⊥.rec)
Iso.fun IsoTrunc₃ = GT.rec trunc [_] 
Iso.inv IsoTrunc₃ = Rec≡/₃.f IsoTrunc₃←
Iso.rightInv IsoTrunc₃ = {!!}
Iso.leftInv IsoTrunc₃ = GT.elim (λ _ → {!!}) λ _ → refl

module X (A : Type ℓ) {B : Type ℓ'} (rels : B → □Ω (Bouquet∙ A)) where
 ⟨_∣_⟩ : Type (ℓ-max ℓ ℓ') 
 ⟨_∣_⟩ = Bouquet∙ A ≡/₃ rels

 ⟨_∣_⟩∙ : Pointed (ℓ-max ℓ ℓ') 
 ⟨_∣_⟩∙ = Bouquet∙ A ≡/₃∙ rels


 record RecSet {ℓ''} (∙X : Pointed ℓ'') 
                   : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
   loopX : A → ⟨ Ω ∙X ⟩

  bq : Bouquet∙ A →∙ ∙X
  fst bq base = _
  fst bq (loop x i) = loopX x i
  snd bq = refl

  record RecGpd : Type (ℓ-max ℓ' ℓ'') where
   field
    sqX : (b : B) → _
    isGroupoidX : _
    
   R : Rec≡/₃ (Bouquet∙ A) rels ∙X
   Rec≡/₃.isGroupoidX R = isGroupoidX
   Rec≡/₃.a→x R = bq
   Rec≡/₃.sq R = sqX

   f = Rec≡/₃.f R

 record ElimSet {ℓ''} (∙X : typ ⟨_∣_⟩∙ → Pointed ℓ') 
                   : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
   loopX : ∀ a → PathP (λ i → typ (∙X [ loop a i ]))
                  (pt (∙X [ base ]))
                  (pt (∙X [ base ]))


  bq : ⟨ Πᵖ∙ (Bouquet∙ A) (∙X ∘ [_]) ⟩
  fst bq base = _
  fst bq (loop x i) = loopX x i
  snd bq = refl

  record ElimGpd : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
   field
    isGroupoidX : _
    sqX : (b : B) → SquareP _ _ _ _ _
    
   R : Elim≡/₃ (Bouquet∙ A) rels ∙X
   Elim≡/₃.isGroupoidX R = isGroupoidX
   Elim≡/₃.a→x R = bq
   Elim≡/₃.sq R = sqX

   f = Elim≡/₃.f R

   f∙ = Elim≡/₃.f∙ R


   -- sqX : ∀ b → SquareP (λ i j → typ (∙X ((□ b) i j)))
   --               {!!}
   --               {!!}
   --               {!λ i → fst f [ rels b ₋₀ i ]!}
   --               {!!}

-- Goal: typ (∙X ((□ b) i i₁))
-- ———— Boundary (wanted) —————————————————————————————————————
-- i₁ = i0 ⊢ fst f [ rels b ₋₀ i ]
-- i₁ = i1 ⊢ fst f [ rels b ₋₁ i ]
-- i = i0 ⊢ fst f [ rels b ₀₋ i₁ ]
-- i = i1 ⊢ fst f [ rels b ₁₋ i₁ ]


--   bq : Bouquet∙ A →∙ ∙X
--   fst bq base = _
--   fst bq (loop x i) = loopX x i
--   snd bq = refl


module _ (IxG : Type ℓ) where

 data Fc : Type ℓ where
  fc : 𝟚 → IxG → Fc
  cns : Fc

 Fc∙ : Pointed ℓ
 Fc∙ = Fc , cns

 mkFc≡ : (IxG → ⟨ Ω A∙ ⟩) → Fc∙ →∙ Ω A∙ 
 fst (mkFc≡ f) (fc b x) = 𝟚.if b then f x else sym (f x)
 fst (mkFc≡ _) cns = _
 snd (mkFc≡ _) = refl


module _ (A : Type ℓ) {B : Type ℓ'} (rels : B → 𝟜 → Fc A) where
 open X A (λ b → fst (mkFc≡ _ loop) ∘ rels b) public



  -- X = ⟨ ∙X ⟩
--   field
--    isGroupoidX : isGroupoid X
--    bq : Bouquet A → X

--    □X : ∀ b → Square
--                (cong bq (Sq'.fc₀₋ (rels b)))
--                (cong bq (Sq'.fc₁₋ (rels b)))
--                (cong bq (Sq'.fc₋₀ (rels b)))
--                (cong bq (Sq'.fc₋₁ (rels b)))

--   f : ⟨_∣_⟩ → X
--   f [ x ] = bq x
--   f ((□ b) i i₁) =  □X b i i₁
--   f (trunc x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) = {!!}




--  Sq = Sq' Fc

--  Sq→SqΩ : ∀ {ℓa} {A : Type ℓa} {base : A} → (loop : IxG → base ≡ base)
--               → Sq → SqΩ (A , base)
--  Sq'.fc₀₋ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₀₋ x)
--  Sq'.fc₁₋ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₁₋ x)
--  Sq'.fc₋₀ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₋₀ x)
--  Sq'.fc₋₁ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₋₁ x)

-- -- module _ (A : Type ℓ) {B : Type ℓ'} (rels : B → Sq A) where
-- --  open X A (Sq→SqΩ _ loop ∘ rels)
   
  
-- -- private
-- --   variable
-- --     A : Type ℓ
-- --     B : Type ℓ'
-- --     rels : B → SqΩ (Bouquet∙ A)


-- -- -- zz : X.⟨ A ∣ rels ⟩ → A
-- -- -- zz [ base ] = {!!}
-- -- -- zz [ loop x i ] = {!!}
-- -- -- zz ((□ b) i i₁) = {!!}
-- -- -- zz (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) = {!!}
