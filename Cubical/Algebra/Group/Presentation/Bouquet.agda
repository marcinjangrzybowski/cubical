{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Bouquet where

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

open import Cubical.HITs.EilenbergMacLane1 as EM


open import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.GroupoidTruncation as GT
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.HITs.FreeGroup as FG renaming (assoc to ·assoc)

open import Cubical.HITs.Bouquet as Bq
open import Cubical.Data.List as List
open import Cubical.Functions.Logic as L
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Data.Int hiding (_·_)
open import Cubical.Data.Sum as ⊎

open import Cubical.Foundations.Pointed

open import Cubical.Homotopy.Loopspace

open import Cubical.Algebra.Group.Instances.SetsAutomorphism

open import Cubical.HITs.FreeGroup.NormalForm.EqEps
open import Cubical.HITs.FreeGroup.NormalForm.Demo

open import Cubical.Homotopy.EilenbergMacLane.Properties


private
  variable
    ℓ ℓ' : Level


 
module _ {ℓ} (A∙ : Pointed ℓ) where
 
 IT→ : ∥ ⟨ Ω A∙ ⟩ ∥₂ → ⟨ Ω (∥ ⟨ A∙ ⟩ ∥₃ , ∣ pt A∙ ∣₃) ⟩
 IT→ = ST.rec (squash₃ _ _) (cong ∣_∣₃)

 IT←'T : ∀ (x : ∥ ⟨ A∙ ⟩ ∥₃)  → hSet ℓ
 IT←'T = GT.rec (isGroupoidHSet)
          λ x → (∥ snd A∙ ≡ x ∥₂) , (isSetSetTrunc)
 
 IT←' : ∀ x → ∣ snd A∙ ∣₃ ≡ x → ⟨ IT←'T x ⟩
 IT←' x = J (λ x _ → ⟨ IT←'T x ⟩) ∣ refl ∣₂


 IT← : ⟨ Ω (∥ ⟨ A∙ ⟩ ∥₃ , ∣ pt A∙ ∣₃) ⟩ → ∥ ⟨ Ω A∙ ⟩ ∥₂ 
 IT← = IT←' _


 IsoΩTrunc₂ : Iso ∥ ⟨ Ω A∙ ⟩ ∥₂ ⟨ Ω (∥ ⟨ A∙ ⟩ ∥₃ , ∣ pt A∙ ∣₃) ⟩
 Iso.fun IsoΩTrunc₂ = IT→
 Iso.inv IsoΩTrunc₂ = IT←
 Iso.rightInv IsoΩTrunc₂ =
    J (λ x y →
      ⟨ GT.elim (λ x → isGroupoidΠ λ (y : ∣ snd A∙ ∣₃ ≡ x )
         → isSet→isGroupoid isSetHProp ) 
         (λ x y → (ST.rec (squash₃ _ _) (cong ∣_∣₃) (IT←' ∣ x ∣₃ y) ≡ y) ,
            squash₃ _ _ _ _ ) x y ⟩)
              (cong (cong ∣_∣₃) (transportRefl _)) {∣ pt A∙ ∣₃}
 Iso.leftInv IsoΩTrunc₂ =
   ST.elim (λ _ → isProp→isSet (squash₂ _ _))
    λ a → cong ∣_∣₂ (substInPathsL _ _ ∙ sym (lUnit _))


private
  variable
    ℓ'' : Level
    -- A : Type ℓ
    A∙ : Pointed ℓ

data 𝟜 : Type where
 ₀₋ ₁₋ ₋₀ ₋₁ : 𝟜


□Ω : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
□Ω A = 𝟜 → ⟨ Ω A ⟩

□Ωfit : □Ω A∙ → ⟨ Ω A∙ ⟩
□Ωfit x  = sym (x ₀₋ ∙' x ₋₁) ∙∙ x ₋₀ ∙∙ x ₁₋


P□Ωfit' : ∀ {ℓ} {A∙ : Pointed ℓ} (P : □Ω A∙ → Type ℓ) →  ⟨ Ω A∙ ⟩ → Type ℓ
P□Ωfit' P x = Σ _ λ x' → P x' × (x ≡ (□Ωfit x'))


P□Ωfit : ∀ {ℓ} {A∙ : Pointed ℓ} → (□Ω A∙ → Type ℓ) → (□Ω A∙ → Type ℓ )
P□Ωfit P x =
  (P□Ωfit' P (x ₋₀))
     × (x ₀₋ ≡ refl) × (x ₋₁ ≡ refl) × (x ₁₋ ≡ refl)  

module _ {ℓ} (A : Pointed ℓ) (rels : □Ω A → Type ℓ) where

 data _≡/₃_ : Type ℓ 


 [_]' : ⟨ A ⟩ → _≡/₃_

 _≡/₃∙_ : Pointed ℓ 
 _≡/₃∙_ = _≡/₃_ , [ pt A ]'


 data _≡/₃_ where

  [_]≡/₃ : ⟨ A ⟩ → _≡/₃_
  □_ : ∀ {b} → rels b → Square {A = _≡/₃_}
                (cong [_]' (b ₀₋))
                (cong [_]' (b ₁₋))
                (cong [_]' (b ₋₀))
                (cong [_]' (b ₋₁))
  -- trunc : isGroupoid _≡/₃_

 [_]' = [_]≡/₃


 record Rec≡/₃ (X : Pointed ℓ') : Type (ℓ-max ℓ ℓ') where
  field
   -- isGroupoidX : isGroupoid ⟨ X ⟩ 
   a→x : A →∙ X 
   sq : ∀ {b} → rels b → Square {A = ⟨ X ⟩}
                (λ i → fst a→x (b ₀₋ i))
                (λ i → fst a→x (b ₁₋ i))
                (λ i → fst a→x (b ₋₀ i))
                (λ i → fst a→x (b ₋₁ i))
   

  f : _≡/₃_ → ⟨ X ⟩
  f [ x ]≡/₃ = fst a→x x
  f ((□ b) i i₁) = sq b i i₁
  -- f (trunc x y p q r s i i₁ i₂) =
  --   isGroupoidX _ _ _ _
  --     (λ i j → f (r i j)) (λ i j → f (s i j))
  --     i i₁ i₂ 
   

  f∙ : _≡/₃∙_ →∙ X
  f∙ = f , snd a→x


 record ElimSet≡/₃ (X : typ _≡/₃∙_ → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
   isSetX : ∀ x → isSet (X x) 
   a→x : ∀ a  → X [ a ]≡/₃
   
  f : ∀ a → (X a)
  f [ x ]≡/₃ = a→x x
  f ((□_ {b} x) i j) =
    isSet→SquareP
      (λ i j → isSetX ((□ x) i j))
        (λ i → a→x (b ₀₋ i))
        (λ i → a→x (b ₁₋ i))
        (λ i → a→x (b ₋₀ i))
        (λ i → a→x (b ₋₁ i))
      i j

 record Elim≡/₃ (X : typ _≡/₃∙_ → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
   -- isGroupoidX : ∀ x → isGroupoid ⟨ ∙X x ⟩ 
   a→x : ∀ a  → X [ a ]≡/₃
   sq : ∀ {b} → (x : rels b) → SquareP (λ i j → X ((□ x) i j))
                (λ i → a→x (b ₀₋ i))
                (λ i → a→x (b ₁₋ i))
                (λ i → a→x (b ₋₀ i))
                (λ i → a→x (b ₋₁ i))
   
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


module _ {ℓ} (A∙ : Pointed ℓ) (rels : □Ω A∙ → Type ℓ) where


 hlp : (□Ω A∙) → ∀ {rels} → ∀ i i₁ → I
     → Partial (i ∨ (~ i) ∨ i₁ ∨ (~ i₁)) (A∙ ≡/₃ rels) 
 hlp b i i₁ k =
      λ {
        (i = i0) → [ compPath'-filler (b ₀₋) (b ₋₁) (~ i₁) (~ k) ]≡/₃
       ;(i = i1) → [ b ₁₋ (i₁ ∨ ~ k) ]≡/₃
       ;(i₁ = i0) → [ doubleCompPath-filler
           (sym (b ₀₋ ∙' b ₋₁)) (b ₋₀) (b ₁₋) (~ k) i ]≡/₃
       ;(i₁ = i1) → [ b ₋₁ (i ∨ ~ k) ]≡/₃
      }
 
 IsoFit : Iso (A∙ ≡/₃ rels) (A∙ ≡/₃ P□Ωfit rels)
 Iso.fun IsoFit [ x ]≡/₃ = [ x ]≡/₃
 Iso.fun IsoFit ((□_ {b} x) i i₁) = 
   hcomp (hlp b i i₁) ((□_ {b = λ { ₋₀ → _ ; _ →  refl}}
               ((b , (x , refl)) , (refl , refl , refl ))) i i₁)
 Iso.inv IsoFit [ x ]≡/₃ = [ x ]≡/₃
 Iso.inv IsoFit (□_ {b} ((b' , (x , p₋₀) ) , p₀₋ , p₋₁ , p₁₋) i i₁) = 
      hcomp (λ k → λ {
        (i = i0) → [ p₀₋ (~ k) i₁ ]≡/₃
       ;(i = i1) → [ p₁₋ (~ k) i₁ ]≡/₃
       ;(i₁ = i0) → [ p₋₀ (~ k) i ]≡/₃
       ;(i₁ = i1) → [ p₋₁ (~ k) i ]≡/₃
      })
      (hcomp (λ k → hlp b' i i₁ (~ k))
        (□_ {b = b'} x i i₁))
       
 Iso.rightInv IsoFit = {!!}
      
 Iso.leftInv IsoFit = {!!}
-- IsoTrunc⊥ : Iso ⟨ A∙ ⟩ (A∙ ≡/₃ ∅)
-- Iso.fun IsoTrunc⊥ = [_]≡/₃ 
-- Iso.inv IsoTrunc⊥ [ x ]≡/₃ = x
-- Iso.rightInv IsoTrunc⊥ [ x ]≡/₃ = refl 
-- Iso.leftInv IsoTrunc⊥ _ = refl
-- -- GT.elim (λ _ → {!!}) λ _ → refl


-- module X' (∙A : Pointed ℓ) (rels : ℙ (□Ω ∙A)) where
--  rels' : ℙ (□Ω ∙A)
--  rels' f = {!!}
--  -- rel₀₋ (f ₀₋) 
 
--  -- open X ∙A {!!} 
 
 

-- -- module X (A : Type ℓ) (rels : _) where
-- --  ⟨_∣_⟩ : Type ℓ 
-- --  ⟨_∣_⟩ = Bouquet∙ A ≡/₃ rels

-- --  ⟨_∣_⟩∙ : Pointed ℓ 
-- --  ⟨_∣_⟩∙ = Bouquet∙ A ≡/₃∙ rels


-- --  record RecSet (∙X : Pointed ℓ') : Type (ℓ-max ℓ ℓ') where
-- --   field
-- --    loopX : A → ⟨ Ω ∙X ⟩

-- --   bq : Bouquet∙ A →∙ ∙X
-- --   fst bq base = _
-- --   fst bq (loop x i) = loopX x i
-- --   snd bq = refl

-- --   record RecGpd : Type (ℓ-max ℓ ℓ') where
-- --    field
-- --     sqX : ∀ {b} → b ∈ rels → _
    
-- --    R : Rec≡/₃ (Bouquet∙ A) rels ∙X
-- --    Rec≡/₃.a→x R = bq
-- --    Rec≡/₃.sq R = sqX

-- --    f = Rec≡/₃.f R

-- --  record ElimProp (P : typ ⟨_∣_⟩∙ → Type ℓ') 
-- --                    : Type (ℓ-max ℓ ℓ') where
-- --   field
-- --    isPropP : ∀ x → isProp (P x) 
-- --    baseP : P [ base ]≡/₃ 


-- --   go : ∀ x → P x 
-- --   go [ x ]≡/₃ = Bq.elimProp (isPropP ∘ [_]≡/₃) baseP x
-- --   go ((□_ {b} x) i j) =
-- --      isSet→SquareP
-- --       (λ i j → isProp→isSet (isPropP (((□ x) i j))) )
-- --         (λ j → Bq.elimProp (λ x₁ → isPropP [ x₁ ]≡/₃) baseP (b ₀₋ j))
-- --         (λ j → Bq.elimProp (λ x₁ → isPropP [ x₁ ]≡/₃) baseP (b ₁₋ j))     
-- --         (λ i → Bq.elimProp (λ x₁ → isPropP [ x₁ ]≡/₃) baseP (b ₋₀ i))
-- --         (λ i →  Bq.elimProp (λ x₁ → isPropP [ x₁ ]≡/₃) baseP (b ₋₁ i)) i j


-- --  record ElimSet (∙X : typ ⟨_∣_⟩∙ → Pointed ℓ') 
-- --                    : Type (ℓ-max ℓ ℓ') where
-- --   field
-- --    loopX : ∀ a → PathP (λ i → typ (∙X [ loop a i ]≡/₃))
-- --                   (pt (∙X [ base ]≡/₃))
-- --                   (pt (∙X [ base ]≡/₃))


-- --   bq : ⟨ Πᵖ∙ (Bouquet∙ A) (∙X ∘ [_]≡/₃) ⟩
-- --   fst bq base = _
-- --   fst bq (loop x i) = loopX x i
-- --   snd bq = refl

-- --   record ElimGpd : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
-- --    field
-- --     sqX : ∀ {b} → (x : b ∈ rels) → SquareP _ _ _ _ _
    
-- --    R : Elim≡/₃ (Bouquet∙ A) rels (fst ∘ ∙X)
-- --    Elim≡/₃.a→x R = fst bq
-- --    Elim≡/₃.sq R = sqX

-- --    f = Elim≡/₃.f R



-- -- --  data PP : typ (Ω (Bouquet∙ A)) → Type ℓ where
-- -- --   pp : ∀ {x} → x ∈ rels → PP (sym (x ₀₋ ∙ x ₋₁) ∙ (x ₋₀ ∙ x ₁₋))

-- -- --  fromPP : ∀ {p} → PP p → Path ⟨ Ω ⟨_∣_⟩∙ ⟩ (cong [_]≡/₃ p) refl
-- -- --  fromPP (pp {x'} x) =
-- -- --    (cong-∙ [_]≡/₃ _ _) ∙
-- -- --      cong (sym ((cong [_]≡/₃ (x' ₀₋ ∙ x' ₋₁))) ∙_)
-- -- --        ((cong-∙ [_]≡/₃ _ _
-- -- --            ∙∙ Square→compPath (□ x) ∙∙
-- -- --             sym (cong-∙ [_]≡/₃ _ _))) ∙
-- -- --               lCancel ((cong [_]≡/₃ (x' ₀₋ ∙ x' ₋₁)))
  
-- -- --  P/ : ℙ ⟨ πGr 0 (Bouquet∙ A) ⟩
-- -- --  P/ = ST.rec isSetHProp
-- -- --    (λ p → ∥ PP p ∥₁ , squash₁)


-- -- --  P/FG : ℙ (FreeGroup A)
-- -- --  P/FG x = {!!} , {!!}
 
-- -- --  𝔹Iso : Iso (EM₁ (G/⇊ (πGr 0 (Bouquet∙ A)) P/)) ∥ ⟨_∣_⟩ ∥₃ 
-- -- --  𝔹Iso = {!!}
 
-- -- -- -- Iso.fun 𝔹Iso = EM.rec _
-- -- -- --    squash₃
-- -- -- --    ∣ [ base ]≡/₃ ∣₃
-- -- -- --    (SQ.rec (squash₃ _ _ ) (ST.rec (squash₃ _ _) (cong (∣_∣₃ ∘ [_]≡/₃)))
-- -- -- --      (rec⇊ _ _ _ (ST.elim3 (λ _ _ _ → isSet→ (isProp→isSet (squash₃ _ _ _ _)))
-- -- -- --         λ a b c → PT.rec (squash₃ _ _ _ _)
-- -- -- --           ((λ p → cong-∙ (∣_∣₃ ∘ [_]≡/₃) _ _ ∙
-- -- -- --                    cong (cong (λ x → ∣ [ x ]≡/₃ ∣₃) a ∙_)
-- -- -- --                      (cong-∙ (∣_∣₃ ∘ [_]≡/₃) _ _ ∙
-- -- -- --                        cong (_∙ (cong (λ x → ∣ [ x ]≡/₃ ∣₃) c))
-- -- -- --                          (cong (cong ∣_∣₃) p) ∙ sym (lUnit _)) ∙
-- -- -- --                      sym (cong-∙ (∣_∣₃ ∘ [_]≡/₃) _ _) ) ∘' fromPP))))
-- -- -- --    (SQ.elimProp2 {!!} (ST.elim2 {!!}
-- -- -- --       λ _ _ → congP (λ _ → cong (∣_∣₃ ∘ [_]≡/₃)) (compPath-filler _ _)))

-- -- -- --  Iso.inv 𝔹Iso =

-- -- -- --   GT.rec emsquash
-- -- -- --    (RecSet.RecGpd.f w)
-- -- -- --   where
-- -- -- --   w' : RecSet (EM₁ (G/⇊ (πGr 0 (Bouquet∙ A)) P/) , embase)
-- -- -- --   RecSet.loopX w' a =  emloop SQ.[ ∣ loop a ∣₂ ]

-- -- -- --   -- w'Lem* : ∀ x → congS {x = base} {y = base} (fst (RecSet.bq w')) {!!} ≡
-- -- -- --   --               emloop SQ.[ ∣ {!!} ∣₂ ]
-- -- -- --   -- w'Lem* x = {!!}


-- -- -- --   w'Lem : ∀ x → congS {x = base} {y = base} (fst (RecSet.bq w')) x ≡
-- -- -- --                 emloop SQ.[ ∣ x ∣₂ ]
-- -- -- --   w'Lem = {!!} where
-- -- -- --    w'LemR : {!!}
-- -- -- --    w'LemR = {!!}

 
-- -- -- --   w : RecSet.RecGpd w'
-- -- -- --   RecSet.RecGpd.sqX w {b} x =
-- -- -- --     let zz : cong [_]≡/₃ (sym (b ₀₋ ∙ b ₋₁) ∙ b ₋₀ ∙ b ₁₋) ≡ refl
-- -- -- --         zz = fromPP (p x)

-- -- -- --         z' : Path (Path (EM₁
-- -- -- --                          (G/⇊ (πGr 0 (Bouquet∙ A)) P/)) embase embase)
-- -- -- --                          _
-- -- -- --                            _
-- -- -- --         z' = refl
-- -- -- --                -- ({!!} ∙ sym (emloop-comp _ SQ.[ ∣ _ ∣₂ ]
-- -- -- --                --                         SQ.[ ∣ _ ∣₂ ]))
-- -- -- --           ∙∙ cong emloop (cong (SQ.[_] ∘' ∣_∣₂) (rUnit _ ∙
-- -- -- --                 (lUnit (((λ i → (b ₀₋ ∙ b ₋₁) (~ i)) ∙ b ₋₀ ∙ b ₁₋) ∙ refl)))
-- -- -- --               ∙∙ SQ.eq/ ∣ refl ∙ ((sym (b ₀₋ ∙ b ₋₁) ∙ (b ₋₀ ∙ b ₁₋))) ∙ refl ∣₂
-- -- -- --                        ∣ refl ∙ refl ∣₂
-- -- -- --                        (_·_↘1g·_ ∣ refl ∣₂
-- -- -- --                           {∣ (sym (b ₀₋ ∙ b ₋₁) ∙ (b ₋₀ ∙ b ₁₋)) ∣₂}
-- -- -- --                            ∣ p x ∣₁ ∣ refl ∣₂)
                        
-- -- -- --              ∙∙ cong (SQ.[_] ∘' ∣_∣₂) (sym (lUnit _)) ) ∙∙ refl
-- -- -- --               -- emloop-1g _

-- -- -- --         z : Path (Path (EM₁
-- -- -- --                          (G/⇊ (πGr 0 (Bouquet∙ A)) P/))
-- -- -- --                            embase
-- -- -- --                            embase)
-- -- -- --                     (cong (fst (RecSet.bq w')) (b ₋₀ ∙ b ₁₋))
-- -- -- --                     (cong (fst (RecSet.bq w')) (b ₀₋ ∙ b ₋₁))
-- -- -- --         z = w'Lem (_ ∙ _) ∙∙ {!z'!} ∙∙ sym (w'Lem (_ ∙ _)) 
-- -- -- --            -- congS {x = b ₋₀ ∙ b ₁₋} {y = b ₀₋ ∙ b ₋₁}
-- -- -- --            --  (cong (fst (RecSet.bq w')))
-- -- -- --            --    {!!}
     
-- -- -- --     in compPath→Square
-- -- -- --         (sym (cong-∙ (fst (RecSet.bq w')) (b ₋₀) (b ₁₋))
-- -- -- --           ∙∙ z ∙∙
-- -- -- --           (cong-∙ (fst (RecSet.bq w')) (b ₀₋) (b ₋₁)))
-- -- -- --  Iso.rightInv 𝔹Iso = {!!}
-- -- -- --  Iso.leftInv 𝔹Iso = {!!}

-- -- -- --  -- GroupIsoPres :
-- -- -- --  --  GroupIso
-- -- -- --  --    (πGr 0 ⟨_∣_⟩∙)
-- -- -- --  --    (G/⇊ (πGr 0 (Bouquet∙ A)) P/)
-- -- -- --  -- Iso.fun (fst GroupIsoPres) =
-- -- -- --  --  ST.rec SQ.squash/ {!!} 
-- -- -- --  -- Iso.inv (fst GroupIsoPres) = {!!}
-- -- -- --  -- Iso.rightInv (fst GroupIsoPres) = {!!}
-- -- -- --  -- Iso.leftInv (fst GroupIsoPres) = {!!}
-- -- -- --  -- snd GroupIsoPres = {!!}

-- -- -- -- -- module _ (IxG : Type ℓ) where

-- -- -- -- --  data Fc : Type ℓ where
-- -- -- -- --   fc : 𝟚 → IxG → Fc
-- -- -- -- --   cns : Fc

-- -- -- -- --  Fc∙ : Pointed ℓ
-- -- -- -- --  Fc∙ = Fc , cns

-- -- -- -- --  mkFc≡ : (IxG → ⟨ Ω A∙ ⟩) → Fc∙ →∙ Ω A∙ 
-- -- -- -- --  fst (mkFc≡ f) (fc b x) = 𝟚.if b then f x else sym (f x)
-- -- -- -- --  fst (mkFc≡ _) cns = _
-- -- -- -- --  snd (mkFc≡ _) = refl


-- -- -- -- -- module Pres (A : Type ℓ) {B : Type ℓ} (rels : B → 𝟜 → Fc A) where
-- -- -- -- --  open X A (λ b → fst (mkFc≡ _ loop) ∘ rels b) public

-- -- -- -- --  module F𝔹 = X A ⊥.rec

-- -- -- -- --  F = freeGroupGroup A

-- -- -- -- --  fc→fg : Fc A → FreeGroup A
-- -- -- -- --  fc→fg (fc x a) = 𝟚.if x then η a else inv (η a)
-- -- -- -- --  fc→fg cns = ε

-- -- -- -- --  rels' : B → 𝟜 → FreeGroup A
-- -- -- -- --  rels' = λ b → fc→fg ∘' rels b 
 


-- -- -- -- --  relatorsF : B → FreeGroup A 
-- -- -- -- --  relatorsF b =
-- -- -- -- --   let r = rels' b
-- -- -- -- --   in inv (r ₁₋ · r ₋₀) · (r ₋₁ · r ₀₋)

-- -- -- -- --  FN = freeGroupGroup (FreeGroup A × B)

-- -- -- -- --  FN→F : GroupHom FN F
-- -- -- -- --  FN→F = fst A→Group≃GroupHom λ (g , b) → inv g · (relatorsF b · g) 

-- -- -- -- --  h→ : ⟨ F ⟩ → GroupHom FN FN
-- -- -- -- --  h→ a = fst A→Group≃GroupHom λ (g , b) → η (g · a , b) 



-- -- -- -- --  -- _∼ₚ_ :  (FreeGroup A) → (FreeGroup A) → Type ℓ 
-- -- -- -- --  -- g ∼ₚ g' = Σ B λ b → let r = rels' b
-- -- -- -- --  --   in Path (FreeGroup A)
-- -- -- -- --  --       (r ₋₁ · (r ₀₋ · g)) (r ₁₋ · (r ₋₀ · g'))


-- -- -- -- --  open GroupTheory F

-- -- -- -- --  module FGS = GroupStr (snd F)
 

-- -- -- -- --  isNormalN : isNormal (imSubgroup FN→F)
-- -- -- -- --  isNormalN a h = PT.map
-- -- -- -- --    λ (g , p) → _ , lemGen g ∙ λ i → (a · (p i · inv a))
-- -- -- -- --   where
-- -- -- -- --    open GroupSolver (freeGroupGroup A)

-- -- -- -- --    lemGen : ∀ y → FN→F .fst (fst (h→ (inv a)) y) ≡
-- -- -- -- --                         (a · (fst FN→F y · inv a))
-- -- -- -- --    lemGen = HIT-FG.propElimCons _ (λ _ → _ , trunc _ _)
-- -- -- -- --      (𝑺 ε (0 · (ε · inv 0)) _)
-- -- -- -- --       λ a₁ x → map-× (cong (_ ·_) x ∙_) (cong (_ ·_) x ∙_)
-- -- -- -- --          ((𝑺 ((inv (0 · -2) · (1 · (0 · -2))) · (2 · (3 · -2)))
-- -- -- -- --               (2 · (((inv 0 · (1 · 0)) · 3) · -2)) _ _ _ _)
-- -- -- -- --         , (𝑺 (inv (inv (0 · -2) · (1 · (0 · -2))) · (2 · (3 · -2)))
-- -- -- -- --              (2 · ((inv (inv 0 · (1 · 0)) · 3) · -2)) _ _ _ _))
      

-- -- -- -- --  P : Group ℓ 
-- -- -- -- --  P = F / (imSubgroup FN→F , isNormalN)

-- -- -- -- --  P'rel : (g h : Path (Bouquet A) base base) → Type ℓ 
-- -- -- -- --  P'rel g h = Σ B λ b → {!!}

-- -- -- -- --  P' : Group ℓ
-- -- -- -- --  fst P' = Path (Bouquet A) base base
-- -- -- -- --             SQ./ P'rel
-- -- -- -- --  snd P' = {!!}
 
-- -- -- -- --  𝔹P = EM₁ P

-- -- -- -- --  -- →𝔹P : ⟨_∣_⟩ → 𝔹P
-- -- -- -- --  -- →𝔹P = RecSet.RecGpd.f w
-- -- -- -- --  --  where
-- -- -- -- --  --  w' : RecSet (EM₁ P , embase)
-- -- -- -- --  --  X.RecSet.loopX w' a = emloop SQ.[ η a ]
  
-- -- -- -- --  --  w : RecSet.RecGpd w'
-- -- -- -- --  --  X.RecSet.RecGpd.sqX w b =
-- -- -- -- --  --   let z : Path ⟨ P ⟩
-- -- -- -- --  --            SQ.[ (fc→fg (rels b ₁₋) · fc→fg (rels b ₋₀)) ]
-- -- -- -- --  --            SQ.[ (fc→fg (rels b ₋₁) · fc→fg (rels b ₀₋)) ]
-- -- -- -- --  --       z = SQ.eq/
-- -- -- -- --  --         (((fc→fg (rels b ₁₋) · fc→fg (rels b ₋₀))))
-- -- -- -- --  --         ((fc→fg (rels b ₋₁) · fc→fg (rels b ₀₋)))
-- -- -- -- --  --          ∣ (inv (η (ε , b))) , {!!} ∣₁
-- -- -- -- --  --   in compPath→Square ({!sym (emloop-comp _ _ _)!} ∙∙ {!!} ∙∙ {!!})


-- -- -- -- --   -- →𝔹P [ base ]≡/₃ = embase
-- -- -- -- --  -- →𝔹P [ loop x i ]≡/₃ = emloop SQ.[ η x ] i
-- -- -- -- --  -- →𝔹P ((□ b) i i₁) = {!!}
 
-- -- -- -- --  -- 𝔹PIso : {!!}
-- -- -- -- --  -- 𝔹PIso = {!!}
 


-- -- -- -- -- -- -- --  𝔹P = {!!}

-- -- -- -- -- -- -- --  -- ℙ = ? / ?

-- -- -- -- -- -- -- -- --  3→2T : ∥ Bouquet A ∥₃ → hSet ℓ
-- -- -- -- -- -- -- -- --  3→2T = GT.rec isGroupoidHSet λ x → ∥ base ≡ x ∥₂ , squash₂ 
-- -- -- -- -- -- -- -- --    -- λ {base → ∥ Path (Bouquet A) base base ∥₂ , squash₂
-- -- -- -- -- -- -- -- --    --   ; (loop a i) → ∥ Path (Bouquet A) base (loop a i) ∥₂ , {!!} }

-- -- -- -- -- -- -- -- --  3→2 : ∀ x → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x) → 
-- -- -- -- -- -- -- -- --              ⟨ 3→2T x ⟩
-- -- -- -- -- -- -- -- --  3→2 x = J (λ x → λ v → ⟨ 3→2T x ⟩) ∣ refl ∣₂

-- -- -- -- -- -- -- -- --  -- 2→3 : ∀ x → Path (Bouquet A) base x 
-- -- -- -- -- -- -- -- --  --           → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ ∣ x ∣₃)
-- -- -- -- -- -- -- -- --  -- 2→3 x = cong ∣_∣₃
-- -- -- -- -- -- -- -- --  --  -- J (λ x _ → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ ∣ x ∣₃)) refl


-- -- -- -- -- -- -- -- --  2→3' : ∀ x → ⟨ 3→2T x ⟩ 
-- -- -- -- -- -- -- -- --            → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x) 
-- -- -- -- -- -- -- -- --  2→3' = GT.elim (λ _ → isGroupoidΠ λ _ → isSet→isGroupoid (squash₃ _ _))
-- -- -- -- -- -- -- -- --             λ x → ST.rec (squash₃ _ _) (cong ∣_∣₃)
 

-- -- -- -- -- -- -- -- --  sec2' : ∀ x → (p : Path (Bouquet A) base x) →
-- -- -- -- -- -- -- -- --                (3→2 (∣ x ∣₃) (2→3' ∣ x ∣₃ ∣ p ∣₂)) ≡ ∣ p ∣₂ 
-- -- -- -- -- -- -- -- --  sec2' x = J (λ x (p : Path (Bouquet A) base x) →
-- -- -- -- -- -- -- -- --                (3→2 (∣ x ∣₃) (2→3' ∣ x ∣₃ ∣ p ∣₂)) ≡ ∣ p ∣₂)
-- -- -- -- -- -- -- -- --                   (cong ∣_∣₂ (transportRefl _))
-- -- -- -- -- -- -- -- --                   -- (cong ∣_∣₂ (transportRefl _ ∙∙ transportRefl _ ∙∙ transportRefl _)
-- -- -- -- -- -- -- -- --                   -- )

-- -- -- -- -- -- -- -- --  sec3 : ∀ x → (p : Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x)  →
-- -- -- -- -- -- -- -- --                (2→3' (x) ((3→2 x p))) ≡ p 
-- -- -- -- -- -- -- -- --  sec3 x = J (λ x → λ (p : Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x)  →
-- -- -- -- -- -- -- -- --                (2→3' (x) ((3→2 x p))) ≡ p)
-- -- -- -- -- -- -- -- --                  λ j i → ∣ doubleCompPath-filler refl (λ _ → base) refl (~ j) i ∣₃
                   

-- -- -- -- -- -- -- -- --  Iso₂₃ : Iso (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ ∣ base ∣₃)
-- -- -- -- -- -- -- -- --              ∥ Path (Bouquet A) base base ∥₂
-- -- -- -- -- -- -- -- --  Iso.fun Iso₂₃ = 3→2 ∣ base ∣₃
-- -- -- -- -- -- -- -- --  Iso.inv Iso₂₃ = (2→3' ∣ base ∣₃)
-- -- -- -- -- -- -- -- --  Iso.rightInv Iso₂₃ = ST.elim (λ _ → isProp→isSet (squash₂ _ _)) (sec2' base)  
-- -- -- -- -- -- -- -- --  Iso.leftInv Iso₂₃ = sec3 ∣ base ∣₃


-- -- -- -- -- -- -- -- --  -- FF : F𝔹.⟨_∣_⟩∙ →∙ (Bouquet∙ A)
-- -- -- -- -- -- -- -- --  -- fst FF [ x ] = x
-- -- -- -- -- -- -- -- --  -- snd FF = {!!}
-- -- -- -- -- -- -- -- --  -- -- fst FF = F𝔹.RecSet.RecGpd.f  w
-- -- -- -- -- -- -- -- --  -- --  where
-- -- -- -- -- -- -- -- --  -- --  w' : F𝔹.RecSet (∥ Bouquet A ∥₃ , ∣ base ∣₃)
-- -- -- -- -- -- -- -- --  -- --  X.RecSet.loopX w' a = cong ∣_∣₃ (loop a)
  
-- -- -- -- -- -- -- -- --  --  w : F𝔹.RecSet.RecGpd w'
-- -- -- -- -- -- -- -- --  --  X.RecSet.RecGpd.isGroupoidX w _ _ = squash₃ _ _
-- -- -- -- -- -- -- -- --  -- snd FF = refl

-- -- -- -- -- -- -- -- --  -- GHF𝔹 : GroupIso {!F𝔹!} F
-- -- -- -- -- -- -- -- --  -- fst GHF𝔹 = {!compIso TruncatedFamiliesIso {A = ?} base !}
-- -- -- -- -- -- -- -- --  -- snd GHF𝔹 = {!!}
 

-- -- -- -- -- -- -- -- -- --  P𝔹 = πGr 1 (Bouquet∙ A ) / (imSubgroup {!!} , {!!})

-- -- -- -- -- -- -- -- -- --   -- X = ⟨ ∙X ⟩
-- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- --    isGroupoidX : isGroupoid X
-- -- -- -- -- -- -- -- -- -- --    bq : Bouquet A → X

-- -- -- -- -- -- -- -- -- -- --    □X : ∀ b → Square
-- -- -- -- -- -- -- -- -- -- --                (cong bq (Sq'.fc₀₋ (rels b)))
-- -- -- -- -- -- -- -- -- -- --                (cong bq (Sq'.fc₁₋ (rels b)))
-- -- -- -- -- -- -- -- -- -- --                (cong bq (Sq'.fc₋₀ (rels b)))
-- -- -- -- -- -- -- -- -- -- --                (cong bq (Sq'.fc₋₁ (rels b)))

-- -- -- -- -- -- -- -- -- -- --   f : ⟨_∣_⟩ → X
-- -- -- -- -- -- -- -- -- -- --   f [ x ] = bq x
-- -- -- -- -- -- -- -- -- -- --   f ((□ b) i i₁) =  □X b i i₁
-- -- -- -- -- -- -- -- -- -- --   f (trunc x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) = {!!}




-- -- -- -- -- -- -- -- -- -- --  Sq = Sq' Fc

-- -- -- -- -- -- -- -- -- -- --  Sq→SqΩ : ∀ {ℓa} {A : Type ℓa} {base : A} → (loop : IxG → base ≡ base)
-- -- -- -- -- -- -- -- -- -- --               → Sq → SqΩ (A , base)
-- -- -- -- -- -- -- -- -- -- --  Sq'.fc₀₋ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₀₋ x)
-- -- -- -- -- -- -- -- -- -- --  Sq'.fc₁₋ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₁₋ x)
-- -- -- -- -- -- -- -- -- -- --  Sq'.fc₋₀ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₋₀ x)
-- -- -- -- -- -- -- -- -- -- --  Sq'.fc₋₁ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₋₁ x)

-- -- -- -- -- -- -- -- -- -- -- -- module _ (A : Type ℓ) {B : Type ℓ'} (rels : B → Sq A) where
-- -- -- -- -- -- -- -- -- -- -- --  open X A (Sq→SqΩ _ loop ∘ rels)
   
  
-- -- -- -- -- -- -- -- -- -- -- -- private
-- -- -- -- -- -- -- -- -- -- -- --   variable
-- -- -- -- -- -- -- -- -- -- -- --     A : Type ℓ
-- -- -- -- -- -- -- -- -- -- -- --     B : Type ℓ'
-- -- -- -- -- -- -- -- -- -- -- --     rels : B → SqΩ (Bouquet∙ A)


-- -- -- -- -- -- -- -- -- -- -- -- -- zz : X.⟨ A ∣ rels ⟩ → A
-- -- -- -- -- -- -- -- -- -- -- -- -- zz [ base ] = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- zz [ loop x i ] = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- zz ((□ b) i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- zz (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) = {!!}
