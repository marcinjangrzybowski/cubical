{-# OPTIONS --safe  --experimental-lossy-unification #-} 
module Cubical.Data.FinData.GTrun2 where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws as GL

open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.SetQuotients renaming ([_] to [_]/ ; rec to rec/ ; elimProp to elimProp/ ; elim to elim/)

open import Cubical.HITs.GroupoidQuotients renaming ([_] to [_]// ; rec to rec// ; elimProp to elimProp// ; elim to elim// ; elimSet to elimSet//)

import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetTruncation renaming (map to map₂)



open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.List
import Cubical.Data.Vec as V
open import Cubical.Data.FinData


open import Cubical.Foundations.Function
open import Cubical.Functions.Logic


open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.SymmetricGroup
open import Cubical.Algebra.Group.Generators

-- open import Cubical.HITs.FreeGroup
-- open import Cubical.HITs.FreeGroup.IPresentation

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)

open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Binary

open import Cubical.Functions.FunExtEquiv


module EMΣ {ℓ ℓ'} {G : Group ℓ'}
             (A' : EM₁ G → Type ℓ)
             (Atrunc : ∀ x → isGroupoid (A' x))
              where

  open GroupStr (snd G)
  -- module M = IsGroupHom (snd m)


  A = A' (embase)

  actR : A → A → Type (ℓ-max ℓ ℓ')
  actR x y = Σ ⟨ G ⟩ λ g → PathP (λ i → A' (emloop g i) ) x y

  actRTrans : ∀ x y z → actR x y → actR y z → actR x z 
  actRTrans x y z (g , p) (h , q) = (g · h) ,
    {!!}


  A// : Type (ℓ-max ℓ ℓ')
  A// = A // actRTrans
  

-- --   actR : A → A → Type (ℓ-max ℓ ℓ')
-- --   actR x y = Σ ⟨ G ⟩ λ g → y ≡ fst (fst m g) x 



  EMG = EM₁ G

  iso// : Iso (Σ _ A') A//
  Iso.fun iso// = uncurry (
    elimEM G (λ _ → isGroupoidΠ λ _ → squash//)
     [_]// (λ g → (toPathP refl ▷ {!funExt (λ x → ?) !}))
     {!!})
  
  Iso.inv iso// =
    rec// actRTrans {!!}
     (embase ,_ )
      (λ r → {!!})
      {!!}
  Iso.rightInv iso// = {!!}
  Iso.leftInv iso// = {!!}

-- --   -- zz : A ≡ A → singlP (singl A) (_ , refl) (_ , refl)
-- --   -- zz p = ΣPathP (p , {!!})

-- --   EM₁FamS : EMG → A ≃ A
-- --   EM₁FamS =
-- --     elimSet G (λ x → {!!})
-- --       (idEquiv A)
-- --       {!!}


-- --   -- EM₁Fam : EMG → ΣType ℓ
-- --   -- EM₁Fam = {!elimSet ? ?!}



-- -- --   EM₁HFam : EMG → hSet ℓ
-- -- --   EM₁HFam = elimEM G
-- -- --    ( λ _ → isGroupoidHSet) (A , isSetA)
-- -- --         G≡ GSq
-- -- --            -- λ g h → compPath-filler _ _
-- -- --            --   ▷
-- -- --            --      (TypeOfHLevel∙' 2 {X = A , isSetA} (ua (fst m g)) (ua (fst m h)))
-- -- --            --    ∙ cong (TypeOfHLevel≡ 2) (sym (uaCompEquiv _ _)
-- -- --            --   ∙ cong ua ( sym ((snd m) .IsGroupHom.pres· g h)))


-- -- -- -- -- --   EM₁HFam : EMG → hSet ℓ
-- -- -- -- -- --   EM₁HFam = elimEM G
-- -- -- -- -- --    ( λ _ → isGroupoidHSet) (A , isSetA)
-- -- -- -- -- --         (TypeOfHLevel≡ 2 ∘ ua ∘ fst m )
-- -- -- -- -- --            λ g h → compPath-filler _ _
-- -- -- -- -- --              ▷
-- -- -- -- -- --                 (TypeOfHLevel∙' 2 {X = A , isSetA} (ua (fst m g)) (ua (fst m h)))
-- -- -- -- -- --               ∙ cong (TypeOfHLevel≡ 2) (sym (uaCompEquiv _ _)
-- -- -- -- -- --              ∙ cong ua ( sym ((snd m) .IsGroupHom.pres· g h)))

-- -- --   EM₁Fam : EMG → Type ℓ
-- -- --   EM₁Fam = fst ∘ EM₁HFam


-- -- -- -- -- --   -- record EMTrunc : Type {!ℓ!} where
-- -- -- -- -- --   --   field
-- -- -- -- -- --   --     loop : EMG
-- -- -- -- -- --   --     val : ⟨ EM₁Fam loop ⟩ 

-- -- --   EMtrunc = Σ EMG EM₁Fam

-- -- --   vanTrunc : Type (ℓ-max ℓ ℓ')
-- -- --   vanTrunc = A // actRTrans

-- -- --   -- module recEMtrunc2 {ℓ'} {B : Type ℓ'} (truncB : isGroupoid B)
-- -- --   --                   (b : A → B)
-- -- --   --                   (p₀ : (g : ⟨ G ⟩) → (a : A) → singl (b a))
-- -- --   --                   (bIds : GroupHom G (idEquivsG B))
-- -- --   --                   where

-- -- --   --   fp : (g : fst G) → (a : A) → Path (singl (b a)) (_ , refl) (_ , refl) 
-- -- --   --   fp g a = ΣPathP ({!!} , {!!})

-- -- --   --   f : EMG → (a : A) → singl (b a)
-- -- --   --   f = elimSet G
-- -- --   --    (λ _ → isSetΠ λ _ → isProp→isSet isPropSingl)
-- -- --   --    (λ _ → _ , refl)
-- -- --   --    (funExt ∘ fp)
-- -- --   --    -- λ g → funExt λ a → ΣPathP ({!cong fst (snd ((fst bIds) g)) !} , {!!}) 


-- -- -- -- funExtDepSq : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} (B : A → Type ℓ') (C : Type ℓ'')
-- -- -- --                 → (aSq : I → I → A)
-- -- -- --          {a₀₀ : B (aSq i0 i0) → C} {a₀₁ : B (aSq i0 i1) → C}
-- -- -- --           (a₀₋ : PathP (λ j → B (aSq i0 j) → C) a₀₀ a₀₁)
-- -- -- --          {a₁₀ : B (aSq i1 i0) → C} {a₁₁ : B (aSq i1 i1) → C}
-- -- -- --          (a₁₋ : PathP (λ j → B (aSq i1 j) → C) a₁₀ a₁₁)
-- -- -- --          (a₋₀ : PathP (λ i → B (aSq i i0) → C) a₀₀ a₁₀)
-- -- -- --          (a₋₁ : PathP (λ i → B (aSq i i1) → C) a₀₁ a₁₁) 
-- -- -- --                 → (

-- -- -- --                 SquareP (λ i j → B (aSq i j))
-- -- -- --                      {!!} {!!} {!!} {!!}
                     
-- -- -- --                      -- a₀₋
-- -- -- --                      -- a₁₋
-- -- -- --                      -- a₋₀
-- -- -- --                      -- a₋₁
-- -- -- --                   → Square {A = C}
-- -- -- --                       {!!}
-- -- -- --                       {!!}
-- -- -- --                       {!!}
-- -- -- --                       {!!})
-- -- -- --                 → SquareP (λ i j → B (aSq i j) → C)
-- -- -- --                    a₀₋ a₁₋ a₋₀ a₋₁                     
-- -- -- -- funExtDepSq = {!!}




-- -- -- -- module recEMtrunc→ {ℓ ℓ'} {A : Type ℓ} (isSetA : isSet A)
-- -- -- --                           {B : Type ℓ'} (isGrpB : isGroupoid B)
-- -- -- --              -- (m : GroupHom G (idEquivsG A))
-- -- -- --              -- (C : Type ℓc) (isSetC : isSet C)
-- -- -- --              -- {ℓ''} {B : Type ℓ''} (truncB : isGroupoid B)
-- -- -- --              where
             
-- -- -- --   module EMa = EMΣ isSetA idGroupHom

-- -- -- --   EMG = EMa.EMG

-- -- -- --   EM₁Fam : EMG → Type (ℓ-max ℓ ℓ')
-- -- -- --   EM₁Fam x = EMa.EM₁Fam x → B

-- -- -- --   emΣ = Σ EMG EM₁Fam

-- -- -- --   isGroupoidEmΣ : isGroupoid emΣ
-- -- -- --   isGroupoidEmΣ = isGroupoidΣ emsquash λ _ → isGroupoidΠ λ _ → isGrpB

-- -- -- --   record _↔ₛ_ (x y : A → B) : Type (ℓ-max ℓ ℓ') where
-- -- -- --     constructor ↔s
-- -- -- --     field
-- -- -- --       F≃ : (A ≃ A)
-- -- -- --       l≡ : x  ≡ y ∘ fst F≃

-- -- -- --   isTrans↔ₛ : BinaryRelation.isTrans _↔ₛ_
-- -- -- --   isTrans↔ₛ a b c (↔s e p) (↔s f q) = 
-- -- -- --     ↔s (e ∙ₑ f) (p ∙ cong (_∘ (fst e)) q)

-- -- -- -- --   -- record _↔ₛ_ (x y : A → B) : Type (ℓ-max ℓ ℓ') where
-- -- -- -- --   --   constructor ↔s
-- -- -- -- --   --   field
-- -- -- -- --   --     F≃ : (A ≃ A)
-- -- -- -- --   --     l≡ : PathP (λ i → ua F≃ i → B) x y

-- -- -- -- --   -- isTrans↔ₛ : BinaryRelation.isTrans _↔ₛ_
-- -- -- -- --   -- isTrans↔ₛ a b c (↔s e p) (↔s f q) =
-- -- -- -- --   --   ↔s (e ∙ₑ f) ({!!} ◁ {!!} ▷ {!!})


-- -- -- --   A→// : Type (ℓ-max ℓ ℓ')
-- -- -- --   A→// = (A → B) // isTrans↔ₛ

-- -- -- --   fromPathP→ : (g : A ≃ A) {x₀ x₁ : A → B} →
-- -- -- --                 PathP (λ z → ua g z → B) x₀ x₁
-- -- -- --                 → x₀ ≡ (x₁ ∘ (fst g))
-- -- -- --   fromPathP→ g p i a = p i (ua-gluePath g (refl {x = (fst g) a}) i) 
    
-- -- -- --   loopP : ∀ g → PathP (λ i → (ua g i → B) → A→//) [_]// [_]//
-- -- -- --   loopP g =     
-- -- -- --     (λ i f  → [ f ∘ EMa.glueP g i ]// ) ▷
-- -- -- --     funExt λ x → eq// {a = x ∘ fst g} {x} (↔s g refl)
    
-- -- -- --     -- λ i f → 
-- -- -- --     --  eq// {a = {!f ∘ fst g!}}
-- -- -- --     --       {b = {!!}} (↔s g {!!}) i


  

-- -- -- --   to// : (x : EMG) (y : EMa.EM₁Fam x → B) → A→//
-- -- -- --   to// = elimEM _ (λ _ → isGroupoidΠ λ _ → squash//)
-- -- -- --     [_]//
-- -- -- --     loopP
-- -- -- --      zz  
-- -- -- --       where
-- -- -- --       -- zzR :
-- -- -- --       --    SquareP (λ i j → EM₁Fam (emcomp (idEquiv A) (idEquiv A) i j) → A→//)
-- -- -- --       --      (loopP (idEquiv A))
-- -- -- --       --    (loopP ((Symmetric-Group A isSetA .snd GroupStr.· (idEquiv A)) (idEquiv A)))
-- -- -- --       --    (λ j → [_]//) (loopP (idEquiv A))
-- -- -- --       -- zzR = {!!}


-- -- -- --       zz' : (g h : A ≃ A) →
-- -- -- --          SquareP (λ i j → (EMa.EM₁Fam (emcomp g h i j) → B) → A→//)
-- -- -- --           ((λ i f →  [ f ∘ EMa.glueP g i ]//))
-- -- -- --           (λ i f → [ f ∘ (EMa.glueP (g ∙ₑ h)) i ]// )
-- -- -- --            refl
           
-- -- -- --             λ i f →  [ f ∘ EMa.glueP h i ∘ fst g ]// 
-- -- -- --            -- (congP (λ _ z → _∘ {!(z ∘ g)!}) (EMa.glueP h))
-- -- -- --       zz' g h = {!!}
-- -- -- --         -- [ f ∘ (EMa.glueEMfam g h i j) ]//
-- -- -- --         -- -- {!!} ∘ {!(_∘ (EMa.glueEMfam g h i j))!}

-- -- -- --       zz : (g h : A ≃ A) →
-- -- -- --          SquareP (λ i j → EM₁Fam (emcomp g h i j) → A→//) (loopP g)
-- -- -- --          (loopP ((Symmetric-Group A isSetA .snd GroupStr.· g) h))
-- -- -- --          (λ j → [_]//) (loopP h)
-- -- -- --       zz g h i j f = {!!}
-- -- -- --         -- {!!} ∘ {!(_∘ (EMa.glueEMfam g h i j))!}
-- -- -- --       -- funExtDepSq _ _ _ _
-- -- -- --       --   λ {_} {_} {a₀₋} {_} {_} {_} {_} {a₋₁}
-- -- -- --       --     sqA → {!!} ▷
-- -- -- --       --       λ j → {!(λ i →
-- -- -- --       --    loopP ((Symmetric-Group A isSetA .snd GroupStr.· g) h) i (a₁₋ i))!}
          
-- -- -- --         --{!compPath-filler ? ?!} ▷ {!!}
-- -- -- --         -- (hcomp
-- -- -- --         --     (λ k →
-- -- -- --         --        λ {
-- -- -- --         --          (i = i0) → {!!}               
-- -- -- --         --        ; (i = i1) → {!!}
-- -- -- --         --        ; (j = i0) → {!!}
-- -- -- --         --        ; (j = i1) → {!!}
-- -- -- --         --        }) {!!}) ∘ 
-- -- -- --         -- {!EMa.unglueEMfam g h i j!}



-- -- -- --   loopP⁻ : (g : A ≃ A) {x₀ x₁ : A → B}
-- -- -- --               → x₀ ≡ x₁ ∘ fst g
-- -- -- --               → PathP (λ i → ua g i → B)
-- -- -- --                   x₀ x₁               
-- -- -- --   loopP⁻ g {x₀} {x₁} p =
-- -- -- --     sym (cong (x₀ ∘_) (funExt (retEq g)))
-- -- -- --     ◁ (λ i → p i ∘ invEq g ∘ ua-unglue g i) ▷
-- -- -- --      cong (x₁ ∘_) (funExt (secEq g))


-- -- -- -- -- isGroupoidEmΣ
-- -- -- --   from// : A→// → emΣ
-- -- -- --   from// = rec// _ isGroupoidEmΣ
-- -- -- --     (embase ,_) p//
-- -- -- --      λ r s → compPath-filler _ _ ▷ p//∙ r s

-- -- -- --     where
-- -- -- --       p// : {a b : A → B} → a ↔ₛ b → (embase , a) ≡ (embase , b)
-- -- -- --       p// (↔s e p) = ΣPathP ((emloop e) , loopP⁻ e p)

-- -- -- --       p//∙ : {a b c : A → B} (r : a ↔ₛ b) (s : b ↔ₛ c) →
-- -- -- --                 p// r ∙ p// s
-- -- -- --                 ≡
-- -- -- --                 (p// (isTrans↔ₛ _ _ _ r s)) 
-- -- -- --       p//∙ {a} {b} {c} (↔s e p) (↔s f q) = ΣPathP∙ _ _ _ _
-- -- -- --         ∙ cong ΣPathP w
-- -- -- --         where
 
-- -- -- --           ww : SquareP
-- -- -- --                   (λ i j → EMa.EM₁Fam
-- -- -- --              (emloop-comp (Symmetric-Group A isSetA) e
-- -- -- --               f (~ i) j) →
-- -- -- --              B)
-- -- -- --              (compPathP→ (EMa.EM₁Fam) (loopP⁻ e p) (loopP⁻ f q))
-- -- -- --              (loopP⁻ (e ∙ₑ f) (p ∙ cong (_∘ fst e) q))
-- -- -- --              refl refl
-- -- -- --           ww i j = {!!}

-- -- -- --           w : ((emloop e) ∙ (emloop f) , compPathP→ (EMa.EM₁Fam) (loopP⁻ e p)
-- -- -- --                  (loopP⁻ f q))
-- -- -- --                 ≡
-- -- -- --                 ((emloop ( e ∙ₑ f)) ,
-- -- -- --                  (loopP⁻ (e ∙ₑ f) (p ∙ cong (_∘ (fst e)) q)))
-- -- -- --           fst (w i) = (emloop-comp _ e f) (~ i)
-- -- -- --           snd (w i) j = ww i j
          
-- -- -- -- --   iso-em-// : Iso emΣ A→//
-- -- -- -- --   Iso.fun iso-em-// = uncurry to//
-- -- -- -- --   Iso.inv iso-em-// = from//
-- -- -- -- --   Iso.rightInv iso-em-// =
-- -- -- -- --     elimSet// _ (λ _ → squash// _ _)
-- -- -- -- --      (λ _ → refl) λ {a} {b} r → {!!}
-- -- -- -- --   Iso.leftInv iso-em-// =
-- -- -- -- --      uncurry (elimSet _ (λ _ → isSetΠ λ _ → isGroupoidEmΣ _ _)
-- -- -- -- --       (λ _ → refl) {!!})
 
-- -- -- -- -- -- --   -- open GroupStr (snd G)  
-- -- -- -- -- -- --   -- module M = IsGroupHom (snd m)

-- -- -- -- -- -- --   -- relIdEq : A → A → Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- --   -- relIdEq x y = Σ ⟨ G ⟩  λ g → fst (fst ((fst m) g)) x ≡  y 

-- -- -- -- -- -- --   -- -- relIdEq' : A → A → Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- --   -- -- relIdEq' x y = ⟨ G ⟩ × (x ≡ y) 


-- -- -- -- -- -- --   -- relIdEqTrans : BinaryRelation.isTrans relIdEq
-- -- -- -- -- -- --   -- relIdEqTrans a b c (g , p) (h , q) =
-- -- -- -- -- -- --   --   (g · h) , ( (funExt⁻ (cong (fst ∘ fst) (M.pres· g h)) a) ∙
-- -- -- -- -- -- --   --     cong (fst (fst (fst m h))) p ) ∙ q

-- -- -- -- -- -- --   -- RelId// =  (_//_ A {R = relIdEq} relIdEqTrans)


-- -- -- -- -- -- -- -- module recEMtrunc→More {ℓ ℓ'} {A : Type ℓ} {G : Group ℓ'} (isGrpA : isGroupoid A)
-- -- -- -- -- -- -- --                (m : GroupHom G (idEquivsG A))
-- -- -- -- -- -- -- --             where
-- -- -- -- -- -- -- --   open GroupStr (snd G)  
-- -- -- -- -- -- -- --   module M = IsGroupHom (snd m)


-- -- -- -- -- -- -- --   module M/ = recEMtrunc→ isGrpA m

-- -- -- -- -- -- -- --   mr : GroupHom G (idEquivsG A)
-- -- -- -- -- -- -- --   fst mr _ = _ , refl
-- -- -- -- -- -- -- --   IsGroupHom.pres· (snd mr) = λ _ _ → isPropSingl _ _
-- -- -- -- -- -- -- --   IsGroupHom.pres1 (snd mr) = isPropSingl _ _
-- -- -- -- -- -- -- --   IsGroupHom.presinv (snd mr) = λ _ → isPropSingl _ _

-- -- -- -- -- -- -- --   mr=m : mr ≡ m
-- -- -- -- -- -- -- --   mr=m = GroupHom≡ (funExt λ _ → isPropSingl _ _)

-- -- -- -- -- -- -- --   module M/r = recEMtrunc→ isGrpA mr

-- -- -- -- -- -- -- --   ≡r// : Iso (EM₁ G × A) M/r.RelId//
-- -- -- -- -- -- -- --   Iso.fun ≡r// (_ , a) = [ a ]//
-- -- -- -- -- -- -- --   Iso.inv ≡r// =
-- -- -- -- -- -- -- --     rec// _ {!!} (embase ,_) (λ (g , p) → cong₂ _,_ (emloop g) p)
-- -- -- -- -- -- -- --       λ gp hq →
-- -- -- -- -- -- -- --         let (g , p) = gp
-- -- -- -- -- -- -- --             (h , q) = hq
-- -- -- -- -- -- -- --         in (λ i j → (emcomp  g h i j  , compPath-filler p q i j)) ▷
-- -- -- -- -- -- -- --           cong (cong₂ _,_ (emloop (g · h)))
-- -- -- -- -- -- -- --           (( GL.lUnit _ ∙ cong (_∙ (p ∙ q))
-- -- -- -- -- -- -- --            (compPathRefl ∙ {!!}
-- -- -- -- -- -- -- --             )) ∙ GL.assoc _ _ _)
-- -- -- -- -- -- -- --           -- λ i → cong₂ _,_ (emloop (g · h)) {!!}
-- -- -- -- -- -- -- --   Iso.rightInv ≡r// = elimSet//
-- -- -- -- -- -- -- --    _ (λ _ → squash// _ _)
-- -- -- -- -- -- -- --    (λ a → refl) λ (g , p) → λ i i₁ → {!!}
-- -- -- -- -- -- -- --   Iso.leftInv ≡r// = uncurry (flip (λ x → elimSet _ (λ _ → {!!}) (refl)
-- -- -- -- -- -- -- --      λ g → toPathP λ i i₁ → {!!} , x))

-- -- -- -- -- -- -- --   -- -- relIdEqTrans' : BinaryRelation.isTrans relIdEq'
-- -- -- -- -- -- -- --   -- -- relIdEqTrans' a b c (g , p) (h , q) = (g · h) , ((refl ∙ p) ∙ q)
-- -- -- -- -- -- -- --   -- --   -- (g · h) , ( (funExt⁻ (cong (fst ∘ fst) (M.pres· g h)) a) ∙
-- -- -- -- -- -- -- --   -- --   --   cong (fst (fst (fst m h))) p ) ∙ q

-- -- -- -- -- -- -- --   -- -- zz : A // relIdEqTrans → A
-- -- -- -- -- -- -- --   -- -- zz = rec// _ isGrpA (idfun _) (λ (g , p) → funExt⁻ (cong fst (snd (fst m g))) _ ∙ p)
-- -- -- -- -- -- -- --   -- --   {!!}
-- -- -- -- -- -- -- --   -- Eq≡Eq' : (_//_ A {R = relIdEq} relIdEqTrans) ≡ (_//_ A {R = relIdEq'} relIdEqTrans')
-- -- -- -- -- -- -- --   -- Eq≡Eq' i = _//_ A {R = λ x y → Σ ⟨ G ⟩ λ g → cong fst (snd ((fst m) g)) (~ i) x ≡ y }
-- -- -- -- -- -- -- --   --   λ a b c (g , p) (h , q) → (g · h) , λ i₁ → {!!}

-- -- -- -- -- -- -- --   -- iso// : Iso (EM₁ G × A) (_//_ A {R = relIdEq} relIdEqTrans)
-- -- -- -- -- -- -- --   -- Iso.fun iso// = {!!}
-- -- -- -- -- -- -- --   -- Iso.inv iso// = {!!}
-- -- -- -- -- -- -- --   -- Iso.rightInv iso// = {!!}
-- -- -- -- -- -- -- --   -- Iso.leftInv iso// = {!!}

-- -- -- -- -- -- -- -- -- module recEMtrunc→ {ℓ ℓ' ℓc} {A : Type ℓ} {G : Group ℓ'} (isSetA : isSet A)
-- -- -- -- -- -- -- -- --              (m : GroupHom G (Symmetric-Group _ isSetA))
-- -- -- -- -- -- -- -- --              (C : Type ℓc) (isSetC : isSet C)
-- -- -- -- -- -- -- -- --              {ℓ''} {B : Type ℓ''} (truncB : isGroupoid B)
-- -- -- -- -- -- -- -- --              where

-- -- -- -- -- -- -- -- --   open EMΣ _ (SymmetricGroup→Hom {A = A} {isSetA = isSetA} isSetC )

-- -- -- -- -- -- -- -- --   module recEMΣ (b : (y : A → C) → B) 
-- -- -- -- -- -- -- -- --               where
-- -- -- -- -- -- -- -- --     bP : (g : A ≃ A) →
-- -- -- -- -- -- -- -- --            PathP (λ i → (y : ua (preCompEquiv {C = C} (invEquiv g)) i) → B) b b
-- -- -- -- -- -- -- -- --     bP g i x = {!b (ua-unglue (preCompEquiv {C = C} (invEquiv g)) i x)!}
-- -- -- -- -- -- -- -- --     -- {!funTypeTransp ? ? ? ?!} ▷ {!!}
-- -- -- -- -- -- -- -- --     -- toPathP ({!funTypeTransp   !} ∙ {!!})

    

-- -- -- -- -- -- -- -- --     -- f : EMtrunc → B
-- -- -- -- -- -- -- -- --     -- f = uncurry
-- -- -- -- -- -- -- -- --     --      (elimEM _ (λ _ → isGroupoidΠ λ _ → truncB)
-- -- -- -- -- -- -- -- --     --        b
-- -- -- -- -- -- -- -- --     --        bP
-- -- -- -- -- -- -- -- --     --        {!!})


-- -- -- -- -- -- -- -- --     f : EMtrunc → B
-- -- -- -- -- -- -- -- --     f = uncurry
-- -- -- -- -- -- -- -- --          (elimEM _ (λ _ → isGroupoidΠ λ _ → truncB)
-- -- -- -- -- -- -- -- --            b
-- -- -- -- -- -- -- -- --            bP
-- -- -- -- -- -- -- -- --            {!!})

-- -- -- -- -- -- -- -- --   -- module recEMtruncSingl {ℓ'} {B : Type ℓ'} (truncB : isGroupoid B)
-- -- -- -- -- -- -- -- --   --                   (b : A → B)
-- -- -- -- -- -- -- -- --   --                   -- (p : (g : ⟨ G ⟩) → PathP (λ i → ua (fst m g ) i → B) b b)
-- -- -- -- -- -- -- -- --   --                   -- (p₀ : (g : ⟨ G ⟩) → (a : A) → b a ≡ b (fst m g .fst a))
-- -- -- -- -- -- -- -- --   --                   -- (bIds : GroupHom G (idEquivsG B))
-- -- -- -- -- -- -- -- --   --                       where
-- -- -- -- -- -- -- -- --   --     f : (x : EMG) (y : EM₁Fam x) → singl {!!}
-- -- -- -- -- -- -- -- --   --     f = {!!}

-- -- -- -- -- -- -- -- -- --   module recEMtrunc {ℓ'} {B : Type ℓ'} (truncB : isGroupoid B)
-- -- -- -- -- -- -- -- -- --                     (b : A → B)
-- -- -- -- -- -- -- -- -- --                     -- (p : (g : ⟨ G ⟩) → PathP (λ i → ua (fst m g ) i → B) b b)
-- -- -- -- -- -- -- -- -- --                     (p₀ : (g : ⟨ G ⟩) → (a : A) → b a ≡ b (fst m g .fst a))
-- -- -- -- -- -- -- -- -- --                     (bIds : GroupHom G (idEquivsG B))
                    
-- -- -- -- -- -- -- -- -- --                     -- (s₀ : (g h : ⟨ G ⟩)
-- -- -- -- -- -- -- -- -- --                     --   → PathP (λ k →
-- -- -- -- -- -- -- -- -- --                     --    PathP (λ j → ua (snd m .IsGroupHom.pres· g h k) j → B)
-- -- -- -- -- -- -- -- -- --                     --      b b )
-- -- -- -- -- -- -- -- -- --                     --  (ua→ (p₀ (g · h)))
-- -- -- -- -- -- -- -- -- --                     --  (ua→ λ a → p₀ g a ∙ p₀ h (fst m g .fst a)))

-- -- -- -- -- -- -- -- -- --                       where

-- -- -- -- -- -- -- -- -- --     module BID = IsGroupHom (snd bIds)
  
-- -- -- -- -- -- -- -- -- --     bE : (g : ⟨ G ⟩) → B → B
-- -- -- -- -- -- -- -- -- --     bE = fst ∘ fst ∘ fst bIds
-- -- -- -- -- -- -- -- -- --     p* : (g : ⟨ G ⟩) → (x : B) → x ≡ bE g x
-- -- -- -- -- -- -- -- -- --     p* = funExt⁻ ∘ cong fst ∘ snd ∘ fst bIds

-- -- -- -- -- -- -- -- -- --     p*· : (g h : ⟨ G ⟩) → (a : A) → PathP
-- -- -- -- -- -- -- -- -- --                       (λ i →  b a ≡ fst (fst (BID.pres· g h i)) (b a))
-- -- -- -- -- -- -- -- -- --                       (λ i → fst (snd (fst bIds (g · h)) i) (b a))
-- -- -- -- -- -- -- -- -- --                       λ i → snd (fst bIds h) i .fst (snd (fst bIds g) i .fst (b a))
-- -- -- -- -- -- -- -- -- --     p*· g h a i = funExt⁻ (cong fst (snd (BID.pres· g h i))) (b a)



-- -- -- -- -- -- -- -- -- --     -- p : ∀ g → (a : A) → b a ≡ b (fst m g .fst a)
-- -- -- -- -- -- -- -- -- --     -- p = {!!}

-- -- -- -- -- -- -- -- -- --     -- p : (g : ⟨ G ⟩) → PathP (λ i → ua (fst m g ) i → B) b b
-- -- -- -- -- -- -- -- -- --     -- p g = ua→ (p₀ g)

-- -- -- -- -- -- -- -- -- --     -- bSA : (g : ⟨ G ⟩) → singl b
-- -- -- -- -- -- -- -- -- --     -- bSA g = b ∘ fst m g .fst , funExt (p₀ g)

-- -- -- -- -- -- -- -- -- --     bSB : (g : ⟨ G ⟩) → singl b
-- -- -- -- -- -- -- -- -- --     bSB g = bE g ∘ b , cong (_∘ b) ((cong fst ∘ snd ∘ fst bIds) g)

-- -- -- -- -- -- -- -- -- --     -- p2 : (g : ⟨ G ⟩) → PathP (λ i → ua (fst m g ) i → B) b b
-- -- -- -- -- -- -- -- -- --     -- p2 g = snd (bSA g) ◁ (λ i → b ∘ (ua-unglue (fst m g) i) )



   

-- -- -- -- -- -- -- -- -- --     module Rec 
-- -- -- -- -- -- -- -- -- --         (p₀* : (g : ⟨ G ⟩) → (a : A) → b (fst m g .fst a) ≡ bE g (b a))
-- -- -- -- -- -- -- -- -- --         (s₀ : (g : ⟨ G ⟩) → (a : A) → p* g (b a) ∙ sym (p₀* g a) ≡ p₀ g a)
-- -- -- -- -- -- -- -- -- --         where

-- -- -- -- -- -- -- -- -- --       p : (g : ⟨ G ⟩) → PathP (λ i → ua (fst m g ) i → B) b b
-- -- -- -- -- -- -- -- -- --       p g = (snd (bSB g) ∙ sym (funExt (p₀* g))) ◁ (λ i → b ∘ (ua-unglue (fst m g) i) )

-- -- -- -- -- -- -- -- -- -- --       p2S : (g : ⟨ G ⟩) → ∀ a → Path (singl (b a)) (_ , refl)
-- -- -- -- -- -- -- -- -- -- --            (bE g (b a) , funExt⁻ ((cong fst ∘ snd ∘ fst bIds) g) ( b a))
-- -- -- -- -- -- -- -- -- -- --       p2S g a i = {!!} , {!!}



-- -- -- -- -- -- -- -- -- -- --       f' : (x : EMG) (y : EM₁Fam x) → B
-- -- -- -- -- -- -- -- -- -- --       f' = elimEM G (λ _ → isGroupoidΠ λ _ → truncB)
-- -- -- -- -- -- -- -- -- -- --           b
-- -- -- -- -- -- -- -- -- -- --           p
-- -- -- -- -- -- -- -- -- -- --           s


-- -- -- -- -- -- -- -- -- -- --         where

-- -- -- -- -- -- -- -- -- -- --           bdS : (g h : ⟨ G ⟩) →
-- -- -- -- -- -- -- -- -- -- --                Square {A = Type (ℓ-max ℓ ℓ')}
-- -- -- -- -- -- -- -- -- -- --                  (λ i → (a : ua (fst m g ) i) → B)
-- -- -- -- -- -- -- -- -- -- --                  (λ i → (a : ua (fst m (g · h) ) i) → B)
-- -- -- -- -- -- -- -- -- -- --                  refl
-- -- -- -- -- -- -- -- -- -- --                  (λ i → (a : ua (fst m h ) i) → B)

-- -- -- -- -- -- -- -- -- -- --           bdS g h = λ i j → ( (compPath-filler _ _) ▷
-- -- -- -- -- -- -- -- -- -- --                (sym (uaCompEquiv (fst m g) (fst m h))
-- -- -- -- -- -- -- -- -- -- --                   ∙ cong ua (sym ((snd m) .IsGroupHom.pres· g h)))) i j → B

-- -- -- -- -- -- -- -- -- -- --           s : (g h : ⟨ G ⟩) →
-- -- -- -- -- -- -- -- -- -- --              SquareP (λ i j → ( (compPath-filler _ _) ▷
-- -- -- -- -- -- -- -- -- -- --                (sym (uaCompEquiv _ _) ∙ cong ua (sym ((snd m) .IsGroupHom.pres· g h)))) i j → B)
-- -- -- -- -- -- -- -- -- -- --                   (p g)
-- -- -- -- -- -- -- -- -- -- --                   (p (g · h))
-- -- -- -- -- -- -- -- -- -- --                   refl
-- -- -- -- -- -- -- -- -- -- --                   (p h)
-- -- -- -- -- -- -- -- -- -- --           s g h i j =
-- -- -- -- -- -- -- -- -- -- --             comp (λ k → doubleWhiskFiller refl (compPath-filler _ _)
-- -- -- -- -- -- -- -- -- -- --               ((sym (uaCompEquiv _ _) ∙ cong ua (sym ((snd m) .IsGroupHom.pres· g h)))) k i j
-- -- -- -- -- -- -- -- -- -- --                 → B)
-- -- -- -- -- -- -- -- -- -- --               (λ k → λ { (i = i0) → (p g) j
-- -- -- -- -- -- -- -- -- -- --                        ; (i = i1) → sR k j 
-- -- -- -- -- -- -- -- -- -- --                        ; (j = i0) → b
-- -- -- -- -- -- -- -- -- -- --                        ; (j = i1) → (p h) i
-- -- -- -- -- -- -- -- -- -- --                        })
-- -- -- -- -- -- -- -- -- -- --               (compPathP→filler (λ x → x) (p g) (p h) i j)

-- -- -- -- -- -- -- -- -- -- --              where



-- -- -- -- -- -- -- -- -- -- --                pp : PathP (λ j₁ → (ua (fst m g) ∙ ua (fst m h)) j₁ → B) b b
-- -- -- -- -- -- -- -- -- -- --                pp = (compPathP→ (λ x → x) (p g) (p h))

-- -- -- -- -- -- -- -- -- -- --                ppMid : PathP (λ j → ua ((fst m g) ∙ₑ (fst m h)) j → B) b b
-- -- -- -- -- -- -- -- -- -- --                ppMid = {!!}
-- -- -- -- -- -- -- -- -- -- --                -- ua→ λ a → p₀ g a ∙ p₀ h (fst m g .fst a)  



-- -- -- -- -- -- -- -- -- -- --                sRl : SquareP (λ k j → uaCompEquiv (fst m g) (fst m h) k j → B )
-- -- -- -- -- -- -- -- -- -- --                        ppMid      
-- -- -- -- -- -- -- -- -- -- --                        pp
-- -- -- -- -- -- -- -- -- -- --                        (λ _ → b)
-- -- -- -- -- -- -- -- -- -- --                        λ _ → b
-- -- -- -- -- -- -- -- -- -- --                sRl = {!!}

-- -- -- -- -- -- -- -- -- -- --                -- postS : (a : A) → Square {A = singl (b a)}
-- -- -- -- -- -- -- -- -- -- --                --     (p2S g a)
-- -- -- -- -- -- -- -- -- -- --                --     (p2S (g · h) a)
-- -- -- -- -- -- -- -- -- -- --                --     refl
-- -- -- -- -- -- -- -- -- -- --                --     (isPropSingl _ _  ∙∙ (p2S h a) ∙∙ isPropSingl _ _)
-- -- -- -- -- -- -- -- -- -- --                -- postS i j  = {!!}


-- -- -- -- -- -- -- -- -- -- --                postS' : (a : A) → Square {A = singl (b a)}
-- -- -- -- -- -- -- -- -- -- --                    (p2S g a ∙ (isPropSingl _ _  ∙∙ (p2S h a) ∙∙ isPropSingl _ _))
-- -- -- -- -- -- -- -- -- -- --                    (p2S (g · h) a)
-- -- -- -- -- -- -- -- -- -- --                    refl
-- -- -- -- -- -- -- -- -- -- --                    refl
-- -- -- -- -- -- -- -- -- -- --                postS' i j  = {!!}

-- -- -- -- -- -- -- -- -- -- --                -- unglueGH : ∀ k j → ua (snd m .IsGroupHom.pres· g h k) j → A
-- -- -- -- -- -- -- -- -- -- --                -- unglueGH k j = ua-unglue (snd m .IsGroupHom.pres· g h k) j



-- -- -- -- -- -- -- -- -- -- --                sRrJ0 : Square {A = (A → B)}
-- -- -- -- -- -- -- -- -- -- --                            (cong (b ∘_) (cong fst (snd m .IsGroupHom.pres· g h)))
-- -- -- -- -- -- -- -- -- -- --                            refl
-- -- -- -- -- -- -- -- -- -- --                            (funExt (p₀* (g · h)) ∙
-- -- -- -- -- -- -- -- -- -- --                               cong (_∘ b) (sym ((cong fst ∘ snd ∘ fst bIds) (g · h)))) 
-- -- -- -- -- -- -- -- -- -- --                            (funExt λ a → sym (p₀ h (fst m g .fst a)) ∙ sym (p₀ g a))
-- -- -- -- -- -- -- -- -- -- --                sRrJ0 = {!s₀ (g · h)!}

-- -- -- -- -- -- -- -- -- -- --                -- sRrJ1 : Square {A = (A → B)}
-- -- -- -- -- -- -- -- -- -- --                --             refl
-- -- -- -- -- -- -- -- -- -- --                --             refl
-- -- -- -- -- -- -- -- -- -- --                --             (cong (_∘ b) (sym (funExt (p* (g · h)))))
-- -- -- -- -- -- -- -- -- -- --                --             (cong (_∘ b) (sym (funExt (p* (g · h)))))
-- -- -- -- -- -- -- -- -- -- --                -- sRrJ1 l _ = (cong (_∘ b) (sym (funExt (p* (g · h))))) l


-- -- -- -- -- -- -- -- -- -- --                sRr : PathP (λ k →
-- -- -- -- -- -- -- -- -- -- --                          PathP (λ j → ua (snd m .IsGroupHom.pres· g h k) j → B)
-- -- -- -- -- -- -- -- -- -- --                            b b )
-- -- -- -- -- -- -- -- -- -- --                        (p (g · h))
-- -- -- -- -- -- -- -- -- -- --                        ppMid

-- -- -- -- -- -- -- -- -- -- --                sRr k j = comp (λ l → ua (snd m .IsGroupHom.pres· g h k) j  → B)
-- -- -- -- -- -- -- -- -- -- --                  {φ = k ∨ j ∨ ~ k ∨ ~ j}
-- -- -- -- -- -- -- -- -- -- --                  (λ l → λ { (k = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- --                           ; (k = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- --                           ; (j = i0) → sRrJ0 l k
-- -- -- -- -- -- -- -- -- -- --                           ; (j = i1) → (cong (_∘ b) (sym (funExt (p* (g · h))))) l
-- -- -- -- -- -- -- -- -- -- --                           }) (( λ a → fst (postS' a k j) ) ∘
-- -- -- -- -- -- -- -- -- -- --                              (ua-unglue (snd m .IsGroupHom.pres· g h k) j)) 
               


-- -- -- -- -- -- -- -- -- -- --                sR : SquareP (λ k j → ((λ i₁ → uaCompEquiv (fst m g) (fst m h) (~ i₁)) ∙
-- -- -- -- -- -- -- -- -- -- --                                      (λ i₁ → ua (snd m .IsGroupHom.pres· g h (~ i₁))))
-- -- -- -- -- -- -- -- -- -- --                               k j →
-- -- -- -- -- -- -- -- -- -- --                               B)
-- -- -- -- -- -- -- -- -- -- --                        pp 
-- -- -- -- -- -- -- -- -- -- --                        (p (g · h))
-- -- -- -- -- -- -- -- -- -- --                        (λ _ → b)
-- -- -- -- -- -- -- -- -- -- --                        λ _ → b
-- -- -- -- -- -- -- -- -- -- --                sR = compPathP'
-- -- -- -- -- -- -- -- -- -- --                    {B = λ x → PathP (λ j → x j → B) b b}
-- -- -- -- -- -- -- -- -- -- --                      {p = sym (uaCompEquiv (fst m g) (fst m h))}
-- -- -- -- -- -- -- -- -- -- --                      {q = sym (cong ua ((snd m .IsGroupHom.pres· g h)))}
-- -- -- -- -- -- -- -- -- -- --                      (symP sRl)
-- -- -- -- -- -- -- -- -- -- --                      (symP sRr)


-- -- -- -- -- -- -- -- -- -- --                -- sL : SquareP (λ i j → compPath-filler (ua (fst m g)) (ua (fst m h)) i j → B)
-- -- -- -- -- -- -- -- -- -- --                --        (p g)
-- -- -- -- -- -- -- -- -- -- --                --        pp
-- -- -- -- -- -- -- -- -- -- --                --        (λ _ → b)
-- -- -- -- -- -- -- -- -- -- --                --        (p h)
-- -- -- -- -- -- -- -- -- -- --                -- sL = compPathP→filler (λ x → x) (p g) (p h) 

-- -- -- -- -- -- -- -- -- -- -- -- -- compPath-filler (ua (fst m g)) (ua (fst m h)) i j → B


-- -- -- -- -- -- -- -- -- -- -- -- -- (ua (fst m g)) (ua (fst m h))

    
-- -- -- -- -- -- -- -- -- -- -- -- --     f : EMtrunc → B
-- -- -- -- -- -- -- -- -- -- -- -- --     f = uncurry f'



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- constFunHLev : ∀ {ℓ'} (B : Type ℓ') →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 Iso (Σ (B → B) λ f → ∀ x → f x ≡ x) (∀ (x : B) → singl x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.fun (constFunHLev B) x x₁ = (fst x x₁) , (sym (snd x x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.inv (constFunHLev B) x = (fst ∘ x) , (sym ∘ snd ∘ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.rightInv (constFunHLev B) b = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.leftInv (constFunHLev B) a = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- recEMtrunc : ∀ {ℓ'} (B : Type ℓ') → (isGroupoid B) → (A → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             → (m' : GroupHom G (Symmetric-Group _ isSetA)) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- recEMtrunc = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- to : A // actRTrans → Σ (EM₁ G) (fst ∘ EM₁Fam)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- to = rec// actRTrans
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ x → embase , x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ r → ΣPathP ((emloop (fst r)) , toPathP (transportRefl _ ∙ sym (snd r))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- from : (e : EM₁ G) → (fst (EM₁Fam e)) → A // actRTrans
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- from = elimEM
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   G (λ _ → isGroupoidΠ λ _ → squash//)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    [_]//
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ g → ua→ λ a → eq// (g , refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isoGQΣ : Iso (A // actRTrans) (Σ _ (fst ∘ EM₁Fam))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.fun isoGQΣ = to
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.inv isoGQΣ = uncurry from
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.rightInv isoGQΣ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.leftInv isoGQΣ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   elimSet// actRTrans (λ _ → squash// _ _) (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     λ {a} {b} (r , p)  → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         -- {!!} ▷ (λ _ → eq// {a = a} {b} (r , p))
  


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ} {A B : Type ℓ} (f : A → B) where 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG : FreeGroup A → FreeGroup B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (η x) = η (f x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (x · x₁) = mapFG x · mapFG x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG ε = ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (inv x) = inv (mapFG x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (assoc x x₁ x₂ i) = (assoc (mapFG x) (mapFG x₁) (mapFG x₂) i) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (idr x i) = idr (mapFG x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (idl x i) = idl (mapFG x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (invr x i) = invr (mapFG x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (invl x i) = invl (mapFG x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (trunc x y p q i i₁) = (trunc _ _ (cong mapFG p) (cong mapFG q) i i₁)
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PermR : ℕ → Type₀ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   invo : ∀ {n} → PermR (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   braid : ∀ {n} → PermR (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   comm : ∀ {n} → Fin n → PermR (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   suc : ∀ {n} → PermR n → PermR (suc n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permRel : ∀ n → PermR n → FreeGroup (Fin n) × FreeGroup (Fin n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permRel .(suc _) invo = η zero , (inv (η zero))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permRel .(suc (suc _)) braid = (η zero · η one) · η zero , (η one · η zero) · η one
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permRel .(suc (suc _)) (comm x) = (η zero · η (suc (suc x))) , (η (suc (suc x)) · η zero)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permRel .(suc _) (suc x) = map-× (mapFG suc) (mapFG suc) (permRel _ x) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm : ℕ → Group ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm n = Presented (permRel (predℕ n))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators : ∀ {n} → ⟨ Perm (suc n) ⟩  → PT.∥ List (Fin n) ∥₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (η x) = PT.∣ [ x ] ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (x · x₁) = PT.map2 _++_ (toGenerators x) (toGenerators x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators ε = PT.∣ [] ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (inv x) = PT.map rev (toGenerators x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (assoc x x₁ x₂ i) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PT.squash₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (PT.map2 _++_ (toGenerators x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (PT.map2 _++_ (toGenerators x₁) (toGenerators x₂)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (PT.map2 _++_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (PT.map2 _++_ (toGenerators x) (toGenerators x₁)) (toGenerators x₂))  i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (idr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (idl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (invr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (invl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (rel i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (trunc x x₁ x₂ y i i₁) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPermFDMorphism : ∀ n → GroupHom (SymData n) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (sucPermFDMorphism n) = sucPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (sucPermFDMorphism n)) x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (y .fst (x .fst k)) }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (sucPermFDMorphism n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc k }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (sucPermFDMorphism n)) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (snd x .equiv-proof k .fst .fst) }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- punchHeadInOutL : ∀ {n} (k : Fin (suc n)) → Σ (List (Fin n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   λ l → concatG (SymData _) (map adjTransposition l) ≡ PunchHeadInOut≃ k 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- punchHeadInOutL {n} zero = [] , refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (punchHeadInOutL {suc n} (suc k)) = zero ∷ map suc (fst (punchHeadInOutL k))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (punchHeadInOutL {suc n} (suc k)) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cong ( swap0and1≃ ∙ₑ_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ({!!} ∙ cong sucPerm (snd (punchHeadInOutL k)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym : ∀ n → ⟨ GeneratedBy (SymData (suc n)) adjTransposition ⟩ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym zero = λ _ → PT.∣ [] , equivEq (funExt λ x → isContr→isProp isContrFin1 _ _) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym (suc n) e = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
      
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in PT.map (λ (l , p') → map suc l ++ fst (punchHeadInOutL (equivFun e zero))   ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (cong {x = (map adjTransposition
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (map suc l ++
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         fst (punchHeadInOutL (equivFun e zero))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          {y = map adjTransposition (map suc l)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ++ map adjTransposition (fst (punchHeadInOutL (fst e zero)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (concatG (SymData (suc (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ sym (concatG· {G = (SymData (suc (suc n)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (map adjTransposition (map suc l))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (map adjTransposition (fst (punchHeadInOutL (equivFun e zero)))))
           
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∙ cong₂ _∙ₑ_ ({!!} ∙ cong sucPerm p') (snd (punchHeadInOutL (equivFun e zero)))) ∙ sym p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (generatedSym n e')


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators : ∀ n → ⟨ GeneratedBy (Perm n) η ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators = {!!}





-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (η x) = PT.∣ [ x ] , sym (idr (η x)) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (x · x₁) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PT.map2 (λ (x , p) (y , q) → (x ++ y) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ({!!} ∙ cong₂ _·_ p q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (PermGenerators n x) (PermGenerators n x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n ε =  PT.∣ [] , refl ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (inv x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    PT.map (λ (x , p) → rev x ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (PermGenerators n x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (assoc x x₁ x₂ i) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    isProp→PathP {!!} {!!} {!!} i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ PermGenerators n (x · (x₁ · x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ PermGenerators n ((x · x₁) · x₂)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (idr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (idl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (invr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (invl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (rel i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (trunc x x₁ x₂ y i i₁) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ : ∀ {n} → ⟨ Perm (suc n) ⟩  → Fin (suc n) ≃ Fin (suc n) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (η x) = adjTransposition x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (x · y) = to≃ x ∙ₑ to≃ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ ε = idEquiv _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (inv x) = invEquiv (to≃ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (assoc x x₁ x₂ i) = (compEquiv-assoc (to≃ x) (to≃ x₁) (to≃ x₂)) i 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (idr x i) = compEquivEquivId (to≃ x) (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (idl x i) = compEquivIdEquiv (to≃ x) (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (invr x i) = invEquiv-is-rinv (to≃ x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (invl x i) = invEquiv-is-linv (to≃ x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel invo i) = swap0and1≃=invEquivSwap0and1 i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel braid i) = swap0and1Braid i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (comm x) i) = commTranspositions x i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (to≃ (rel (suc {suc n} ix) i)) zero = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (to≃ (rel (suc {suc n} ix) i)) (suc x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (to≃ (rel (suc {suc n} ix) i)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- ({!!} ∙∙ (λ i → sucPerm (to≃ (rel ix i))) ∙∙ equivEq {!!}) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (trunc x x₁ x₂ y i i₁) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL : ∀ {ℓ} {A : Type ℓ} {n} → V.Vec A n → ⟨ Perm n ⟩ → V.Vec A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL (x₁ V.∷ x₂ V.∷ l) (η zero) = (x₂ V.∷ x₁ V.∷ l)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL (x₁ V.∷ x₂ V.∷ l) (η (suc x)) = (x₁ V.∷ (onL (x₂ V.∷ l) (η x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (x · x₁) = onL (onL l x) x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l ε = l
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (inv x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (assoc x x₁ x₂ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (idr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (idl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (invr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (invl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (rel ix i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (trunc x x₁ x₂ y i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ to≃ (fromFree (mapFG suc (fst (permRel (suc n) ix))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ to≃ (fromFree (mapFG suc (snd (permRel (suc n) ix))))





-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GeneratedBy : ∀ {ℓ ℓg} → (G : Group ℓ) → (A : Type ℓg) → (A → fst G) → hProp (ℓ-max ℓ ℓg)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (GeneratedBy G A f) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (x : fst G) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∃ (List A) (λ l → x ≡ foldr (GroupStr._·_ (snd G) ∘ f) (GroupStr.1g (snd G)) l )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (GeneratedBy G A f) = isPropΠ λ _ → PT.squash₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GeneratedBy' : ∀ {ℓ ℓg} → (G : Group ℓ) → (A : Type ℓg) → (A → fst G) → hProp (ℓ-max ℓ ℓg)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (GeneratedBy' G A f) = PT.∥ (  (x : fst G) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Σ (List A) (λ l → x ≡ foldr (GroupStr._·_ (snd G) ∘ f) (GroupStr.1g (snd G)) l )) ∥₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (GeneratedBy' G A f) = PT.squash₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasS→≃ : ∀ {ℓ} → {A B : Type ℓ} → (f : A → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → PT.∥ Σ (B → A) (λ g → section f g × retract f g ) ∥₁ → isEquiv f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasS→≃ f = PT.rec (isPropIsEquiv _) λ x → isoToIsEquiv (iso f (fst x) (fst (snd x)) (snd (snd x)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasSR→≃ : ∀ {ℓ} → {A B : Type ℓ} → (f : A → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → PT.∥ hasSection f ∥₁ → PT.∥ hasRetract f ∥₁ → isEquiv f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasSR→≃ f = PT.rec2 (isPropIsEquiv _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  λ x x₁ → isoToIsEquiv (biInvEquiv→Iso-right (biInvEquiv _ (fst x) (snd x) (fst x₁) (snd x₁))) 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ} (G H : Group ℓ) (A : Type ℓ) (g : _ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (genG : ⟨ GeneratedBy' G A g ⟩ ) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (m : GroupHom G H)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (genH : ⟨ GeneratedBy' H A (fst m ∘ g) ⟩ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (f : H .fst → G .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (pp : ∀ a → f (fst m (g a)) ≡ g a )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           -- (m' : GroupHom H G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open GroupStr (snd G)  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isEquivM : isEquiv (fst m)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isEquivM = hasS→≃ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (PT.map2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ gH gG →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           let s = λ b → cong (fst m ∘ f) (snd (gH b)) ∙∙ {!!} ∙∙ sym (snd (gH b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              , (s
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               , λ a → cong (f ∘ (fst m)) ((snd (gG a)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ∙∙ sym (snd (gG a))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         genH genG)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- (PT.map
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   (λ gH →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      let f' = (λ x → foldr (GroupStr._·_ (snd G) ∘ g) (GroupStr.1g (snd G)) (fst (gH x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      in f' , (λ b → {!!} ∙ sym (snd (gH b)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   genH ) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- (PT.map2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   (λ gH gG →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      let f'' : H .fst → G .fst 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          f'' = (λ x → foldr (GroupStr._·_ (snd G) ∘ g) (GroupStr.1g (snd G)) (fst (gH x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          -- f' = λ x → foldr (GroupStr._·_ (snd G) ∘ g) (GroupStr.1g (snd G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          --   (fst (gG (f'' x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      in f'' , λ a → {!sym (snd (gH (fst m a)))!}  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   genH genG ) 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- genH' : ⟨ GeneratedBy H A (fst m ∘ g) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- genH' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM : ∀ xs → fst m (foldr (λ x₂ → snd G GroupStr.· g x₂) 1g xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      foldr (λ x₂ → snd H GroupStr.· h x₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (GroupStr.1g (snd H)) xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM = {!!} 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM' : ∀ xs → fst m' (foldr (λ x₂ → snd H GroupStr.· h x₂) (GroupStr.1g (snd H)) xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      foldr (λ x₂ → snd G GroupStr.· g x₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (GroupStr.1g (snd G)) xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM' = {!!} 




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- sec : section (fst m) (fst m')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- sec x = PT.rec2 {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ (xs , p) (ys , q) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      let z = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      in cong (fst m ∘ fst m') p ∙ {!!} ∙ sym p ) (genH x) (genH (fst m (fst m' x)))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   sec : section (fst m) (fst m')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   sec x = PT.rec2 {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ (x , p) (y , q) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        let z = sym q ∙ cong (fst m') p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        in {!!} ∙ (foldM x) ∙ sym p ) (genH x) (genG (fst m' x))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isInjectiveGen : isInjective m
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isInjectiveGen x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   PT.rec2 (isPropΠ λ _ → is-set _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (λ x₂ x₃ p →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       let pp = sym p ∙ snd x₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       in snd x₂ ∙ {!pp!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (genG x) (genH (fst m x))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPermFDMorphism : ∀ n → GroupHom (SymData n) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (sucPermFDMorphism n) = sucPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (sucPermFDMorphism n)) x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (y .fst (x .fst k)) }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (sucPermFDMorphism n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc k }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (sucPermFDMorphism n)) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (snd x .equiv-proof k .fst .fst) }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PLaws  : {n : ℕ} → List (Fin n) → List (Fin n) → Type where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pInvo : ∀ {n} → PLaws {suc n} (zero ∷ zero ∷ []) []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pComm : ∀ {n} → ∀ k → PLaws {suc (suc n)} (zero ∷ suc (suc k) ∷ []) (suc (suc k) ∷ zero ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pBraid : ∀ {n} → PLaws {suc (suc n)} (zero ∷ one ∷ zero ∷ []) (one ∷ zero ∷ one ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p↑ : ∀ {n k k'} → PLaws {n} k k' → PLaws {suc n} (map suc k) (map suc k')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p← : ∀ {n k k' x} → PLaws {n} k k' → PLaws {n} (x ∷ k) (x ∷ k')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p→ : ∀ {n k k' x} → PLaws {n} k k' → PLaws {n} (k ∷ʳ x) (k' ∷ʳ x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPL : ∀ {n} → (_ / PLaws {n}) → (_ / PLaws {suc n}) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPL =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   rec/ squash/ ([_]/ ∘ map suc) (λ _ _ → eq/ _ _ ∘ p↑)
  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷ʳPL : ∀ {n} → ∀ x → (_ / PLaws {n}) → (_ / PLaws {n}) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷ʳPL x = rec/ squash/ ([_]/ ∘ (_∷ʳ x)) (λ _ _ → eq/ _ _ ∘ p→)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷PL : ∀ {n} → ∀ x → (_ / PLaws {n}) → (_ / PLaws {n}) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷PL x = rec/ squash/ ([_]/ ∘ (x ∷_)) (λ _ _ → eq/ _ _ ∘ p←)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- map-++ : ∀ {ℓ} {A B : Type ℓ} (f : A → B) → ∀ xs ys → map f (xs ++ ys) ≡ (map f xs) ++ (map f ys) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- map-++ f [] ys = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- map-++ f (x ∷ xs) ys = cong (_ ∷_) (map-++ f xs ys)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- rev-map : ∀ {ℓ} {A B : Type ℓ} (f : A → B) → ∀ xs → map f (rev xs) ≡ rev (map f xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- rev-map f = ind refl λ {a} {l} p → map-++ f (rev l) [ a ] ∙ cong (_∷ʳ f a) p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w : ∀ n → (a b : List (Fin n)) → PLaws {n} a b → Path (_ / PLaws {n}) [ rev a ]/ [ rev b ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ pInvo = eq/ _ _ pInvo
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (pComm k) = sym (eq/ _ _ (pComm k))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ pBraid = eq/ _ _ pBraid
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (p↑ {n} {a} {b} p) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let w' = w _ _ _ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      p' = cong sucPL w'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in cong [_]/ (sym (rev-map _ a)) ∙∙ p' ∙∙ cong [_]/ (rev-map _ b)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (p← {x = x} p) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let w' = w _ _ _ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in cong (∷ʳPL x) w'

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (p→ {k = k} {k' = k'} {x = x} p) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let w' = w _ _ _ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in cong [_]/ (rev-snoc k _) ∙∙ cong (∷PL x) w' ∙∙  sym (cong [_]/ (rev-snoc k' _))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www : ∀ n → (a b c : List (Fin n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PLaws b c → Path (_ / PLaws {n}) [ a ++ b ]/ [ a ++ c ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www n [] b c x = eq/ _ _ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www n (x₁ ∷ a) b c x = cong (∷PL x₁) (www n a b c x)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www2 : ∀ n → (a b c : List (Fin n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PLaws a b → Path (_ / PLaws {n}) [ a ++ c ]/ [ b ++ c ]/

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www2 n a b [] x = cong [_]/ (++-unit-r _) ∙∙ eq/ _ _ x ∙∙ cong [_]/ (sym (++-unit-r _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www2 n a b (x₁ ∷ c) x = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong [_]/ (sym (++-assoc a [ x₁ ] c)) ∙∙ www2 _ _ _ c (p→ {x = x₁} x) ∙∙ cong [_]/ (++-assoc b [ x₁ ] c)  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∙Perm_ : ∀ {n} → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∙Perm_ {n} = rec2 squash/ (λ x y → [ x ++ y ]/) (www2 n) (www n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePerm : ∀ {n} → (k : Fin (suc n)) →  (_ / PLaws {n})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePerm {n} zero = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePerm {suc n} (suc k) = [  [ zero ]  ]/ ∙Perm sucPL (cyclePerm k)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assocPerm : ∀ {n} → (x y z : List (Fin n) / PLaws) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (x ∙Perm (y ∙Perm z)) ≡ ((x ∙Perm y) ∙Perm z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assocPerm = elimProp3 (λ _ _ _ → squash/ _ _) λ a b c → cong [_]/ (sym (++-assoc a b c))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permInvo : ∀ {n} → ∀ a → PLaws {n} (a ∷ a ∷ []) []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permInvo zero = pInvo
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permInvo (suc a) = p↑ (permInvo a)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm' : ℕ → Group ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Perm' n) = _ / PLaws {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.1g (snd (Perm' n)) = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr._·_ (snd (Perm' n)) = _∙Perm_ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.inv (snd (Perm' n)) = rec/ squash/ ([_]/ ∘ rev) (λ a b p → w n a b p)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.isGroup (snd (Perm' n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   makeIsGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     squash/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     assocPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (elimProp/ (λ _ → squash/ _ _) λ _ → cong ([_]/) (++-unit-r _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ((elimProp/ (λ _ → squash/ _ _) λ _ → refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (elimProp/ (λ _ → squash/ _ _) (ind refl λ {a = a} {l}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p → sym (assocPerm [ [ a ] ]/ [ l ]/ [ rev ([ a ] ++ l) ]/)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ∙ cong ([ [ a ] ]/ ∙Perm_) ( assocPerm [ l ]/ [ rev l ]/ [ _ ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∙ cong (_∙Perm [ [ a ] ]/) p) ∙ eq/ _ _ (permInvo a)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (elimProp/ (λ _ → squash/ _ _) (ind refl λ {a = a} {l}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p → sym (assocPerm [ rev l ]/ [ [ a ] ]/ [ _ ]/)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ∙ cong ([ rev l ]/ ∙Perm_) ( assocPerm [ [ a ] ]/ [ [ a ] ]/ [ _ ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∙ cong (_∙Perm [ l ]/) (eq/ _ _ (permInvo a))) ∙ p))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evenTest : ℕ → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evenTest zero = true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evenTest (suc x) = not (evenTest x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm : ℕ → Group ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm = Perm' ∘ predℕ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPermMorphism : ∀ n → GroupHom (Perm n) (Perm (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPermMorphism zero = idGroupHom
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (sucPermMorphism (suc n)) = sucPL
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (sucPermMorphism (suc n))) =  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp2 (λ _ _ → squash/ _ _ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    λ a b → cong [_]/ (map-++ suc a b)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (sucPermMorphism (suc n))) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (sucPermMorphism (suc n))) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp/ (λ _ → squash/ _ _) λ a → cong [_]/ (rev-map suc a)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermMorphism : ∀ n → isInjective (sucPermMorphism n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermMorphism zero = λ _ → idfun _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermMorphism (suc n) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimProp/ (λ _ → isPropΠ λ _ → squash/ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} --(ind (λ _ → refl) λ x x₁ → {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermFDMorphism : ∀ n → isInjective (sucPermFDMorphism n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermFDMorphism = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedPerm : ∀ n → ⟨ GeneratedBy (Perm' n) (Fin n) ([_]/ ∘ [_]) ⟩ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedPerm n = elimProp/ (λ _ → PT.squash₁ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (ind PT.∣ [] , refl ∣₁ (λ {a} → PT.map λ x → a ∷ fst x , cong ([ [ a ] ]/ ∙Perm_) (snd x)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym : ∀ n → ⟨ GeneratedBy (SymData (suc n)) (Fin n) adjTransposition ⟩ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym zero = λ _ → PT.∣ [] , equivEq (funExt λ x → isContr→isProp isContrFin1 _ _) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym (suc n) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in PT.map (λ (l , p') → map suc l ++ {!!}  , p ∙ {!!}) (generatedSym n e')

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH : ∀ n → (a b : List (Fin n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PLaws a b → ∀ k →  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fst (foldr (λ k y → adjTransposition k ∙ₑ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (idEquiv (Fin (suc n))) a) k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fst (foldr (λ k y → adjTransposition k ∙ₑ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (idEquiv (Fin (suc n))) b) k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ pInvo = λ { zero → refl ; one → refl ; (suc (suc k)) → refl }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (pComm k') = λ { zero → refl ; one → refl ; (suc (suc k)) → refl }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ pBraid = λ { zero → refl ; one → refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ; (suc (suc zero)) → refl ; (suc (suc (suc k))) → refl}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p↑ {k = k} {k'} x) zero = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p↑ {k = k} {k'} x) (suc j) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!} ∙∙ cong suc (PermHomH _ k k' x j) ∙∙ {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p← x) k = {!PermHomH _ _ _ (x) k!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p→ x) k = {!PermHomH _ _ _ (x) k!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm : ∀ n → fst (SymData (suc n)) → fst (Perm' n) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm zero x = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm (suc n) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in  sucPL (toPerm n e') ∙Perm cyclePerm (equivFun e zero) 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev : ∀ {ℓ} (G : Group ℓ) → (xs : List (fst G)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foldr (GroupStr._·_ (snd G)) (GroupStr.1g (snd G)) (rev xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     GroupStr.inv (snd G) (foldr ((GroupStr._·_ (snd G))) ((GroupStr.1g (snd G))) xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev' : ∀ {ℓ ℓg} (G : Group ℓ) (A : Type ℓg) (f : A → fst G) → (xs : List A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foldr (GroupStr._·_ (snd G) ∘ f) (GroupStr.1g (snd G)) (rev xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     GroupStr.inv (snd G) (foldr ((GroupStr._·_ (snd G)) ∘ f) ((GroupStr.1g (snd G))) xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev' G A f [] = sym (GroupTheory.inv1g G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev' G A f (x ∷ xs) = {!!} ∙ sym ((GroupTheory.invDistr G) _ _)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHom : ∀ n → GroupHom (Perm' n) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom n) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   rec/ (isSetΣ (isSet→ isSetFin) (λ _ → isProp→isSet (isPropIsEquiv _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (foldr (λ k y → adjTransposition k ∙ₑ y ) (idEquiv _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a b x → equivEq (funExt (PermHomH n a b x)))



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimProp2 (λ _ _ → isSetΣ (isSet→ isSetFin) (λ _ → isProp→isSet (isPropIsEquiv _)) _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (ind (λ _ → sym (compEquivIdEquiv _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        λ {a} p b → cong (compEquiv (adjTransposition a)) (p b) ∙ compEquiv-assoc _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom n)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp/ (λ _ → isSetΣ (isSet→ isSetFin) (λ _ → isProp→isSet (isPropIsEquiv _)) _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   λ l → fold-rev' (SymData (suc n)) (Fin n) adjTransposition l


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHL : ∀ n → ∀ e → PermHom (suc n) .fst (sucPL (toPerm _ e)) ≡ sucPerm e 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHL = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRRR : ∀ n → ∀ k → [ [ k ] ]/ ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (toPerm n (fst (PermHom _) [ [ k ] ]/))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRRR (suc n) k = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRRR (suc n) (suc k) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRR : ∀ n → ∀ k → cyclePerm (suc k) ≡ (toPerm n (fst (PermHom _) (cyclePerm (suc k))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRR .(suc _) zero = isSurPermHomHRRR _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRR .(suc (suc n)) (suc {suc n} k) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- cong (λ x → ([ [ zero ] ]/ ∙Perm sucPL x)) (isSurPermHomHRR _ k) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --  {!!} ∙ cong (toPerm _) (sym (IsGroupHom.pres· (snd (PermHom (suc _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   [ [ zero ] ]/ (sucPL (cyclePerm (fst {!!} {!!})))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR : ∀ n → ∀ k → fst (PermHom n) (cyclePerm k) ≡ (PunchHeadInOut≃ {suc n} k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR n zero = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR .(suc _) one = equivEq refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR .(suc _) (suc (suc k)) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IsGroupHom.pres· (snd (PermHom (suc _))) [ [ zero ] ]/ (sucPL (cyclePerm (suc k) ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∙ cong₂ _∙ₑ_ (compEquivEquivId _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ((cong {x = (cyclePerm (suc k) )} {y = (toPerm _ (fst (PermHom _) (cyclePerm (suc k))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ((fst (PermHom _)) ∘ sucPL) (isSurPermHomHRR _ k) ∙ isSurPermHomHL _ (fst (PermHom _) (cyclePerm (suc k))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∙ (cong sucPerm (isSurPermHomHR _ (suc k))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomH : ∀ n → ∀ x → PermHom n .fst (toPerm n x) ≡ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomH zero x = equivEq (funExt λ x → isContr→isProp isContrFin1 _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomH (suc n) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in  (IsGroupHom.pres· (snd (PermHom (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (sucPL (toPerm _ e')) (cyclePerm (equivFun e zero))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∙ cong₂ {x = PermHom _ .fst (sucPL (toPerm _ e'))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            {y = sucPerm e'}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      _∙ₑ_ {!!} {!!}) ∙ sym p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- (isSurPermHomHL _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- (isSurPermHomHR _ (equivFun e zero))) ∙ sym p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHom : ∀ n → isSurjective (PermHom n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHom n x =  PT.∣ (toPerm _ x) , isSurPermHomH n x ∣₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjPermHom : ∀ n → isInjective (PermHom n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjPermHom n =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp/ (λ _ → isPropΠ λ _ → squash/ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (ind (λ _ → refl) λ {a} _ p →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- ∙ eq/ _ _ (permInvo a))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm : ∀ n → (a : (_ / PLaws {suc n})) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  Σ (Fin (suc (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    λ k → Σ ((_ / PLaws {n})) λ e' → sucPL e' ∙Perm cyclePerm k ≡ a 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHom : ∀ n → GroupHom (Perm (suc n)) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom zero) _ = idEquiv _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom zero)) _ _ = equivEq refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom zero)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom zero)) _ = equivEq refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom (suc n)) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (k , e' , p) = unwindPerm _ e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in sucPerm ((fst (PermHom n)) e') ∙ₑ PunchHeadInOut≃ k 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom (suc n))) = {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom (suc n))) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom (suc n))) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHom⁻ : ∀ n → GroupHom (SymData (suc n)) (Perm (suc n)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom⁻ zero) _ = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom⁻ zero)) _ _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom⁻ zero)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom⁻ zero)) _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom⁻ (suc n)) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in  sucPL ((fst (PermHom⁻ n)) e') ∙Perm cyclePerm (equivFun e zero) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom⁻ (suc n))) x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom⁻ (suc n))) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (GroupStr.·IdR (snd (Perm (suc (suc n)))) (sucPL
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (fst (PermHom⁻ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          _ ))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- cong sucPL (GroupStr.·IdR (snd (Perm (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   {!(fst (PermHom⁻ n) _)!}) ∙ {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom⁻ (suc n))) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in {!!}  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePermAgree : ∀ n → ∀ k → (PunchHeadInOut≃ k) ≡ fst (PermHom (suc n)) (cyclePerm k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePermAgree = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP : ∀ n → (a b : List (Fin n)) → PLaws a b → evenTest (length a) ≡ evenTest (length b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc _) .(zero ∷ zero ∷ []) .[] pInvo = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc (suc _)) .(zero ∷ suc (suc k) ∷ []) .(suc (suc k) ∷ zero ∷ []) (pComm k) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc (suc _)) .(zero ∷ one ∷ zero ∷ []) .(one ∷ zero ∷ one ∷ []) pBraid = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc _) .(map suc _) .(map suc _) (p↑ {k = k} {k'} x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  cong evenTest (length-map suc k) ∙∙ wPP _ _ _ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∙∙ sym (cong evenTest (length-map suc k'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP n .(_ ∷ _) .(_ ∷ _) (p← x) = cong not (wPP _ _ _ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP n .(_ ∷ʳ _) .(_ ∷ʳ _) (p→ x) = {!!} ∙∙ cong not (wPP _ _ _ x) ∙∙ {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- parity : ∀ {n} → (_ / PLaws {n}) → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- parity {n} = rec/ isSetBool (evenTest ∘ length ) (wPP n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm : ∀ n → (a : (_ / PLaws {suc n})) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  Σ (Fin (suc (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    λ k → Σ ((_ / PLaws {n})) λ e' → sucPL e' ∙Perm cyclePerm k ≡ a 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm zero x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   if parity x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   then zero , [ [] ]/ , {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   else one , [ [] ]/ , {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm (suc n) a = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (sucPermFDMorphism n) = sucPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (sucPermFDMorphism n)) x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (y .fst (x .fst k)) }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (sucPermFDMorphism n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc k }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (sucPermFDMorphism n)) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (snd x .equiv-proof k .fst .fst) }




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermParity : ∀ n → GroupHom (Perm' n) BoolGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermParity n) = rec/ isSetBool (evenTest ∘ length ) (wPP n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermParity n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimProp2 (λ _  _ → isSetBool _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- elimProp/ {!!} (ind (elimProp/ (λ _ → isSetBool _ _) (λ _ → refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   λ {a} {l} → ind {B = λ l → ((y : List (Fin n) / PLaws) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       rec/ isSetBool (λ x → evenTest (length x)) (wPP n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       ((Perm n .snd GroupStr.· [ l ]/) y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       (BoolGroup .snd GroupStr.· evenTest (length l))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       (rec/ isSetBool (λ x → evenTest (length x)) (wPP n) y)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      (y : List (Fin n) / PLaws) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      rec/ isSetBool (λ x → evenTest (length x)) (wPP n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      ((Perm n .snd GroupStr.· [ a ∷ l ]/) y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      (BoolGroup .snd GroupStr.· not (evenTest (length l)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      (rec/ isSetBool (λ x → evenTest (length x)) (wPP n) y)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       (λ p → elimProp/ {!!} {!!}) (λ p p' → elimProp/ {!!} {!!}) l) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermParity n)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermParity n)) = elimProp/ (λ _ → isSetBool _ _) {!!}
