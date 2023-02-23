{-

Eilenberg–Mac Lane type K(G, 1)

-}

{-# OPTIONS --cubical --no-import-sorts --safe  --experimental-lossy-unification #-}
module Cubical.HITs.EilenbergMacLane1.Properties where

open import Cubical.HITs.EilenbergMacLane1.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ⊥-rec) hiding (elim)


open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Properties

open import Cubical.Algebra.AbGroup.Base

open import Cubical.Functions.Morphism

private
  variable
    ℓG ℓ : Level

module _ ((G , str) : Group ℓG) where

  open GroupStr str

  elimGroupoid :
   {B : EM₁ (G , str) → Type ℓ}
          → ((x : EM₁ (G , str)) → isGroupoid (B x))
          → (b : B embase)
          → (bloop : ((g : G) → PathP (λ i → B (emloop g i)) b b))
          → ((g h : G) → PathP (λ i → PathP (λ j → B (emcomp g h j i))
                                 (bloop g i) (bloop (g · h) i)) (λ _ → b) (bloop h))
          → (x : EM₁ (G , str))
          → B x
  elimGroupoid Bgroup b bloop bcomp embase = b
  elimGroupoid Bgroup b bloop bcomp (emloop x i) = bloop x i
  elimGroupoid Bgroup b bloop bcomp (emcomp g h j i) = bcomp g h i j
  elimGroupoid {B = B} Bgroup b bloop bcomp (emsquash g h p q r s i j k) = help i j k
    where
    help : PathP (λ i → PathP (λ j → PathP (λ k → B (emsquash g h p q r s i j k))
                 (elimGroupoid Bgroup b bloop bcomp g)
                 (elimGroupoid Bgroup b bloop bcomp h))
                 (λ k → elimGroupoid Bgroup b bloop bcomp (p k))
                 λ k → elimGroupoid Bgroup b bloop bcomp (q k))
                 (λ j k → elimGroupoid Bgroup b bloop bcomp (r j k))
                 λ j k → elimGroupoid Bgroup b bloop bcomp (s j k)
    help = toPathP (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (Bgroup _) _ _) _ _ _ _)

  elimSet : {B : EM₁ (G , str) → Type ℓ}
          → ((x : EM₁ (G , str)) → isSet (B x))
          → (b : B embase)
          → ((g : G) → PathP (λ i → B (emloop g i)) b b)
          → (x : EM₁ (G , str))
          → B x
  elimSet Bset b bloop embase = b
  elimSet Bset b bloop (emloop g i) = bloop g i
  elimSet Bset b bloop (emcomp g h i j) =
    isSet→SquareP
      (λ i j → Bset (emcomp g h i j))
      (λ j → bloop g j) (λ j → bloop (g · h) j)
      (λ i → b) (λ i → bloop h i)
      i j
  elimSet Bset b bloop (emsquash x y p q r s i j k) =
    isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (Bset x))
      _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (emsquash x y p q r s) i j k
    where
      g = elimSet Bset b bloop


  record EMelim (B : EM₁ (G , str) → Type ℓ) : Type (ℓ-max ℓ ℓG) where
    no-eta-equality
    field
      isGrpB :(x : EM₁ (G , str)) → isGroupoid (B x)
      b : B embase
      bPathP : (g : G) → PathP (λ i → B (emloop g i)) b b
      bSqP : (g h : G) →
        SquareP (λ i j → B (emcomp g h i j))
           (bPathP g)
           (bPathP (g · h))
           refl
           (bPathP h)

    f : ∀ x → B x
    f embase = b
    f (emloop x i) = bPathP x i
    f (emcomp g h j i) = bSqP g h j i
      -- isSet→SquareP (λ j i → isSetB (emcomp g h j i))
      --   (bPathP g) (bPathP (g · h)) refl (bPathP h) j i 

    f (emsquash x y p q r s i j k) =
          isOfHLevel→isOfHLevelDep 3 (λ x → isGrpB x)
          _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (emsquash x y p q r s) i j k

    

  record EMelimSet (B : EM₁ (G , str) → Type ℓ) : Type (ℓ-max ℓ ℓG) where
    no-eta-equality
    field
      isSetB :(x : EM₁ (G , str)) → isSet (B x)
      b : B embase
      bPathP : (g : G) → PathP (λ i → B (emloop g i)) b b

    f : ∀ x → B x
    f embase = b
    f (emloop x i) = bPathP x i
    f (emcomp g h j i) =
      isSet→SquareP (λ j i → isSetB (emcomp g h j i))
        (bPathP g) (bPathP (g · h)) refl (bPathP h) j i 

    f (emsquash x y p q r s i j k) =
          isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (isSetB x))
          _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (emsquash x y p q r s) i j k

  record EMelimProp (B : EM₁ (G , str) → Type ℓ) : Type (ℓ-max ℓ ℓG) where
    no-eta-equality
    field
      isPropB :(x : EM₁ (G , str)) → isProp (B x)
      b : B embase
      -- bPathP : (g : G) → PathP (λ i → B (emloop g i)) b b

    fR : EMelimSet B
    EMelimSet.isSetB fR x = isProp→isSet (isPropB x)
    EMelimSet.b fR = b
    EMelimSet.bPathP fR g =
      isProp→PathP (λ i → isPropB ((emloop g) i)) b b

    f : ∀ x → B x
    f = EMelimSet.f fR

  elimProp : {B : EM₁ (G , str) → Type ℓ}
             → ((x : EM₁ (G , str)) → isProp (B x))
             → B embase
             → (x : EM₁ (G , str))
             → B x
  elimProp Bprop b x =
    elimSet
      (λ x → isProp→isSet (Bprop x))
      b
      (λ g → isProp→PathP (λ i → Bprop ((emloop g) i)) b b)
      x


  -- record EMelimSet2sym (B : EM₁ (G , str) → EM₁ (G , str) → Type ℓ) : Type (ℓ-max ℓ ℓG) where
  --   no-eta-equality
  --   field
  --     isSetB :(x y : EM₁ (G , str)) → isSet (B x y)
  --     symB : ∀ x y → B x y → B y x
  --     b : B embase embase
  --     bPathP : (g : G) → PathP (λ i → B embase (emloop g i)) b b
      

  --   fR' : EMelimSet (λ z → B embase z)
  --   EMelimSet.isSetB fR' = isSetB embase
  --   EMelimSet.b fR' = b
  --   EMelimSet.bPathP fR' = bPathP

  --   fR'' : (g : G) → EMelimProp
  --            (λ z →
  --        PathP (λ z₁ → B (emloop g z₁) z) (EMelimSet.f fR' z)
  --        (EMelimSet.f fR' z))
  --   EMelimProp.isPropB (fR'' g) x = {!!}
  --   EMelimProp.b (fR'' g) = {!congP (λ _ → symB _ _) (bPathP g)!}

  --   fR : EMelimSet (λ z → (y : EM₁ _) → B z y)
  --   EMelimSet.isSetB fR x = isSetΠ λ y → isSetB x y
  --   EMelimSet.b fR = EMelimSet.f fR'
  --   EMelimSet.bPathP fR g = funExt (EMelimProp.f (fR'' g))

  --   f : ∀ x y → B x y
  --   f = EMelimSet.f fR


  elimProp2 : {C : EM₁ (G , str) → EM₁ (G , str) → Type ℓ}
    → ((x y : EM₁ (G , str)) → isProp (C x y))
    → C embase embase
    → (x y : EM₁ (G , str))
    → C x y
  elimProp2 Cprop c =
    elimProp
      (λ x → isPropΠ (λ y → Cprop x y))
      (elimProp (λ y → Cprop embase y) c)

  elim : {B : EM₁ (G , str) → Type ℓ}
       → ((x : EM₁ (G , str)) → isGroupoid (B x))
       → (b : B embase)
       → (bloop : (g : G) → PathP (λ i → B (emloop g i)) b b)
       → ((g h : G) → SquareP (λ i j → B (emcomp g h i j))
            (bloop g) (bloop (g · h)) (λ j → b) (bloop h))
       → (x : EM₁ (G , str))
       → B x
  elim Bgpd b bloop bcomp embase = b
  elim Bgpd b bloop bcomp (emloop g i) = bloop g i
  elim Bgpd b bloop bcomp (emcomp g h i j) = bcomp g h i j
  elim Bgpd b bloop bcomp (emsquash x y p q r s i j k) =
    isOfHLevel→isOfHLevelDep 3 Bgpd
      _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (emsquash x y p q r s) i j k
    where
      g = elim Bgpd b bloop bcomp

  record EMrec {B : Type ℓ} (grpB :  isGroupoid B) : Type (ℓ-max ℓ ℓG) where
    no-eta-equality
    field
      b : B
      bloop : G → b ≡ b
      bComp : (g h : G) → Square (bloop g) (bloop (g · h)) refl (bloop h)

    f : EM₁ (G , str) → B  
    f embase = b
    f (emloop x i) = bloop x i
    f (emcomp g h j i) = bComp g h j i
    f (emsquash x x₁ p q r s i i₁ i₂) =
      grpB _ _ _ _ (λ i j → f (r i j)) (λ i j → f (s i j)) i i₁ i₂

  rec : {B : Type ℓ}
      → isGroupoid B
      → (b : B)
      → (bloop : G → b ≡ b)
      → ((g h : G) → Square (bloop g) (bloop (g · h)) refl (bloop h))
      → (x : EM₁ (G , str))
      → B
  rec Bgpd = elim (λ _ → Bgpd)


  record EMrecSet {B : Type ℓ} (setB :  isSet B) : Type (ℓ-max ℓ ℓG) where
   no-eta-equality
   field
     b : B
     bloop : G → b ≡ b

   fr : EMrec (isSet→isGroupoid setB)
   EMrec.b fr = b
   EMrec.bloop fr = bloop
   EMrec.bComp fr _ _ = isSet→isSet' setB _ _ _ _

   f : EM₁ _ → B
   f = EMrec.f fr


  -- toG : (x y : EM₁ (G , str)) → x ≡ y → {!!}
  -- toG x y = J _ (elimSet (λ _ → isSet→ is-set) (λ x → x) {!!} x)
  
  module _ {ℓH} {(H , str') : Group ℓH} where

    module H' =  GroupStr str'

    gh→em₂→ : GroupHom ((G , str)) ((H , str')) → EM₁ (G , str) → EM₁ (H , str')
    gh→em₂→ (f , fhom) =
      rec
        emsquash
        embase
        (λ x → emloop (f x))
        λ g h →
          compPath-filler _ _ ▷ 
           (sym (emloop-comp _ (f g) (f h))  ∙ cong emloop (sym (pres· g h)))
     where
       open IsGroupHom fhom
    
