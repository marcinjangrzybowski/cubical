{-

This file contains quotient groups

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.QuotientGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Functions.Logic
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_·_; elim)
open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Binary.Base

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup

open import Cubical.HITs.FreeGroup.NormalForm.Demo


private
  variable
    ℓ : Level

module _ (G' : Group ℓ) (H' : Subgroup G') (Hnormal : isNormal H') where

  open BinaryRelation
  open isSubgroup (snd H')
  open GroupStr (snd G')
  open GroupTheory G'
  private
    G = ⟨ G' ⟩

  _~_ : G → G → Type ℓ
  x ~ y = x · inv y ∈ ⟪ H' ⟫

  isRefl~ : isRefl _~_
  isRefl~ x = subst-∈ ⟪ H' ⟫ (sym (·InvR x)) id-closed

  isSym~ : isSym _~_
  isSym~ a b x = subst-∈ ⟪ H' ⟫
    ( (inv (a · inv b)) gs⟨ G' ⟩ (b · inv a))
    (inv-closed x)

  isTrans~ : isTrans _~_
  isTrans~ a b c x x₁ =
    subst-∈ ⟪ H' ⟫ (((a · inv b) · b · inv c) gs⟨ G' ⟩ (a · inv c) ) (op-closed x x₁)
  
  isEquivRel~ : isEquivRel _~_
  isEquivRel.reflexive isEquivRel~ = isRefl~
  isEquivRel.symmetric isEquivRel~ = isSym~
  isEquivRel.transitive isEquivRel~ = isTrans~
  
  G/H : Type ℓ
  G/H = G /s _~_

  1/H : G/H
  1/H = [ 1g ]

  _·/H_ : G/H → G/H → G/H
  x ·/H y = setQuotBinOp isRefl~ isRefl~ _·_ rem x y
   where
   rem : (a a' b b' : G)
       → a · inv a' ∈ ⟪ H' ⟫
       → b · inv b' ∈ ⟪ H' ⟫
       → (a · b) · inv (a' · b') ∈ ⟪ H' ⟫
   rem a a' b b' haa' hbb' = subst-∈ ⟪ H' ⟫
      (cong (_ ·_) (sym (invDistr _ _))) rem5
     where
     rem1 : (inv a' · a) · b · inv b' ∈ ⟪ H' ⟫
     rem1 = ·CommNormalSubgroup H' Hnormal
              (op-closed  hbb' (·CommNormalSubgroup H' Hnormal haa'))

     rem2 : ((inv a' · a) · b) · inv b' ∈ ⟪ H' ⟫
     rem2 = subst-∈ ⟪ H' ⟫ (·Assoc _ _ _) rem1

     rem3 : inv b' · (inv a' · a) · b ∈ ⟪ H' ⟫
     rem3 = ·CommNormalSubgroup H' Hnormal rem2

     rem5 : (a · b) · inv b' · inv a' ∈ ⟪ H' ⟫
     rem5 = ·CommNormalSubgroup H' Hnormal (subst-∈ ⟪ H' ⟫
        (inv b' · (inv a' · a) · b gs⟨ G' ⟩ (inv b' · inv a') · a · b) rem3)

  inv/H : G/H → G/H
  inv/H = setQuotUnaryOp inv rem
    where
    rem : (a a' : G) → a · inv a' ∈ ⟪ H' ⟫ → inv a · inv (inv a') ∈ ⟪ H' ⟫
    rem a a' haa' = subst-∈ ⟪ H' ⟫
        (inv a · a' gs⟨ G' ⟩ inv a · inv (inv a'))
        rem1
      where
      
      rem1 : inv a · a' ∈ ⟪ H' ⟫
      rem1 = ·CommNormalSubgroup H' Hnormal
         (subst-∈ ⟪ H' ⟫
           (inv (a · inv a') gs⟨ G' ⟩ a' · inv a)
           (inv-closed haa'))

  ·/H-assoc : (a b c : G/H) → (a ·/H (b ·/H c)) ≡ ((a ·/H b) ·/H c)
  ·/H-assoc = elimProp3 (λ x y z → squash/ _ _) λ x y z → cong [_] (·Assoc x y z)

  ·/H-rid : (a : G/H) → (a ·/H 1/H) ≡ a
  ·/H-rid = elimProp (λ x → squash/ _ _) λ x → cong [_] (·IdR x)

  ·/H-invr : (a : G/H) → (a ·/H inv/H a) ≡ 1/H
  ·/H-invr = elimProp (λ x → squash/ _ _) λ x → cong [_] (·InvR x)

  asGroup : Group ℓ
  asGroup = makeGroup-right 1/H _·/H_ inv/H squash/ ·/H-assoc ·/H-rid ·/H-invr


_/_ : (G : Group ℓ) → (H : NormalSubgroup G) → Group ℓ
G / H = asGroup G (H .fst) (H .snd)

[_]/G : {G : Group ℓ} {H : NormalSubgroup G} → ⟨ G ⟩ → ⟨ G / H ⟩
[ x ]/G = [ x ]

-- Quotienting by a trivial subgroup
module _ {G' : Group ℓ} (H' : NormalSubgroup G')
         (contrH : (x y : fst G') → _~_ G' (fst H') (snd H') x y → x ≡ y) where
  private
    -- open isSubgroup (snd H')
    open GroupStr (snd G')
    open GroupTheory G'
    G = fst G'
    G/H' = fst (G' / H')

    Code : (g : G) → G/H' → hProp ℓ
    Code g =
      elim (λ _ → isSetHProp)
        (λ a → (g ≡ a) , is-set _ _)
        λ a b r → Σ≡Prop (λ _ → isPropIsProp) (cong (g ≡_) (contrH a b r))

    decode : (g : G) (x : G/H') → [ g ] ≡ x → Code g x .fst
    decode g x = J (λ x _ → Code g x .fst) refl

  trivialRel→elimPath : {g h : G} → Path G/H' [ g ] [ h ] → g ≡ h
  trivialRel→elimPath {g = g} {h = h} = decode g [ h ]

  trivialRelIso : GroupIso G' (G' / H')
  Iso.fun (fst trivialRelIso) g = [ g ]
  Iso.inv (fst trivialRelIso) =
    rec is-set (λ g → g) contrH
  Iso.rightInv (fst trivialRelIso) =
    elimProp (λ _ → squash/ _ _) λ _ → refl
  Iso.leftInv (fst trivialRelIso) _ = refl
  snd trivialRelIso =
    makeIsGroupHom λ _ _ → refl

module _ (G : Group ℓ) (P : ℙ ⟨ G ⟩) where
 open GroupTheory G
 module G = GroupStr (snd G)


 -- open GroupSolver G

 data _⇊_ : ⟨ G ⟩ → ⟨ G ⟩ → Type ℓ where
  _·_↘1g·_ : ∀ g {x} → x ∈ P → ∀ h → (g G.· (x  G.· h)) ⇊ (g G.· h)


 ⇊1g/ : ∀ {x} → x ∈ P →  x ⇊ G.1g
 ⇊1g/ {x} p = subst2 _⇊_ (G.·IdL _ ∙ G.·IdR _) (G.·IdR _) (G.1g · p ↘1g· G.1g)
 
 rec⇊ : ∀ {ℓ'} (B : ⟨ G ⟩ → ⟨ G ⟩ → Type ℓ') →
              (∀ g x h → x ∈ P →
                B (g G.· (x  G.· h)) ((g G.· h)) ) → ∀ x y → x ⇊ y →  B x y
 rec⇊ B x .(g G.· _ G.· h) _ (g · x₁ ↘1g· h) = x _ _ _ x₁
 
 ⟨G⟩/ : Type ℓ
 ⟨G⟩/ = ⟨ G ⟩ /s _⇊_

 _eq⇊_ : Rel ⟨ G ⟩ ⟨ G ⟩ ℓ 
 g eq⇊ h = Path ⟨G⟩/ [ g ] [ h ]

 P' : ℙ ⟨ G ⟩
 P' g = (Path ⟨G⟩/ [ g ] [ G.1g ]) , squash/ _ _

 P⊂P' : P ⊆ P' 
 P⊂P' x x₁ =
  cong [_] (x gs⟨ G ⟩ G.1g G.· x G.· G.1g) ∙∙
   eq/ _ _ (G.1g · x₁ ↘1g· G.1g)
    ∙∙ cong [_] (G.·IdR _)
 
 G/⇊ : Group ℓ
 fst G/⇊ = ⟨G⟩/
 GroupStr.1g (snd G/⇊) = [ G.1g ] 
 GroupStr._·_ (snd G/⇊) =
      rec2 squash/
     (λ g h → [ g G.· h ])
      (λ {_ _ c (_·_↘1g·_ g {x'} x h) → eq/ _ _
         (subst2 _⇊_ (g G.· x' G.· h G.· c gs⟨ G ⟩
               (g G.· x' G.· h) G.· c) (G.·Assoc _ _ _)
              (g · x ↘1g· (h G.· c)))})
      λ {a _ _ (g · x ↘1g· h) → eq/ _ _
        (subst2 _⇊_ (sym (G.·Assoc _ _ _)) (sym (G.·Assoc _ _ _))
          ((a G.· g) · x ↘1g· h))}
 GroupStr.inv (snd G/⇊) =
  rec squash/ ([_] ∘ G.inv)
    λ { _ _ (_·_↘1g·_ g {x'} x h) →
         cong [_] ( G.inv (g G.· x' G.· h) gs⟨ G ⟩ G.inv h G.· G.inv (g G.· x'))
          ∙∙ sym (eq/ _ _ (G.inv h · x ↘1g· G.inv (g G.· x'))) ∙∙
          cong [_] (G.inv h G.· x' G.· G.inv (g G.· x') gs⟨ G ⟩ G.inv (g G.· h))
        }
 GroupStr.isGroup (snd G/⇊) = makeIsGroup
   squash/
     (elimProp3 (λ _ _ _ → squash/ _ _)
       λ _ _ _ → cong [_] (G.·Assoc _ _ _))
   (elimProp (λ _ → squash/ _ _)
     λ _ → cong [_] (G.·IdR _))
     ((elimProp (λ _ → squash/ _ _)
     λ _ → cong [_] (G.·IdL _)))
   (elimProp (λ _ → squash/ _ _)
     λ _ → cong [_] (G.·InvR _))
   (elimProp (λ _ → squash/ _ _)
     λ _ → cong [_] (G.·InvL _))

 GQ = G / ((_ , isSubgroupNC P) , snd (normalClosure P))

 GroupIsoG'⟨G⟩/ : GroupIso G/⇊ GQ 
 fst GroupIsoG'⟨G⟩/ = setQuotientsIso
   (λ { _ _ (_·_↘1g·_ g {x'} x h) → eq/ _ _
        PT.∣ subst (∈NC P)
         (g G.· x' G.· G.inv g gs⟨ G ⟩ (g G.· x' G.· h) G.· G.inv (g G.· h))
         (∈normal g (∈inj x)) ∣₁ })
   λ a b → PT.rec (squash/ _ _)
   (((_∙ GroupTheory.invInv G/⇊ [ _ ])
     ∘ GroupTheory.invUniqueL G/⇊ {[ a ]} {[ _ ]}) ∘ w)
  where
  w : ∀ {g} → ∈NC {G' = G} P g → Path ⟨G⟩/ [ g ] [ G.1g ]
  w  ∈id = refl
  w (∈inj x) = eq/ _ _
    (subst2 _⇊_ (G.·IdL _ ∙ G.·IdR _) (G.·IdL _) (G.1g · x ↘1g· G.1g))
  w (∈inv x) = cong (GroupStr.inv (snd G/⇊)) (w x) ∙ cong [_] inv1g
  w (∈op x x₁) = cong₂ ( GroupStr._·_ (snd G/⇊)) (w x) (w x₁) ∙
     cong [_] (G.·IdL _)
  w (∈normal g x) = cong (GroupStr._·_ (snd G/⇊) [ g ])
    (cong (flip
      (GroupStr._·_ (snd G/⇊)) [ G.inv g ]) (w x) ∙ cong [_] (G.·IdL _))
        ∙ cong [_] (G.·InvR g)

 IsGroupHom.pres· (snd GroupIsoG'⟨G⟩/) =
  elimProp2 (λ _ _ → squash/ _ _) λ _ _ → refl
 IsGroupHom.pres1 (snd GroupIsoG'⟨G⟩/) = refl
 IsGroupHom.presinv (snd GroupIsoG'⟨G⟩/) =
   elimProp (λ _ → squash/ _ _) λ _ → refl
