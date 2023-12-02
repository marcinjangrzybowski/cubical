{-

Weak Equivalence between Categories

-}
{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.Equivalence.WeakEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Foundations.Equiv
  renaming (isEquiv to isEquivMap)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Category.Properties
open import Cubical.Categories.Equivalence
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary

open import Cubical.Foundations.Equiv.BiInvertible

open import Cubical.HITs.PropositionalTruncation as ∥∥₁

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C C' : Category ℓC ℓC'
    D : Category ℓD ℓD'
    F : Functor C D


open Functor
open Category

-- Weak equivalences of categories,
-- namely fully-faithful and essentially surjective functors

record isWeakEquivalence {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
        (func : Functor C D) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field

    fullfaith : isFullyFaithful   func
    esssurj   : isEssentiallySurj func


record WeakEquivalence (C : Category ℓC ℓC') (D : Category ℓD ℓD')
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  constructor weakEquivalence
  field

    func : Functor C D
    isWeakEquiv : isWeakEquivalence func

open isWeakEquivalence
open WeakEquivalence


isPropIsWeakEquivalence : isProp (isWeakEquivalence F)
isPropIsWeakEquivalence =
  isPropRetract (λ x → fullfaith x , esssurj x) _ (λ _ → refl)
         (isProp× (isPropΠ2 λ _ _ → isPropIsEquiv _)
                  (isPropΠ λ _ → squash₁))


-- Equivalence is always weak equivalence.

isEquiv→isWeakEquiv : isEquivalence F → isWeakEquivalence F
isEquiv→isWeakEquiv isequiv .fullfaith = isEquiv→FullyFaithful isequiv
isEquiv→isWeakEquiv isequiv .esssurj   = isEquiv→Surj isequiv


-- Weak equivalence between univalent categories is equivalence,
-- in other words, they admit explicit inverse functor.

module _
  (isUnivC : isUnivalent C)
  (isUnivD : isUnivalent D)
  where

  open isUnivalent

  isEquivF-ob : {F : Functor C D} → isWeakEquivalence F → isEquivMap (F .F-ob)
  isEquivF-ob {F = F} is-w-equiv = isEmbedding×isSurjection→isEquiv
    (isFullyFaithful→isEmbd-ob isUnivC isUnivD {F = F} (is-w-equiv .fullfaith) ,
     isSurj→isSurj-ob isUnivD {F = F} (is-w-equiv .esssurj))

  isWeakEquiv→isEquiv : {F : Functor C D} → isWeakEquivalence F → isEquivalence F
  isWeakEquiv→isEquiv is-w-equiv =
    isFullyFaithful+isEquivF-ob→isEquiv (is-w-equiv .fullfaith) (isEquivF-ob is-w-equiv)



weRefl : WeakEquivalence C C
func weRefl = Id
fullfaith (isWeakEquiv weRefl) x y = idIsEquiv _
esssurj (isWeakEquiv weRefl) d = ∣ d , idCatIso ∣₁


isWETransport : (p : C ≡ D) → isWeakEquivalence (Transport p)
fullfaith (isWETransport {C = C} p) _ _ = isEquivTransport _
esssurj (isWETransport {C = C} p) d =
  ∣ (subst⁻ Category.ob p d) , pathToIso (substSubst⁻ _ _ _) ∣₁

module _ {Ob Ob' : Type ℓC} (e : Ob ≃ Ob')
                {H[_,_] : Ob → Ob → Type ℓC'}
                {H'[_,_] : Ob' → Ob' → Type ℓC'}
                (e[_,_] : ∀ x y → H[ x , y ] ≃ H'[ e ≃$ x , e ≃$  y ])
                where 

  RelP : PathP (λ i → ua e i → ua e i → Type ℓC')
            H[_,_] H'[_,_]
  RelP i x y = Glue H'[ ua-unglue e i x , ua-unglue e i y ]
      λ { (i = i0) → _ , e[ x , y ]
        ; (i = i1) → _ , idEquiv _ } 


module _ {ℓ'} {Ob' : Type ℓC} {H'[_,_] : Ob' → Ob' → Type ℓC'} where
 
  

  TyRPJ : Type _
  TyRPJ = ∀ (Ob : Type ℓC) (e : Ob ≃ Ob') (H[_,_] : Ob → Ob → Type ℓC')
             → (h[_,_] :  ∀ x y → H[ x , y ] ≃ H'[ e ≃$ x , e ≃$  y ])
             → Type ℓ'  
  
  RelPJ : (T : TyRPJ) → (T Ob' (idEquiv _) H'[_,_] λ _ _ → idEquiv _ )
                      → ∀ {Ob} e H[_,_] h → T Ob e H[_,_] h 
  RelPJ T x {Ob} = EquivJ
    (λ ob e → ∀ H h → T ob e H h)
     λ H h → subst (uncurry (T Ob' (idEquiv Ob')))
      ((isPropRetract
           (λ (o , r) → o , funExt₂ λ x y → sym (ua (r x y)))
           (λ (o , r) → o , λ x y → pathToEquiv λ i → r (~ i) x y )
           (λ (o , r) → cong (o ,_) (funExt₂ λ x y → equivEq
              (funExt λ _ → transportRefl _)))
          (isPropSingl {a = H'[_,_]})) _ _) x



module _
  {C C' : Category ℓC ℓC'}
  (isUnivC : isUnivalent C)
  (isUnivC' : isUnivalent C')
  where

 open CategoryPath
 
 module _ {F} (we : isWeakEquivalence {C = C} {C'} F) where

  open Category 
  module 𝑪₀ = Category C
  module 𝑪₁ = Category C'

  ob≃ : Σ (𝑪₀.ob → 𝑪₁.ob) isEquivMap
  ob≃ = _ , isEquivF-ob isUnivC isUnivC' we

  Hom≃ : ∀ x y → 𝑪₀.Hom[ x , y ] ≃ 𝑪₁.Hom[ ob≃ ≃$ x , ob≃ ≃$  y ]
  Hom≃ _ _ = F-hom F , fullfaith we _ _


  HomPathP : PathP (λ i → ua ob≃ i → ua ob≃ i → Type ℓC')
               𝑪₀.Hom[_,_] 𝑪₁.Hom[_,_]
  HomPathP = RelP _ Hom≃

  WeakEquivlance→CategoryPath : CategoryPath C C'
  p WeakEquivlance→CategoryPath = ua ob≃
  h WeakEquivlance→CategoryPath = HomPathP
  id≡ WeakEquivlance→CategoryPath = RelPJ {H'[_,_] = 𝑪₁.Hom[_,_]}
    (λ Ob e H[_,_] h[_,_] →
      (id* : ∀ {x : Ob} → H[ x , x ]) →
      ({x : Ob} → (h[ x , _ ] ≃$ id*) ≡ C' .id {e ≃$ x} )
      → PathP (λ i → {x : ua e i} → RelP e h[_,_] i x x) id* λ {x} → C' .id {x})
    (λ _ x i → glue (λ {(i = i0) → _ ; (i = i1) → _ }) (x i))
      _ _ Hom≃ (C .id) (F-id F)

  ⋆≡ WeakEquivlance→CategoryPath = RelPJ {H'[_,_] = 𝑪₁.Hom[_,_]}
    (λ Ob e H[_,_] h[_,_] → (⋆* : BinaryRelation.isTrans' H[_,_]) →
      (∀ {x y z : Ob} f g → (h[ x , z ] ≃$ (⋆* f g)) ≡
            C' ._⋆_ (h[ x , _ ] ≃$ f) (h[ y , _ ] ≃$ g) )
      → PathP (λ i → BinaryRelation.isTrans' (RelP e h[_,_] i))
           (⋆*)  (λ {x y z} → C' ._⋆_ {x} {y} {z}))
    (λ _ x i f g → glue 
     (λ {(i = i0) → _ ; (i = i1) → _ }) (x (unglue _ f) (unglue _ g) i  ))
      _ _ Hom≃ (C ._⋆_) (F-seq F)


 CategoryPath→WeakEquivlance : CategoryPath C C' → WeakEquivalence C C'
 func (CategoryPath→WeakEquivlance _) = _
 isWeakEquiv (CategoryPath→WeakEquivlance b) = isWETransport (mk≡ b)

 open Iso

      
 IsoCategoryPath : Iso (WeakEquivalence C C') (CategoryPath C C')
 fun IsoCategoryPath = WeakEquivlance→CategoryPath ∘f isWeakEquiv
 inv IsoCategoryPath = CategoryPath→WeakEquivlance
 rightInv IsoCategoryPath b = CategoryPath≡
     (λ i i₁ →
        Glue _ {φ = ~ i₁ ∨ i₁ ∨ i}
           (λ _ → _ , equivPathP
              {e = ob≃ (isWETransport (mk≡ b))} {f = idEquiv _}
                    (transport-fillerExt⁻ (p b)) i₁))
      λ i i₁ x y →
        Glue (C' .Hom[_,_] (unglue _ x) (unglue _ y)) 
                   λ { (i₁ = i0) → _ , Hom≃ (isWETransport (mk≡ b)) _ _
                      ;(i₁ = i1) → _ , idEquiv _
                      ;(i = i1) → _ , _
            , isProp→PathP (λ i₁ → isPropΠ2 λ x y →
                    isPropIsEquiv (transp (λ i₂ →
         let tr = transp (λ j → p b (i₁ ∨ (i₂ ∧ j))) (~ i₂ ∨ i₁)
         in h b (i₂ ∨ i₁) (tr x) (tr y)) i₁))
          (λ _ _ → snd (Hom≃ (isWETransport (mk≡ b)) _ _))
          (λ _ _ → snd (idEquiv _)) i₁ x y }
    
 leftInv IsoCategoryPath we = cong₂ weakEquivalence
   (Functor≡ (transportRefl ∘f (F-ob (func we)))
              λ {c} {c'} f → (λ j → transport
      (λ i → HomPathP (isWeakEquiv we) i
         (transport-filler-ua' (ob≃ (isWeakEquiv we)) c  j i)
         (transport-filler-ua' (ob≃ (isWeakEquiv we)) c' j i))
      f) ▷ transportRefl _ )
   (isProp→PathP (λ _ → isPropIsWeakEquivalence) _ _ )
  

 WeakEquivalence≃Path : WeakEquivalence C C' ≃ (C ≡ C')
 WeakEquivalence≃Path =
   isoToEquiv (compIso IsoCategoryPath CategoryPathIso)
