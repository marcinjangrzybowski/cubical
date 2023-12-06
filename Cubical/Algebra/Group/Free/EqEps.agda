{-# OPTIONS --safe #-}

module Cubical.Algebra.Group.Free.EqEps where

-- open import Cubical.HITs.FreeGroup.Base renaming (assoc to ·assoc)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv.Properties
-- open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Relation.Nullary

open import Cubical.Functions.Involution
open import Cubical.Functions.FunExtEquiv

open import Cubical.Functions.Embedding
import Cubical.Functions.Logic as L

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive as OR
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe
import Cubical.Data.Int as Int
import Cubical.Data.Fin as Fin

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/₂_ ; [_] to [_]/)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
-- open import Cubical.HITs.TypeQuotients as TQ renaming ([_] to [_]/ₜ ; eq/ to eq/ₜ )


open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels
open import Cubical.Relation.Binary.Base

open import Cubical.Algebra.Group.Free.Base

open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Groups
open import Cubical.Categories.NaturalTransformation


private
  variable
    ℓ : Level

module _ (A : Type ℓ) where

 open NormalForm A

 infixl 10 _⇊1g

 data _⇊1g : [𝟚× A ] → Type ℓ where
  [] : [] ⇊1g
  cj : ∀ x → ∀ xs → xs ⇊1g →   (x ∷ (xs ∷ʳ not₁ x) ) ⇊1g
  _·_ : ∀ xs ys → xs ⇊1g → ys ⇊1g →  (xs ++ ys) ⇊1g

 _r·_ : ∀ {xs ys} → xs ⇊1g → ys ⇊1g → (xs ++ ys) ⇊1g
 _r·_ = _·_ _ _ 

 ¬⇊1g[len≡1] : ∀ xs → length xs ≡ 1 → ¬ xs ⇊1g
 ¬⇊1g[len≡1] .[] x [] = znots x
 ¬⇊1g[len≡1] .(_ ∷ (_ ∷ʳ _)) x (cj _ xs _) =
   snotz ((+-comm 1 _ ∙ sym (length++ xs _)) ∙ injSuc x) 
 ¬⇊1g[len≡1] .(xs ++ ys) x ((xs · ys) x₁ x₂) =
  ⊎.rec (flip (¬⇊1g[len≡1] ys) x₂ ∘ snd)
        ((flip (¬⇊1g[len≡1] xs) x₁ ∘ fst))
    (m+n≡1→m≡0×n≡1⊎m≡1n≡0 {length xs} {length ys} (sym (length++ xs ys) ∙ x))

 ⇊1gWillReduceView : ∀ b a ys → ys ⇊1g → WillReduce b a ys →
      Σ ((Σ _ _⇊1g) × (Σ _ _⇊1g))
        λ ((rl , _) , (rr , _)) →
           rl ++ [ b , a ] ++ rr ≡ tail ys
 ⇊1gWillReduceView b a .(x ∷ (xs ∷ʳ _)) (cj x xs x₃) x₁ =
   ((_ , x₃) , (_ , [])) , cong (xs ∷ʳ_) x₁
 ⇊1gWillReduceView b a .([] ++ ys) (([] · ys) x x₂) x₁ =
   ⇊1gWillReduceView b a ys x₂ x₁
 ⇊1gWillReduceView b a .((_ ∷ _) ++ ys) ((xs@(_ ∷ _) · ys) x x₂) x₁ =
   let (((rl , rlR) , (rr , rrR)) , p) = ⇊1gWillReduceView b a xs x x₁ 
   in ((_ , rlR) , (_ , (_ · _) rrR x₂)) ,
     sym (++-assoc rl _ _) ∙ cong (_++ ys) p

 ⇊1g⇒HasRedex : ∀ xs → 0 < length xs → xs ⇊1g → HasRedex xs 
 ⇊1g⇒HasRedex .(x₁ ∷ ([] ∷ʳ not₁ x₁)) x (cj x₁ [] x₂) =
   inl (symIsRedex _ _ refl)
 ⇊1g⇒HasRedex .(x₁ ∷ ((x₃ ∷ xs) ∷ʳ not₁ x₁)) x (cj x₁ (x₃ ∷ xs) x₂) =
   inr (HasRedex∷ʳ (⇊1g⇒HasRedex _ _ x₂))
 ⇊1g⇒HasRedex .([] ++ ys) x (([] · ys) x₁ x₂) = ⇊1g⇒HasRedex _ x x₂
 ⇊1g⇒HasRedex .((x₃ ∷ xs) ++ ys) x (((x₃ ∷ xs) · ys) x₁ x₂) =
  HasRedex++ _ _ (⇊1g⇒HasRedex _ _ x₁)

 isNormalised⇊1g : ∀ xs → IsNormalised xs →  xs ⇊1g → xs ≡ []
 isNormalised⇊1g [] _ _ = refl
 isNormalised⇊1g (x₂ ∷ xs) x x₁ = ⊥.rec (x (⇊1g⇒HasRedex _ _ x₁))


 ⇊1g-invLi : ∀ {xs} → xs ⇊1g → (invLi xs) ⇊1g
 ⇊1g-invLi [] = []
 ⇊1g-invLi (cj x xs x₁) =
   subst _⇊1g (cong (_∷ invLi (x ∷ xs)) (sym (not₁not₁ _) )
    ∙ cong (_∷ʳ _) (sym (invLi++ xs [ not₁ x ]))) (cj x _ (⇊1g-invLi x₁))
 ⇊1g-invLi ((xs · ys) x x₁) =
   subst _⇊1g (sym (invLi++ xs ys)) (⇊1g-invLi x₁ r· ⇊1g-invLi x)

 ⇊1gRot : ∀ xs → xs ⇊1g → _⇊1g (rot xs)
 ⇊1gRot [] x = []
 ⇊1gRot xs@(x'@(b , a) ∷ xs') x =
  let (((rl , rlR) , (rr , rrR)) , p) = ⇊1gWillReduceView (not b) a xs x refl
  in subst _⇊1g ((λ i → (++-assoc rl ([ not b , a ] ++ rr)
               [ not₁not₁ x' i ]) (~ i)) ∙ cong (_∷ʳ x') p)
       (rlR r· cj (not b , a) _ rrR)

 ⇊1g++comm : ∀ xs ys → (xs ++ ys) ⇊1g → (ys ++ xs) ⇊1g
 ⇊1g++comm [] ys = subst _⇊1g (sym (++-unit-r ys)) 
 ⇊1g++comm (x₁ ∷ xs) ys x = 
   subst _⇊1g (++-assoc ys _ _) 
      (⇊1g++comm xs _ (subst _⇊1g (++-assoc xs _ _) (⇊1gRot _ x)))

 pop⇊1gHead : ∀ {xs} → HeadIsRedex xs → xs ⇊1g → _⇊1g (tail (tail xs)) 
 pop⇊1gHead x (cj x₁ [] r) = []
 pop⇊1gHead x (cj x₁ (x₂ ∷ xs) r) =
   subst (_⇊1g ∘ (xs ∷ʳ_)) (symIsRedex _ _ x) (⇊1gRot _ r)
 pop⇊1gHead x (([] · ys) r r₁) = pop⇊1gHead x r₁
 pop⇊1gHead x (((x₁ ∷ []) · ys) r r₁) = ⊥.rec (¬⇊1g[len≡1] [ x₁ ] refl r)
 pop⇊1gHead x (((_ ∷ _ ∷ _) · ys) r r₁) = pop⇊1gHead x r r· r₁

 ⇊1gCJ : ∀ xs ys → _⇊1g (ys ++ xs ++ invLi ys) → xs ⇊1g
 ⇊1gCJ xs [] = subst _⇊1g (++-unit-r xs) 
 ⇊1gCJ xs (x₁ ∷ ys) x =
  ⇊1gCJ xs ys (pop⇊1gHead refl 
   (⇊1g++comm (x₁ ∷ ys ++ xs ++ invLi ys) [ not₁ x₁ ]
    (subst _⇊1g (cong (x₁ ∷_) (cong (ys ++_) (sym (++-assoc xs _ _))
           ∙ sym (++-assoc ys _ _))) x)))
 
 nf-uR : ∀ xs ys
    → IsNormalised (invLi xs)
    → IsNormalised ys
    → (invLi xs ++ ys) ⇊1g → xs ≡ ys
 nf-uR xs [] nXs x₁ r = sym (invol-invLi xs) ∙ cong invLi 
      (isNormalised⇊1g _ nXs (subst _⇊1g (++-unit-r _) r))
 nf-uR [] (x₃ ∷ ys) x x₁ x₂ = ⊥.rec (x₁ (⇊1g⇒HasRedex _ _ x₂))
 nf-uR xs@(_ ∷ _) (x₃ ∷ ys) nXs nYs r =
   let ww = subst _⇊1g (cong (x₃ ∷_) (sym (++-assoc ys _ _)))
              (⇊1g++comm (invLi xs) _ r)
       www = subst (0 <_)
           (sym (+-suc _ _)
             ∙ sym (length++ (invLi xs) _)) _
   in (⊎.rec (⊎.rec (λ p → cong₂ _∷_
          (sym (not₁not₁ _) ∙ sym (symIsRedex _ _ p))
          (nf-uR (tail xs) _ (fst IsNormalisedInvLi
             (invEq (IsNormalisedInvLi {xs}) nXs ∘ inr) ) (nYs ∘ inr)
               (⇊1g++comm _ (invLi (tail xs))
                  (pop⇊1gHead p (⇊1g++comm _ [ _ ] ww)))))
        (⊥.rec ∘ IsNormalised[x] x₃) ∘S
       subst HasRedex (cong ((_++ _) ∘ take 1)
         (rev-rev (Li.map not₁ xs))))
        (⊥.rec ∘ ⊎.rec nXs nYs)
    ∘S HasRedexSplit++ {invLi xs}
    ∘S ⇊1g⇒HasRedex _ www) r
 
 infixr 5 _·_⁻¹≡ε

 record _·_⁻¹≡ε (xs ys : _) : Type ℓ where
  constructor [_]≡ε
  field
   ≡ε :  (xs ++ invLi ys) ⇊1g

 open _·_⁻¹≡ε public

 open BinaryRelation
 open isEquivRel

 ·⁻¹≡ε-refl : isRefl _·_⁻¹≡ε
 ·⁻¹≡ε-refl [] = [ [] ]≡ε
 ≡ε (·⁻¹≡ε-refl (x ∷ xs)) =
   subst _⇊1g (sym (++-assoc [ x ] xs (invLi (x ∷ xs)) ∙
         cong (x ∷_) (sym (++-assoc xs (invLi xs) _))))
     (cj x _ (≡ε (·⁻¹≡ε-refl xs)))

 ·⁻¹≡ε-sym : isSym _·_⁻¹≡ε
 ≡ε (·⁻¹≡ε-sym a b [ p ]≡ε) = 
    subst _⇊1g (invLi++ a (invLi b) ∙
       cong (_++ invLi a) (invol-invLi b)) (⇊1g-invLi p)
 
 ·⁻¹≡ε-trans : isTrans _·_⁻¹≡ε
 ≡ε (·⁻¹≡ε-trans xs ys zs [ p ]≡ε [ q ]≡ε) =
    ⇊1g++comm (invLi zs) xs
      (⇊1gCJ (invLi zs ++ xs) ys
        (subst _⇊1g (++-assoc ys _ _ ∙
         cong (ys ++_) (sym (++-assoc (invLi zs) _ _))) (q r· p)))
         
 ·⁻¹≡ε-isEquivRel : isEquivRel _·_⁻¹≡ε
 reflexive ·⁻¹≡ε-isEquivRel = ·⁻¹≡ε-refl
 symmetric ·⁻¹≡ε-isEquivRel = ·⁻¹≡ε-sym
 transitive ·⁻¹≡ε-isEquivRel = ·⁻¹≡ε-trans

 open Iso

 List/↘↙ : Type ℓ
 List/↘↙ = _ /₂ _·_⁻¹≡ε

 _↘↙_ = _·_⁻¹≡ε

 _↘↙++↘↙_ : ∀ {xsL xsR ysL ysR} →
    xsL ↘↙ ysL → xsR ↘↙ ysR →
      (xsL ++ xsR) ↘↙ (ysL ++ ysR)
 ≡ε (_↘↙++↘↙_ {xsL} {xsR} {ysL} {ysR} [ p ]≡ε [ q ]≡ε) =
   subst _⇊1g (sym (++-assoc xsL _ _))
     (⇊1g++comm _ xsL
       (subst _⇊1g (++-assoc xsR _ _ ∙∙
           (λ i → xsR ++ ++-assoc (invLi ysR) (invLi ysL) xsL (~ i)) ∙∙
           ( λ i → ++-assoc xsR (invLi++ ysL ysR (~ i)) xsL (~ i)))
         (q r· ⇊1g++comm xsL _ p)))
     
 List/↘↙· : List/↘↙ → List/↘↙ → List/↘↙
 List/↘↙· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
    (λ _ _ c → eq/ _ _ ∘ _↘↙++↘↙ (·⁻¹≡ε-refl c))
    (λ a _ _ → eq/ _ _ ∘ (·⁻¹≡ε-refl a) ↘↙++↘↙_ )

 List/↘↙GroupStr : GroupStr List/↘↙
 GroupStr.1g List/↘↙GroupStr = [ [] ]/
 GroupStr._·_ List/↘↙GroupStr = List/↘↙·
 GroupStr.inv List/↘↙GroupStr =
  SQ.rec squash/ ([_]/ ∘ invLi)
     λ xs ys → sym ∘S eq/ _ _ ∘S [_]≡ε
     ∘S subst (_⇊1g ∘ (invLi ys ++_)) (sym (invol-invLi xs))
     ∘S ⇊1g++comm xs (invLi ys) ∘S ≡ε
        
 GroupStr.isGroup List/↘↙GroupStr = makeIsGroup squash/
  (SQ.elimProp3 (λ _ _ _ → squash/ _ _)
      λ xs _ _ → cong SQ.[_] (sym (++-assoc xs _ _)))
  (SQ.elimProp (λ _ → squash/ _ _) λ xs → cong SQ.[_] (++-unit-r xs))
  (SQ.elimProp (λ _ → squash/ _ _) λ _ → refl)
  (SQ.elimProp (λ _ → squash/ _ _) λ xs → sym (eq/ _ _
     ([ ⇊1g-invLi (≡ε (·⁻¹≡ε-refl xs)) ]≡ε)))
  (SQ.elimProp (λ _ → squash/ _ _) λ xs → eq/ _ _ [
     subst _⇊1g (cong (invLi xs ++_) (invol-invLi xs) ∙
       sym (++-unit-r _)) (≡ε (·⁻¹≡ε-refl (invLi xs))) ]≡ε)

 List/↘↙group : Group ℓ
 List/↘↙group = _ , List/↘↙GroupStr 

 ≡→red : ∀ a b → Iso ([ a ]/ ≡ [ b ]/) ∥ a · b ⁻¹≡ε ∥₁
 ≡→red = isEquivRel→TruncIso ·⁻¹≡ε-isEquivRel


 module _ (_≟_ : Discrete A) where

  isSetA = Discrete→isSet _≟_

  isSet[𝟚×] = isOfHLevelList 0 (isSet× isSetBool isSetA)

  IsRedex? : ∀ x x' → Dec (IsRedex x x')
  IsRedex? _ _ = discreteΣ 𝟚._≟_ (λ _ → _≟_) _ _ 

  HeadIsRedex? : ∀ xs → Dec (HeadIsRedex xs)
  HeadIsRedex? [] = no lower
  HeadIsRedex? (x ∷ []) = no lower
  HeadIsRedex? (x ∷ x' ∷ _) = IsRedex? x x'

  preη· : ∀ x xs → Dec (HeadIsRedex (x ∷ xs)) → [𝟚× A ]
  preη· _ xs (yes _) = tail xs
  preη· x xs (no _) = x ∷ xs

  preη·-N : ∀ {x xs} hir? → IsNormalised xs → IsNormalised (preη· x xs hir?) 
  preη·-N (yes _) = IsNormalisedTail _
  preη·-N (no ¬p) = ⊎.rec ¬p

  sec-preη· : ∀ x xs p q → IsNormalised xs → preη· (not₁ x) (preη· x xs p) q ≡ xs
  sec-preη· x (x₂ ∷ xs) (yes p) (no ¬p) x₁ =
    cong (_∷ xs) (sym (symIsRedex _ _ p))
  sec-preη· x (x₂ ∷ x₃ ∷ xs) (yes p) (yes p₁) x₁ =
    ⊥.rec (x₁ (inl (symIsRedex _ _ p ∙ p₁)))
  sec-preη· x xs (no ¬p) (no ¬p₁) x₁ = ⊥.rec (¬p₁ refl)
  sec-preη· x xs (no ¬p) (yes p) _ = refl

  η· : (Bool × A) → [𝟚× A ] → [𝟚× A ]
  η· x xs = preη· _ _ (HeadIsRedex? (x ∷ xs))

  η·∷ : ∀ x xs → (HeadIsRedex (x ∷ xs) → ⊥) → η· x xs ≡ x ∷ xs
  η·∷ x xs x₁ = cong (λ u → preη· x xs u)
   (≡no (HeadIsRedex? (x ∷ xs)) x₁)
  
  nη· : (Bool × A) → (Σ _ IsNormalised) → (Σ _ IsNormalised)
  fst (nη· x x₁) = η· x (fst x₁)
  snd (nη· x x₁) = preη·-N (HeadIsRedex? _) (snd x₁)


  η·iso : (Bool × A) → Iso _ _
  Iso.fun (η·iso x) = nη· x
  Iso.inv (η·iso x) = nη· (not₁ x)
  Iso.rightInv (η·iso x) b =
    Σ≡Prop (λ _ → isPropIsNormalised)
     (funExt⁻ (cong η· (sym (not₁not₁ x)) ) (η· (not₁ x) (fst b)) 
      ∙ sec-preη· (not₁ x) _ (HeadIsRedex? _) (HeadIsRedex? _) (snd b))
  Iso.leftInv (η·iso x) a =
    Σ≡Prop (λ _ → isPropIsNormalised)
     (sec-preη· x _ (HeadIsRedex? _) (HeadIsRedex? _) (snd a))

  η·≃ = isoToEquiv ∘ η·iso
  
  normalise : ∀ xs → Σ _ λ xs' →
    (xs' · xs ⁻¹≡ε) × IsNormalised xs'
  normalise = Li.elim ([] , [ [] ]≡ε , lower )
   λ {x} {xs} (xs' , [ u ]≡ε , v) →
    let zz : ∀ xs' uu u → (preη· x xs' uu ++ invLi (x ∷ xs)) ⇊1g
        zz =
          λ { xs' (no ¬p) → subst (_⇊1g ∘S (x ∷_)) (++-assoc xs' _ _) ∘ cj x _
             ; [] (yes ())
             ; (_ ∷ xs') (yes p) →
                  subst _⇊1g (λ i → ++-assoc xs' (invLi xs)
                       [ symIsRedex _ _ p i ] i) ∘ ⇊1gRot _ }
        h = HeadIsRedex? _
    in  _ , [ zz xs' h u ]≡ε , preη·-N h v

  IsoNF : Iso (Σ _ IsNormalised) List/↘↙
  fun IsoNF = [_]/ ∘ fst 
  Iso.inv IsoNF =
   SQ.rec (isSetΣ isSet[𝟚×] (λ _ → isProp→isSet isPropIsNormalised))
   ((λ (_ , _ , u) → _ , u) ∘ normalise)
   λ _ _ →
     let (a' , t  , u ) = normalise _ ; (b' , t' , u') = normalise _
     in  Σ≡Prop (λ _ → isPropIsNormalised) ∘S sym
      ∘S nf-uR _ _ (fst (IsNormalisedInvLi {b'}) u') u
      ∘S ⇊1g++comm a' (invLi b') ∘S ≡ε
      ∘S flip (·⁻¹≡ε-trans _ _ _) (·⁻¹≡ε-sym _ _ t')
      ∘S ·⁻¹≡ε-trans _ _ _ t
  rightInv IsoNF = SQ.elimProp (λ _ → squash/ _ _)
    (eq/ _ _ ∘ fst ∘ snd ∘ normalise) 
  leftInv IsoNF = Σ≡Prop (λ _ → isPropIsNormalised) ∘ uncurry
   (Li.elim (λ _ → refl) λ f v →
   let lem : ∀ uu → preη· _ _ uu ≡ _ ∷ _
       lem =
        λ { (yes p) → ⊥.rec (v (inl (subst (WillReduce _ _) (f (v ∘ inr)) p)))
          ; (no ¬p) → refl }
   in lem (HeadIsRedex? _) ∙ cong (_ ∷_) (f (v ∘ inr)))
