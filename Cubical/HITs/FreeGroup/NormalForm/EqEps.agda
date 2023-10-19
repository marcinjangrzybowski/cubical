{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.NormalForm.EqEps where

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

open import Cubical.HITs.FreeGroup.NormalForm.Base

open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Groups
open import Cubical.Categories.NaturalTransformation

open import Cubical.HITs.Bouquet renaming (elimProp to elimBouquetProp)
  hiding (winding)
private
  variable
    ℓ : Level

module _ (A : Type ℓ) where

 open NormalForm A

 data Red : [𝟚× A ] → Type ℓ where
  red[] : Red []
  cj : ∀ x → ∀ xs → Red xs →  Red (x ∷ (xs ∷ʳ not₁ x) )
  _·_ : ∀ xs ys → Red xs → Red ys → Red (xs ++ ys)

 _r·_ : ∀ {xs ys} → Red xs → Red ys → Red (xs ++ ys)
 _r·_ = _·_ _ _ 

 ¬Red[len≡1] : ∀ xs → length xs ≡ 1 → ¬ Red xs
 ¬Red[len≡1] .[] x red[] = znots x
 ¬Red[len≡1] .(_ ∷ (_ ∷ʳ _)) x (cj _ xs _) =
   snotz ((+-comm 1 _ ∙ sym (length++ xs _)) ∙ injSuc x) 
 ¬Red[len≡1] .(xs ++ ys) x ((xs · ys) x₁ x₂) =
  ⊎.rec (flip (¬Red[len≡1] ys) x₂ ∘ snd)
        ((flip (¬Red[len≡1] xs) x₁ ∘ fst))
    (m+n≡1→m≡0×n≡1⊎m≡1n≡0 {length xs} {length ys} (sym (length++ xs ys) ∙ x))

 RedWillReduceView : ∀ b a ys → Red ys → WillReduce b a ys →
      Σ ((Σ _ Red) × (Σ _ Red))
        λ ((rl , _) , (rr , _)) →
           rl ++ [ b , a ] ++ rr ≡ tail ys
 RedWillReduceView b a .(x ∷ (xs ∷ʳ _)) (cj x xs x₃) x₁ =
   ((_ , x₃) , (_ , red[])) , cong (xs ∷ʳ_) x₁
 RedWillReduceView b a .([] ++ ys) (([] · ys) x x₂) x₁ =
   RedWillReduceView b a ys x₂ x₁
 RedWillReduceView b a .((_ ∷ _) ++ ys) ((xs@(_ ∷ _) · ys) x x₂) x₁ =
   let (((rl , rlR) , (rr , rrR)) , p) = RedWillReduceView b a xs x x₁ 
   in ((_ , rlR) , (_ , (_ · _) rrR x₂)) ,
     sym (++-assoc rl _ _) ∙ cong (_++ ys) p

 Red⇒HasRedex : ∀ xs → 0 < length xs → Red xs → HasRedex xs 
 Red⇒HasRedex .(x₁ ∷ ([] ∷ʳ not₁ x₁)) x (cj x₁ [] x₂) =
   inl (symIsRedex _ _ refl)
 Red⇒HasRedex .(x₁ ∷ ((x₃ ∷ xs) ∷ʳ not₁ x₁)) x (cj x₁ (x₃ ∷ xs) x₂) =
   inr (HasRedex∷ʳ (Red⇒HasRedex _ _ x₂))
 Red⇒HasRedex .([] ++ ys) x (([] · ys) x₁ x₂) = Red⇒HasRedex _ x x₂
 Red⇒HasRedex .((x₃ ∷ xs) ++ ys) x (((x₃ ∷ xs) · ys) x₁ x₂) =
  HasRedex++ _ _ (Red⇒HasRedex _ _ x₁)

 isNormalisedRed : ∀ xs → ⟨ IsNormalised xs ⟩ →  Red xs → xs ≡ []
 isNormalisedRed [] _ _ = refl
 isNormalisedRed (x₂ ∷ xs) x x₁ = ⊥.rec (x (Red⇒HasRedex _ _ x₁))


 Red-invLi : ∀ {xs} → Red xs → Red (invLi xs)
 Red-invLi red[] = red[]
 Red-invLi (cj x xs x₁) =
   subst Red (cong (_∷ invLi (x ∷ xs)) (sym (not₁not₁ _) )
    ∙ cong (_∷ʳ _) (sym (invLi++ xs [ not₁ x ]))) (cj x _ (Red-invLi x₁))
 Red-invLi ((xs · ys) x x₁) =
   subst Red (sym (invLi++ xs ys)) (Red-invLi x₁ r· Red-invLi x)

 redRot : ∀ xs → Red xs → Red (rot xs)
 redRot [] x = red[]
 redRot xs@(x'@(b , a) ∷ xs') x =
  let (((rl , rlR) , (rr , rrR)) , p) = RedWillReduceView (not b) a xs x refl
  in subst Red ((λ i → (++-assoc rl ([ not b , a ] ++ rr)
               [ not₁not₁ x' i ]) (~ i)) ∙ cong (_∷ʳ x') p)
       (rlR r· cj (not b , a) _ rrR)

 red++comm : ∀ xs ys →  Red (xs ++ ys) → Red (ys ++ xs)
 red++comm [] ys = subst Red (sym (++-unit-r ys)) 
 red++comm (x₁ ∷ xs) ys x = 
   subst Red (++-assoc ys _ _) 
      (red++comm xs _ (subst Red (++-assoc xs _ _) (redRot _ x)))

 popRedHead : ∀ {xs} → HeadIsRedex xs → Red xs → Red (tail (tail xs)) 
 popRedHead x (cj x₁ [] r) = red[]
 popRedHead x (cj x₁ (x₂ ∷ xs) r) =
   subst (Red ∘ (xs ∷ʳ_)) (symIsRedex _ _ x) (redRot _ r)
 popRedHead x (([] · ys) r r₁) = popRedHead x r₁
 popRedHead x (((x₁ ∷ []) · ys) r r₁) = ⊥.rec (¬Red[len≡1] [ x₁ ] refl r)
 popRedHead x (((_ ∷ _ ∷ _) · ys) r r₁) = popRedHead x r r· r₁

 RedCJ : ∀ xs ys → Red (ys ++ xs ++ invLi ys) → Red xs
 RedCJ xs [] = subst Red (++-unit-r xs) 
 RedCJ xs (x₁ ∷ ys) x =
  RedCJ xs ys (popRedHead refl 
   (red++comm (x₁ ∷ ys ++ xs ++ invLi ys) [ not₁ x₁ ]
    (subst Red (cong (x₁ ∷_) (cong (ys ++_) (sym (++-assoc xs _ _))
           ∙ sym (++-assoc ys _ _))) x)))
 
 nf-uR : ∀ xs ys → ⟨ IsNormalised (invLi xs) ⟩
    → ⟨ IsNormalised ys ⟩ → Red (invLi xs ++ ys) → xs ≡ ys
 nf-uR xs [] nXs x₁ r = sym (invol-invLi xs) ∙ cong invLi 
      (isNormalisedRed _ nXs (subst Red (++-unit-r _) r))
 nf-uR [] (x₃ ∷ ys) x x₁ x₂ = ⊥.rec (x₁ (Red⇒HasRedex _ _ x₂))
 nf-uR xs@(_ ∷ _) (x₃ ∷ ys) nXs nYs r =
   let ww = subst Red (cong (x₃ ∷_) (sym (++-assoc ys _ _)))
              (red++comm (invLi xs) _ r)
       www = subst (0 <_)
           (sym (+-suc _ _)
             ∙ sym (length++ (invLi xs) _)) _
   in (⊎.rec (⊎.rec (λ p → cong₂ _∷_
          (sym (not₁not₁ _) ∙ sym (symIsRedex _ _ p))
          (nf-uR (tail xs) _ (fst IsNormalisedInvLi
             (snd (IsNormalisedInvLi {xs}) nXs ∘ inr) ) (nYs ∘ inr)
               (red++comm _ (invLi (tail xs))
                  (popRedHead p (red++comm _ [ _ ] ww)))))
        (⊥.rec ∘ IsNormalised[x] x₃) ∘'
       subst HasRedex (cong ((_++ _) ∘ take 1)
         (rev-rev (Li.map not₁ xs))))
        (⊥.rec ∘ ⊎.rec nXs nYs)
    ∘' HasRedexSplit++ {invLi xs}
    ∘' Red⇒HasRedex _ www) r
 
 infixr 5 _·_⁻¹≡ε

 record _·_⁻¹≡ε (xs ys : _) : Type ℓ where
  constructor [_]≡ε
  field
   ≡ε : Red (xs ++ invLi ys)

 open _·_⁻¹≡ε public

 open BinaryRelation
 open isEquivRel

 ·⁻¹≡ε-refl : isRefl _·_⁻¹≡ε
 ·⁻¹≡ε-refl [] = [ red[] ]≡ε
 ≡ε (·⁻¹≡ε-refl (x ∷ xs)) =
   subst Red (sym (++-assoc [ x ] xs (invLi (x ∷ xs)) ∙
         cong (x ∷_) (sym (++-assoc xs (invLi xs) _))))
     (cj x _ (≡ε (·⁻¹≡ε-refl xs)))

 ·⁻¹≡ε-sym : isSym _·_⁻¹≡ε
 ≡ε (·⁻¹≡ε-sym a b [ p ]≡ε) = 
    subst Red (invLi++ a (invLi b) ∙
       cong (_++ invLi a) (invol-invLi b)) (Red-invLi p)
 
 ·⁻¹≡ε-trans : isTrans _·_⁻¹≡ε
 ≡ε (·⁻¹≡ε-trans xs ys zs [ p ]≡ε [ q ]≡ε) =
    red++comm (invLi zs) xs
      (RedCJ (invLi zs ++ xs) ys
        (subst Red (++-assoc ys _ _ ∙
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
   subst Red (sym (++-assoc xsL _ _))
     (red++comm _ xsL
       (subst Red (++-assoc xsR _ _ ∙∙
           (λ i → xsR ++ ++-assoc (invLi ysR) (invLi ysL) xsL (~ i)) ∙∙
           ( λ i → ++-assoc xsR (invLi++ ysL ysR (~ i)) xsL (~ i)))
         (q r· red++comm xsL _ p)))
     
 List/↘↙· : List/↘↙ → List/↘↙ → List/↘↙
 List/↘↙· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
    (λ _ _ c → eq/ _ _ ∘ _↘↙++↘↙ (·⁻¹≡ε-refl c))
    (λ a _ _ → eq/ _ _ ∘ (·⁻¹≡ε-refl a) ↘↙++↘↙_ )

 List/↘↙GroupStr : GroupStr List/↘↙
 GroupStr.1g List/↘↙GroupStr = [ [] ]/
 GroupStr._·_ List/↘↙GroupStr = List/↘↙·
 GroupStr.inv List/↘↙GroupStr =
  SQ.rec squash/ ([_]/ ∘ invLi)
     λ xs ys → sym ∘' eq/ _ _ ∘' [_]≡ε
     ∘' subst (Red ∘ (invLi ys ++_)) (sym (invol-invLi xs))
     ∘' red++comm xs (invLi ys) ∘' ≡ε
        
 GroupStr.isGroup List/↘↙GroupStr = makeIsGroup squash/
  (SQ.elimProp3 (λ _ _ _ → squash/ _ _)
      λ xs _ _ → cong SQ.[_] (sym (++-assoc xs _ _)))
  (SQ.elimProp (λ _ → squash/ _ _) λ xs → cong SQ.[_] (++-unit-r xs))
  (SQ.elimProp (λ _ → squash/ _ _) λ _ → refl)
  (SQ.elimProp (λ _ → squash/ _ _) λ xs → sym (eq/ _ _
     ([ Red-invLi (≡ε (·⁻¹≡ε-refl xs)) ]≡ε)))
  (SQ.elimProp (λ _ → squash/ _ _) λ xs → eq/ _ _ [
     subst Red (cong (invLi xs ++_) (invol-invLi xs) ∙
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

  preη·-N : ∀ {x xs} hir? → ⟨ IsNormalised xs ⟩ → ⟨ IsNormalised (preη· x xs hir?) ⟩ 
  preη·-N (yes _) = IsNormalisedTail _
  preη·-N (no ¬p) = ⊎.rec ¬p

  sec-preη· : ∀ x xs p q → ⟨ IsNormalised xs ⟩ → preη· (not₁ x) (preη· x xs p) q ≡ xs
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
  
  nη· : (Bool × A) → (Σ _ (fst ∘ IsNormalised)) → (Σ _ (fst ∘ IsNormalised))
  fst (nη· x x₁) = η· x (fst x₁)
  snd (nη· x x₁) = preη·-N (HeadIsRedex? _) (snd x₁)


  η·iso : (Bool × A) → Iso _ _
  Iso.fun (η·iso x) = nη· x
  Iso.inv (η·iso x) = nη· (not₁ x)
  Iso.rightInv (η·iso x) b =
    Σ≡Prop (snd ∘ IsNormalised)
     (funExt⁻ (cong η· (sym (not₁not₁ x)) ) (η· (not₁ x) (fst b)) 
      ∙ sec-preη· (not₁ x) _ (HeadIsRedex? _) (HeadIsRedex? _) (snd b))
  Iso.leftInv (η·iso x) a =
    Σ≡Prop (snd ∘ IsNormalised)
     (sec-preη· x _ (HeadIsRedex? _) (HeadIsRedex? _) (snd a))

  η·≃ = isoToEquiv ∘ η·iso

  CodeBouquet : Bouquet A → Type ℓ
  CodeBouquet base = Σ _ (fst ∘ IsNormalised)
  CodeBouquet (loop a i) = ua (η·≃ (true , a)) i

  co→ : ∀ x → base ≡ x → CodeBouquet x
  co→ x p = subst CodeBouquet p ([] , lower)

  co←base-step : Bool × A
                          → Path (Bouquet A) base base
                         
  co←base-step (b , a) = ((if b then (idfun _) else sym) (loop a)) 

  co←base : [𝟚× A ] → Path (Bouquet A) base base
  co←base = Li.rec refl (flip _∙_ ∘ co←base-step)

  co←Sq' : (a : A) → (x : [𝟚× A ]) (y : ((λ r → fst r) ∘ IsNormalised) x) →
      ∀ u → PathP (λ i → base ≡ loop a i)
      (λ i → Li.rec (λ _ → base) (flip _∙_ ∘ co←base-step) x i)
      (λ i → Li.rec (λ _ → base) (flip _∙_ ∘ co←base-step) (preη· (true , a) x u )
       i)
  co←Sq' a ((false , snd₁) ∷ xs) y (yes p) = 
    cong (λ x' → co←base ((false , x') ∷ xs)) (cong snd (sym p))
      ◁ symP (compPath-filler (co←base xs) (sym (loop a)))
  co←Sq' a xs y (no ¬p) = compPath-filler _ _
  co←Sq' a ((true , snd₁) ∷ xs) y (yes p) = ⊥.rec (true≢false (cong fst p))
  
  co←Sq : (a : A) → SquareP (λ i j →  ua (η·≃ (true , a)) i → Bouquet A)
                       (λ j x → co←base (fst x) j)
                       (λ j x → co←base (fst x) j)
                       (λ i _ → base)
                       (λ i _ → loop a i)
  co←Sq a = congP (λ _ → funExt) (ua→ (uncurry
     (λ xs y → co←Sq' a xs y (HeadIsRedex? ((true , a) ∷ xs)))))

  co← : ∀ x → CodeBouquet x → base ≡ x 
  co← base = co←base ∘ fst
  co← (loop a i) x j = co←Sq a i j x

  coSec : ∀ x → section (co← x) (co→ x)
  coSec _ = J (λ x b → co← x (co→ x b) ≡ b) refl

  coRet : (x : [𝟚× A ]) (y : ((λ r → fst r) ∘ IsNormalised) x) →
            fst (subst CodeBouquet (co← base (x , y)) ([] , lower))
                  ≡ x
  coRet [] y = refl
  coRet (x@(b , a) ∷ xs) y =
    cong fst (substComposite CodeBouquet (co← base (xs , y ∘ inr))
      (co←base-step x) _)
      ∙∙
      cong (fst ∘ subst CodeBouquet (co←base-step x))
         (Σ≡Prop (snd ∘ IsNormalised) (coRet xs (y ∘ inr))) ∙∙
      lem b xs (y ∘ inr) ∙ η·∷ x xs (y ∘ inl)

   where
   lem : ∀ b xs y → fst
      (subst CodeBouquet (co←base-step (b , a)) (xs , y))
      ≡ η· (b , a) xs
   lem false xs y = cong fst (~uaβ (η·≃ (true , a)) (xs , y ))
   lem true xs y = cong fst (uaβ (η·≃ (true , a)) (xs , y ))
   
  codeDecode : Iso (Path (Bouquet A) base base)
                   (Σ _ (fst ∘ IsNormalised))
  fun codeDecode p = subst CodeBouquet p ([] , lower)
  inv codeDecode = co← base
  rightInv codeDecode = Σ≡Prop (snd ∘ IsNormalised) ∘ uncurry coRet
  leftInv codeDecode = coSec base
  
  normalise : ∀ xs → Σ _ λ xs' →
    (xs' · xs ⁻¹≡ε) × ⟨ IsNormalised xs' ⟩
  normalise = Li.elim ([] , [ red[] ]≡ε , lower )
   λ {x} {xs} (xs' , [ u ]≡ε , v) →
    let zz : ∀ xs' uu u → Red (preη· x xs' uu ++ invLi (x ∷ xs))
        zz =
          λ { xs' (no ¬p) → subst (Red ∘' (x ∷_)) (++-assoc xs' _ _) ∘ cj x _
             ; [] (yes ())
             ; (_ ∷ xs') (yes p) →
                  subst Red (λ i → ++-assoc xs' (invLi xs)
                       [ symIsRedex _ _ p i ] i) ∘ redRot _ }
        h = HeadIsRedex? _
    in  _ , [ zz xs' h u ]≡ε , preη·-N h v

  IsoNF : Iso (Σ _ (fst ∘ IsNormalised)) List/↘↙
  fun IsoNF = [_]/ ∘ fst 
  Iso.inv IsoNF =
   SQ.rec (isSetΣ isSet[𝟚×] (isProp→isSet ∘ snd ∘ IsNormalised))
   ((λ (_ , _ , u) → _ , u) ∘ normalise)
   λ _ _ → let (a' , t  , u ) = normalise _
               (b' , t' , u') = normalise _
           in  Σ≡Prop (snd ∘ IsNormalised) ∘' sym
            ∘' nf-uR _ _ (fst (IsNormalisedInvLi {b'}) u') u
            ∘' red++comm a' (invLi b') ∘' ≡ε
            ∘' flip (·⁻¹≡ε-trans _ _ _) (·⁻¹≡ε-sym _ _ t')
            ∘' ·⁻¹≡ε-trans _ _ _ t
  rightInv IsoNF = SQ.elimProp (λ _ → squash/ _ _)
    (eq/ _ _ ∘ fst ∘ snd ∘ normalise) 
  leftInv IsoNF = Σ≡Prop (snd ∘ IsNormalised) ∘ uncurry
   (Li.elim (λ _ → refl) λ f v →
   let lem : ∀ uu → preη· _ _ uu ≡ _ ∷ _
       lem =
        λ { (yes p) → ⊥.rec (v (inl (subst (WillReduce _ _) (f (v ∘ inr)) p)))
          ; (no ¬p) → refl }
   in lem (HeadIsRedex? _) ∙ cong (_ ∷_) (f (v ∘ inr)))

 module HIT-FG where

  open import Cubical.HITs.FreeGroup renaming (rec to recFG ; elimProp to elimPropFG) public

  open NF (freeGroupGroup A) η renaming (inv to invFG)  

  FG→L/↘↙ : GroupHom (freeGroupGroup A) (_ , List/↘↙GroupStr)
  FG→L/↘↙ = recFG ([_]/ ∘ [_] ∘ (true ,_))

  module gh/ = IsGroupHom (snd (FG→L/↘↙))
  open GroupTheory (freeGroupGroup A)

  open IsGroupHom

  Red→FG≡ : ∀ a → Red a → fromList a ≡ ε
  Red→FG≡ .[] red[] = refl
  Red→FG≡ .(x ∷ (xs ∷ʳ not₁ x)) (cj x xs x₁) =
        cong (η* x ·fg_) (fromList· xs [ not₁ x ] ∙
          cong₂ _·fg_ (Red→FG≡ xs x₁) (·IdR _) ∙ ·IdL _) ∙
           redex-ε-η* x (not₁ x) (symIsRedex _ _ refl)
  Red→FG≡ .(xs ++ ys) ((xs · ys) x x₁) = fromList· xs ys
      ∙∙ cong₂ _·fg_ (Red→FG≡ _ x) (Red→FG≡ _ x₁) ∙∙ ·IdL _

  fromListInv : (xs : List (Bool × A)) →
     fromList (invLi xs) ≡ invFG (fromList xs)
  fromListInv [] = sym (GroupTheory.inv1g (freeGroupGroup A))
  fromListInv (x ∷ xs) = (fromList· (invLi xs) _ ∙
           cong (fromList (invLi xs) ·fg_) (w' x))
        ∙∙ cong (_·fg invFG (η* x)) (fromListInv xs) ∙∙  sym (invDistr _ _) 
   where
   w' : ∀ x → fromList [ not₁ x ] ≡ invFG (η* x)
   w' = λ { (false , a) → ·IdR _ ∙ sym (invInv _) ; (true , a) → ·IdR _ }

  fromL/ : List/↘↙ → _
  fromL/ = SQ.rec trunc fromList
    λ a b →
    _∙ (sym (fromListInv (invLi b))
            ∙ cong fromList (invol-invLi b)) ∘' invUniqueL
     ∘' sym (fromList· a (invLi b)) ∙_ ∘' Red→FG≡ _ ∘' ≡ε

  section-FG-L/↘↙ : ∀ a → fst (FG→L/↘↙) (fromList a) ≡ [ a ]/
  section-FG-L/↘↙ [] = refl
  section-FG-L/↘↙ (x ∷ xs) = gh/.pres· (η* x) (fromList xs) ∙
        cong (List/↘↙· (fst FG→L/↘↙ (η* x)))
          (section-FG-L/↘↙ xs) ∙ w x where
    w : ∀ x → List/↘↙· (fst FG→L/↘↙ (η* x)) [ xs ]/ ≡ [ x ∷ xs ]/
    w = λ { (false , a) → refl ; (true , a) → refl } 

  isGroupHomFromL/ : IsGroupHom List/↘↙GroupStr fromL/ (snd (freeGroupGroup A))
  pres· isGroupHomFromL/ = SQ.elimProp2 (λ _ _ → trunc _ _) fromList·
  pres1 isGroupHomFromL/ = refl
  presinv isGroupHomFromL/ = SQ.elimProp (λ _ → trunc _ _) fromListInv
  
  GroupIso-FG-L/↘↙ : GroupIso (freeGroupGroup A) (List/↘↙group)
  fun (fst GroupIso-FG-L/↘↙) = fst FG→L/↘↙
  Iso.inv (fst GroupIso-FG-L/↘↙) = fromL/
  rightInv (fst GroupIso-FG-L/↘↙) =  
     SQ.elimProp (λ _ → squash/ _ _) section-FG-L/↘↙
  leftInv (fst GroupIso-FG-L/↘↙) =
    funExt⁻ (congS fst (freeGroupHom≡
        {f = compGroupHom FG→L/↘↙ (fromL/ , isGroupHomFromL/)}
        {g = idGroupHom} (sym ∘ idr ∘ η )))
  snd GroupIso-FG-L/↘↙ = snd FG→L/↘↙



  module NFmore (isSetA : isSet A) where
   isSet[𝟚×A] = isOfHLevelList 0 (isSet× isSetBool isSetA)

   isPropNF : ∀ g → isProp (NF g) 
   isPropNF = λ g →
     λ (xs nf u , v) (xs' nf u' , v') →
      let zz = PT.rec (isSet[𝟚×A] xs xs')
               (sym
             ∘' nf-uR _ _ (fst IsNormalisedInvLi v') v
             ∘' red++comm xs (invLi xs')
             ∘' ≡ε ) (Iso.fun (≡→red xs xs') (
               isoInvInjective (fst (GroupIso-FG-L/↘↙))
                _ _ (u ∙ (sym u'))))
      in λ i → zz i
        nf isProp→PathP (λ i → trunc (fromList (zz i)) g) u u' i
         , isProp→PathP (λ i → snd (IsNormalised (zz i))) v v' i

   ηInj : ∀ a a' → Path (FreeGroup A) (η a) (η a') → a ≡ a'
   ηInj a a' = 
         PT.rec (isSetA _ _)
           ((λ { (inl p) i → snd (p i)
               ; (inr (inl ())) ; (inr (inr ()))})
            ∘' Red⇒HasRedex _ _ ∘' ≡ε )  
      ∘' Iso.fun (≡→red _ _)
      ∘' isoInvInjective (fst (GroupIso-FG-L/↘↙))
         [ [ true , _ ] ]/ [ [ true , _ ] ]/
      ∘' ·IdR _ ∙∙_∙∙ sym (·IdR _)

   NF-η : ∀ a → (nfa : NF (η a)) → [ true , a ] ≡ NF.𝒘 nfa
   NF-η a nfa = PT.rec (isSet[𝟚×A] _ _) (λ u → 
    nf-uR _ _ (IsNormalised[x] (true , a))
     (NF.isNormalised𝒘 nfa) (red++comm _ [ false , a ] (≡ε u)))
      (Iso.fun (≡→red _ _) (isoInvInjective (fst (GroupIso-FG-L/↘↙))
             [ NF.𝒘 nfa ]/ [ [ (true , a) ] ]/
               (NF.fromList𝒘≡ nfa ∙ (sym (·IdR _)))))
   
   ΠNF⇒DiscreteA : (∀ g → NF g) → Discrete A
   ΠNF⇒DiscreteA nF a a' = 
    let nff = nF (η a · invFG (η a'))
    in PT.rec (isPropDec (isSetA _ _))
       (λ r → ⊎.rec
         (yes ∘ sym ∘ cong snd)
         (no ∘ ⊎.rec (λ p pp → lower (subst (WillReduce false a)
         (isNormalisedRed _ (NF.isNormalised𝒘 nff)
          (popRedHead (cong (true ,_) (sym pp)) r)) p))
                      (const ∘ NF.isNormalised𝒘 nff))
           (Red⇒HasRedex _ _ r))
        (PT.map (red++comm (NF.𝒘 nff) _ ∘ ≡ε)
        (Iso.fun (≡→red _ _) (isoInvInjective (fst (GroupIso-FG-L/↘↙))
             [ NF.𝒘 nff ]/ [ (true , a) ∷ [ false , a' ] ]/
               (NF.fromList𝒘≡ nff ∙ cong (η a ·_) (sym (·IdR _))))))

   NF⇔ : (∀ g → NF g) ≃ Discrete A 
   NF⇔ = propBiimpl→Equiv (isPropΠ isPropNF) isPropDiscrete
     ΠNF⇒DiscreteA
     λ _≟_ g →
       let e = compIso (fst (GroupIso-FG-L/↘↙)) (invIso (IsoNF _≟_))
           (g' , n) = Iso.fun e g
       in g' nf Iso.leftInv e g , n
        
  discreteFreeGroup : Discrete A → Discrete (FreeGroup A)
  discreteFreeGroup _≟_ =
    isoPresDiscrete
      (compIso
         (IsoNF _≟_)
         (invIso (fst (GroupIso-FG-L/↘↙))))
      (discreteΣProp
        (discreteList (discreteΣ 𝟚._≟_ λ _ → _≟_))
        (snd ∘ IsNormalised))
