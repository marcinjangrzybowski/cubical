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

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/₂_ ; [_] to [_]/)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
-- open import Cubical.HITs.TypeQuotients as TQ renaming ([_] to [_]/ₜ ; eq/ to eq/ₜ )


open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.HITs.FreeGroup.NormalForm.Base

open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Groups

open import Cubical.HITs.Bouquet renaming (elimProp to elimBouquetProp)
  hiding (winding)
private
  variable
    ℓ : Level


module _ (A : Type ℓ) where

 open NormalForm A

 invLi : List (Bool × A) → List (Bool × A)
 invLi = rev ∘ Li.map (map-fst not)

 invLi++ : ∀ xs ys → invLi (xs ++ ys) ≡
                 invLi ys ++ invLi xs
 invLi++ xs ys =
   sym (cong rev (map++ _ xs ys)) ∙
     rev-++ (Li.map _ xs) (Li.map _ ys)
 
 invol-invLi : isInvolution invLi
 invol-invLi xs =
  sym (rev-map-comm (map-fst not) (invLi xs)) ∙
    cong (Li.map (map-fst not))
      (rev-rev (Li.map (map-fst not) xs))
     ∙ map-∘ (map-fst not) (map-fst not) xs ∙
     (λ i → Li.map (map-fst (λ x → notnot x i) ) xs) ∙ map-id xs

 revRed : ∀ xs → Red xs → Red (rev xs)
 revRed .[] red[] = red[]
 revRed .(x ∷ (xs ∷ʳ not₁ x)) (cj x xs r) =
   subst Red ((λ i → ++-assoc [ not₁ x ] (rev xs) [ not₁not₁ x i ] (~ i))
     ∙ cong (_∷ʳ x) (sym (rev-++ xs _) ))
       (cj (not₁ x) _ (revRed xs r))
 revRed .(xs ++ ys) ((xs · ys) r r₁) =
   subst Red (sym (rev-++ xs _))
    (_·_ _ _ (revRed _ r₁) (revRed _ r))

 not₁Red : ∀ xs → Red xs → Red (Li.map not₁ xs)
 not₁Red .[] red[] = red[]
 not₁Red .(x ∷ (xs ∷ʳ not₁ x)) (cj x xs x₁) =
   subst Red (cong (not₁ x ∷_) (map++ _ xs _)) (cj (not₁ x) _ (not₁Red _ x₁))
 not₁Red .(xs ++ ys) ((xs · ys) x x₁) =
    subst Red (map++ _ xs _)
      (_·_ _ _ (not₁Red _ x) (not₁Red _ x₁))
 
 Red-invLi : ∀ xs → Red xs → Red (invLi xs)
 Red-invLi xs = revRed _ ∘ not₁Red _ 


 IsNormalisedRev : ∀ xs → IsNormalised xs
                        → IsNormalised (rev xs)
 IsNormalisedRev [] u = u
 IsNormalisedRev (x ∷ xs) u = {!!}


--  IsNormalisedInvLi : ∀ xs → IsNormalised xs
--                           → IsNormalised (invLi xs)
--  IsNormalisedInvLi [] x = tt*
--  IsNormalisedInvLi (x₁ ∷ xs) x = {!!}
 
-- --  nf-uR : ∀ xs ys
-- --     → IsNormalised xs → IsNormalised ys
-- --              → Red (invLi xs ++ ys) → xs ≡ ys 
-- --  nf-uR [] ys nXs nYs r = sym (isNormalisedRed ys nYs r)
-- --  nf-uR xs@(_ ∷ _) [] nXs nYs r = ⊥.rec (¬cons≡nil
-- --    (isNormalisedRed xs nXs
-- --          (subst Red (cong invLi (++-unit-r (invLi xs))
-- --            ∙ invol-invLi xs) (Red-invLi _ r))))
-- --  nf-uR (x ∷ xs) (y ∷ ys) nXs nYs r with hasRedexSplitCases++
-- --      (invLi (x ∷ xs)) ((y ∷ ys)) (fst (Red⇒HasRedex _ ((subst {y = length (invLi (x ∷ xs) ++ y ∷ ys)}
-- --                          (zero <_)
-- --                           (sym (+-comm (length (invLi (x ∷ xs))) _)
-- --                            ∙ sym (length++ (invLi (x ∷ xs)) _)) tt)) r)) 
-- --  ... | inl (inl x₁) = 
-- --    ⊥.rec (IsNormalised→¬HaseRedex _ {!nXs!} (fst x₁))
-- --  ... | inl (inr x₁) =
-- --       ⊥.rec (IsNormalised→¬HaseRedex _ nYs (fst x₁))
-- --  ... | inr (z , x₁ , fst₁ , snd₁) =
-- --    let xsWR = (WillReduceʳRev⇒WillReduce _ _
-- --          (Li.map (map-fst not) (x ∷ xs)) fst₁)
-- --    in cong₂ _∷_ ((sym (not₁not₁ x) ∙ sym xsWR) ∙ sym (symIsRedex _ _ snd₁))
-- --          (nf-uR xs ys (snd nXs) (snd nYs)
-- --            (subst Red (z ∙ cong (_++ ys) (init∷ʳ _ _)) (reduceRed _
-- --              ((fst (Red⇒HasRedex _
-- --                (subst {y = length (invLi (x ∷ xs) ++ y ∷ ys)}
-- --                          (zero <_)
-- --                           (sym (+-comm (length (invLi (x ∷ xs))) _)
-- --                            ∙ sym (length++ (invLi (x ∷ xs)) _)) tt) r))) r)))

-- -- --  infixr 5 _·_⁻¹≡ε

-- -- --  record _·_⁻¹≡ε (xs ys : _) : Type ℓ where
-- -- --   constructor [_]≡ε
-- -- --   field
-- -- --    ≡ε : Red (xs ++ invLi ys)

-- -- --  open _·_⁻¹≡ε public


-- -- --  open BinaryRelation
-- -- --  open isEquivRel

-- -- --  ·⁻¹≡ε-refl : isRefl _·_⁻¹≡ε
-- -- --  ·⁻¹≡ε-refl [] = [ red[] ]≡ε
-- -- --  ≡ε (·⁻¹≡ε-refl (x ∷ xs)) =
-- -- --    subst Red (sym (++-assoc [ x ] xs (invLi (x ∷ xs)) ∙
-- -- --          cong (x ∷_) (sym (++-assoc xs (invLi xs) _))))
-- -- --      (cj x _ (≡ε (·⁻¹≡ε-refl xs)))

-- -- --  ·⁻¹≡ε-sym : isSym _·_⁻¹≡ε
-- -- --  ≡ε (·⁻¹≡ε-sym a b [ p ]≡ε) = 
-- -- --    subst Red (invol-invLi (b ++ invLi a))
-- -- --      (Red-invLi (invLi (b ++ invLi a))
-- -- --        (subst Red (cong (_++ invLi b) (sym (invol-invLi a))
-- -- --            ∙ sym (invLi++ b (invLi a))) p))
 
-- -- --  ·⁻¹≡ε-trans : isTrans _·_⁻¹≡ε
-- -- --  ≡ε (·⁻¹≡ε-trans xs ys zs [ p ]≡ε [ q ]≡ε) = 
-- -- --    hlp _ xs _ (invLi zs) (≤-refl (length (invLi ys ++ invLi (invLi ys))))
-- -- --      (≡ε (·⁻¹≡ε-refl (invLi ys)))
-- -- --      (subst Red (++-assoc xs _ _
-- -- --       ∙ cong (xs ++_) (λ i → ++-assoc (invLi ys)
-- -- --         (invol-invLi ys (~ i)) (invLi zs) (~ i))) (_·_ _ _ p q))
-- -- --    where
-- -- --    hlp : ∀ n xs ys zs →
-- -- --      length ys ≤ n → Red ys → Red (xs ++ ys ++ zs) → Red (xs ++ zs) 
-- -- --    hlp _ _ [] _ _ _ x = x
-- -- --    hlp (suc n) xs ys@(y ∷ ys') zs ≤sn Red-ys r =
-- -- --     let (hr , p) = Red⇒HasRedex ys _ Red-ys
-- -- --     in hlp n xs (reduce ys hr) zs
-- -- --              (≤-trans {suc (length (reduce _ hr))} {length ys} {suc n}
-- -- --                           (reduce-length-≤ ys hr) ≤sn)
-- -- --              p
-- -- --              (subst Red (++reduce xs (ys ++ zs) _
-- -- --                      ∙ cong (xs ++_) (reduce++ ys zs hr))
-- -- --                  (reduceRed _ (++HasRedex xs _ (HasRedex++ _ zs hr)) r)
-- -- --                  )

-- -- --  ·⁻¹≡ε-isEquivRel : isEquivRel _·_⁻¹≡ε
-- -- --  reflexive ·⁻¹≡ε-isEquivRel = ·⁻¹≡ε-refl
-- -- --  symmetric ·⁻¹≡ε-isEquivRel = ·⁻¹≡ε-sym
-- -- --  transitive ·⁻¹≡ε-isEquivRel = ·⁻¹≡ε-trans

-- -- --  open Iso

-- -- --  RedInRed' : ∀ xs ys k → k ≤ length xs →
-- -- --       Red ys  → Red xs →  Red (take k xs ++ ys ++ drop k xs) 
-- -- --  RedInRed' xs ys zero _ = _r·_
-- -- --  RedInRed' .[] ys (suc k) _ r red[] = subst Red (sym (++-unit-r ys)) r

-- -- --  RedInRed' .(x ∷ (xs ∷ʳ not₁ x)) ys (suc k) k< r r*@(cj x xs r') with ≤-split {m = k} {n = suc (length xs)}  (subst (k ≤_) (length++ xs [ _ ] ∙ +-comm _ 1) k<)
-- -- --  ... | inl k<' =
-- -- --   let z = RedInRed' xs ys k k<' r r'
-- -- --   in subst Red (cong (x ∷_) {!!}) (cj x _ z)
-- -- --  ... | inr x₁ = subst Red (cong (x ∷_) {!!} ) (r* r· r )
  
-- -- --  RedInRed' .(xs ++ ys₁) ys (suc k) k< r ((xs · ys₁) r' r'') = {!!}


-- -- --  RedInRed : ∀ xs ys zs → 
-- -- --       Red ys → Red (xs ++ zs) → Red (xs ++ ys ++ zs) 
-- -- --  RedInRed = {!!}


-- -- --  List/↘↙ : Type ℓ
-- -- --  List/↘↙ = _ /₂ _·_⁻¹≡ε

-- -- --  _↘↙_ = _·_⁻¹≡ε

-- -- --  _↘↙++↘↙_ : ∀ {xsL xsR ysL ysR} →
-- -- --     xsL ↘↙ ysL → xsR ↘↙ ysR →
-- -- --       (xsL ++ xsR) ↘↙ (ysL ++ ysR)
-- -- --  ≡ε (_↘↙++↘↙_ {xsL} {xsR} {ysL} {ysR} [ p ]≡ε [ q ]≡ε) =
-- -- --    subst Red (cong (xsL ++_) (++-assoc xsR (invLi ysR) _)
-- -- --                     ∙∙ sym (++-assoc xsL _ _)
-- -- --                     ∙∙ cong ((xsL ++ xsR) ++_) (sym (invLi++ ysL ysR)))
-- -- --             (RedInRed xsL _ _ q p )
     


-- -- --  List/↘↙· : List/↘↙ → List/↘↙ → List/↘↙
-- -- --  List/↘↙· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
-- -- --     (λ _ _ c → eq/ _ _ ∘ _↘↙++↘↙ (·⁻¹≡ε-refl c))
-- -- --     (λ a _ _ → eq/ _ _ ∘ (·⁻¹≡ε-refl a) ↘↙++↘↙_ )




 

-- -- --  -- lemInv' : ∀ xs ys → Red (xs ++ ys) → Red (invLi xs ++ invLi ys) 
-- -- --  -- lemInv' xs ys r++ with


-- -- --  lemInv : ∀ xs ys → Red (xs ++ ys) → Red (invLi xs ++ invLi ys) 
-- -- --  lemInv xs ys r++ = {!!}

-- -- --  List/↘↙GroupStr : GroupStr List/↘↙
-- -- --  GroupStr.1g List/↘↙GroupStr = [ [] ]/
-- -- --  GroupStr._·_ List/↘↙GroupStr = List/↘↙·
-- -- --  GroupStr.inv List/↘↙GroupStr =
-- -- --   SQ.rec squash/ ([_]/ ∘ invLi)
-- -- --     λ xs ys → eq/ _ _ ∘' ([_]≡ε ∘' lemInv xs (invLi ys) ) ∘' ≡ε
              
-- -- --  GroupStr.isGroup List/↘↙GroupStr = makeIsGroup squash/
-- -- --   (SQ.elimProp3 (λ _ _ _ → squash/ _ _)
-- -- --       λ xs _ _ → cong SQ.[_] (sym (++-assoc xs _ _)))
-- -- --   (SQ.elimProp (λ _ → squash/ _ _) λ xs → cong SQ.[_] (++-unit-r xs))
-- -- --   (SQ.elimProp (λ _ → squash/ _ _) λ _ → refl)
-- -- --   (SQ.elimProp (λ _ → squash/ _ _) λ xs → sym (eq/ _ _
-- -- --      ([ Red-invLi (xs ++ invLi xs) (≡ε (·⁻¹≡ε-refl xs)) ]≡ε)))
-- -- --   (SQ.elimProp (λ _ → squash/ _ _) λ xs → eq/ _ _ [
-- -- --      subst Red (cong (invLi xs ++_) (invol-invLi xs) ∙
-- -- --        sym (++-unit-r _)) (≡ε (·⁻¹≡ε-refl (invLi xs))) ]≡ε)

-- -- --  List/↘↙group : Group ℓ
-- -- --  List/↘↙group = _ , List/↘↙GroupStr 
 

-- -- --  module HIT-FG where

-- -- --   open import Cubical.HITs.FreeGroup renaming (rec to recFG ; elimProp to elimPropFG) public

-- -- --   open FG (freeGroupGroup A) η renaming (inv to invFG)  

-- -- --   FG→L/↘↙ : GroupHom (freeGroupGroup A) (_ , List/↘↙GroupStr)
-- -- --   FG→L/↘↙ = recFG ([_]/ ∘ [_] ∘ (true ,_))

-- -- --   open IsGroupHom (snd (FG→L/↘↙))

-- -- --   Red→FG≡ : ∀ a → Red a → fromList a ≡ ε
  
-- -- --   Red→FG≡ .[] red[] = refl
-- -- --   Red→FG≡ .(x ∷ (xs ∷ʳ not₁ x)) (cj x xs x₁) =
-- -- --         cong (η* x ·fg_) (fromList· xs [ not₁ x ] ∙
-- -- --           cong₂ _·fg_ (Red→FG≡ xs x₁) (·IdR _) ∙ ·IdL _) ∙
-- -- --            redex-ε-η* x (not₁ x) (symIsRedex _ _ refl)
-- -- --   Red→FG≡ .(xs ++ ys) ((xs · ys) x x₁) =
-- -- --     fromList· xs ys
-- -- --       ∙∙ cong₂ _·fg_ (Red→FG≡ _ x) (Red→FG≡ _ x₁)
-- -- --       ∙∙ ·IdL _
  
-- -- --   section-FG-L/↘↙ : ∀ a → fst (FG→L/↘↙) (fromList a) ≡ [ a ]/
-- -- --   section-FG-L/↘↙ [] = refl
-- -- --   section-FG-L/↘↙ (x ∷ xs) = pres· (η* x) (fromList xs) ∙
-- -- --         cong (List/↘↙· (fst FG→L/↘↙ (η* x)))
-- -- --           (section-FG-L/↘↙ xs)  ∙
-- -- --            w x
-- -- --     where
-- -- --     w : ∀ x → List/↘↙· (fst FG→L/↘↙ (η* x)) [ xs ]/ ≡ [ x ∷ xs ]/
-- -- --     w (false , a) = refl
-- -- --     w (true , a) = refl


-- -- --   fromListInv : (xs : List (Bool × A)) →
-- -- --      fromList (invLi xs) ≡ invFG (fromList xs)
-- -- --   fromListInv [] = sym (GroupTheory.inv1g (freeGroupGroup A))
-- -- --   fromListInv (x ∷ xs) = 
-- -- --        (fromList· (invLi xs) [ not₁ x ] ∙
-- -- --            cong (fromList (invLi xs) ·fg_)
-- -- --             (w' x)
-- -- --             )
-- -- --         ∙∙ cong (_·fg invFG (η* x)) (fromListInv xs) ∙∙  sym (invDistr _ _) 
-- -- --    where
-- -- --    open GroupTheory (freeGroupGroup A)

-- -- --    w' : ∀ x → fromList [ not₁ x ] ≡ invFG (η* x)
-- -- --    w' = λ { (false , a) → ·IdR _ ∙ sym (invInv _) ; (true , a) → ·IdR _ }

-- -- --   fromL/ : List/↘↙ → _
-- -- --   fromL/ = SQ.rec trunc fromList
-- -- --     λ a b →
-- -- --         _∙ (sym (fromListInv (invLi b))
-- -- --             ∙ cong fromList (invol-invLi b))
-- -- --      ∘' invUniqueL
-- -- --      ∘' sym (fromList· a (invLi b)) ∙_
-- -- --      ∘' Red→FG≡ _
-- -- --      ∘' ≡ε
-- -- --    where
-- -- --    open GroupTheory (freeGroupGroup A)
   
-- -- --   fromL/pres· : ∀ a b → fromL/ (List/↘↙· a b) ≡ fromL/ a ·fg fromL/ b 
-- -- --   fromL/pres· = SQ.elimProp2 (λ _ _ → trunc _ _) fromList·

-- -- --   fromL/presinv : ∀ xs →
-- -- --        fromL/ (GroupStr.inv List/↘↙GroupStr xs) ≡
-- -- --       invFG (fromL/ xs)
-- -- --   fromL/presinv = SQ.elimProp (λ _ → trunc _ _) w
-- -- --    where
-- -- --    open GroupTheory (freeGroupGroup A)

-- -- --    w' : ∀ x → fromList [ not₁ x ] ≡ invFG (η* x)
-- -- --    w' (false , a) = ·IdR _ ∙ sym (invInv _)
-- -- --    w' (true , a) = ·IdR _

-- -- --    w : (xs : List (Bool × A)) →
-- -- --       fromList (invLi xs) ≡ invFG (fromList xs)
-- -- --    w [] = sym inv1g
-- -- --    w (x ∷ xs) = 
-- -- --         (fromList· (invLi xs) [ not₁ x ] ∙
-- -- --             cong (fromList (invLi xs) ·fg_) (w' x))
-- -- --          ∙∙ cong (_·fg invFG (η* x)) (w xs) ∙∙  sym (invDistr _ _) 
  
-- -- --   retract-FG-L/↘↙ : ∀ b →  fromL/ (fst (FG→L/↘↙) b) ≡ b
-- -- --   retract-FG-L/↘↙ = 
-- -- --      elimPropFG (λ _ → trunc _ _)
-- -- --        (λ _ → ·IdR _)
-- -- --        (λ g1 g2 p1 p2 →
-- -- --          cong fromL/ (pres· g1 g2) ∙
-- -- --            fromL/pres· (fst (FG→L/↘↙) g1) (fst (FG→L/↘↙) g2) ∙
-- -- --             cong₂ _·fg_ p1 p2)
-- -- --        refl
-- -- --        λ g p → cong fromL/ (presinv g) ∙
-- -- --           fromL/presinv (fst (FG→L/↘↙) g) ∙ cong invFG p 

-- -- --   GroupIso-FG-L/↘↙ : GroupIso (freeGroupGroup A) (List/↘↙group)
-- -- --   Iso.fun (fst GroupIso-FG-L/↘↙) = _
-- -- --   Iso.inv (fst GroupIso-FG-L/↘↙) = fromL/

-- -- --   Iso.rightInv (fst GroupIso-FG-L/↘↙) =
-- -- --     SQ.elimProp (λ _ → squash/ _ _)
-- -- --      section-FG-L/↘↙
-- -- --   Iso.leftInv (fst GroupIso-FG-L/↘↙) = retract-FG-L/↘↙
-- -- --   snd GroupIso-FG-L/↘↙ = snd FG→L/↘↙

-- -- -- -- module Categorical where

-- -- -- -- open Functor



-- -- -- -- -- freeGroupFunctor' : Functor (SET ℓ) (GroupCategory {ℓ})
-- -- -- -- -- F-ob freeGroupFunctor' = List/↘↙group ∘ fst
-- -- -- -- -- fst (F-hom freeGroupFunctor' f) =
-- -- -- -- --  SQ.rec squash/ ([_]/ ∘ Li.map (map-snd f))
-- -- -- -- --   λ a b p → eq/ _ _ [ {!≡ε p!} ]≡ε
-- -- -- -- -- snd (F-hom freeGroupFunctor' f) = {!!}
-- -- -- -- -- F-id freeGroupFunctor' = {!!}
-- -- -- -- -- F-seq freeGroupFunctor' = {!!}

-- -- -- -- -- --  ↘↙refl : isRefl _↘↙_
-- -- -- -- -- --  ↘↙refl _ = _ , ↓refl _ , ↓refl _ 

-- -- -- -- -- --  ↘↙sym : isSym _↘↙_
-- -- -- -- -- --  ↘↙sym _ _ = map-snd λ (x , y) → y , x 

-- -- -- -- -- --  ↘↙trans : isTrans _↘↙_
-- -- -- -- -- --  ↘↙trans _ _ _ (_ , (u , v)) (_ , (u' , v')) =
-- -- -- -- -- --   let (_ , (u'' , v'')) = ↙↘⇒↘↙ _ _ _ (v , u')
-- -- -- -- -- --   in _ , ↓trans _ _ _ u u'' , ↓trans _ _ _ v' v'' 

-- -- -- -- -- --  ↘↙isEquivRel : isEquivRel _↘↙_
-- -- -- -- -- --  reflexive ↘↙isEquivRel = ↘↙refl
-- -- -- -- -- --  symmetric ↘↙isEquivRel = ↘↙sym
-- -- -- -- -- --  transitive ↘↙isEquivRel = ↘↙trans


-- -- -- -- -- --  _↘↙++↘↙_ : ∀ {xsL xsR ysL ysR} →
-- -- -- -- -- --     xsL ↘↙ ysL → xsR ↘↙ ysR →
-- -- -- -- -- --       (xsL ++ xsR) ↘↙ (ysL ++ ysR)
-- -- -- -- -- --  (_ , xl , yl) ↘↙++↘↙ (_ , xr , yr) = _ , (xl ↓++↓ xr) , (yl ↓++↓ yr)


-- -- -- -- -- --  List/↘↙ : Type ℓ
-- -- -- -- -- --  List/↘↙ = _ /₂ _↘↙_


-- -- -- -- -- -- ≡no : ∀ {A : Type ℓ} x y → Path (Dec A) x (no y)
-- -- -- -- -- -- ≡no (yes p) y = ⊥.rec (y p)
-- -- -- -- -- -- ≡no (no ¬p) y i = no (isProp¬ _ ¬p y i)


-- -- -- -- -- -- module _ (A : Type ℓ) where

-- -- -- -- -- --  open NormalForm A

-- -- -- -- -- --  IsRedex→Red : ∀ x y → IsRedex x y → Red (x ∷ y ∷ [])
-- -- -- -- -- --  IsRedex→Red x y q =
-- -- -- -- -- --    (subst Red (cong ((x ∷_) ∘ [_])
-- -- -- -- -- --     (sym ((symIsRedex _ _ q)))) (cj x _ red[]))


-- -- -- -- -- --  lem↙↘⇒↘↙'' : ∀ x ys zs → (q : WillReduce (fst x) (snd x) ys) →
-- -- -- -- -- --      ys ↓ zs →
-- -- -- -- -- --      Σ _ λ zs' → reduce (x ∷ ys) (inl q) ↓ zs' × ((x ∷ zs) ↓ zs') 
-- -- -- -- -- --  lem↙↘⇒↘↙'' x ys .[] q (x₁ NormalForm.↓[]) =
-- -- -- -- -- --   let (((rl' , rlR') , (rr' , rrR')) , p'') =
-- -- -- -- -- --           RedWillReduceView _ _ _ x₁ q
-- -- -- -- -- --   in x ∷ [] , (subst (_↓ [ x ]) (p'' ∙ sym (reduceHead x ys q))
-- -- -- -- -- --          (rlR' ∶ x ↓∷ (rrR' ↓[]))  , (↓refl _))
-- -- -- -- -- --  lem↙↘⇒↘↙'' x .([] ++ x₂ ∷ _) .(x₂ ∷ zs) q (NormalForm._∶_↓∷_ {[]} x₁ x₂ {zs} x₃) =
-- -- -- -- -- --    zs , x₃ , Red++↓ (IsRedex→Red _ _ q) (↓refl zs)
-- -- -- -- -- --  lem↙↘⇒↘↙'' x .((x₄ ∷ xs) ++ x₂ ∷ ys) .(x₂ ∷ zs) q (NormalForm._∶_↓∷_ {x₄ ∷ xs} x₁ {ys} x₂ {zs} x₃) = 
-- -- -- -- -- --    let (((rl' , rlR') , (rr' , rrR')) , p'') =
-- -- -- -- -- --           RedWillReduceView _ _ _ x₁ q
-- -- -- -- -- --    in x ∷ x₂ ∷ zs , subst (_↓ (x ∷ x₂ ∷ zs))
-- -- -- -- -- --        (sym (++-assoc rl' (x ∷ rr') _) ∙ cong (_++ x₂ ∷ ys) p'')
-- -- -- -- -- --         (rlR' ∶ x ↓∷ (rrR' ∶ x₂ ↓∷ x₃)) , ↓refl _ 


-- -- -- -- -- --  lem↙↘⇒↘↙' : ∀ ys zs → (r : HasRedex ys) → ys ↓ zs →
-- -- -- -- -- --                   Σ _ λ zs' → (reduce _ r ↓ zs') × (zs ↓ zs')
-- -- -- -- -- --  lem↙↘⇒↘↙' ys .[] r (x ↓[]) =
-- -- -- -- -- --    [] , (reduceRed ys r x ↓[] , (red[] ↓[]))
-- -- -- -- -- --  lem↙↘⇒↘↙' .(xs ++ x₁ ∷ ys) .(x₁ ∷ zs) r (NormalForm._∶_↓∷_ {xs} x {ys} x₁ {zs} x₂) with hasRedexSplitCases++ xs (x₁ ∷ ys) r 
-- -- -- -- -- --  ... | inl (inl (u , v)) = x₁ ∷ zs ,
-- -- -- -- -- --    subst (_↓ (x₁ ∷ zs)) v (Red++↓ (reduceRed xs u x) (x₁ ∷↓ x₂) ) , ↓refl _
-- -- -- -- -- --  ... | inl (inr (inl x₃ , v)) =
-- -- -- -- -- --    let (zs' , u' , v') = lem↙↘⇒↘↙'' x₁ ys zs x₃ x₂
-- -- -- -- -- --    in zs' , subst (_↓ zs')
-- -- -- -- -- --         (v) (Red++↓ x u') , v'
-- -- -- -- -- --  ... | inl (inr (inr u , v)) = 
-- -- -- -- -- --         let (zs' , p , q) = lem↙↘⇒↘↙' (ys) ( zs) u x₂ 
-- -- -- -- -- --         in x₁ ∷ zs' , subst (_↓ (x₁ ∷ zs')) v (x ∶ x₁ ↓∷ p) ,
-- -- -- -- -- --              (x₁ ∷↓ q ) 
-- -- -- -- -- --  ... | inr (p , x₂' , (w , p')) =
-- -- -- -- -- --     let (((rl' , rlR') , (rr' , rrR')) , p'') =
-- -- -- -- -- --           RedWillReduceʳView _ _ _ x w
-- -- -- -- -- --         z = rlR' ∶ x₁ ↓∷ Red++↓ rrR' x₂
-- -- -- -- -- --     in x₁ ∷ zs , subst (_↓ (x₁ ∷ zs))
-- -- -- -- -- --                      ((cong (λ x₁ → rl' ++ x₁ ∷ rr' ++ ys) ((symIsRedex _ _ p'))
-- -- -- -- -- --                       ∙ sym (++-assoc rl' _ _))
-- -- -- -- -- --                       ∙∙ cong (_++ ys) p''
-- -- -- -- -- --                       ∙∙ sym p ) z
-- -- -- -- -- --                , ↓refl _

-- -- -- -- -- --  ↓→↘↙ : ∀ xs ys → xs ↓ ys → xs ↘↙ ys 
-- -- -- -- -- --  ↓→↘↙ xs ys x = ys , x , ↓refl ys
 
-- -- -- -- -- --  ↙↘⇒↘↙' : ∀ n xs ys zs → (length ys ≤ n) → xs ↙ ys ↘ zs
-- -- -- -- -- --     → (xs ↘↙ zs) 
-- -- -- -- -- --  ↙↘⇒↘↙' zero xs [] zs ys≤n (↓xs , ↓zs) =
-- -- -- -- -- --    [] ,
-- -- -- -- -- --    subst (_↓ []) (sym ([]↓ xs ↓xs)) (↓refl []) ,
-- -- -- -- -- --    subst (_↓ []) (sym ([]↓ zs ↓zs)) (↓refl [])
-- -- -- -- -- --  ↙↘⇒↘↙' (suc n) xs ys zs ys≤n (↓xs , ↓zs) =
-- -- -- -- -- --    ⊎.rec (λ xs<ys →
-- -- -- -- -- --        let (hr , p) = ≢↓→HasRedex _ _ xs<ys ↓xs
-- -- -- -- -- --            (zs* , ↓zs* , zs↓zs*) = lem↙↘⇒↘↙' ys zs hr ↓zs
-- -- -- -- -- --            r-ys≤n = ≤-trans {suc (length (reduce _ hr))} {length ys} {suc n}
-- -- -- -- -- --                         (reduce-length-≤ ys hr) ys≤n
-- -- -- -- -- --            (zs' , xs↓zs' , zs*↓zs') =
-- -- -- -- -- --                ↙↘⇒↘↙' n xs (reduce _ hr) zs*
-- -- -- -- -- --                  r-ys≤n (p , ↓zs*)
-- -- -- -- -- --         in zs' , xs↓zs' , ↓trans _ _ _ zs↓zs* (zs*↓zs'))
       
-- -- -- -- -- --       (λ p → 
-- -- -- -- -- --          let p' = ↓EqualLengths⇒≡ {ys} {xs} ↓xs (sym p)
-- -- -- -- -- --          in zs , subst (_↓ zs) p' ↓zs , ↓refl zs )
-- -- -- -- -- --      (≤-split {length xs} {length ys} (↓⇒length≥ {ys} {xs} ↓xs))
 

-- -- -- -- -- --  ↓reduce : ∀ xs r → xs ↓ reduce xs r 
-- -- -- -- -- --  ↓reduce (x ∷ xs) (inr x₁) = x ∷↓ (↓reduce xs x₁)
-- -- -- -- -- --  ↓reduce (x ∷ x₂ ∷ xs) (inl x₁) = Red++↓ (IsRedex→Red _ _ x₁) (↓refl xs)
 
-- -- -- -- -- --  ↙↘⇒↘↙ : ∀ xs ys zs → xs ↙ ys ↘ zs → Σ _ (xs ↘_↙ zs) 
-- -- -- -- -- --  ↙↘⇒↘↙ xs ys zs = ↙↘⇒↘↙' _ xs ys zs (≤-refl (length ys))

-- -- -- -- -- --  N↘↙N→≡ : ∀ xs ys → xs ↘↙ ys →
-- -- -- -- -- --      IsNormalised xs →
-- -- -- -- -- --      IsNormalised ys → xs ≡ ys
-- -- -- -- -- --  N↘↙N→≡ xs ys (zs , xs↓ , ys↓) xsN ysN =
-- -- -- -- -- --    minimalNormalised xs zs xsN xs↓ ∙
-- -- -- -- -- --     sym (minimalNormalised ys zs ysN ys↓)
    
-- -- -- -- -- --  open BinaryRelation
-- -- -- -- -- --  open isEquivRel

-- -- -- -- -- --  ↘↙refl : isRefl _↘↙_
-- -- -- -- -- --  ↘↙refl _ = _ , ↓refl _ , ↓refl _ 

-- -- -- -- -- --  ↘↙sym : isSym _↘↙_
-- -- -- -- -- --  ↘↙sym _ _ = map-snd λ (x , y) → y , x 

-- -- -- -- -- --  ↘↙trans : isTrans _↘↙_
-- -- -- -- -- --  ↘↙trans _ _ _ (_ , (u , v)) (_ , (u' , v')) =
-- -- -- -- -- --   let (_ , (u'' , v'')) = ↙↘⇒↘↙ _ _ _ (v , u')
-- -- -- -- -- --   in _ , ↓trans _ _ _ u u'' , ↓trans _ _ _ v' v'' 

-- -- -- -- -- --  ↘↙isEquivRel : isEquivRel _↘↙_
-- -- -- -- -- --  reflexive ↘↙isEquivRel = ↘↙refl
-- -- -- -- -- --  symmetric ↘↙isEquivRel = ↘↙sym
-- -- -- -- -- --  transitive ↘↙isEquivRel = ↘↙trans


-- -- -- -- -- --  _↘↙++↘↙_ : ∀ {xsL xsR ysL ysR} →
-- -- -- -- -- --     xsL ↘↙ ysL → xsR ↘↙ ysR →
-- -- -- -- -- --       (xsL ++ xsR) ↘↙ (ysL ++ ysR)
-- -- -- -- -- --  (_ , xl , yl) ↘↙++↘↙ (_ , xr , yr) = _ , (xl ↓++↓ xr) , (yl ↓++↓ yr)


-- -- -- -- -- --  List/↘↙ : Type ℓ
-- -- -- -- -- --  List/↘↙ = _ /₂ _↘↙_

-- -- -- -- -- --  -- List/ₜ↘↙ : Type ℓ
-- -- -- -- -- --  -- List/ₜ↘↙ = _ /ₜ _↘↙_



-- -- -- -- -- --  List/↘↙· : List/↘↙ → List/↘↙ → List/↘↙
-- -- -- -- -- --  List/↘↙· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
-- -- -- -- -- --     (λ _ _ c → eq/ _ _ ∘ _↘↙++↘↙ (↘↙refl c))
-- -- -- -- -- --     (λ a _ _ → eq/ _ _ ∘ (↘↙refl a) ↘↙++↘↙_ )


-- -- -- -- -- --  Iso-↘↙-≡ : ∀ a b → Iso ([ a ]/ ≡ [ b ]/) ∥ a ↘↙ b ∥₁
-- -- -- -- -- --  Iso-↘↙-≡ = isEquivRel→TruncIso ↘↙isEquivRel

-- -- -- -- -- --  ≡→↘↙ : ∀ a b → ([ a ]/ ≡ [ b ]/) →  ∥ a ↘↙ b ∥₁
-- -- -- -- -- --  ≡→↘↙ _ _ = Iso.fun (Iso-↘↙-≡ _ _)


 

-- -- -- -- -- --  -- [_]₂/ : List (Bool × ∥ A ∥₂) → List/↘↙
-- -- -- -- -- --  -- [_]₂/ = {!
-- -- -- -- -- --  --   ∘ ST.map ?!}

-- -- -- -- -- --  NormalForm : List (Bool × A)  → Type ℓ
-- -- -- -- -- --  NormalForm xs = Σ _ λ l → (xs ↓ l) × IsNormalised l
 
-- -- -- -- -- --  NormalForm/ : List/↘↙ → Type ℓ
-- -- -- -- -- --  NormalForm/ g = Σ _ λ l → ([ l ]/ ≡ g) × IsNormalised l

-- -- -- -- -- --  invLi : List (Bool × A) → List (Bool × A)
-- -- -- -- -- --  invLi = rev ∘ Li.map (map-fst not)

-- -- -- -- -- --  invLi++ : ∀ xs ys → invLi (xs ++ ys) ≡
-- -- -- -- -- --                  invLi ys ++ invLi xs
-- -- -- -- -- --  invLi++ xs ys =
-- -- -- -- -- --    sym (cong rev (map++ _ xs ys)) ∙
-- -- -- -- -- --      rev-++ (Li.map _ xs) (Li.map _ ys)
 
-- -- -- -- -- --  invol-invLi : isInvolution invLi
-- -- -- -- -- --  invol-invLi xs =
-- -- -- -- -- --   sym (rev-map-comm (map-fst not) (invLi xs)) ∙
-- -- -- -- -- --     cong (Li.map (map-fst not))
-- -- -- -- -- --       (rev-rev (Li.map (map-fst not) xs))
-- -- -- -- -- --      ∙ map-∘ (map-fst not) (map-fst not) xs ∙
-- -- -- -- -- --      (λ i → Li.map (map-fst (λ x → notnot x i) ) xs) ∙ map-id xs
    

-- -- -- -- -- --  Red-invLi : ∀ xs → Red xs → Red (invLi xs)
-- -- -- -- -- --  Red-invLi .[] red[] = red[]
-- -- -- -- -- --  Red-invLi .(x ∷ (xs ∷ʳ not₁ x)) (cj x xs x₁) =
-- -- -- -- -- --    let z = cj x _ (Red-invLi _ x₁)
-- -- -- -- -- --    in subst Red (cong
-- -- -- -- -- --      (_∷ rev (Li.map (map-fst not) xs) ++ (not (fst x) , snd x) ∷ [])
-- -- -- -- -- --        (sym (not₁not₁ x)) ∙ cong (_∷ʳ (not₁ x))
-- -- -- -- -- --      (sym (invLi++ xs [ not₁ x ])) ) z
-- -- -- -- -- --  Red-invLi .(xs ++ ys) ((xs · ys) x x₁) =
-- -- -- -- -- --    subst Red (sym (invLi++ xs ys))
-- -- -- -- -- --      ((_ · _) (Red-invLi _ x₁) (Red-invLi _ x))

-- -- -- -- -- --  invLi-↓ : ∀ xs ys → xs ↓ ys → invLi xs ↓ invLi ys
-- -- -- -- -- --  invLi-↓ xs .[] (x ↓[]) = Red-invLi _ x ↓[] 
-- -- -- -- -- --  invLi-↓ .(xs ++ x₁ ∷ ys) .(x₁ ∷ _) (_∶_↓∷_ {xs} x {ys} x₁ y) = 
-- -- -- -- -- --    subst (_↓ _) (sym (invLi++ xs (_ ∷ ys)))
-- -- -- -- -- --      (↓++Red (Red-invLi _ x) ((invLi-↓ _ _ y) ↓++↓ (↓refl _)) ) 

-- -- -- -- -- --  invLi-↙↘ : ∀ xs ys → xs ↙↘ ys → (invLi xs) ↙↘ (invLi ys)
-- -- -- -- -- --  invLi-↙↘ xs ys (zs , ↓xs , ↓ys) =
-- -- -- -- -- --    (invLi zs) ,
-- -- -- -- -- --      invLi-↓ _ _ ↓xs , invLi-↓ _ _ ↓ys

-- -- -- -- -- --  Red[XS++invLiXS] : ∀ xs → Red (xs ++ invLi xs)
-- -- -- -- -- --  Red[XS++invLiXS] [] = red[]
-- -- -- -- -- --  Red[XS++invLiXS] (x ∷ xs) =
-- -- -- -- -- --    subst Red (sym (++-assoc [ x ] xs (invLi (x ∷ xs)) ∙
-- -- -- -- -- --          cong (x ∷_) (sym (++-assoc xs (invLi xs) _))))
-- -- -- -- -- --      (cj x _ (Red[XS++invLiXS] xs))
 
-- -- -- -- -- --  XS++invLiXS↓[] : ∀ xs → (xs ++ invLi xs) ↓ []
-- -- -- -- -- --  XS++invLiXS↓[] xs = Red[XS++invLiXS] xs ↓[] 

-- -- -- -- -- --  invLiXS++XS↓[] : ∀ xs → (invLi xs ++ xs) ↓ []
-- -- -- -- -- --  invLiXS++XS↓[] xs = 
-- -- -- -- -- --    subst (λ xs' → (invLi xs ++ xs') ↓ [])
-- -- -- -- -- --       (invol-invLi xs)
-- -- -- -- -- --      (XS++invLiXS↓[] (invLi xs))


-- -- -- -- -- --  invLi-↘↙ : ∀ xs ys → xs ↘↙ ys → (invLi xs) ↘↙ (invLi ys)
-- -- -- -- -- --  invLi-↘↙ xs ys (zs , ↓xs , ↓ys) =
-- -- -- -- -- --    (invLi zs) ,
-- -- -- -- -- --      invLi-↓ _ _ ↓xs , invLi-↓ _ _ ↓ys




-- -- -- -- -- --  List/↘↙GroupStr : GroupStr List/↘↙
-- -- -- -- -- --  GroupStr.1g List/↘↙GroupStr = SQ.[ [] ]
-- -- -- -- -- --  GroupStr._·_ List/↘↙GroupStr = List/↘↙·



-- -- -- -- -- --  GroupStr.inv List/↘↙GroupStr =
-- -- -- -- -- --    SQ.rec squash/ (SQ.[_] ∘ invLi)
-- -- -- -- -- --     λ _ _ → eq/ _ _ ∘ invLi-↘↙ _ _
-- -- -- -- -- --  GroupStr.isGroup List/↘↙GroupStr = makeIsGroup
-- -- -- -- -- --    squash/ (SQ.elimProp3
-- -- -- -- -- --      (λ _ _ _ → squash/ _ _)
-- -- -- -- -- --       λ xs ys zs → cong SQ.[_] (sym (++-assoc xs ys zs)))
-- -- -- -- -- --    (SQ.elimProp
-- -- -- -- -- --      (λ _ → squash/ _ _)
-- -- -- -- -- --      λ xs → cong SQ.[_] (++-unit-r xs))
-- -- -- -- -- --    (SQ.elimProp
-- -- -- -- -- --      (λ _ → squash/ _ _)
-- -- -- -- -- --      λ _ → refl)
-- -- -- -- -- --    (SQ.elimProp
-- -- -- -- -- --      (λ _ → squash/ _ _)
-- -- -- -- -- --      λ xs → eq/ _ _ (↓→↘↙ _ [] (XS++invLiXS↓[] xs)))
-- -- -- -- -- --    (SQ.elimProp
-- -- -- -- -- --      (λ _ → squash/ _ _)
-- -- -- -- -- --      λ xs → eq/ _ _ (↓→↘↙ _ [] (invLiXS++XS↓[] xs)))

-- -- -- -- -- --  List/↘↙Group : Group _
-- -- -- -- -- --  List/↘↙Group = (_ ,  List/↘↙GroupStr)


-- -- -- -- -- --  Red[x,y⁻¹]⇒x≡y : ∀ a a' → Red ((true , a) ∷ [ (false , a') ]) → a ≡ a' 
-- -- -- -- -- --  Red[x,y⁻¹]⇒x≡y a a' r = cons-inj₁ (w _ refl r) 
-- -- -- -- -- --   where
-- -- -- -- -- --   w : ∀ xs → length xs ≡ 2 → Red xs → Li.map snd (init xs) ≡ Li.map snd (tail xs)
-- -- -- -- -- --   w .[] x NormalForm.red[] = refl
-- -- -- -- -- --   w .(x₁ ∷ ([] ∷ʳ not₁ x₁)) x (NormalForm.cj x₁ [] x₂) = refl
-- -- -- -- -- --   w .(x₁ ∷ ((x₃ ∷ xs) ∷ʳ not₁ x₁)) x (NormalForm.cj x₁ (x₃ ∷ xs) x₂) =
-- -- -- -- -- --     ⊥.rec (snotz ((+-comm 1 (length xs) ∙ sym (length++ xs [ not₁ x₁ ]))
-- -- -- -- -- --       ∙ injSuc (injSuc x)))
    
-- -- -- -- -- --   w .([] ++ ys) x (([] NormalForm.· ys) x₁ x₂) = w ys x x₂
-- -- -- -- -- --   w .((x₃ ∷ xs) ++ []) x (((x₃ ∷ xs) NormalForm.· []) x₁ x₂) =
-- -- -- -- -- --      cong ((Li.map snd) ∘ init ∘ (x₃ ∷_)) (++-unit-r xs)
-- -- -- -- -- --       ∙∙ w _ (cong (suc ∘ length) (sym (++-unit-r xs)) ∙ x) x₁
-- -- -- -- -- --       ∙∙ cong (Li.map snd) (sym (++-unit-r xs))
-- -- -- -- -- --   w .((x₃ ∷ []) ++ x₄ ∷ ys) x (((x₃ ∷ []) NormalForm.· (x₄ ∷ ys)) x₁ x₂) =
-- -- -- -- -- --     ⊥.rec (¬Red[len≡1] _ refl x₁)
-- -- -- -- -- --   w .((x₃ ∷ x₅ ∷ xs) ++ x₄ ∷ _) x (((x₃ ∷ x₅ ∷ xs) NormalForm.· ys@(x₄ ∷ _)) x₁ x₂) = ⊥.rec (snotz ((sym (+-suc _ _) ∙ sym (length++ xs ys) ) ∙ injSuc (injSuc x)))


-- -- -- -- -- --  -- List/ₜ↘↙ηIso : A → Iso List/ₜ↘↙ List/ₜ↘↙
-- -- -- -- -- --  -- Iso.fun (List/ₜ↘↙ηIso x) = TQ.rec ([_]/ₜ ∘ ((true , x) ∷_))
-- -- -- -- -- --  --    λ _ _ p → eq/ₜ _ _
-- -- -- -- -- --  --      (((true , x) ∷ fst p) , ((true , x) ∷↓ fst (snd p)) ,
-- -- -- -- -- --  --        ((true , x) ∷↓ (snd (snd p))))
-- -- -- -- -- --  -- Iso.inv (List/ₜ↘↙ηIso x) =
-- -- -- -- -- --  --   TQ.rec ([_]/ₜ ∘ ((false , x) ∷_))
-- -- -- -- -- --  --    λ _ _ p → eq/ₜ _ _
-- -- -- -- -- --  --      (((false , x) ∷ fst p) , ((false , x) ∷↓ fst (snd p)) ,
-- -- -- -- -- --  --        ((false , x) ∷↓ (snd (snd p))))
-- -- -- -- -- --  -- Iso.rightInv (List/ₜ↘↙ηIso x) [ a ]/ₜ =
-- -- -- -- -- --  --   eq/ₜ _ _ (a , Red++↓ (cj (true , x) [] red[]) (↓refl a) , ↓refl a)
-- -- -- -- -- --  -- Iso.rightInv (List/ₜ↘↙ηIso x) (eq/ₜ a b r i) j =
-- -- -- -- -- --  --   {!!}
-- -- -- -- -- --  --   -- TQ.elim (λ a → eq/ₜ _ _ {!!})
-- -- -- -- -- --  --   --  λ a b _ → toPathP {!!}
-- -- -- -- -- --  -- Iso.leftInv (List/ₜ↘↙ηIso x) = {!!}

-- -- -- -- -- --  -- isPropNormalForm : ∀ g → isProp (NormalForm/ [ g ]/)
-- -- -- -- -- --  -- isPropNormalForm g (l , p , n) (l' , p' , n') =
-- -- -- -- -- --  --   {!!}

-- -- -- -- -- --  module isSetA (isSetA : isSet A) where

-- -- -- -- -- --   isSet[𝟚×A] = isOfHLevelList 0 (isSet× isSetBool isSetA)

-- -- -- -- -- --   isPropNormalForm/ : ∀ g → isProp (NormalForm/ g)
-- -- -- -- -- --   isPropNormalForm/ = SQ.elimProp (λ _ → isPropIsProp)
-- -- -- -- -- --     λ xs (l , p , n) (l' , p' , n') →      
-- -- -- -- -- --       let h = λ _ → (isProp× (squash/ _ _) (isPropIsNormalised _))
-- -- -- -- -- --       in PT.rec (isSetΣ isSet[𝟚×A]
-- -- -- -- -- --          (isProp→isSet ∘ h) _ _)
-- -- -- -- -- --               (λ p* → ΣPathPProp h (N↘↙N→≡ _ _ p* n n'))
-- -- -- -- -- --               (≡→↘↙ l l' (p ∙ sym p'))




-- -- -- -- -- --  module _ (_≟_ : Discrete A) where

-- -- -- -- -- --   isSetA = Discrete→isSet _≟_

-- -- -- -- -- --   open isSetA isSetA

-- -- -- -- -- --   IsNormalised⊎HasRedex : ∀ a → IsNormalised a ⊎ HasRedex a
-- -- -- -- -- --   IsNormalised⊎HasRedex a = w _ a (≤-refl (length a)) where
-- -- -- -- -- --    w : ∀ n a → length a ≤ n → IsNormalised a ⊎ HasRedex a
-- -- -- -- -- --    w _ [] _ = inl _
-- -- -- -- -- --    w _ (_ ∷ []) _ =  inl ((λ ()) , tt*)
-- -- -- -- -- --    w (suc n) ((b , a) ∷ xs@((b' , a') ∷ xs')) x  with a ≟ a' | b 𝟚.≟ (not b')
-- -- -- -- -- --    ... | ww | no ¬p =
-- -- -- -- -- --      ⊎.map (¬p ∘ cong fst ,_) inr (w n xs x)
-- -- -- -- -- --    ... | yes p₁ | yes p = inr (inl (ΣPathP (p , p₁)))
-- -- -- -- -- --    ... | no ¬p | yes p = ⊎.map (¬p ∘ cong snd ,_) inr (w n xs x)


-- -- -- -- -- --   discreteA→NormalForm : ∀ xs → NormalForm xs
-- -- -- -- -- --   discreteA→NormalForm xs = w' _ xs (≤-refl (length xs))
   
-- -- -- -- -- --    where
-- -- -- -- -- --    w' : ∀ n a → length a ≤ n → Σ _ λ xs → a ↓ xs × IsNormalised xs
-- -- -- -- -- --    w' _ [] _ = [] , ↓refl [] , tt*
-- -- -- -- -- --    w' (suc n) a x with IsNormalised⊎HasRedex a
-- -- -- -- -- --    ... | inl nrmA = a , ↓refl a , nrmA
-- -- -- -- -- --    ... | inr x₁ =
-- -- -- -- -- --       let (z , u , v) =
-- -- -- -- -- --            w' n (reduce a x₁) (
-- -- -- -- -- --              ≤-trans {suc (length (reduce a x₁))}
-- -- -- -- -- --                {length a} {suc n} (reduce-length-≤ a x₁) x)
-- -- -- -- -- --       in z , ↓trans _ _ _ (↓reduce a x₁) u , v

-- -- -- -- -- --   IsoΣIsNormalisedList/↘↙ : Iso (Σ _ IsNormalised) List/↘↙
-- -- -- -- -- --   Iso.fun IsoΣIsNormalisedList/↘↙ = [_]/ ∘ fst
-- -- -- -- -- --   Iso.inv IsoΣIsNormalisedList/↘↙ =
-- -- -- -- -- --     SQ.rec ((isSetΣ (isOfHLevelList 0 (isSet× isSetBool (Discrete→isSet _≟_)))
-- -- -- -- -- --          (isProp→isSet ∘ isPropIsNormalised)))
-- -- -- -- -- --           (λ xs → _ , snd (snd (discreteA→NormalForm xs)))
-- -- -- -- -- --           λ a b (c , a↓ , b↓) →
-- -- -- -- -- --            ΣPathPProp isPropIsNormalised
-- -- -- -- -- --             (N↘↙N→≡ _ _ --↓→↘↙ _ _ b↓
-- -- -- -- -- --               (↘↙trans _ _ _
-- -- -- -- -- --                 (↘↙trans _ _ _
-- -- -- -- -- --                   (↘↙sym _ _  (↓→↘↙ _ _ (fst (snd (discreteA→NormalForm a)))))
-- -- -- -- -- --                    (↓→↘↙ _ _ a↓))
-- -- -- -- -- --                   (↘↙trans _ _ _ (↘↙sym _ _ (↓→↘↙ _ _ b↓))
-- -- -- -- -- --                 (↓→↘↙ _ _ (fst (snd (discreteA→NormalForm b))))))
-- -- -- -- -- --              (snd (snd (discreteA→NormalForm a)))
-- -- -- -- -- --              (snd (snd (discreteA→NormalForm b))))
-- -- -- -- -- --   Iso.rightInv IsoΣIsNormalisedList/↘↙ =
-- -- -- -- -- --     SQ.elimProp (λ _ → squash/ _ _)
-- -- -- -- -- --      λ a → eq/ _ _ (
-- -- -- -- -- --       ↘↙sym _ _ (↓→↘↙ _ _ (fst (snd (discreteA→NormalForm a)))))
-- -- -- -- -- --   Iso.leftInv IsoΣIsNormalisedList/↘↙ (xs , nrmXs) =
-- -- -- -- -- --    ΣPathPProp isPropIsNormalised
-- -- -- -- -- --     (N↘↙N→≡ _ _ ((↘↙sym _ _ (↓→↘↙ _ _ (fst (snd (discreteA→NormalForm xs))))))
-- -- -- -- -- --      ((snd (snd (discreteA→NormalForm xs)))) nrmXs)


-- -- -- -- -- --   WillReduce? : ∀ b a xs → Dec (WillReduce b a xs)
-- -- -- -- -- --   WillReduce? b a [] = no λ ()
-- -- -- -- -- --   WillReduce? b a (x ∷ xs) = discreteΣ 𝟚._≟_ (λ _ → _≟_) _ _



-- -- -- -- -- --   f∷ : (a : A) (b : Bool) → ((xs , _) : Σ _ IsNormalised) →
-- -- -- -- -- --        Dec (WillReduce b a xs) → Σ _ IsNormalised
-- -- -- -- -- --   f∷ a b (xs , p) (no ¬p) = ((b , a) ∷ xs) , (¬p , p)
-- -- -- -- -- --   f∷ a b (x ∷ xs , p) (yes p₁) = xs , snd p


-- -- -- -- -- --   ∷equiv : ∀ A → Σ _ IsNormalised ≃ Σ _ IsNormalised
-- -- -- -- -- --   ∷equiv a' = isoToEquiv w

-- -- -- -- -- --    where
-- -- -- -- -- --    ri : ∀ b → (a : Σ _ IsNormalised) → ∀ u v → 
-- -- -- -- -- --            fst (f∷ a' (not b) (f∷ a' b a u) v) ≡ fst a
-- -- -- -- -- --    ri b a (no ¬p) (yes p) = refl
-- -- -- -- -- --    ri b (x ∷ fst₁ , snd₁) (yes p) (no ¬p) =
-- -- -- -- -- --     cong (_∷ fst₁) (sym (symIsRedex _ _ p)) 
-- -- -- -- -- --    ri b (x ∷ fst₁ , snd₁) (no ¬p) (no ¬p₁) = ⊥.rec (¬p₁ refl)
-- -- -- -- -- --    ri b ([] , snd₁) (no ¬p) (no ¬p₁) = ⊥.rec (¬p₁ refl)
-- -- -- -- -- --    ri b (x ∷ x₁ ∷ fst₁ , snd₁) (yes p) (yes p₁) =
-- -- -- -- -- --       ⊥.rec (fst snd₁ ((symIsRedex _ _ p) ∙ p₁))   
 
-- -- -- -- -- --    w : Iso (Σ (List (Bool × A)) IsNormalised)
-- -- -- -- -- --          (Σ (List (Bool × A)) IsNormalised)
-- -- -- -- -- --    Iso.fun w xs = f∷ a' true xs (WillReduce? _ _ _)
-- -- -- -- -- --    Iso.inv w xs = f∷ a' false xs (WillReduce? _ _ _)
-- -- -- -- -- --    Iso.rightInv w xs = ΣPathPProp isPropIsNormalised
-- -- -- -- -- --      (ri false xs (WillReduce? false a' _)
-- -- -- -- -- --       (WillReduce? true a' (fst (f∷ a' false xs (WillReduce? _ _ _))))) 
-- -- -- -- -- --    Iso.leftInv w xs =
-- -- -- -- -- --      ΣPathPProp isPropIsNormalised
-- -- -- -- -- --      (ri true xs (WillReduce? true a' _)
-- -- -- -- -- --       (WillReduce? false a' (fst (f∷ a' true xs (WillReduce? _ _ _)))))
  
-- -- -- -- -- --   BuCode : Bouquet A → Type ℓ
-- -- -- -- -- --   BuCode base = Σ _ IsNormalised
-- -- -- -- -- --   BuCode (loop a i) = ua (∷equiv a) i
  
-- -- -- -- -- --   BuPath : List (Bool × A) → Path (Bouquet A) base base
-- -- -- -- -- --   BuPath = foldr (flip _∙_ ∘' uncurry (if_then loop else sym ∘ loop)) refl

-- -- -- -- -- --   encodeBu : ∀ x → base ≡ x → BuCode x
-- -- -- -- -- --   encodeBu x p = subst BuCode p ([] , _) 


-- -- -- -- -- --   decodeBuSq : ∀ a → PathP (λ i → (ua (∷equiv a) i) →
-- -- -- -- -- --                         base ≡ loop a i)
-- -- -- -- -- --                         (BuPath ∘ fst)
-- -- -- -- -- --                         (BuPath ∘ fst)
-- -- -- -- -- --   decodeBuSq a = ua→ (λ (x , y) → w x y (WillReduce? _ _ _))
-- -- -- -- -- --    where

-- -- -- -- -- --    w : ∀ x y → ∀ u → Square
-- -- -- -- -- --                     (BuPath x)
-- -- -- -- -- --                     (BuPath (fst (f∷ a true (x , y) u) ))
-- -- -- -- -- --                     refl
-- -- -- -- -- --                     (loop a)
-- -- -- -- -- --    w [] y (no ¬p) = compPath-filler refl (loop a)
-- -- -- -- -- --    w ((false , snd₁) ∷ xs) y (yes p) =
-- -- -- -- -- --     cong (BuPath xs ∙_) (cong (sym ∘ loop ∘ snd) (sym p))
-- -- -- -- -- --       ◁ symP (compPath-filler _ _)
-- -- -- -- -- --    w ((true , snd₁) ∷ xs) y (yes p) =
-- -- -- -- -- --      ⊥.rec (true≢false (cong fst p))
     
-- -- -- -- -- --    w ((b , snd₁) ∷ xs) y (no ¬p) =
-- -- -- -- -- --      (rUnit _ ∙∙ cong (BuPath ((b , snd₁) ∷ xs) ∙_)
-- -- -- -- -- --        (sym (rCancel (loop a))) ∙∙ assoc _ _ _) ◁ symP (compPath-filler _ _) 

-- -- -- -- -- --   decodeBu : ∀ x → BuCode x → base ≡ x
-- -- -- -- -- --   decodeBu base = BuPath ∘ fst
-- -- -- -- -- --   decodeBu (loop x i) x₁ j = decodeBuSq x i x₁ j


-- -- -- -- -- --   encodeDecode : section (encodeBu base) (decodeBu base)
-- -- -- -- -- --   encodeDecode ([] , snd₁) = ΣPathPProp isPropIsNormalised refl
-- -- -- -- -- --   encodeDecode (x ∷ xs , (p , q)) =
-- -- -- -- -- --    let z = encodeDecode (xs , q)
-- -- -- -- -- --        z' = cong (transp
-- -- -- -- -- --            (λ i →
-- -- -- -- -- --               BuCode
-- -- -- -- -- --               (foldr
-- -- -- -- -- --                (flip _∙_ ∘' uncurry (if_then loop else sym ∘ loop))
-- -- -- -- -- --                (λ _ → base) xs i)) i0) (transportRefl {A = Σ _ IsNormalised}
-- -- -- -- -- --                    ([] , tt*)) ∙ z
-- -- -- -- -- --    in cong (transp
-- -- -- -- -- --       (λ j →
-- -- -- -- -- --          BuCode
-- -- -- -- -- --          ((if fst x then loop else (λ x₁ i → loop x₁ (~ i))) (snd x) j))
-- -- -- -- -- --       i0) z' ∙ uncurry ww x p q 

-- -- -- -- -- --    where
-- -- -- -- -- --    ww : ∀ b a p q → transp
-- -- -- -- -- --       (λ j →
-- -- -- -- -- --          BuCode
-- -- -- -- -- --          ((if b then loop else (λ x₁ i → loop x₁ (~ i))) a j))
-- -- -- -- -- --       i0 (xs , q)
-- -- -- -- -- --       ≡ ((b , a) ∷ xs , p , q)
-- -- -- -- -- --    ww false a p q =
-- -- -- -- -- --      cong₂ (f∷ a false)
-- -- -- -- -- --       (transportRefl (xs , q)) (toPathP (≡no _ p))
-- -- -- -- -- --    ww true a p q = transportRefl _ ∙    
-- -- -- -- -- --     cong (f∷ a true _) (≡no _ p)
 
   
-- -- -- -- -- --   decodeEncodeBu : ∀ x → retract (encodeBu x) (decodeBu x)
-- -- -- -- -- --   decodeEncodeBu x = J (λ x p →
-- -- -- -- -- --     decodeBu x (transp (λ i → BuCode (p i)) i0 ([] , tt*)) ≡ p)
-- -- -- -- -- --      refl

-- -- -- -- -- --   EnDeIso : Iso (Path (Bouquet A) base base) (Σ _ IsNormalised)
-- -- -- -- -- --   Iso.fun EnDeIso = encodeBu base 
-- -- -- -- -- --   Iso.inv EnDeIso = decodeBu base
-- -- -- -- -- --   Iso.rightInv EnDeIso = encodeDecode
-- -- -- -- -- --   Iso.leftInv EnDeIso = decodeEncodeBu base

-- -- -- -- -- --   isGroupoidBouquet : isGroupoid (Bouquet A)
-- -- -- -- -- --   isGroupoidBouquet = elimBouquetProp
-- -- -- -- -- --     (λ _ → isPropΠ λ _ → isPropIsSet)
-- -- -- -- -- --     (elimBouquetProp (λ _ → isPropIsSet)
-- -- -- -- -- --        (isOfHLevelRetractFromIso 2
-- -- -- -- -- --          EnDeIso (isSetΣ isSet[𝟚×A] (isProp→isSet ∘ isPropIsNormalised))))
  
-- -- -- -- -- --   -- GroupStrΣNormalForm : GroupStr (Σ _ IsNormalised)
-- -- -- -- -- --   -- GroupStr.1g GroupStrΣNormalForm =  [] , tt*
-- -- -- -- -- --   -- GroupStr._·_ GroupStrΣNormalForm (xs , _) (ys , _) =
-- -- -- -- -- --   --  _ , snd (snd (discreteA→NormalForm (xs ++ ys))) 
-- -- -- -- -- --   -- GroupStr.inv GroupStrΣNormalForm (xs , _) =
-- -- -- -- -- --   --  _ , snd (snd (discreteA→NormalForm (invLi xs)))
-- -- -- -- -- --   -- GroupStr.isGroup GroupStrΣNormalForm =
-- -- -- -- -- --   --   makeIsGroup
-- -- -- -- -- --   --     (isSetΣ (isOfHLevelList 0 (isSet× isSetBool (Discrete→isSet _≟_)))
-- -- -- -- -- --   --        (isProp→isSet ∘ isPropIsNormalised))
-- -- -- -- -- --   --     (λ (xs , _) (ys , _) (zs , _) →
-- -- -- -- -- --   --       ΣPathPProp isPropIsNormalised
-- -- -- -- -- --   --         (N↘↙N→≡ _ _ {!!}
-- -- -- -- -- --   --            ((snd (snd (discreteA→NormalForm
-- -- -- -- -- --   --             (xs ++ fst (discreteA→NormalForm (ys ++ zs)))))))
-- -- -- -- -- --   --             ((snd (snd (discreteA→NormalForm
-- -- -- -- -- --   --             (fst (discreteA→NormalForm (xs ++ ys)) ++ zs)))))))
-- -- -- -- -- --   --     {!!} {!!}
-- -- -- -- -- --   --     {!!} {!!} 


-- -- -- -- -- --   discreteA→NormalForm/ : ∀ a → NormalForm/ a
-- -- -- -- -- --   discreteA→NormalForm/  =
-- -- -- -- -- --     SQ.elimProp isPropNormalForm/
-- -- -- -- -- --       ((λ (z , u , v) →
-- -- -- -- -- --           z , eq/ _ _ (↘↙sym _ _ (↓→↘↙ _ _ u)) , v)  ∘ discreteA→NormalForm)

-- -- -- -- -- --   discreteList/↘↙ : Discrete List/↘↙
-- -- -- -- -- --   discreteList/↘↙ =
-- -- -- -- -- --     discreteSetQuotients ↘↙isEquivRel
-- -- -- -- -- --       λ a₀ a₁ →
-- -- -- -- -- --         let (n₀ , a₀↓n₀ , isNrmN₀) = discreteA→NormalForm a₀
-- -- -- -- -- --             (n₁ , a₁↓n₁ , isNrmN₁) = discreteA→NormalForm a₁
-- -- -- -- -- --         in mapDec
-- -- -- -- -- --               (λ n₀≡n₁ → n₁ , subst (a₀ ↓_) n₀≡n₁ a₀↓n₀ , a₁↓n₁)
-- -- -- -- -- --               (λ n₀≢n₁ a₀↘↙a₁ → n₀≢n₁ (N↘↙N→≡ _ _
-- -- -- -- -- --                  (↘↙trans _ _ _
-- -- -- -- -- --                     (↘↙trans _ _ _
-- -- -- -- -- --                      (↘↙sym _ _ (↓→↘↙ _ _ a₀↓n₀))
-- -- -- -- -- --                       a₀↘↙a₁) (↓→↘↙ _ _ a₁↓n₁)) isNrmN₀ isNrmN₁))
-- -- -- -- -- --             (discreteList (discreteΣ 𝟚._≟_ (λ _ → _≟_)) n₀ n₁)


-- -- -- -- -- --  module HIT-FG where

-- -- -- -- -- --    open import Cubical.HITs.FreeGroup renaming (rec to recFG ; elimProp to elimPropFG) public

-- -- -- -- -- --    open FG (freeGroupGroup A) η renaming (inv to invFG)  

-- -- -- -- -- --    FG→L/↘↙ : GroupHom (freeGroupGroup A) (_ , List/↘↙GroupStr)
-- -- -- -- -- --    FG→L/↘↙ = recFG ([_]/ ∘ [_] ∘ (true ,_))

-- -- -- -- -- --    open IsGroupHom (snd (FG→L/↘↙))

-- -- -- -- -- --    Red→FG≡ : ∀ a → Red a → fromList a ≡ ε
-- -- -- -- -- --    Red→FG≡ .[] red[] = refl
-- -- -- -- -- --    Red→FG≡ .(x ∷ (xs ∷ʳ not₁ x)) (cj x xs x₁) =
-- -- -- -- -- --          cong (η* x ·fg_) (fromList· xs [ not₁ x ] ∙
-- -- -- -- -- --            cong₂ _·fg_ (Red→FG≡ _ x₁) (·IdR _) ∙ ·IdL _) ∙
-- -- -- -- -- --             redex-ε-η* x (not₁ x) (symIsRedex _ _ refl)
-- -- -- -- -- --    Red→FG≡ .(xs ++ ys) ((xs · ys) x x₁) =
-- -- -- -- -- --      fromList· xs ys
-- -- -- -- -- --        ∙∙ cong₂ _·fg_ (Red→FG≡ _ x) (Red→FG≡ _ x₁)
-- -- -- -- -- --        ∙∙ ·IdL _
  
-- -- -- -- -- --    ↓→FG≡ : (a b : List (Bool × A)) → a ↓ b → fromList a ≡ fromList b
-- -- -- -- -- --    ↓→FG≡ a .[] (x ↓[]) = Red→FG≡ _ x
-- -- -- -- -- --    ↓→FG≡ .(xs ++ x₁ ∷ ys) .(x₁ ∷ _) (_∶_↓∷_ {xs} x {ys} x₁ x₂) =
-- -- -- -- -- --      fromList· xs (x₁ ∷ ys) ∙∙
-- -- -- -- -- --        cong (_·fg fromList (x₁ ∷ ys)) (Red→FG≡ xs x) ∙
-- -- -- -- -- --          ·IdL _ ∙∙ cong (η* x₁ ·fg_) (↓→FG≡ _ _ x₂)

-- -- -- -- -- --    ↘↙→FG≡ : (a b : List (Bool × A)) → a ↘↙ b → fromList a ≡ fromList b
-- -- -- -- -- --    ↘↙→FG≡ a b (c , a↓ , b↓) = ↓→FG≡ a c a↓  ∙ sym (↓→FG≡ b c b↓)

-- -- -- -- -- --    section-FG-L/↘↙ : ∀ a → fst (FG→L/↘↙) (fromList a) ≡ [ a ]/
-- -- -- -- -- --    section-FG-L/↘↙ [] = refl
-- -- -- -- -- --    section-FG-L/↘↙ (x ∷ xs) =
-- -- -- -- -- --       pres· (η* x) (fromList xs) ∙
-- -- -- -- -- --         cong (List/↘↙· (fst FG→L/↘↙ (η* x)))
-- -- -- -- -- --           (section-FG-L/↘↙ xs)  ∙
-- -- -- -- -- --            w x
-- -- -- -- -- --     where
-- -- -- -- -- --     w : ∀ x → List/↘↙· (fst FG→L/↘↙ (η* x)) [ xs ]/ ≡ [ x ∷ xs ]/
-- -- -- -- -- --     w (false , a) = refl
-- -- -- -- -- --     w (true , a) = refl

-- -- -- -- -- --    fromL/ : List/↘↙ → _
-- -- -- -- -- --    fromL/ = SQ.rec trunc fromList ↘↙→FG≡

-- -- -- -- -- --    fromL/pres· : ∀ a b → fromL/ (List/↘↙· a b) ≡ fromL/ a ·fg fromL/ b 
-- -- -- -- -- --    fromL/pres· = SQ.elimProp2 (λ _ _ → trunc _ _) fromList·

-- -- -- -- -- --    fromL/presinv : ∀ xs →
-- -- -- -- -- --         fromL/ (GroupStr.inv List/↘↙GroupStr xs) ≡
-- -- -- -- -- --        invFG (fromL/ xs)
-- -- -- -- -- --    fromL/presinv = SQ.elimProp (λ _ → trunc _ _) w
-- -- -- -- -- --     where
-- -- -- -- -- --     open GroupTheory (freeGroupGroup A)

-- -- -- -- -- --     w' : ∀ x → fromL/ [ [ not₁ x ] ]/ ≡ invFG (η* x)
-- -- -- -- -- --     w' (false , a) = ·IdR _ ∙ sym (invInv _)
-- -- -- -- -- --     w' (true , a) = ·IdR _
   
-- -- -- -- -- --     w : (xs : List (Bool × A)) →
-- -- -- -- -- --        fromL/ [ invLi xs ]/ ≡ invFG (fromL/ [ xs ]/)
-- -- -- -- -- --     w [] = sym inv1g
-- -- -- -- -- --     w (x ∷ xs) = 
-- -- -- -- -- --          (fromL/pres· ([ invLi xs ]/) [ [ not₁ x ] ]/ ∙
-- -- -- -- -- --              cong (fromL/ [ invLi xs ]/ ·fg_) (w' x))
-- -- -- -- -- --           ∙∙ cong (_·fg invFG (η* x)) (w xs) ∙∙  sym (invDistr _ _) 
  
-- -- -- -- -- --    retract-FG-L/↘↙ : ∀ b →  fromL/ (fst (FG→L/↘↙) b) ≡ b
-- -- -- -- -- --    retract-FG-L/↘↙ =
-- -- -- -- -- --      elimPropFG (λ _ → trunc _ _)
-- -- -- -- -- --        (λ _ → ·IdR _)
-- -- -- -- -- --        (λ g1 g2 p1 p2 →
-- -- -- -- -- --          cong fromL/ (pres· g1 g2) ∙
-- -- -- -- -- --            fromL/pres· (fst (FG→L/↘↙) g1) (fst (FG→L/↘↙) g2) ∙
-- -- -- -- -- --             cong₂ _·fg_ p1 p2)
-- -- -- -- -- --        refl
-- -- -- -- -- --        λ g p → cong fromL/ (presinv g) ∙
-- -- -- -- -- --           fromL/presinv (fst (FG→L/↘↙) g) ∙ cong invFG p 

-- -- -- -- -- --    GroupIso-FG-L/↘↙ : GroupIso (freeGroupGroup A) (_ , List/↘↙GroupStr)
-- -- -- -- -- --    Iso.fun (fst GroupIso-FG-L/↘↙) = _
-- -- -- -- -- --    Iso.inv (fst GroupIso-FG-L/↘↙) = fromL/
    
-- -- -- -- -- --    Iso.rightInv (fst GroupIso-FG-L/↘↙) =
-- -- -- -- -- --      SQ.elimProp (λ _ → squash/ _ _)
-- -- -- -- -- --       section-FG-L/↘↙
-- -- -- -- -- --    Iso.leftInv (fst GroupIso-FG-L/↘↙) = retract-FG-L/↘↙
-- -- -- -- -- --    snd GroupIso-FG-L/↘↙ = snd FG→L/↘↙

   

-- -- -- -- -- --    isInjective-η : ∀ a a' → η a ≡ η a' → ∥ a ≡ a' ∥₁
-- -- -- -- -- --    isInjective-η a a' p =
-- -- -- -- -- --      PT.map ((cong  snd  ∘ cons-inj₁) ∘ (λ p → N↘↙N→≡ [ true , a ] [ true , a' ]
-- -- -- -- -- --                p ((λ ()) , tt*) ((λ ()) , tt*)))
-- -- -- -- -- --            (≡→↘↙ _ _ (invEq (congEquiv
-- -- -- -- -- --              (isoToEquiv (invIso (fst (GroupIso-FG-L/↘↙)))))
-- -- -- -- -- --               (·IdR _ ∙∙ p ∙∙ sym (·IdR _))))

-- -- -- -- -- --  ↘↙Nrm⇒↓Nrm : ∀ xs ys → IsNormalised ys → xs ↘↙ ys → xs ↓ ys
-- -- -- -- -- --  ↘↙Nrm⇒↓Nrm xs ys nrmYs (zs , xs↓ , ys↓) =
-- -- -- -- -- --    subst (xs ↓_) (sym (minimalNormalised ys zs nrmYs ys↓)) xs↓

 

              
-- -- -- -- -- --  open HIT-FG

-- -- -- -- -- --  module _ (isSetA : isSet A) where
  

-- -- -- -- -- --   isContrNormalForm/⇒discreteA : 
-- -- -- -- -- --      (∀ a → isContr (NormalForm/ a))
-- -- -- -- -- --      → Discrete A
-- -- -- -- -- --   isContrNormalForm/⇒discreteA nf a a' =
-- -- -- -- -- --    let ((xs , u , v) , _) = nf ([ (true , a) ∷ [ (false , a') ] ]/)
-- -- -- -- -- --    in PT.rec (isPropDec (isSetA _ _))
-- -- -- -- -- --      (λ u → w' xs ((↘↙Nrm⇒↓Nrm _ _ v (↘↙sym _ _ u)))
-- -- -- -- -- --           (↓⇒length≥ (↘↙Nrm⇒↓Nrm _ _ v ((↘↙sym _ _ u)))) v) (≡→↘↙  _ _ u)
-- -- -- -- -- --    where
-- -- -- -- -- --     w' : ∀ xs → 
-- -- -- -- -- --           ((true , a) ∷ [ (false , a') ]) ↓ xs → length xs ≤ 2 
-- -- -- -- -- --           → IsNormalised xs → Dec (a ≡ a')
-- -- -- -- -- --     w' [] (x₁ ↓[]) _ x = yes (Red[x,y⁻¹]⇒x≡y _ _ x₁)
-- -- -- -- -- --     w' ((false , snd₁) ∷ []) x₁ _ x =
-- -- -- -- -- --       ⊥.rec (
-- -- -- -- -- --          znots (cong (Int.abs ∘ winding ∘ fromL/) (eq/ _ _ (↓→↘↙ _ _ x₁) )))
-- -- -- -- -- --     w' ((true , snd₁) ∷ []) x₁ _ x = 
-- -- -- -- -- --       ⊥.rec (
-- -- -- -- -- --          znots (cong (Int.abs ∘ winding ∘ fromL/) (eq/ _ _ (↓→↘↙ _ _ x₁) )))
-- -- -- -- -- --     w' (x₂ ∷ x₃ ∷ []) x₁ _ x = no λ p → fst x
-- -- -- -- -- --       let p' = ↓EqualLengths⇒≡  x₁ refl
-- -- -- -- -- --       in subst2 IsRedex (cons-inj₁ p') (cons-inj₁ (cong tail p'))
-- -- -- -- -- --              (cong (true ,_) p)
-- -- -- -- -- --     w' (x₂ ∷ x₃ ∷ x₄ ∷ xs) x₁ ()

-- -- -- -- -- --   isContrNormalForm/⇔discreteA :
-- -- -- -- -- --     ⟨ ((∀ a → isContr (NormalForm/ a))
-- -- -- -- -- --         , (isPropΠ (λ _ → isPropIsContr)))
-- -- -- -- -- --       L.⇔ Discrete A , isPropDiscrete ⟩
-- -- -- -- -- --   fst isContrNormalForm/⇔discreteA =
-- -- -- -- -- --     isContrNormalForm/⇒discreteA
-- -- -- -- -- --   snd isContrNormalForm/⇔discreteA (_≟_) a =
-- -- -- -- -- --     discreteA→NormalForm/ _≟_ a ,
-- -- -- -- -- --       isSetA.isPropNormalForm/ isSetA _ _
 

-- -- -- -- -- --  -- discreteA→NormalForm : Discrete A → ∀ a → NormalForm/ a
-- -- -- -- -- --  -- discreteA→NormalForm _≟_ =
-- -- -- -- -- --  --   SQ.elimProp isPropNormalForm/
-- -- -- -- -- --  --     λ a →
-- -- -- -- -- --  --       let (z , u , v) = w' _ a (≤-refl (length a))
-- -- -- -- -- --  --       in z , eq/ _ _ u , ∣ v ∣₁

-- -- -- -- -- --  --  where
-- -- -- -- -- --  --  w : ∀ n a → length a ≤ n → IsNormalised a ⊎ HasRedex a
-- -- -- -- -- --  --  w _ [] _ = inl _
-- -- -- -- -- --  --  w _ (_ ∷ []) _ =  inl ((λ ()) , tt*)
-- -- -- -- -- --  --  w (suc n) ((b , a) ∷ xs@((b' , a') ∷ xs')) x  with a ≟ a' | b 𝟚.≟ (not b')
-- -- -- -- -- --  --  ... | ww | no ¬p =
-- -- -- -- -- --  --    ⊎.map (¬p ∘ cong fst ,_) inr (w n xs x)
-- -- -- -- -- --  --  ... | yes p₁ | yes p = inr (inl (ΣPathP (p , p₁)))
-- -- -- -- -- --  --  ... | no ¬p | yes p = ⊎.map (¬p ∘ cong snd ,_) inr (w n xs x)


-- -- -- -- -- --  --  w' : ∀ n a → length a ≤ n → Σ _ λ xs → xs ↘↙ a × IsNormalised xs
-- -- -- -- -- --  --  w' _ [] _ = [] , ↘↙refl [] , tt*
-- -- -- -- -- --  --  w' (suc n) a x with w (suc n) a x
-- -- -- -- -- --  --  ... | inl nrmA = a , ↘↙refl a , nrmA
-- -- -- -- -- --  --  ... | inr x₁ =
-- -- -- -- -- --  --     let (z , u , v) =
-- -- -- -- -- --  --          w' n (reduce a x₁) (
-- -- -- -- -- --  --            ≤-trans {suc (length (reduce a x₁))}
-- -- -- -- -- --  --              {length a} {suc n} (reduce-length-≤ a x₁) x)
-- -- -- -- -- --  --     in z , ↘↙trans _ _ _ u (↘↙sym _ _ (↓→↘↙ _ _ (↓reduce a x₁))) , v
   
  
