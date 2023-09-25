{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.NormalFormIndexedPrim where

-- open import Cubical.HITs.FreeGroup.Base renaming (assoc to ·assoc)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

-- open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
-- open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Functions.Involution

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
import Cubical.Data.Fin as Fin

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/₂_ ; [_] to [_]/)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base


private
  variable
    ℓ : Level

module _ {A : Type ℓ} where

 ++=[] : ∀ (xs ys : List A) → xs ++ ys ≡ [] → ys ≡ [] 
 ++=[] [] ys x = x
 ++=[] (x₁ ∷ xs) ys x = ⊥.rec (¬cons≡nil x)

 pop : List A → List A 
 pop [] = []
 pop (x ∷ []) = []
 pop (x ∷ xs@(_ ∷ _)) = x ∷ pop xs

 tail : List A → List A
 tail [] = []
 tail (x ∷ xs) = xs

 pop-red-lem : ∀ (x : A) xs → ¬ (xs ≡ []) → (x ∷ pop xs) ≡ (pop (x ∷ xs))
 pop-red-lem x [] x₁ = ⊥.rec (x₁ refl)
 pop-red-lem x (x₂ ∷ xs) x₁ = refl

 pop∷ʳ : ∀ x xs → pop (xs ∷ʳ x) ≡ xs
 pop∷ʳ x [] = refl
 pop∷ʳ x (x₁ ∷ []) = refl
 pop∷ʳ x (x₁ ∷ x₂ ∷ xs) = cong (x₁ ∷_) (pop∷ʳ x (x₂ ∷ xs))

 pop++ : ∀ x xs ys → xs ++ pop (x ∷ ys) ≡ pop (xs ++ x ∷ ys) 
 pop++ x [] ys = refl
 pop++ x (x₁ ∷ []) ys = refl
 pop++ x (x₁ ∷ x₂ ∷ xs) ys =
  cong (x₁ ∷_) (pop++ x (x₂ ∷ xs) ys)

 length≡0→≡[] : ∀ (xs : List A) → length xs ≡ 0 → xs ≡ []
 length≡0→≡[] [] x = refl
 length≡0→≡[] (x₁ ∷ xs) x = ⊥.rec (snotz x)
 
module NormalForm (A : Type ℓ) where


 IsRedex : Bool × A → Bool × A → Type ℓ
 IsRedex (b , x) (b' , x') = (b ≡ not b') × (x ≡ x')

 symIsRedex : ∀ x y → IsRedex x y → IsRedex y x
 symIsRedex x y (u , v) = (sym (notnot _) ∙ sym (cong not u) , sym v)
 
 WillReduce : Bool → A → (xs : List (Bool × A)) → Type ℓ
 WillReduce _ _ [] = ⊥* 
 WillReduce b x (h ∷ _) = IsRedex (b , x) h

 WillReduceʳ : Bool → A → (xs : List (Bool × A)) → Type ℓ
 WillReduceʳ _ _ [] = ⊥*
 WillReduceʳ b x (h' ∷ []) = IsRedex (b , x) h'
 WillReduceʳ b x (_ ∷ xs@(_ ∷ _)) = WillReduceʳ b x xs

   

 HeadIsRedex : List (Bool × A) → Type ℓ
 HeadIsRedex [] = ⊥*
 HeadIsRedex ((b , a) ∷ xs) = WillReduce b a xs

 IsNormalised : List (Bool × A) → Type ℓ
 IsNormalised [] = Unit*
 IsNormalised ((b , x) ∷ xs) = (¬ WillReduce b x xs)  × IsNormalised xs

 WillReduce∷ʳ : ∀ x x' xs → WillReduce (fst x) (snd x) xs →
                 WillReduce (fst x) (snd x) (xs ∷ʳ x')
 WillReduce∷ʳ x x' (x₂ ∷ xs) x₁ = x₁


 WillReduceʳ∷ : ∀ x x' xs → WillReduceʳ (fst x) (snd x) xs →
                 WillReduceʳ (fst x) (snd x) (x' ∷ xs)
 WillReduceʳ∷ _ _ (_ ∷ _) x = x

 WillReduceʳ[∷ʳ] : ∀ b a xs x →
   WillReduceʳ b a (xs ∷ʳ x) →
   IsRedex (b , a) x
 WillReduceʳ[∷ʳ] b a [] x p = p
 WillReduceʳ[∷ʳ] b a (x₂ ∷ []) x p = p
 WillReduceʳ[∷ʳ] b a (_ ∷ xs@(_ ∷ _)) =
   WillReduceʳ[∷ʳ] b a xs


 WillReduce++ʳ : ∀ {x xs ys} → WillReduce (fst x) (snd x) xs →
                 WillReduce (fst x) (snd x) (xs ++ ys)
 WillReduce++ʳ {xs = _ ∷ _} u = u

 WillReduceʳ++ : ∀ {x xs ys} → WillReduceʳ (fst x) (snd x) ys →
                 WillReduceʳ (fst x) (snd x) (xs ++ ys)
 WillReduceʳ++ {xs = []} u = u
 WillReduceʳ++ {x'} {xs = x ∷ xs} {ys} u =
   WillReduceʳ∷ x' _ (xs ++ ys) (WillReduceʳ++ {xs = xs} {ys} u)

 CasesWillReduce++ : ∀ x xs ys → Type ℓ
 CasesWillReduce++ x xs ys =
   ((xs ≡ []) × WillReduce (fst x) (snd x) ys)
     ⊎ WillReduce (fst x) (snd x) xs

 casesWillReduce++ : ∀ x xs ys → WillReduce (fst x) (snd x) (xs ++ ys)
   → CasesWillReduce++ x xs ys
 casesWillReduce++ x [] ys q = inl (refl , q)
 casesWillReduce++ x (x₁ ∷ xs) ys q = inr q

 CasesWillReduceʳ++ : ∀ x xs ys → Type ℓ
 CasesWillReduceʳ++ x xs ys =
   ((ys ≡ []) × WillReduceʳ (fst x) (snd x) xs)
     ⊎ WillReduceʳ (fst x) (snd x) ys
-- snocView
 -- casesWillReduceʳ++' : ∀ x xs ys → WillReduceʳ (fst x) (snd x) (xs ++ ys)
 --   → SnocView ys → CasesWillReduceʳ++ x xs ys
 -- casesWillReduceʳ++' x xs .[] x₁ nil = {!!}
 -- casesWillReduceʳ++' x xs .(xs₁ ∷ʳ x₂) x₁ (snoc x₂ xs₁ x₃) = {!!}
 
 -- casesWillReduceʳ++ : ∀ x xs ys → WillReduceʳ (fst x) (snd x) (xs ++ ys)
 --   → CasesWillReduceʳ++ x xs ys
 -- casesWillReduceʳ++ = {!!}
  

 IsNormalised∷ᵣ : ∀ x xs → IsNormalised (xs ∷ʳ x) → IsNormalised xs 
 IsNormalised∷ᵣ x [] x₁ = tt*
 IsNormalised∷ᵣ x (x₂ ∷ xs) x₁ =
   fst x₁ ∘ WillReduce∷ʳ _ _ _  , IsNormalised∷ᵣ x xs (snd x₁)

 IsNormalised++ : ∀ xs ys → IsNormalised (xs ++ ys) →
      IsNormalised xs × IsNormalised ys
 IsNormalised++ [] ys x = _ , x
 IsNormalised++ (x₁ ∷ xs) ys (u , v) = 
  let (u' , v')  = IsNormalised++ xs ys v
  in (u ∘  WillReduce++ʳ , u') , v'

 HasRedex : List (Bool × A) → Type ℓ
 HasRedex [] = ⊥*
 HasRedex xs@(_ ∷ xs') = HeadIsRedex xs ⊎ HasRedex xs'



 ¬HasRedex[x] : ∀ x → ¬ HasRedex [ x ] 
 ¬HasRedex[x] x (inl ())
 ¬HasRedex[x] x (inr ())

 HasRedex∷ʳ : ∀ xs x → HasRedex xs → HasRedex (xs ∷ʳ x) 
 HasRedex∷ʳ (x₂ ∷ xs) x (inr x₁) =
   inr (HasRedex∷ʳ xs x x₁)
 HasRedex∷ʳ (x₂ ∷ x₃ ∷ xs) x (inl x₁) =
   inl x₁


 HasRedex++ : ∀ xs ys → HasRedex xs → HasRedex (xs ++ ys)  
 HasRedex++ (x₁ ∷ xs) ys (inr x) = inr (HasRedex++ xs ys x)
 HasRedex++ (x₁ ∷ x₂ ∷ xs) ys (inl x) = inl x

 ++HasRedex : ∀ xs ys → HasRedex ys → HasRedex (xs ++ ys)  
 ++HasRedex [] ys x = x
 ++HasRedex (x₁ ∷ xs) ys x =
   inr (++HasRedex xs ys x)
 
 reduce : ∀ xs → HasRedex xs → List (Bool × A)
 reduce (x ∷ xs) (inr u) = x ∷ reduce xs u
 reduce (_ ∷ _ ∷ xs) (inl x) = xs

 reduce++ : ∀ xs ys hr → reduce _ (HasRedex++ xs ys hr) ≡ reduce _ hr ++ ys
 reduce++ (x ∷ xs) ys (inr x₁) = cong (x ∷_) (reduce++ xs ys x₁)
 reduce++ (x ∷ x₂ ∷ xs) ys (inl x₁) = refl

 ++reduce : ∀ xs ys hr → reduce _ (++HasRedex xs ys hr) ≡ xs ++ reduce _ hr
 ++reduce [] ys hr = refl
 ++reduce (x ∷ xs) ys hr = cong (x ∷_) (++reduce xs ys hr)


 reduceLength : ∀ xs hr → 2 + length (reduce xs hr) ≡ length xs 
 reduceLength (_ ∷ xs) (inr u) =
   cong  suc (reduceLength xs u)
 reduceLength (_ ∷ _ ∷ _) (inl _) = refl

 IsNormalised→¬HaseRedex : ∀ xs → IsNormalised xs → ¬ HasRedex xs
 IsNormalised→¬HaseRedex (x₂ ∷ x₃ ∷ xs) x (inl x₁) = fst x x₁
 IsNormalised→¬HaseRedex (x₂ ∷ xs) x (inr x₁) = 
   IsNormalised→¬HaseRedex _ (snd x) x₁ 
 
 -- infixr 5 _∷_ 


 not₁ : (Bool × A) → (Bool × A)
 not₁ = map-fst not

 not₁not₁ : ∀ x → not₁ (not₁ x) ≡ x 
 not₁not₁ (x , y) = cong (_, y) (notnot x) 

 
 WillReduceʳ++' : ∀ b a xs x₃ ys →
  WillReduceʳ b a (xs ++ x₃ ∷ ys) →  WillReduceʳ b a (x₃ ∷ ys)
 WillReduceʳ++' b a [] x₃ ys x = x
 WillReduceʳ++' b a (x₁ ∷ []) x₃ ys x = x
 WillReduceʳ++' b a (x₁ ∷ x₂ ∷ xs) x₃ ys x =
    WillReduceʳ++' b a (x₂ ∷ xs) x₃ ys x
   
 data Red : (List (Bool × A)) → Type ℓ where
  red[] : Red []
  cj : ∀ x → ∀ xs → Red xs →  Red (x ∷ (xs ∷ʳ not₁ x) )
  _·_ : ∀ xs ys → Red xs → Red ys → Red (xs ++ ys)

 HasRedexSplitCases++ : (xs : List (Bool × A)) → (ys : List (Bool × A)) →
   HasRedex (xs ++ ys) → Type ℓ
 HasRedexSplitCases++ xs ys hrx =
   ((Σ _ λ rxXs → reduce xs rxXs ++ ys ≡ reduce _ hrx)
      ⊎ (Σ _ λ rxYs → xs ++ reduce ys rxYs ≡ reduce _ hrx)) ⊎
     ((reduce _ hrx ≡ pop xs ++ tail ys) ×
            Σ (Bool × A) λ (b , a) →
          WillReduceʳ (not b) a xs ×
            WillReduce b a ys)

 reduceHead : ∀ x ys u → reduce (x ∷ ys) (inl u) ≡ tail ys
 reduceHead x (x₁ ∷ ys) u = refl
 
 hasRedexSplitCases++ : ∀ xs ys hr →
    HasRedexSplitCases++ xs ys hr
 hasRedexSplitCases++ [] ys hr = inl (inr (hr , refl))
 hasRedexSplitCases++ (x ∷ xs) ys (inr u) =
   ⊎.map (⊎.map (λ v → inr (fst v) , cong (x ∷_) (snd v))
         (λ (v , q) → v , cong (x ∷_) q))
      (λ (p , (a , b) , u , v) →
          (cong (x ∷_) p ∙ cong (_++ (tail ys))
           (pop-red-lem x xs
            (lower ∘ flip (subst (WillReduceʳ (not a) b)) u))) ,
              (a , b) , WillReduceʳ∷ (not a , b) x xs u , v)
     (hasRedexSplitCases++ xs ys u)

 hasRedexSplitCases++ (x ∷ []) ys (inl u) =
   inr (reduceHead x ys u , _ , (refl , refl) , u)
 hasRedexSplitCases++ (x ∷ x₂ ∷ xs) ys (inl u) =
   inl (inl (inl u , refl))

 RedWillReduceView : ∀ b a ys → Red ys → WillReduce b a ys →
      Σ ((Σ _ Red) × (Σ _ Red))
        λ ((rl , _) , (rr , _)) →
           rl ++ [ b , a ] ++ rr ≡ tail ys
 RedWillReduceView b a .(x ∷ (xs ∷ʳ _)) (cj x xs x₃) x₁ =
   ((_ , x₃) , (_ , red[])) , cong (xs ∷ʳ_) (ΣPathP x₁)
 RedWillReduceView b a .([] ++ ys) (([] · ys) x x₂) x₁ =
   RedWillReduceView b a ys x₂ x₁
 RedWillReduceView b a .((_ ∷ _) ++ ys) ((xs@(_ ∷ _) · ys) x x₂) x₁ =
   let (((rl , rlR) , (rr , rrR)) , p) = RedWillReduceView b a xs x x₁ 
   in ((_ , rlR) , (_ , (_ · _) rrR x₂)) ,
     sym (++-assoc rl _ _) ∙ cong (_++ ys) p

 RedWillReduceʳView : ∀ b a ys → Red ys → WillReduceʳ b a ys →
      Σ ((Σ _ Red) × (Σ _ Red))
        λ ((rl , _) , (rr , _)) →
           rl ++ [ b , a ] ++ rr ≡ pop ys
 RedWillReduceʳView b a .(x ∷ (xs ∷ʳ not₁ x)) (cj x xs x₂) x₁ =
   ((_ , red[]) , (_ , x₂)) , cong (_∷ xs) (ΣPathP
     (WillReduceʳ[∷ʳ] b  a (x ∷ xs) (not₁ x) x₁) ∙
      not₁not₁ _) ∙ sym (pop∷ʳ (not₁ x) (x ∷ xs))
 RedWillReduceʳView b a .(xs ++ []) ((xs · []) x x₂) x₁ =
  let z = RedWillReduceʳView b a xs x (subst (WillReduceʳ b a) (++-unit-r xs) x₁)
  in map-snd (_∙ cong pop (sym (++-unit-r xs))) z 
 RedWillReduceʳView b a .(xs ++ _ ∷ _) ((xs · ys@(_ ∷ _)) x x₂) x₁ =
  let (((rl , rlR) , (rr , rrR)) , p) = RedWillReduceʳView b a ys x₂
        (WillReduceʳ++' b a xs _ _ x₁) 
  in ((_ , (_ · _) x rlR) , (_ , rrR)) ,
    ++-assoc xs rl _ ∙ cong (xs ++_) p ∙
     pop++ _ _ _




 HasRedexSplitCases∷ : ∀ x x' →
      (xs : List (Bool × A)) → HasRedex (x ∷ (xs ∷ʳ x')) → Type ℓ
 HasRedexSplitCases∷ (b , a) (b' , a') xs hr =
   ((WillReduce b a xs × (reduce _ hr ≡ (tail xs ∷ʳ (b' , a'))))
     ⊎ (WillReduceʳ b' a' xs × (reduce _ hr ≡ ((b , a) ∷ pop xs))))
    ⊎ ((Σ _ λ rdxs → (b , a) ∷ (reduce xs rdxs ∷ʳ (b' , a')) ≡ reduce _ hr  )
     ⊎ (reduce _ hr ≡ []))


 hasRedexSplitCases∷ : ∀ x x' xs hr → HasRedexSplitCases∷ x x' xs hr
 hasRedexSplitCases∷ x x' [] (inl _) =
  inr (inr refl)
 hasRedexSplitCases∷ x x' [] (inr u) =
  ⊎.rec (⊥.rec ∘ lower) (⊥.rec ∘ lower) u
 hasRedexSplitCases∷ x x' (x'' ∷ xs) (inl u) =
    inl (inl (u , refl))
 hasRedexSplitCases∷ x x' (x'' ∷ []) (inr (inl u)) =
   inl (inr (symIsRedex _ _ u , refl))
 hasRedexSplitCases∷ x x' (x'' ∷ []) (inr (inr u)) =
   ⊎.rec (⊥.rec ∘ lower) (⊥.rec ∘ lower) u
   
 hasRedexSplitCases∷ x x' (x'' ∷ xs@(x* ∷ xs')) (inr u) =
   ⊎.rec (⊎.rec
         (λ (l , m) →
           inr (inl (inl l , sym (cong (x ∷_) m))))
         λ (l , m) →
           inl (inr (l , (cong (x ∷_) m))))
      (⊎.rec (λ (rdx , p) →
           inr (inl ((inr rdx) , cong (x ∷_) p)))
        λ p → ⊥.rec (snotz
          ((+-comm 1 (length xs') ∙ sym (length++ xs' [ _ ])) ∙ (injSuc (injSuc ( sym (reduceLength _ u)))) ∙ cong length p)))
     (hasRedexSplitCases∷ x'' x' xs u)

 reduceRed : ∀ xs hr → Red xs → Red (reduce xs hr)
 reduceRed .(x ∷ (xs ∷ʳ not₁ x)) hr (cj x xs x₁) with (hasRedexSplitCases∷ x (not₁ x) xs hr)
 ... | inl (inl (wr , p)) =
   let (((rl' , rlR') , (rr' , rrR')) , p') =
         RedWillReduceView _ _ _ x₁ wr
   in subst Red (sym (++-assoc rl' _ _) ∙∙ cong (_∷ʳ (not₁ x)) p' ∙∙ sym p)
         ((_ · _) rlR' (cj x _ rrR'))
 ... | inl (inr (wr , p)) =
   let (((rl' , rlR') , (rr' , rrR')) , p') =
         RedWillReduceʳView _ _ _ x₁ wr
   in subst Red (++-assoc (x ∷ rl') [ not₁ x ] _ ∙∙ cong (x ∷_) p' ∙∙ sym p)
           ((_ · _)  (cj x _ rlR') rrR')
 ... | inr (inl (hr , p)) =
        subst Red p (cj x _ (reduceRed xs hr x₁))
       
 ... | inr (inr p) = subst Red (sym p) red[]
 reduceRed .(xs ++ ys) hr ((xs · ys) x x₁) with (hasRedexSplitCases++ xs ys hr)
 ... | inl (inl (x₂ , q)) =
   let z = reduceRed xs x₂ x
       z' = (_ · _) z x₁ 
   in subst Red q z'
 ... | inl (inr (x₂ , q)) =
   let z = reduceRed ys x₂ x₁
         
    in subst Red q ((_ · _) x z)
 ... | inr (p* , (b , a) , rX , rY) =
   let (((rl , rlR) , (rr , rrR)) , p) = RedWillReduceʳView (not b) a xs x rX 
       (((rl' , rlR') , (rr' , rrR')) , p') = RedWillReduceView b a ys x₁ rY
       z = (_ · _) ((_ · _) rlR
              (cj ((not b , a)) _ ((_ · _) rrR rlR'))) rrR'
   in subst Red ((
         (λ i → (rl ++ ((not b , a) ∷
           (++-assoc rr  rl' [ not₁not₁ (b , a) i ] i))) ++ rr')
           ∙∙ cong (_++ rr') (sym (++-assoc rl ((not b , a) ∷ rr)
            (rl' ++ [ b , a ])))
              ∙
            ++-assoc (rl ++ (not b , a) ∷ rr) _ _ ∙
             cong ((rl ++ (not b , a) ∷ rr) ++_)
              (++-assoc rl' _ _) ∙∙ cong₂ _++_ p p') ∙ sym p*) z


 reduce-HasRedex∷ʳ : ∀ x₁ xs₁ r' x → reduce (x₁ ∷ xs₁) r' ∷ʳ not₁ x ≡
      reduce ((x₁ ∷ xs₁) ∷ʳ not₁ x)
      (HasRedex∷ʳ ((fst x₁ , snd x₁) ∷ xs₁) (not₁ x) r')
 reduce-HasRedex∷ʳ x₁ (x₃ ∷ xs₁) (inl x₂) x = refl
 reduce-HasRedex∷ʳ x₁ (x₃ ∷ xs₁) (inr x₂) x = 
     cong (x₁ ∷_)
        (reduce-HasRedex∷ʳ x₃ xs₁ x₂ _)
 
 Red⇒HasRedex : ∀ xs → 0 < length xs → Red xs → Σ _ λ hr → Red (reduce xs hr) 
 Red⇒HasRedex .(x ∷ ([] ∷ʳ not₁ x)) _ (cj x [] r) = 
   inl (symIsRedex _ _ (refl , refl)) , red[]
 Red⇒HasRedex .(x ∷ ((_ ∷ _) ∷ʳ not₁ x)) _ (cj x xs@(_ ∷ _) r) =
   let (r' , p) = Red⇒HasRedex xs _ r
   in inr (HasRedex∷ʳ _ _ r') , subst Red (cong (x ∷_) (reduce-HasRedex∷ʳ _ _ r' _)) (cj x _ p)
 Red⇒HasRedex .(xs ++ []) q ((xs · []) rX rY) = 
   subst (λ xs → Σ _ λ hr → Red (reduce xs hr)) (sym (++-unit-r xs))
     (Red⇒HasRedex _ (subst (λ xs → 0 < length xs) (++-unit-r xs) q) rX)
 Red⇒HasRedex .(xs ++ x ∷ ys) q ((xs · (x ∷ ys)) rX rY) = 
   let (r' , p) = Red⇒HasRedex _ _ rY
   in ++HasRedex _ _ r' ,
      subst Red (sym (++reduce xs (x ∷ ys) r')) ((_ · _) rX p)


 reduce-length-≤ : ∀ x ys rdx → length (reduce (x ∷ ys) rdx) ≤ length ys
 reduce-length-≤ x ys rdx =
   <-weaken {m = length (reduce (x ∷ ys) rdx)}
    (≡→≤ (injSuc (reduceLength _ rdx)))

 reduce-length-≤' : ∀ ys rdx → length (reduce (ys) rdx) < length ys
 reduce-length-≤' (x ∷ ys) rdx = reduce-length-≤ x ys rdx

 inferRed' : ∀ n xs ys → length ys ≤ n → ∀ zs
             → Red (xs ++ ys ++ zs)
             → Red ys
             → Red (xs ++ zs)
 inferRed' n xs [] x zs x₁ x₂ = x₁
 inferRed' (suc n) xs ys@(_ ∷ ys') x zs x₁ r = 
   let (rdx , _) = Red⇒HasRedex _ _ r
   in inferRed' n xs (reduce ys rdx)
        ((≤-trans {length (reduce ys rdx)} {(length ys')} {n}
          (reduce-length-≤ _ ys' rdx)
         x)) zs
           (subst Red (++reduce xs (ys ++ zs) _ ∙
              cong (xs ++_) (reduce++ ys zs rdx))
            ((reduceRed _ (++HasRedex _ _ (HasRedex++ _ _ rdx)))
              x₁))
           (reduceRed _ rdx r)

 inferRed : ∀ xs ys zs → Red (xs ++ ys ++ zs) → Red ys → Red (xs ++ zs)
 inferRed xs ys = inferRed' _ xs ys (≤-refl (length ys))


 infixr 5 _∶_↓∷_


 data _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ where
  _↓[] : ∀ {xs} → Red xs → xs ↓ []
  _∶_↓∷_ : ∀ {xs} → Red xs → ∀ {ys} x {zs} → ys ↓ zs → (xs ++ x ∷ ys ) ↓ (x ∷ zs)

 open BinaryRelation

 _∷↓_ : ∀ {xs ys} x → xs ↓ ys → (x ∷ xs) ↓ (x ∷ ys)
 _∷↓_ = red[] ∶_↓∷_

 _++↓_ : ∀ {xs ys} zs → xs ↓ ys → (zs ++ xs) ↓ (zs ++ ys)
 [] ++↓ x = x
 (x₁ ∷ zs) ++↓ x = x₁ ∷↓ (zs ++↓ x)

 ↓refl : isRefl _↓_ 
 ↓refl [] = red[] ↓[]
 ↓refl (x ∷ xs) = red[] ∶ x ↓∷ ↓refl xs
 
 _↙_↘_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
 xs ↙ ys ↘ zs = ys ↓ xs × (ys ↓ zs)

 _↘_↙_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
 xs ↘ ys ↙ zs = xs ↓ ys × (zs ↓ ys)

 Red++↓ : ∀ {xs ys zs} → Red zs →  xs ↓ ys → (zs ++ xs) ↓ ys   
 Red++↓ x (x₁ ↓[]) = (_ · _) x x₁ ↓[]
 Red++↓ {.(xs ++ x₂ ∷ _)} {.(x₂ ∷ _)} {zs} x (_∶_↓∷_ {xs} x₁ x₂ x₃) = 
   subst (_↓ (x₂ ∷ _)) (++-assoc zs xs _) (((_ · _) x x₁) ∶ x₂ ↓∷ x₃)

 ↓++Red : ∀ {xs ys zs} → Red zs →  xs ↓ ys → (xs ++ zs) ↓ ys   
 ↓++Red x (x₁ ↓[]) = (_ · _) x₁ x ↓[]
 ↓++Red x (_∶_↓∷_ {xs} x₁ {ys} x₂ {zs} x₃) = 
   let z = x₁ ∶ x₂ ↓∷  (↓++Red x x₃)
   in subst (_↓ (x₂ ∷ _)) (sym (++-assoc xs (x₂ ∷ ys) _)) z

 ↓⇒length≥ : ∀ {xs ys} → xs ↓ ys → length ys ≤ length xs
 ↓⇒length≥ (x ↓[]) = tt
 ↓⇒length≥ (_∶_↓∷_ {xs} x {ys} x₁ {zs} x₂) = 
  let z' = ≤-+-weaken {suc (length zs)} {k = length xs} (↓⇒length≥ x₂)
  in subst (suc (length zs) ≤_) (sym (length++ xs (x₁ ∷ ys))) z'


 ↓EqualLengths⇒≡ : ∀ {xs ys} → xs ↓ ys → length xs ≡ length ys → xs ≡ ys
 ↓EqualLengths⇒≡ {xs} (x ↓[]) x₁ = length≡0→≡[] _ x₁
 ↓EqualLengths⇒≡ (_∶_↓∷_ {xs} x {ys} x₂ {zs} x₃) p = 
   let z = ↓⇒length≥ x₃
       xs≡[] : xs ≡ []
       xs≡[] = length≡0→≡[] xs (≤0→≡0 (k+l≡m+n-⊓-k≤m-⇒n≤l {length zs}
                {1} {length ys} {suc (length xs) }
                  (+-comm (length zs) 1 ∙∙ sym p ∙∙
                    ((length++ xs (x₂ ∷ ys) ∙
                     +-suc (length xs) (length ys))
                      ∙ +-comm (suc (length xs)) ((length ys)) )) z))
   in cong (_++ (x₂ ∷ ys)) xs≡[] ∙
        cong (x₂ ∷_) (↓EqualLengths⇒≡ x₃
          (injSuc
           (cong (λ xs → length (xs ++ x₂ ∷ ys)) (sym (xs≡[])) ∙ p )))





 []↓ : ∀ xs → [] ↓ xs → xs ≡ [] 
 []↓ [] x = refl
 []↓ (x₁ ∷ xs) x = ⊥.rec (↓⇒length≥ x)

 ↓[x]View : ∀ a x → a ↓ [ x ] →
    Σ (_ × _) λ (aL , aR) → (aL ++ x ∷ aR ≡ a) × Red aL × Red aR
 ↓[x]View .(_ ++ x ∷ _) x (x₁ ∶ .x ↓∷ (x₂ ↓[])) = 
   _ , (refl , (x₁ , x₂))
 
 ↓View++' : ∀ a b c b++c → ((b ++ c) ≡ b++c) → a ↓ (b++c) →
   Σ (_ × _) λ (aL , aR) → ((aL ↓ b) × (aR ↓ c)) × (aL ++ aR ≡ a)
 ↓View++' a [] c b++c x x₁ =
   ([] , a) , (↓refl [] , subst (a ↓_) (sym x) x₁) , refl
 ↓View++' a (x₂ ∷ b) c .[] x (x₁ ↓[]) = ⊥.rec (¬cons≡nil x)
 ↓View++' .(xs ++ x₃ ∷ ys) (x₂ ∷ b) c .(x₃ ∷ zs) x (_∶_↓∷_ {xs} x₁ {ys} x₃ {zs} x₄) = 
  let ((aL , aR) , (l↓ , r↓) , p)  = ↓View++' _ b c _ (cons-inj₂ x) x₄
  in (xs ++ x₂ ∷ aL , aR) , ((Red++↓ x₁ (x₂ ∷↓ l↓) , r↓) ,
       ++-assoc xs _ _ ∙
        cong (xs ++_) (cong₂ _∷_ (cons-inj₁ x) p))

 ↓trans[] : ∀ a b → Red b → a ↓ b → Red a
 ↓trans[] a .[] red[] (x ↓[]) = x
 ↓trans[] a .(x ∷ (xs ∷ʳ not₁ x)) (cj x xs x₂) x₁ =
  let ((aL , aR) , (l↓ , r↓) , p)  =
           ↓View++' a [ x ] (xs ∷ʳ (not₁ x)) _ refl
            x₁
      ((aL' , aR') , (l↓' , r↓') , p')  =
           ↓View++' aR xs [ not₁ x ] _ refl r↓
      Red-aL' = ↓trans[] aL' xs x₂ l↓'
      ((q1* , q2*) , pa1 , q1 , q2) = ↓[x]View _ _ l↓
      ((q3* , q4*) , pa2 , q3 , q4) = ↓[x]View _ _ r↓'
      z = (_ · _) q1 ((_ · _)
            (cj x _ ((_ · _) ((_ · _) q2 Red-aL') q3)) q4)
  in subst Red ((λ i → ++-assoc q1* [ x ]
                 (++-assoc (q2* ++  aL') q3* [ not₁ x ] i ++ q4*)
                 (~ i)) ∙∙  cong ((q1* ++ [ x ]) ++_)
                          (++-assoc (q2* ++ aL') _ _ ∙ ++-assoc (q2*) aL' _) ∙
                            sym (++-assoc (q1* ++ [ x ]) q2* _)
                         ∙∙
                (λ i → (++-assoc q1* [ x ] q2* ∙ pa1) i
                 ++ aL' ++ (++-assoc q3* _ q4* ∙ pa2) i)
          ∙ cong (aL ++_) p' ∙ p) z


 ↓trans[] a .(xs ++ ys) ((xs · ys) x x₂) x₁ =
  let ((aL , aR) , (l↓ , r↓) , p)  = ↓View++' a xs ys _ refl x₁
      xx = ↓trans[] aL xs x l↓
      yy = ↓trans[] aR ys x₂ r↓
  in subst Red p ((_ · _) xx yy)

 _↓++↓_ : ∀ {xs xs' ys ys'} → xs ↓ ys → xs' ↓ ys' → (xs ++ xs') ↓ (ys ++ ys') 
 (x ↓[]) ↓++↓ x₁ = Red++↓ x x₁ 
 _↓++↓_ {xs' = xs'} (_∶_↓∷_ {xs} x {ys} x₂ {zs} x₃) x₁ =
  let z = x₃ ↓++↓ x₁
  in subst (_↓ (x₂ ∷ zs ++ _)) (sym (++-assoc xs (x₂ ∷ ys) xs'))
      (Red++↓ x (x₂ ∷↓ z))

 ↓trans : isTrans _↓_
 ↓trans a b [] x (x₁ ↓[]) = ↓trans[] _ _ x₁ x ↓[]
 ↓trans a b (x₂ ∷ c) x x₁ =
   let ((aL , aR) , (l↓ , r↓) , p) = ↓View++' b [ x₂ ] c _ refl x₁
       ((aL' , aR') , (l↓' , r↓') , p') = ↓View++' a aL aR b p x
       z = ↓trans _ _ c r↓' r↓
       ((q1* , q2*) , pa1 , q1 , q2) = ↓[x]View _ _ l↓
       ((aL* , aR*) , (l↓* , r↓*) , p*) =
         ↓View++' aL' q1* (x₂ ∷ q2*) aL pa1 l↓'
       ((aL*' , aR*') , (l↓*' , r↓*') , p*') =
         ↓View++' aR* [ x₂ ] q2* _ refl r↓*
       ww' = Red++↓ (↓trans[] aL* q1* q1 l↓*)
          (↓++Red (↓trans[] aR*' q2* q2 r↓*') l↓*')
       ww = subst (_↓ [ x₂ ]) (cong (aL* ++_) p*' ∙ p*) ww'
   in subst (_↓ (x₂ ∷ c)) p' (ww ↓++↓ z)
 
 
 ↘↙⇒↙↘ : ∀ xs ys zs → xs ↘ ys ↙ zs → Σ _ (xs ↙_↘ zs) 
 ↘↙⇒↙↘ xs .[] zs ((x ↓[]) , (x₁ ↓[])) =
   (xs ++ zs) , ↓++Red x₁ (↓refl _) , Red++↓ x (↓refl _)
 ↘↙⇒↙↘ .(_ ++ x₁ ∷ _) .(x₁ ∷ _) .(xs ++ x₁ ∷ _) (_∶_↓∷_  {xs'} x x₁ u , _∶_↓∷_ {xs} x₂ .x₁ v) = 
   let (zs' , (u' , v')) = ↘↙⇒↙↘ _ _ _ (u , v)
   in (xs ++ xs') ++ x₁ ∷ zs' ,
        subst (_↓ (xs' ++ x₁ ∷ _)) (sym (++-assoc xs xs' _))
           (Red++↓ x₂ (xs' ++↓ (x₁ ∷↓ u'))) ,
            subst (_↓ (xs ++ x₁ ∷ _)) (sym (++-assoc xs xs' _))
              (xs ++↓ (Red++↓ x (x₁ ∷↓ v')))


 _↙↘_ : _ → _ → Type ℓ
 xs ↙↘ ys = Σ _ (xs ↙_↘ ys)

 _↘↙_ : _ → _ → Type ℓ
 xs ↘↙ ys = Σ _ (xs ↘_↙ ys)

 open isEquivRel


 ↙↘refl : isRefl _↙↘_
 ↙↘refl _ = _ , ↓refl _ , ↓refl _ 

 ↙↘sym : isSym _↙↘_
 ↙↘sym _ _ = map-snd λ (x , y) → y , x 

 ↙↘trans : isTrans _↙↘_
 ↙↘trans _ _ _ (_ , (u , v)) (_ , (u' , v')) =
  let (_ , (u'' , v'')) = ↘↙⇒↙↘ _ _ _ (v , u')
  in _ , ↓trans _ _ _ u'' u , ↓trans _ _ _ v'' v' 

 ↙↘isEquivRel : isEquivRel _↙↘_
 reflexive ↙↘isEquivRel = ↙↘refl
 symmetric ↙↘isEquivRel = ↙↘sym
 transitive ↙↘isEquivRel = ↙↘trans


 isNormalisedRed : ∀ xs → IsNormalised xs →  Red xs → xs ≡ []
 isNormalisedRed [] isNrmxs _ = refl
 isNormalisedRed (x ∷ xs) isNrmxs r = ⊥.rec
   (IsNormalised→¬HaseRedex _ isNrmxs (fst (Red⇒HasRedex _ _ r)))


 minimalNormalised : ∀ xs ys → IsNormalised xs → xs ↓ ys → xs ≡ ys
 minimalNormalised _ _ isNrmXs q = 
     ↓EqualLengths⇒≡ q (w _ _ isNrmXs q)
  where
  w : ∀ xs ys → IsNormalised xs → xs ↓ ys → length xs ≡ length ys
  w xs .[] isNrmXs (x ↓[]) = cong length (isNormalisedRed _ isNrmXs x)
  w .(xs ++ x₁ ∷ ys) .(x₁ ∷ zs) isNrmXs (_∶_↓∷_ {xs} x {ys} x₁ {zs} q) =
    let (nrmXs , nrmX₁∷ys) = (IsNormalised++  xs (x₁ ∷ ys) isNrmXs)
        xs≡[] = isNormalisedRed _ nrmXs x
     in cong (λ xs → length (xs ++ x₁ ∷ ys)) xs≡[] ∙
          cong suc (w _ _ (snd (IsNormalised++ [ x₁ ] ys nrmX₁∷ys)) q) 
 

 ≢↓→HasRedex : ∀ xs ys → length ys < length xs →
      xs ↓ ys → Σ (HasRedex xs) λ hr → reduce _ hr ↓ ys
 ≢↓→HasRedex xs .[] x (x₁ ↓[]) = map-snd _↓[] (Red⇒HasRedex _ x x₁) 
 ≢↓→HasRedex .([] ++ x₂ ∷ ys) .(x₂ ∷ zs) x (_∶_↓∷_ {[]} x₁ {ys} x₂ {zs} x₃) =
  let (p , q) = ≢↓→HasRedex _ _ x x₃
  in inr p , (x₂ ∷↓ q)
 ≢↓→HasRedex .((x₄ ∷ xs) ++ x₂ ∷ _) .(x₂ ∷ _) x (_∶_↓∷_ {x₄ ∷ xs} x₁ x₂ {zs} x₃) = 
  let (p , q) = Red⇒HasRedex _ _ x₁
  in  HasRedex++ _ _ p , subst (_↓ (x₂ ∷ zs)) (sym (reduce++ _ _ p)) (Red++↓ q (x₂ ∷↓ x₃))

 reduce↓ : ∀ {xs ys} hr
     → xs ↓ ys
     → IsNormalised ys
     → reduce xs hr ↓ ys
 reduce↓ hr (x ↓[]) x₁ = reduceRed _ hr x ↓[]
 reduce↓ hr (x ∶ x₂ ↓∷ x₃) x₁ with hasRedexSplitCases++ _ (x₂ ∷ _) hr
 ... | inl (inl (hr' , p)) =
       subst (_↓ (x₂ ∷ _)) p (reduceRed _ hr' x ∶ x₂ ↓∷ x₃)
 reduce↓ hr (_∶_↓∷_ {xs} x {ys} x' (x₂ ↓[])) x₁ | inl (inr (inl u , p)) =
   let (((_ , rlR') , (_ , rrR')) , p'') =
            RedWillReduceView _ _ _ x₂ u 
   in subst (_↓ (_ ∷ _)) (cong (xs ++_) (p'' ∙ sym (reduceHead _ _ u)) ∙ p)
        (Red++↓ x (rlR' ∶ x' ↓∷ (rrR' ↓[])))
   
 reduce↓ hr (x ∶ _ ↓∷ _∶_↓∷_ {[]} x₂ x₃ x₄) x₁ | inl (inr (inl u , p)) =
    ⊥.rec (fst x₁ u)
 reduce↓ hr (_∶_↓∷_ {xs₁} x _ (_∶_↓∷_ {x₅ ∷ xs} x₂ {ys} x₃ x₄)) x₁ | inl (inr (inl u , p)) = 
  let (((rl' , rlR') , (rr' , rrR')) , p'') =
          RedWillReduceView _ _ _ x₂ u
  in subst (_↓ (_ ∷ _)) (cong (xs₁ ++_) (sym (++-assoc rl' _ _))
       ∙ cong (λ xs → xs₁ ++ xs ++ x₃ ∷ ys) p'' ∙ p)
         (Red++↓ x (rlR' ∶ _ ↓∷ rrR' ∶ x₃ ↓∷ x₄))
 ... | inl (inr (inr u , p)) =
    subst (_↓ (_ ∷ _)) p (x ∶ x₂ ↓∷ reduce↓ u x₃ (snd x₁))
 ... | inr (p , x₂' , (w , p')) =
    let (((rl' , rlR') , (rr' , rrR')) , p'') =
          RedWillReduceʳView _ _ _ x w
        p* = cong (λ x* → rl' ++ x* ∷ rr') ((ΣPathP (symIsRedex _ _ p')))  ∙ p''
        z = rlR' ∶ x₂ ↓∷ Red++↓ rrR' x₃
    in subst (_↓ (_ ∷ _)) ( sym (++-assoc rl' _ _) ∙ cong (_++ _) p* ∙ sym p)
          z
 

 -- Red↓→↓Red : ∀ a b → Red a → a ↓ b → Red b
 -- Red↓→↓Red a b x x₁ = {!!}

 N↙↘N→≡' : ∀ n xs ys → (q : xs ↙↘ ys) → length (fst q) ≤ n → 
     IsNormalised xs →
     IsNormalised ys → Σ (xs ↙↘ ys) λ q' → length xs ≡ length (fst q')
 N↙↘N→≡' zero xs ys ([] , ↓xs , ↓ys) g xsN ysN =
   ([] , ↓xs , ↓ys) , cong length ([]↓ _ ↓xs)
 N↙↘N→≡' (suc n) xs ys q@(zs , ↓xs , ↓ys) g xsN ysN =
  ⊎.rec
    (λ lenXS<lenZS →
       let (w , _) = ≢↓→HasRedex zs xs lenXS<lenZS ↓xs
         
       in N↙↘N→≡' n xs ys
           (_ , (reduce↓ w ↓xs xsN) , reduce↓ w ↓ys ysN)
           (≤-trans {length (reduce _ w)} {suc (length (reduce _ w))}
                {n}
              (≤-suc-weaken {(length (reduce _ w))}
                (≤-refl (length (reduce _ w))))
             (subst (_≤ suc n) (sym (reduceLength _ w)) g)) xsN ysN)
    (q ,_)
   (≤-split {length xs} {length zs} (↓⇒length≥ ↓xs))


 N↙↘N→≡-eqLen : ∀ xs ys → (q : xs ↙↘ ys) → length xs ≡ length (fst q) → 
     IsNormalised xs →
     IsNormalised ys → xs ≡ ys
 N↙↘N→≡-eqLen xs ys (zs , ↓xs , ↓ys) p xsN ysN =
   let zs≡xs = ↓EqualLengths⇒≡ ↓xs (sym p) 
       zsN = subst IsNormalised (sym zs≡xs) xsN
   in sym zs≡xs ∙ minimalNormalised zs ys zsN ↓ys
 
 N↙↘N→≡ : ∀ xs ys → xs ↙↘ ys →
     IsNormalised xs →
     IsNormalised ys → xs ≡ ys
 N↙↘N→≡ xs ys q xsN ysN =
  let (q' , p) = N↙↘N→≡' (length (fst q)) xs ys q
        (≤-refl (length (fst q))) xsN ysN
  in N↙↘N→≡-eqLen xs ys q' p xsN ysN


 _↙↘++↙↘_ : ∀ {xsL xsR ysL ysR} →
    xsL ↙↘ ysL → xsR ↙↘ ysR →
      (xsL ++ xsR) ↙↘ (ysL ++ ysR)
 (_ , xl , yl) ↙↘++↙↘ (_ , xr , yr) = _ , (xl ↓++↓ xr) , (yl ↓++↓ yr)


 List/↙↘ : Type ℓ
 List/↙↘ = _ /₂ _↙↘_


 List/↙↘· : List/↙↘ → List/↙↘ → List/↙↘
 List/↙↘· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
    (λ _ _ c → eq/ _ _ ∘ _↙↘++↙↘ (↙↘refl c))
    (λ a _ _ → eq/ _ _ ∘ (↙↘refl a) ↙↘++↙↘_ )


 Iso-↙↘-≡ : ∀ a b → Iso ([ a ]/ ≡ [ b ]/) ∥ a ↙↘ b ∥₁
 Iso-↙↘-≡ = isEquivRel→TruncIso ↙↘isEquivRel

 ≡→↙↘ : ∀ a b → ([ a ]/ ≡ [ b ]/) →  ∥ a ↙↘ b ∥₁
 ≡→↙↘ _ _ = Iso.fun (Iso-↙↘-≡ _ _)
 
 NormalForm/ : List/↙↘ → Type ℓ
 NormalForm/ g = Σ _ λ l → ([ l ]/ ≡ g) × ∥ IsNormalised l ∥₁





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
    

 Red-invLi : ∀ xs → Red xs → Red (invLi xs)
 Red-invLi .[] red[] = red[]
 Red-invLi .(x ∷ (xs ∷ʳ not₁ x)) (cj x xs x₁) =
   let z = cj x _ (Red-invLi _ x₁)
   in subst Red (cong
     (_∷ rev (Li.map (map-fst not) xs) ++ (not (fst x) , snd x) ∷ [])
       (sym (not₁not₁ x)) ∙ cong (_∷ʳ (not₁ x))
     (sym (invLi++ xs [ not₁ x ])) ) z
 Red-invLi .(xs ++ ys) ((xs · ys) x x₁) =
   subst Red (sym (invLi++ xs ys))
     ((_ · _) (Red-invLi _ x₁) (Red-invLi _ x))

 invLi-↓ : ∀ xs ys → xs ↓ ys → invLi xs ↓ invLi ys
 invLi-↓ xs .[] (x ↓[]) = Red-invLi _ x ↓[] 
 invLi-↓ .(xs ++ x₁ ∷ ys) .(x₁ ∷ _) (_∶_↓∷_ {xs} x {ys} x₁ y) = 
   subst (_↓ _) (sym (invLi++ xs (_ ∷ ys)))
     (↓++Red (Red-invLi _ x) ((invLi-↓ _ _ y) ↓++↓ (↓refl _)) ) 

 invLi-↙↘ : ∀ xs ys → xs ↙↘ ys → (invLi xs) ↙↘ (invLi ys)
 invLi-↙↘ xs ys (zs , ↓xs , ↓ys) =
   (invLi zs) ,
     invLi-↓ _ _ ↓xs , invLi-↓ _ _ ↓ys

 Red[XS++invLiXS] : ∀ xs → Red (xs ++ invLi xs)
 Red[XS++invLiXS] [] = red[]
 Red[XS++invLiXS] (x ∷ xs) =
   subst Red (sym (++-assoc [ x ] xs (invLi (x ∷ xs)) ∙
         cong (x ∷_) (sym (++-assoc xs (invLi xs) _))))
     (cj x _ (Red[XS++invLiXS] xs))
 
 XS++invLiXS↓[] : ∀ xs → (xs ++ invLi xs) ↓ []
 XS++invLiXS↓[] xs = Red[XS++invLiXS] xs ↓[] 

 invLiXS++XS↓[] : ∀ xs → (invLi xs ++ xs) ↓ []
 invLiXS++XS↓[] xs = 
   subst (λ xs' → (invLi xs ++ xs') ↓ [])
      (invol-invLi xs)
     (XS++invLiXS↓[] (invLi xs))

 ↓→↙↘ : ∀ {xs ys} → xs ↓ ys → xs ↙↘ ys
 ↓→↙↘ x = _ , ↓refl _ , x
 

 List/↙↘Group : GroupStr List/↙↘
 GroupStr.1g List/↙↘Group = SQ.[ [] ]
 GroupStr._·_ List/↙↘Group = List/↙↘·

 GroupStr.inv List/↙↘Group =
   SQ.rec squash/ (SQ.[_] ∘ invLi)
    λ _ _ → eq/ _ _ ∘ invLi-↙↘ _ _
 GroupStr.isGroup List/↙↘Group = makeIsGroup
   squash/ (SQ.elimProp3
     (λ _ _ _ → squash/ _ _)
      λ xs ys zs → cong SQ.[_] (sym (++-assoc xs ys zs)))
   (SQ.elimProp
     (λ _ → squash/ _ _)
     λ xs → cong SQ.[_] (++-unit-r xs))
   (SQ.elimProp
     (λ _ → squash/ _ _)
     λ _ → refl)
   (SQ.elimProp
     (λ _ → squash/ _ _)
     λ xs → eq/ _ _ (↓→↙↘ {ys = []} (XS++invLiXS↓[] xs)))
   (SQ.elimProp
     (λ _ → squash/ _ _)
     λ xs → eq/ _ _ (↓→↙↘ {ys = []} (invLiXS++XS↓[] xs)))




-- -- -- --  module FG (freeGroupGroup : Group ℓ) (η : A → ⟨ freeGroupGroup ⟩) where 

-- -- -- --   FreeGroup = ⟨ freeGroupGroup ⟩

-- -- -- --   open GroupStr (snd freeGroupGroup) renaming (_·_ to _·fg_) public


-- -- -- --   open GroupTheory freeGroupGroup

-- -- -- --   η* : Bool × A → FreeGroup
-- -- -- --   η* (b , a) = (if b then idfun _ else inv) (η a)

-- -- -- --   fromList' : FreeGroup → List (Bool × A) → FreeGroup
-- -- -- --   fromList' = foldr (_·fg_ ∘ η*) 

-- -- -- --   fromList : List (Bool × A) → FreeGroup
-- -- -- --   fromList = fromList' 1g

-- -- -- --   fromList· : ∀ xs ys → fromList (xs ++ ys) ≡
-- -- -- --                             fromList xs ·fg fromList ys
-- -- -- --   fromList· [] _ = sym (·IdL _)
-- -- -- --   fromList· (_ ∷ xs) _ =
-- -- -- --    cong (_ ·fg_) (fromList· xs _) ∙
-- -- -- --     ·Assoc _ _ _

-- -- -- --   redex-ε-η* : ∀ x x' → IsRedex x x' → η* x ·fg η* x' ≡ 1g
-- -- -- --   redex-ε-η* (false , _) (false , _) (p , _) = ⊥.rec (false≢true p)
-- -- -- --   redex-ε-η* (false , x) (true , _) (_ , q) = 
-- -- -- --     cong (inv (η x) ·fg_) (cong (η) (sym q)) ∙ ·InvL (η x) 
-- -- -- --   redex-ε-η* (true , x) (false , _) (_ , q) =
-- -- -- --     cong (η x ·fg_) (cong (inv ∘ η) (sym q)) ∙ ·InvR (η x)
-- -- -- --   redex-ε-η* (true , _) (true , _) (p , _) = ⊥.rec (true≢false p)

-- -- -- --   NormalForm : FreeGroup → Type ℓ
-- -- -- --   NormalForm g = Σ _ λ l → (fromList l ≡ g) × IsNormalised l
-- -- -- --   module _ (isSetA : isSet A) where
  
-- -- -- --    isPropNormalForm : ∀ g → isProp (NormalForm g)
-- -- -- --    isPropNormalForm g (l , p , n) (l' , p' , n') =
-- -- -- --      {!!}



-- -- -- -- --  module HIT-FG where

-- -- -- -- --   open import Cubical.HITs.FreeGroup renaming (rec to recFG ; elimProp to elimPropFG)

-- -- -- -- --   open FG (freeGroupGroup A) η renaming (inv to invFG)
  

-- -- -- -- --   FG→L/↙↘ : GroupHom (freeGroupGroup A) (_ , List/↙↘Group)
-- -- -- -- --   FG→L/↙↘ = recFG ([_]/ ∘ [_] ∘ (true ,_))

-- -- -- -- --   open IsGroupHom (snd (FG→L/↙↘))

-- -- -- -- --   Red→FG≡ : ∀ a → Red a → fromList a ≡ ε
-- -- -- -- --   Red→FG≡ .[] red[] = refl
-- -- -- -- --   Red→FG≡ .(x ∷ (xs ∷ʳ not₁ x)) (cj x xs x₁) =
-- -- -- -- --         cong (η* x ·fg_) (fromList· xs [ not₁ x ] ∙
-- -- -- -- --           cong₂ _·fg_ (Red→FG≡ _ x₁) (·IdR _) ∙ ·IdL _) ∙
-- -- -- -- --            redex-ε-η* x (not₁ x) (symIsRedex _ _ (refl , refl))
-- -- -- -- --   Red→FG≡ .(xs ++ ys) ((xs · ys) x x₁) =
-- -- -- -- --     fromList· xs ys
-- -- -- -- --       ∙∙ cong₂ _·fg_ (Red→FG≡ _ x) (Red→FG≡ _ x₁)
-- -- -- -- --       ∙∙ ·IdL _
  
-- -- -- -- --   ↓→FG≡ : (a b : List (Bool × A)) → a ↓ b → fromList a ≡ fromList b
-- -- -- -- --   ↓→FG≡ a .[] (x ↓[]) = Red→FG≡ _ x
-- -- -- -- --   ↓→FG≡ .(xs ++ x₁ ∷ ys) .(x₁ ∷ _) (_∶_↓∷_ {xs} x {ys} x₁ x₂) =
-- -- -- -- --     fromList· xs (x₁ ∷ ys) ∙∙
-- -- -- -- --       cong (_·fg fromList (x₁ ∷ ys)) (Red→FG≡ xs x) ∙
-- -- -- -- --         ·IdL _ ∙∙ cong (η* x₁ ·fg_) (↓→FG≡ _ _ x₂)

-- -- -- -- --   ↙↘→FG≡ : (a b : List (Bool × A)) → a ↙↘ b → fromList a ≡ fromList b
-- -- -- -- --   ↙↘→FG≡ a b (c , ↓a , ↓b) = sym (↓→FG≡ c a ↓a)  ∙ ↓→FG≡ c b ↓b

-- -- -- -- --   section-FG-L/↙↘ : ∀ a → fst (FG→L/↙↘) (fromList a) ≡ [ a ]/
-- -- -- -- --   section-FG-L/↙↘ [] = refl
-- -- -- -- --   section-FG-L/↙↘ (x ∷ xs) =
-- -- -- -- --      pres· (η* x) (fromList xs) ∙
-- -- -- -- --        cong (List/↙↘· (fst FG→L/↙↘ (η* x)))
-- -- -- -- --          (section-FG-L/↙↘ xs)  ∙
-- -- -- -- --           w x
-- -- -- -- --    where
-- -- -- -- --    w : ∀ x → List/↙↘· (fst FG→L/↙↘ (η* x)) [ xs ]/ ≡ [ x ∷ xs ]/
-- -- -- -- --    w (false , a) = refl
-- -- -- -- --    w (true , a) = refl

-- -- -- -- --   fromL/ : List/↙↘ → _
-- -- -- -- --   fromL/ = SQ.rec trunc fromList ↙↘→FG≡

-- -- -- -- --   fromL/pres· : ∀ a b → fromL/ (List/↙↘· a b) ≡ fromL/ a ·fg fromL/ b 
-- -- -- -- --   fromL/pres· = SQ.elimProp2 (λ _ _ → trunc _ _) fromList·

-- -- -- -- --   fromL/presinv : ∀ xs →
-- -- -- -- --        fromL/ (GroupStr.inv List/↙↘Group xs) ≡
-- -- -- -- --       invFG (fromL/ xs)
-- -- -- -- --   fromL/presinv = SQ.elimProp (λ _ → trunc _ _) w
-- -- -- -- --    where
-- -- -- -- --    open GroupTheory (freeGroupGroup A)

-- -- -- -- --    w' : ∀ x → fromL/ [ [ not₁ x ] ]/ ≡ invFG (η* x)
-- -- -- -- --    w' (false , a) = ·IdR _ ∙ sym (invInv _)
-- -- -- -- --    w' (true , a) = ·IdR _
   
-- -- -- -- --    w : (xs : List (Bool × A)) →
-- -- -- -- --       fromL/ [ invLi xs ]/ ≡ invFG (fromL/ [ xs ]/)
-- -- -- -- --    w [] = sym inv1g
-- -- -- -- --    w (x ∷ xs) = 
-- -- -- -- --         (fromL/pres· ([ invLi xs ]/) [ [ not₁ x ] ]/ ∙
-- -- -- -- --             cong (fromL/ [ invLi xs ]/ ·fg_) (w' x))
-- -- -- -- --          ∙∙ cong (_·fg invFG (η* x)) (w xs) ∙∙  sym (invDistr _ _) 
  
-- -- -- -- --   retract-FG-L/↙↘ : ∀ b →  fromL/ (fst (FG→L/↙↘) b) ≡ b
-- -- -- -- --   retract-FG-L/↙↘ =
-- -- -- -- --     elimPropFG (λ _ → trunc _ _)
-- -- -- -- --       (λ _ → ·IdR _)
-- -- -- -- --       (λ g1 g2 p1 p2 →
-- -- -- -- --         cong fromL/ (pres· g1 g2) ∙
-- -- -- -- --           fromL/pres· (fst (FG→L/↙↘) g1) (fst (FG→L/↙↘) g2) ∙
-- -- -- -- --            cong₂ _·fg_ p1 p2)
-- -- -- -- --       refl
-- -- -- -- --       λ g p → cong fromL/ (presinv g) ∙
-- -- -- -- --          fromL/presinv (fst (FG→L/↙↘) g) ∙ cong invFG p 

-- -- -- -- --   GroupIso-FG-L/↙↘ : GroupIso (freeGroupGroup A) (_ , List/↙↘Group)
-- -- -- -- --   Iso.fun (fst GroupIso-FG-L/↙↘) = _
-- -- -- -- --   Iso.inv (fst GroupIso-FG-L/↙↘) = fromL/
    
-- -- -- -- --   Iso.rightInv (fst GroupIso-FG-L/↙↘) =
-- -- -- -- --     SQ.elimProp (λ _ → squash/ _ _)
-- -- -- -- --      section-FG-L/↙↘
-- -- -- -- --   Iso.leftInv (fst GroupIso-FG-L/↙↘) = retract-FG-L/↙↘
-- -- -- -- --   snd GroupIso-FG-L/↙↘ = snd FG→L/↙↘
