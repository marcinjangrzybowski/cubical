{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.NormalFormIndexed where

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
 
module NormalForm {A : Type ℓ} where


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

 Red⇒HasRedex : ∀ xs → 0 < length xs → Red xs → HasRedex xs 
 Red⇒HasRedex .(x ∷ ([] ∷ʳ not₁ x)) _ (cj x [] r) =
   inl (symIsRedex _ _ (refl , refl))
 Red⇒HasRedex .(x ∷ ((_ ∷ _) ∷ʳ not₁ x)) _ (cj x xs@(_ ∷ _) r) =
   inr (HasRedex∷ʳ _ _ (Red⇒HasRedex xs _ r))
 Red⇒HasRedex .(xs ++ []) q ((xs · []) rX rY) = 
   subst HasRedex (sym (++-unit-r xs))
     (Red⇒HasRedex _ (subst (λ xs → 0 < length xs) (++-unit-r xs) q) rX)
 Red⇒HasRedex .(xs ++ x ∷ ys) q ((xs · (x ∷ ys)) rX rY) =
   ++HasRedex _ _ (Red⇒HasRedex _ _ rY)

 reduce-length-≤ : ∀ x ys rdx → length (reduce (x ∷ ys) rdx) ≤ length ys
 reduce-length-≤ x ys rdx =
   <-weaken {m = length (reduce (x ∷ ys) rdx)}
    (≡→≤ (injSuc (reduceLength _ rdx)))

 inferRed' : ∀ n xs ys → length ys ≤ n → ∀ zs
             → Red (xs ++ ys ++ zs)
             → Red ys
             → Red (xs ++ zs)
 inferRed' n xs [] x zs x₁ x₂ = x₁
 inferRed' (suc n) xs ys@(_ ∷ ys') x zs x₁ r = 
   let rdx = Red⇒HasRedex _ _ r
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

 open isEquivRel

 ↙↘isEquivRel : isEquivRel _↙↘_
 reflexive ↙↘isEquivRel _ = _ , ↓refl _ , ↓refl _ 
 symmetric ↙↘isEquivRel _ _ = map-snd λ (x , y) → y , x
 transitive ↙↘isEquivRel _ _ _ (_ , (u , v)) (_ , (u' , v')) =
  let (_ , (u'' , v'')) = ↘↙⇒↙↘ _ _ _ (v , u')
  in _ , ↓trans _ _ _ u'' u , ↓trans _ _ _ v'' v'


 isNormalisedRed : ∀ xs → IsNormalised xs →  Red xs → xs ≡ []
 isNormalisedRed [] isNrmxs _ = refl
 isNormalisedRed (x ∷ xs) isNrmxs r = ⊥.rec
   (IsNormalised→¬HaseRedex _ isNrmxs (Red⇒HasRedex _ _ r))


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
      xs ↓ ys → HasRedex xs
 ≢↓→HasRedex xs .[] x (x₁ ↓[]) = Red⇒HasRedex _ x x₁
 ≢↓→HasRedex .([] ++ x₂ ∷ ys) .(x₂ ∷ zs) x (_∶_↓∷_ {[]} x₁ {ys} x₂ {zs} x₃) =
   inr (≢↓→HasRedex _ _ x x₃)
 ≢↓→HasRedex .((x₄ ∷ xs) ++ x₂ ∷ _) .(x₂ ∷ _) x (_∶_↓∷_ {x₄ ∷ xs} x₁ x₂ x₃) =
   HasRedex++ _ _ (Red⇒HasRedex _ _ x₁) 

 reduce↓ : ∀ {xs ys} hr
     → xs ↓ ys
     → IsNormalised ys
     → reduce xs hr ↓ ys
 reduce↓ hr (x ↓[]) x₁ = reduceRed _ hr x ↓[]
 reduce↓ hr (x ∶ x₂ ↓∷ x₃) x₁ with hasRedexSplitCases++ _ (x₂ ∷ _) hr
 ... | inl (inl (hr' , p)) =
       subst (_↓ (x₂ ∷ _)) p (reduceRed _ hr' x ∶ x₂ ↓∷ x₃)
 reduce↓ hr (x ∶ _ ↓∷ (x₂ ↓[])) x₁ | inl (inr (inl u , p)) = {!!}
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
 


 N↙↘N→≡' : ∀ n xs ys → (q : xs ↙↘ ys) → length (fst q) ≤ n → 
     IsNormalised xs →
     IsNormalised ys → Σ (xs ↙↘ ys) λ q' → length xs ≡ length (fst q')
 N↙↘N→≡' zero xs ys ([] , ↓xs , ↓ys) g xsN ysN =
   ([] , ↓xs , ↓ys) , cong length ([]↓ _ ↓xs)
 N↙↘N→≡' (suc n) xs ys q@(zs , ↓xs , ↓ys) g xsN ysN =
  ⊎.rec
    (λ lenXS<lenZS →
       let w = ≢↓→HasRedex zs xs lenXS<lenZS ↓xs
         
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


 --  ⊎.rec {!!}
 --    (λ lenXs≡lenZs →
 --      let zs≡xs = ↓EqualLengths⇒≡ ↓xs (sym lenXs≡lenZs) 
 --          zsN = subst IsNormalised (sym zs≡xs) xsN
 --       in sym zs≡xs ∙ minimalNormalised zs ys zsN ↓ys)
 --    (≤-split {length xs} {length zs} (↓⇒length≥ ↓xs))

 -- Normal↙↘Normal→≡ : ∀ xs ys → xs ↙↘ ys →
 --     IsNormalised xs →
 --     IsNormalised ys → xs ≡ ys
 -- Normal↙↘Normal→≡ xs [] (zs , u , (x ↓[])) nX nY =
 --   isNormalisedRed xs nX (↓trans[]* _ _ x u)
 -- Normal↙↘Normal→≡ [] xs@(_ ∷ _) (zs , (x ↓[]) , u) _ nX =
 --   sym (isNormalisedRed xs nX (↓trans[]* _ _ x u))
 -- Normal↙↘Normal→≡ (x₁ ∷ xs) (x ∷ ys) (zs , u , v) nX nY =
 --  {!!}

-- -- ((xs ++ xs') ++ x₁ ∷ zs') ↓ (xs' ++ x₁ ∷ ys)

-- -- -- --  -- (rl ++ (not b , a) ∷ ((rr ++ rl') ∷ʳ not₁ (not b , a))) ++ rr' ≡
-- -- -- --  --    (rl ++ [ not b , a ] ++ rr) ++ rl' ++ [ b , a ] ++ rr'

-- -- -- -- --  red∷' : ∀ x xs x∷xs → ListPath.Cover (x ∷ xs) x∷xs → Red (x∷xs) →
-- -- -- -- --     Σ (_ × _) λ (xsL , xsR) → Red xsL × Red xsR ×
-- -- -- -- --          (xs ≡ xsL ++ [ not₁ x ] ++ xsR)
-- -- -- -- --  red∷' x xs .(x₁ ∷ (xs₁ ∷ʳ y)) x₂ (cj x₁ y x₃ xs₁ x₄) =
-- -- -- -- --    (xs₁ , []) , (x₄ , red[] ,
-- -- -- -- --      ListPath.decode _ _ (snd x₂) ∙
-- -- -- -- --       cong (xs₁ ∷ʳ_)
-- -- -- -- --        (ΣPathP (sym (notnot _) ∙ cong not (sym (fst x₃)) , (sym (snd x₃))) ∙
-- -- -- -- --        sym (cong not₁ (fst x₂))))
-- -- -- -- --  red∷' x xs .([] ++ ys) x₂ (([] · ys) x₃ x₄) = red∷' x xs ys x₂ x₄  
-- -- -- -- --  red∷' x xs .((x₁ ∷ xs₁) ++ ys) x₂ (((x₁ ∷ xs₁) · ys) x₃ x₄) =
-- -- -- -- --    let ((xs' , ys') , (xs'R , ys'R , p)) = red∷' x (xs₁) (x₁ ∷ xs₁) (fst x₂ , ListPath.reflCode xs₁) x₃
-- -- -- -- --    in (xs' , ys' ++ ys) , xs'R , ((ys' · ys) ys'R x₄ ,
-- -- -- -- --         ListPath.decode _ _  (snd x₂) ∙ cong (_++ ys) p ∙ ++-assoc xs'  _ ys) 
   
-- -- -- -- --  red∷ : ∀ x xs → Red (x ∷ xs) →
-- -- -- -- --     Σ (_ × _) λ (xsL , xsR) → Red xsL × Red xsR ×
-- -- -- -- --          (xs ≡ xsL ++ [ not₁ x ] ++ xsR)
-- -- -- -- --  red∷ x xs = red∷' x xs _ (ListPath.reflCode (x ∷ xs))
 
-- -- -- -- --  reduceRed : ∀ xs hr → Red xs → Red (reduce xs hr)
-- -- -- -- --  reduceRed .(x ∷ ([] ∷ʳ y)) (inl x₃) (cj x y x₁ [] x₂) = red[]
-- -- -- -- --  reduceRed .(x ∷ ((x₄ ∷ xs) ∷ʳ y)) (inl x₃) (cj x y x₁ (x₄ ∷ xs) x₂) =
-- -- -- -- --    let ((xs' , ys') , (xs'R , ys'R , p)) = red∷ x₄ xs x₂
-- -- -- -- --        z' = (xs' · (_ ∷ (ys' ∷ʳ _))) xs'R (cj x x₄ x₃ ys' ys'R)
-- -- -- -- --    in subst Red ({!!} ∙ cong (_∷ʳ y) (sym p)) z'
-- -- -- -- --  reduceRed .(x ∷ (xs ∷ʳ y)) (inr x₃) (cj x y x₁ xs x₂) = {!!}
-- -- -- -- --  reduceRed .(xs ++ ys) hr ((xs · ys) x x₁) = {!!}
 
-- -- -- -- --  -- inferRed : ∀ xs++ys xs ys → xs++ys ≡ xs ++ ys →  Red (xs++ys) → Red xs → Red ys
-- -- -- -- --  -- inferRed .[] xs ys p red[] Rx = {!!}
-- -- -- -- --  -- inferRed .(x ∷ (xs₁ ∷ʳ y)) xs ys p (cj x y x₁ xs₁ Rxy) Rx =
-- -- -- -- --  --   {!!}
-- -- -- -- --  -- inferRed .(xs₁ ++ ys₁) xs ys p ((xs₁ · ys₁) Rxy Rxy₁) Rx = {!!}



-- -- -- -- -- --  data Red* {ℓX} (X : Type ℓX) : Type ℓX where
-- -- -- -- -- --   [] : Red* X
-- -- -- -- -- --   _∷_ : X ⊎ Red* X → Red* X → Red* X

-- -- -- -- -- --  infixr 5 _cj∷_ _cj⁺∷_ _cj⁻∷_ _·∷_ 

-- -- -- -- -- --  pattern _cj∷_ a xs = (inl a) ∷ xs  
-- -- -- -- -- --  pattern _cj⁺∷_ a xs = (inl (true  , a)) ∷ xs  
-- -- -- -- -- --  pattern _cj⁻∷_ a xs = (inl (false  , a)) ∷ xs  
-- -- -- -- -- --  pattern _·∷_ xs ys = (inr xs) ∷ ys  

-- -- -- -- -- --  mapRed : ∀ {ℓX} {X} {ℓX'} {X'} → (X → X') → Red* {ℓX} X → Red* {ℓX'} X'
-- -- -- -- -- --  mapRedHlp : ∀ {ℓX} {X} {ℓX'} {X'} → (X → X') →
-- -- -- -- -- --                      (X ⊎ Red* {ℓX} X)
-- -- -- -- -- --                     → (X' ⊎ Red* {ℓX'} X')
-- -- -- -- -- --  mapRedHlp f (inl x) = inl (f x)
-- -- -- -- -- --  mapRedHlp f (inr x) = inr (mapRed f x)
-- -- -- -- -- --  mapRed f [] = []
-- -- -- -- -- --  mapRed f (x ∷ y) = mapRedHlp f x ∷ mapRed f y

-- -- -- -- -- --  Red = Red* (Bool × A)
-- -- -- -- -- --  Shp = Red* Unit
 
-- -- -- -- -- --  IdxHlp : ∀ {ℓX} {X} → X ⊎ Red* {ℓX} X → Type

-- -- -- -- -- --  Idx : ∀ {ℓX} {X} → Red* {ℓX} X → Type

-- -- -- -- -- --  IdxHlp (inl x) = Unit
-- -- -- -- -- --  IdxHlp (inr x) = Idx x

-- -- -- -- -- --  Idx [] = ⊥
-- -- -- -- -- --  Idx (x ∷ xs) = IdxHlp x ⊎ Idx xs

-- -- -- -- -- --  discreteIdx : ∀ {ℓX} {X} → (r : Red* {ℓX} X) →
-- -- -- -- -- --                  Discrete (Idx r)
-- -- -- -- -- --  discreteIdxHlp : ∀ {ℓX} {X} → (r : _) →
-- -- -- -- -- --                  Discrete (IdxHlp {ℓX} {X} r)
-- -- -- -- -- --  discreteIdxHlp (inl x) _ _ = yes refl
-- -- -- -- -- --  discreteIdxHlp (inr x) = discreteIdx x
-- -- -- -- -- --  discreteIdx (x ∷ r) = discrete⊎ (discreteIdxHlp x) (discreteIdx r)

-- -- -- -- -- --  shp : Red → Shp 
-- -- -- -- -- --  shp = mapRed λ _ → _
 
-- -- -- -- -- --  lookupIdx : ∀ r → Idx r → Bool × A
-- -- -- -- -- --  lookupIdxHlp : (r' : (Bool × A) ⊎ Red) → IdxHlp r' → Bool × A 
-- -- -- -- -- --  lookupIdxHlp (inl x₁) x = x₁
-- -- -- -- -- --  lookupIdxHlp (inr x₁) x = lookupIdx x₁ x
-- -- -- -- -- --  lookupIdx (x₁ ∷ r) (inl x) = lookupIdxHlp x₁ x
-- -- -- -- -- --  lookupIdx (x₁ ∷ r) (inr x) = lookupIdx r x

-- -- -- -- -- --  tabulateIdx : ∀ {ℓX} {X} s → (Idx {ℓX} {X} s → (Bool × A)) → Red
-- -- -- -- -- --  tabulateIdxHlp : ∀ {ℓX} {X} s → ((IdxHlp {ℓX} {X} s) → Bool × A)
-- -- -- -- -- --                       → (Bool × A) ⊎ Red* (Bool × A)
-- -- -- -- -- --  tabulateIdxHlp (inl _) x = inl (x tt)
-- -- -- -- -- --  tabulateIdxHlp (inr x₁) x = inr (tabulateIdx x₁ x)

 
-- -- -- -- -- --  tabulateIdx [] x = []
-- -- -- -- -- --  tabulateIdx (x₁ ∷ s) x =
-- -- -- -- -- --    tabulateIdxHlp x₁ (x ∘ inl) ∷ tabulateIdx s (x ∘ inr)

-- -- -- -- -- --  not₁ : (Bool × A) → (Bool × A)
-- -- -- -- -- --  not₁ = map-fst not

-- -- -- -- -- --  not₁not₁ : ∀ x → not₁ (not₁ x) ≡ x 
-- -- -- -- -- --  not₁not₁ (x , y) = cong (_, y) (notnot x) 
 
-- -- -- -- -- --  evRed : Red → List (Bool × A)
-- -- -- -- -- --  evRed [] = []
-- -- -- -- -- --  evRed (x cj∷ xs) = x ∷ (evRed xs ∷ʳ not₁ x)
-- -- -- -- -- --  evRed (x ·∷ xs) = evRed x ++ evRed xs

-- -- -- -- -- --  redLen : ∀ {ℓX} {X} → Red* {ℓX} X → ℕ
-- -- -- -- -- --  redLenHlp : ∀ {ℓX} {X} → X ⊎ Red* {ℓX} X → ℕ
-- -- -- -- -- --  redLenHlp (inl x) = 1
-- -- -- -- -- --  redLenHlp (inr x) = redLen x
-- -- -- -- -- --  redLen [] = 0
-- -- -- -- -- --  redLen (x ∷ xs) = redLenHlp x + redLen xs

-- -- -- -- -- --  lenEvRed≡redLen·2 : ∀ r → 
-- -- -- -- -- --        redLen r ℕ.· 2 ≡ length (evRed r)
-- -- -- -- -- --  lenEvRed≡redLen·2 [] = refl
-- -- -- -- -- --  lenEvRed≡redLen·2 (x cj∷ r) = cong suc
-- -- -- -- -- --    ((cong suc (lenEvRed≡redLen·2 r) ∙
-- -- -- -- -- --      sym (+-comm (length (evRed r)) 1))
-- -- -- -- -- --     ∙ sym (length++ (evRed r) [ not₁ x ]))
-- -- -- -- -- --  lenEvRed≡redLen·2 (x ·∷ r) =
-- -- -- -- -- --       sym (·-distribʳ (redLen x) (redLen r) 2)
-- -- -- -- -- --     ∙∙  cong₂ _+_ (lenEvRed≡redLen·2 x) (lenEvRed≡redLen·2 r)
-- -- -- -- -- --     ∙∙ sym (length++ (evRed x) (evRed r))
 
-- -- -- -- -- --  isEmptyRed : ∀ {ℓX} {X} → Red* {ℓX} X → Type
-- -- -- -- -- --  isEmptyRed [] = Unit
-- -- -- -- -- --  isEmptyRed (x cj∷ x₁) = ⊥
-- -- -- -- -- --  isEmptyRed (x ·∷ x₁) = isEmptyRed x × isEmptyRed x₁ 

-- -- -- -- -- --  ¬isEmptyRed : ∀ {ℓX} {X} → Red* {ℓX} X → Type
-- -- -- -- -- --  ¬isEmptyRed [] = ⊥
-- -- -- -- -- --  ¬isEmptyRed (x cj∷ x₁) = Unit
-- -- -- -- -- --  ¬isEmptyRed (x ·∷ x₁) = ¬isEmptyRed x ⊎ ¬isEmptyRed x₁ 
 
-- -- -- -- -- --  isLeafIdx : ∀ {ℓX} {X} s → Idx {ℓX} {X} s → Type
-- -- -- -- -- --  isLeafIdxHlp : ∀ {ℓX} {X} s → Red* {ℓX} X → IdxHlp {ℓX} {X} s → Type
-- -- -- -- -- --  isLeafIdxHlp (inl x₁) xs x = isEmptyRed xs
-- -- -- -- -- --  isLeafIdxHlp (inr x₁) xs x = isLeafIdx x₁ x
-- -- -- -- -- --  isLeafIdx (x ∷ s) (inl x₁) = isLeafIdxHlp x s x₁
-- -- -- -- -- --  isLeafIdx (x ∷ s) (inr x₁) = isLeafIdx s x₁

-- -- -- -- -- --  Idx×𝟚 : Red → Type
-- -- -- -- -- --  Idx×𝟚 r = Idx r × Bool
 
-- -- -- -- -- --  lookupIdx' : ∀ r → Idx r → Bool → (Bool × A)
-- -- -- -- -- --  lookupIdx' r idx b =
-- -- -- -- -- --    map-fst (b ⊕_) (lookupIdx r idx)


-- -- -- -- -- --  [idx] : ∀ {ℓX} {X} r → List (Idx {ℓX} {X} r × Bool)
-- -- -- -- -- --  [idx] [] = []
-- -- -- -- -- --  [idx] (a cj∷ r) =
-- -- -- -- -- --    (inl _ , false) ∷ (Li.map (map-fst inr) ([idx] r) ∷ʳ (inl _ , true))
-- -- -- -- -- --  [idx] (r' ·∷ r) =
-- -- -- -- -- --    Li.map (map-fst inl) ([idx] r')
-- -- -- -- -- --     ++ Li.map (map-fst inr) ([idx] r) 

-- -- -- -- -- --  idx→k : ∀ {ℓX} {X} r → Idx {ℓX} {X} r → Bool → ℕ 
-- -- -- -- -- --  idx→k (x₂ ∷ r) (inr x) b = (redLenHlp x₂ ℕ.· 2) + idx→k r x b
-- -- -- -- -- --  idx→k (x₁ cj∷ r) (inl x) false = 0
-- -- -- -- -- --  idx→k (x₁ cj∷ r) (inl x) true = suc (redLen r ℕ.· 2)
-- -- -- -- -- --  idx→k (x₁ ·∷ r) (inl x) b = idx→k x₁ x b

-- -- -- -- -- --  -- idx→k<len·2 : ∀ {ℓX} {X} r →
-- -- -- -- -- --  --   (ix : Idx {ℓX} {X} r) → ∀ b
-- -- -- -- -- --  --   → idx→k r ix b < redLen r ℕ.· 2
-- -- -- -- -- --  -- idx→k<len·2 (x ∷ r) (inr x₁) b = {!!}
-- -- -- -- -- --  -- idx→k<len·2 (x cj∷ r) (inl x₁) false = tt
-- -- -- -- -- --  -- idx→k<len·2 (x cj∷ r) (inl x₁) true = ≤-refl (redLen r ℕ.· 2)
-- -- -- -- -- --  -- idx→k<len·2 (x ·∷ r) (inl x₁) b =
-- -- -- -- -- --  --  ≤-trans {suc (idx→k x x₁ b)}
-- -- -- -- -- --  --   {redLen x ℕ.· 2} {(redLen x + redLen r) ℕ.· 2} (idx→k<len·2 x x₁ b)
-- -- -- -- -- --  --     (subst (redLen x ℕ.· 2 ≤_)
-- -- -- -- -- --  --       (·-distribʳ (redLen x) (redLen r) 2)
-- -- -- -- -- --  --        (k≤k+n (redLen x ℕ.· 2)))

-- -- -- -- -- --  Fin·2 : ∀ n → Type
-- -- -- -- -- --  Fin·2 n = Σ _ λ k → (k < n ℕ.· 2)

-- -- -- -- -- --  IsoFinS·2 : ∀ n → Iso (Fin·2 (suc n)) (Unit ⊎ (Unit ⊎ (Fin·2 n)) )
-- -- -- -- -- --  Iso.fun (IsoFinS·2 n) (zero , k<) = inl _
-- -- -- -- -- --  Iso.fun (IsoFinS·2 n) (suc zero , k<) = inr (inl _)
-- -- -- -- -- --  Iso.fun (IsoFinS·2 n) (suc (suc k) , k<) = inr (inr (k , k<))
-- -- -- -- -- --  Iso.inv (IsoFinS·2 n) (inl x) = 0 , _
-- -- -- -- -- --  Iso.inv (IsoFinS·2 n) (inr (inl x)) = 1 , _
-- -- -- -- -- --  Iso.inv (IsoFinS·2 n) (inr (inr (k , k<))) = suc (suc k) , k< 
-- -- -- -- -- --  Iso.rightInv (IsoFinS·2 n) (inl x) = refl
-- -- -- -- -- --  Iso.rightInv (IsoFinS·2 n) (inr (inl x)) = refl
-- -- -- -- -- --  Iso.rightInv (IsoFinS·2 n) (inr (inr x)) =
-- -- -- -- -- --   cong (inr {A = Unit} ∘ inr) (Σ≡Prop
-- -- -- -- -- --     (λ k → OR.isProp≤ {suc k}
-- -- -- -- -- --       {n ℕ.· 2}) refl)
-- -- -- -- -- --  Iso.leftInv (IsoFinS·2 n) (zero , k<) = refl
-- -- -- -- -- --  Iso.leftInv (IsoFinS·2 n) (suc zero , k<) = refl
-- -- -- -- -- --  Iso.leftInv (IsoFinS·2 n) (suc (suc k) , k<) =
-- -- -- -- -- --    (Σ≡Prop
-- -- -- -- -- --     (λ k → OR.isProp≤ {k}
-- -- -- -- -- --       {suc (n ℕ.· 2)}) refl)
 
-- -- -- -- -- --  -- IsoFin⊎ : ∀ n m → Iso ((Fin·2 n) ⊎ (Fin·2 m)) (Fin·2 (n + m)) 
-- -- -- -- -- --  -- IsoFin⊎ zero m = compIso ⊎.⊎-swap-Iso
-- -- -- -- -- --  --   (compIso (⊎Iso idIso (compIso Σ-swap-Iso (ΣEmptyIso _))) ⊎-⊥-Iso)
-- -- -- -- -- --  -- IsoFin⊎ (suc n) m =
-- -- -- -- -- --  --   compIso (⊎Iso (IsoFinS·2 n) (idIso))
-- -- -- -- -- --  --     (compIso (compIso
-- -- -- -- -- --  --        (compIso ⊎-assoc-Iso
-- -- -- -- -- --  --          (⊎Iso idIso ⊎-assoc-Iso)) (⊎Iso idIso (⊎Iso idIso (IsoFin⊎ n m))))
-- -- -- -- -- --  --       (invIso (IsoFinS·2  (n + m))))

-- -- -- -- -- --  IsoFinS⊎ : ∀ n → Iso (Unit ⊎ (Σ _ (_< n))) (Σ _ (_< (suc n)))
-- -- -- -- -- --  Iso.fun (IsoFinS⊎ n) (inl x) = zero , _
-- -- -- -- -- --  Iso.fun (IsoFinS⊎ n) (inr (k , k<)) = (suc k , k<)
-- -- -- -- -- --  Iso.inv (IsoFinS⊎ n) (zero , k<) = inl _
-- -- -- -- -- --  Iso.inv (IsoFinS⊎ n) (suc k , k<) = inr (k , k<)
-- -- -- -- -- --  Iso.rightInv (IsoFinS⊎ n) (zero , k<) = refl
-- -- -- -- -- --  Iso.rightInv (IsoFinS⊎ n) (suc k , k<) = refl
-- -- -- -- -- --  Iso.leftInv (IsoFinS⊎ n) (inl x) = refl
-- -- -- -- -- --  Iso.leftInv (IsoFinS⊎ n) (inr x) = refl


-- -- -- -- -- --  IsoFin⊎ : ∀ n m → Iso ((Σ _ (_< n)) ⊎ (Σ _ (_< m))) (Σ _ (_< (n + m)))
-- -- -- -- -- --  IsoFin⊎ zero m =
-- -- -- -- -- --    compIso ⊎.⊎-swap-Iso
-- -- -- -- -- --    (compIso (⊎Iso idIso (compIso Σ-swap-Iso (ΣEmptyIso _))) ⊎-⊥-Iso)
-- -- -- -- -- --  IsoFin⊎ (suc n) m =
-- -- -- -- -- --    compIso (⊎Iso (invIso (IsoFinS⊎ n)) (idIso))
-- -- -- -- -- --      (compIso
-- -- -- -- -- --        (compIso ⊎-assoc-Iso
-- -- -- -- -- --          ((⊎Iso idIso (IsoFin⊎ n m))))
-- -- -- -- -- --          (IsoFinS⊎ (n + m)))
     

-- -- -- -- -- --  Iso-Fin·2 : Iso (Bool) (Fin·2 1)
-- -- -- -- -- --  Iso.fun Iso-Fin·2 false = 0 , _
-- -- -- -- -- --  Iso.fun Iso-Fin·2 true = 1 , _
-- -- -- -- -- --  Iso.inv Iso-Fin·2 (zero , _) = false
-- -- -- -- -- --  Iso.inv Iso-Fin·2 (suc zero , _) = true
-- -- -- -- -- --  Iso.rightInv Iso-Fin·2 (zero , _) = refl
-- -- -- -- -- --  Iso.rightInv Iso-Fin·2 (suc zero , _) = refl
-- -- -- -- -- --  Iso.leftInv Iso-Fin·2 false = refl
-- -- -- -- -- --  Iso.leftInv Iso-Fin·2 true = refl


-- -- -- -- -- --  Iso-cntr'-lem1 : ∀ k → (k' : (Fin·2 (suc k))) → 
-- -- -- -- -- --     ((¬ fst k' ≡ zero) × (¬ suc (fst k') ≡ ((suc k) ℕ.· 2))) → predℕ (fst k') < k ℕ.· 2
-- -- -- -- -- --  Iso-cntr'-lem1 k (zero , k'<) (x , y) = ⊥.rec (x refl)
-- -- -- -- -- --  Iso-cntr'-lem1 k (suc k' , k'<) (x , y) = 
-- -- -- -- -- --        ⊎.rec (λ x → x) (⊥.rec ∘ y ∘ cong suc)
-- -- -- -- -- --         (≤-split {suc k'} {suc (k ℕ.· 2)} k'<)


-- -- -- -- -- --  -- Iso-cntr'-lem2 : ∀ k → (k' : (Fin·2 k)) → 
-- -- -- -- -- --  --      (¬ suc (fst k') ≡ zero) × (¬ suc (suc (fst k')) ≡ (suc k) ℕ.· 2)
-- -- -- -- -- --  -- Iso-cntr'-lem2 k k' = snotz , {!!}


-- -- -- -- -- --  Iso-cntr' : ∀ k → Iso (Σ (Fin·2 (suc k)) λ k' →
-- -- -- -- -- --                      (¬ (fst k' ≡ zero) ) × (¬ (suc (fst k') ≡ ((suc k) ℕ.· 2))))
-- -- -- -- -- --                        (Fin·2 k)

-- -- -- -- -- --  fst (Iso.fun (Iso-cntr' k) x) = predℕ (fst (fst x))
-- -- -- -- -- --  snd (Iso.fun (Iso-cntr' k) x) = uncurry (Iso-cntr'-lem1 k) x
-- -- -- -- -- --  fst (Iso.inv (Iso-cntr' k) x) = suc (fst x) , <-weaken {n = k ℕ.· 2} (snd x)
-- -- -- -- -- --  snd ((Iso.inv (Iso-cntr' k)) (k' , k'<)) =
-- -- -- -- -- --    snotz , <→≢ {k'} { k ℕ.· 2} k'< ∘ cong (predℕ ∘ predℕ)
-- -- -- -- -- --  Iso.rightInv (Iso-cntr' k) b = Σ≡Prop (
-- -- -- -- -- --    λ x → OR.isProp≤ {suc x} { k ℕ.· 2}) refl
-- -- -- -- -- --  Iso.leftInv (Iso-cntr' k) x =
-- -- -- -- -- --    Σ≡Prop (λ x → isProp× (isProp¬ _) (isProp¬ _))
-- -- -- -- -- --      (Σ≡Prop (λ x → OR.isProp≤ {suc x} { (suc k) ℕ.· 2})
-- -- -- -- -- --        (sym (suc-predℕ _ (fst (snd x)))))

-- -- -- -- -- --  Iso-cntr'R : ∀ k → Iso
-- -- -- -- -- --       (Bool ⊎
-- -- -- -- -- --        Σ (Fin·2 (suc k))
-- -- -- -- -- --        (λ k' → (¬ fst k' ≡ zero) × (¬ suc (fst k') ≡ (suc k) ℕ.· 2)))
-- -- -- -- -- --       (Fin·2 (suc k))
-- -- -- -- -- --  Iso-cntr'R k = w
-- -- -- -- -- --   where

-- -- -- -- -- --   wInv : (k' : Fin·2 (suc k))
-- -- -- -- -- --      → Dec (fst k' ≡ zero)
-- -- -- -- -- --      → Dec (suc (fst k') ≡ (suc k) ℕ.· 2)
-- -- -- -- -- --      → _
-- -- -- -- -- --   wInv k' (yes p) x₁ = inl false
-- -- -- -- -- --   wInv k' (no ¬p) (yes p) = inl true
-- -- -- -- -- --   wInv k' (no ¬p) (no ¬p₁) = inr (k' , ¬p , ¬p₁)

-- -- -- -- -- --   to = ⊎.rec
-- -- -- -- -- --       (if_then ((suc (k ℕ.· 2))) , ≤-refl (suc (k ℕ.· 2))
-- -- -- -- -- --     else zero , _) fst

-- -- -- -- -- --   wLI : ∀ a u v → wInv (to a) u v ≡ a 
-- -- -- -- -- --   wLI (inl false) (yes p) v = refl
-- -- -- -- -- --   wLI (inl true) (yes p) v = ⊥.rec (snotz p)
-- -- -- -- -- --   wLI (inr (x , x₁)) (yes p) v = ⊥.rec (fst x₁ p)
-- -- -- -- -- --   wLI (inl false) (no ¬p) (yes p) = ⊥.rec (znots (injSuc p))
-- -- -- -- -- --   wLI (inl true) (no ¬p) (yes p) = refl
-- -- -- -- -- --   wLI (inr (x , x₁)) (no ¬p) (yes p) = ⊥.rec (snd x₁ p)
-- -- -- -- -- --   wLI (inl false) (no ¬p) (no ¬p₁) = ⊥.rec (¬p refl)
-- -- -- -- -- --   wLI (inl true) (no ¬p) (no ¬p₁) = ⊥.rec (¬p₁ refl)
-- -- -- -- -- --   wLI (inr x) (no ¬p) (no ¬p₁) = cong inr
-- -- -- -- -- --     (Σ≡Prop (λ x → isProp× (isProp¬ _) (isProp¬ _))
-- -- -- -- -- --      (Σ≡Prop (λ x → OR.isProp≤ {suc x} { (suc k) ℕ.· 2})
-- -- -- -- -- --        refl))
  
-- -- -- -- -- --   wRI : ∀ k' k< u → ⊎.rec
-- -- -- -- -- --       (if_then suc (k ℕ.· 2) , ≤-refl (k ℕ.· 2) else zero , tt)
-- -- -- -- -- --       (λ r → fst r)
-- -- -- -- -- --       (wInv (suc k' , k<) (no snotz) u)
-- -- -- -- -- --       ≡ (suc k' , k<)
-- -- -- -- -- --   wRI k' k< (yes p) = Σ≡Prop (λ x → OR.isProp≤ {x}) (sym (injSuc p))
-- -- -- -- -- --   wRI k' k< (no ¬p) = refl

-- -- -- -- -- --   w : Iso _ _
-- -- -- -- -- --   Iso.fun w = to
-- -- -- -- -- --   Iso.inv w x = wInv x (discreteℕ _ _ ) (discreteℕ _ _ ) 
-- -- -- -- -- --   Iso.rightInv w (zero , snd₁) = refl
-- -- -- -- -- --   Iso.rightInv w (suc k' , k<) = wRI k' k< (discreteℕ _ _)
-- -- -- -- -- --   Iso.leftInv w a = wLI a (discreteℕ _ _ ) (discreteℕ _ _ )


-- -- -- -- -- --  Iso-cntr : ∀ k → Iso (Bool ⊎ Fin·2 k) (Fin·2 (suc k))

-- -- -- -- -- --  Iso-cntr k =
-- -- -- -- -- --    compIso (⊎Iso idIso (invIso (Iso-cntr' k)))
-- -- -- -- -- --     (Iso-cntr'R k) 

-- -- -- -- -- --  IsoIdxFin·2 : ∀ r → Iso (Idx×𝟚 r) (Fin·2 (redLen r)) 
-- -- -- -- -- --  IsoIdxFin·2Hlp : ∀ (r : _ ⊎ Red) → Iso (IdxHlp r × Bool) (Fin·2 (redLenHlp r))
-- -- -- -- -- --  IsoIdxFin·2Hlp (inl x) = compIso lUnit×Iso Iso-Fin·2
-- -- -- -- -- --  IsoIdxFin·2Hlp (inr x) = IsoIdxFin·2 x


-- -- -- -- -- --  FinRec≡Iso : ∀ {n m} → n ≡ m → Iso (Σ _ (_< n)) (Σ _ (_< m)) 
-- -- -- -- -- --  FinRec≡Iso {n} {m} p = Σ-cong-iso-snd w
-- -- -- -- -- --   where
-- -- -- -- -- --   w : ∀ x → Iso (x < n) (x < m)
-- -- -- -- -- --   Iso.fun (w x) = subst (x <_) p 
-- -- -- -- -- --   Iso.inv (w x) = subst (x <_) (sym p)
-- -- -- -- -- --   Iso.rightInv (w x) b = OR.isProp≤ {suc x} {m} _ _
-- -- -- -- -- --   Iso.leftInv (w x) a = OR.isProp≤ {suc x} {n} _ _

-- -- -- -- -- --  IsoIdxFin·2 [] = compIso (compIso (ΣEmptyIso _) (invIso (ΣEmptyIso _)))
-- -- -- -- -- --                    Σ-swap-Iso 
-- -- -- -- -- --  IsoIdxFin·2 (x cj∷ r) =
-- -- -- -- -- --    let z = IsoIdxFin·2 r
-- -- -- -- -- --    in compIso
-- -- -- -- -- --          (compIso Σ⊎Iso (⊎Iso lUnit×Iso (IsoIdxFin·2 r)))
-- -- -- -- -- --          (Iso-cntr (redLen r))

   
-- -- -- -- -- --  IsoIdxFin·2 (x ·∷ r) =
-- -- -- -- -- --    compIso (compIso Σ⊎Iso
-- -- -- -- -- --      (⊎Iso (IsoIdxFin·2 x) (IsoIdxFin·2 r)))
-- -- -- -- -- --       (compIso (IsoFin⊎ (redLen x ℕ.· 2) (redLen r ℕ.· 2))
-- -- -- -- -- --        (FinRec≡Iso (·-distribʳ (redLen x) (redLen r) 2)))
    
-- -- -- -- -- -- --  -- k→idx : ∀ {ℓX} {X} r →
-- -- -- -- -- -- --  --   ∀ k → (k < redLen r ℕ.· 2) → Σ (Idx {ℓX} {X} r × Bool)
-- -- -- -- -- -- --  --      (λ (ix , b) → idx→k r ix b ≡ k) 
-- -- -- -- -- -- --  -- k→idx (x₁ cj∷ r) zero x = (inl _ , false) , refl
-- -- -- -- -- -- --  -- k→idx (x₁ cj∷ r) (suc k) x = {!!}
-- -- -- -- -- -- --  -- k→idx (x₁ ·∷ r) k x = {!!}
 
-- -- -- -- -- --  RedRels : ∀ {ℓX} {X} r → (x : Idx {ℓX} {X} r) → (y : Idx r) →
-- -- -- -- -- --       (Σ ((Σ Type Dec) × (Σ Type Dec) × (Σ Type Dec) × (Σ Type Dec))
-- -- -- -- -- --        λ ((⊃r , _) , (⊇r , _) , (<r , _) , (≤r , _)) →
-- -- -- -- -- --          (⊃r → ⊇r) × (x ≡ y → ⊇r) ×
-- -- -- -- -- --           (<r → ≤r) × (x ≡ y → ≤r))
          
-- -- -- -- -- --  RedRels (x₁ ∷ r) (inr x) (inl x₂) =
-- -- -- -- -- --    ((⊥ , no λ ()) , (⊥ , no λ ()) , (⊥ , no λ ()) , (⊥ , no λ ())) ,
-- -- -- -- -- --    (λ ()) , lower ∘ ⊎.⊎Path.encode (inr x) (inl x₂) ,
-- -- -- -- -- --     (λ ()) , lower ∘ ⊎.⊎Path.encode (inr x) (inl x₂)
-- -- -- -- -- --  RedRels (x₁ ∷ r) (inr x) (inr x₂) =
-- -- -- -- -- --   let (z , (p , p' , p'' , p''')) = RedRels r x x₂
-- -- -- -- -- --   in z , p , p' ∘ isEmbedding→Inj ⊎.isEmbedding-inr _ _ ,
-- -- -- -- -- --          p'' , p''' ∘ isEmbedding→Inj ⊎.isEmbedding-inr _ _
-- -- -- -- -- --  RedRels (x₁ cj∷ r) (inl x) (inl x₂) =
-- -- -- -- -- --   ((⊥ , no λ ()) , (Unit , yes tt) , (⊥ , no λ ()) , Unit , yes tt) ,
-- -- -- -- -- --    (λ _ → tt) , ((λ _ → tt) , (λ _ → tt) , (λ _ → tt))
-- -- -- -- -- --  RedRels (r ·∷ _) (inl x) (inl x₂) =
-- -- -- -- -- --   let (z , (p , p' , p'' , p''')) = RedRels r x x₂
-- -- -- -- -- --   in z , p , p' ∘ isEmbedding→Inj ⊎.isEmbedding-inl _ _ ,
-- -- -- -- -- --          p'' , p''' ∘ isEmbedding→Inj ⊎.isEmbedding-inl _ _
-- -- -- -- -- --  RedRels (x₁ cj∷ r) (inl x) (inr x₂) =
-- -- -- -- -- --    ((Unit , yes tt) , (Unit , yes tt) , (⊥ , no λ ()) , (⊥ , no λ ())) ,
-- -- -- -- -- --    (λ x₃ → tt) , (λ _ → tt) , ((λ ()) , lower ∘ ⊎.⊎Path.encode (inl x) (inr x₂))
-- -- -- -- -- --  RedRels (x₁ ·∷ r) (inl x) (inr x₂) =
-- -- -- -- -- --    ((⊥ , no λ ()) , (⊥ , no λ ()) , (Unit , yes tt) , (Unit , yes tt)) ,
-- -- -- -- -- --    ((λ ())) , lower ∘ ⊎.⊎Path.encode (inl x) (inr x₂) , (λ x₃ → tt) , (λ _ → tt)

-- -- -- -- -- --  module _ {ℓX} {X} {r : Red* {ℓX} X} (x y : Idx r) where
-- -- -- -- -- --   rr = fst (RedRels r x y)
  
-- -- -- -- -- --   _<r_ : Type
-- -- -- -- -- --   _<r_ = fst (fst (snd (snd rr)))

-- -- -- -- -- --   _≤r_ : Type
-- -- -- -- -- --   _≤r_ = fst (snd (snd (snd rr)))

-- -- -- -- -- --   _⊃r_ : Type
-- -- -- -- -- --   _⊃r_ = fst (fst (rr))
  
-- -- -- -- -- --   _⊇r_ : Type
-- -- -- -- -- --   _⊇r_ = fst (fst (snd rr))

-- -- -- -- -- --  module _ {ℓX} {X} {r : Red* {ℓX} X} (x y : Idx r) where
-- -- -- -- -- --   adjIdxCases : Type
-- -- -- -- -- --   adjIdxCases =
-- -- -- -- -- --        (x ≡ y)
-- -- -- -- -- --      ⊎ ((x <r y) ⊎ ((x ⊇r y) ⊎ (y ⊇r x) ))

-- -- -- -- -- --  HasRedexSplitCases++ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- --  HasRedexSplitCases++ xs ys =
-- -- -- -- -- --    (HasRedex xs ⊎ HasRedex ys) ⊎
-- -- -- -- -- --      Σ ((Bool × A))
-- -- -- -- -- --         λ (b , a) →
-- -- -- -- -- --           WillReduceʳ (not b) a xs ×
-- -- -- -- -- --             WillReduce b a ys
 
-- -- -- -- -- --  hasRedexSplitCases++ : ∀ xs ys → HasRedex (xs ++ ys) →
-- -- -- -- -- --     HasRedexSplitCases++ xs ys
-- -- -- -- -- --  hasRedexSplitCases++ [] ys x = inl (inr x)

-- -- -- -- -- --  hasRedexSplitCases++ (x ∷ xs) ys (inr u) =
-- -- -- -- -- --   ⊎.map (⊎.map inr (idfun _))
-- -- -- -- -- --      (λ ((a , b) , (u , v)) →
-- -- -- -- -- --        (a , b) , WillReduceʳ∷ (not a , b) x xs u , v)
-- -- -- -- -- --      (hasRedexSplitCases++ xs ys u)
-- -- -- -- -- --  hasRedexSplitCases++ (x ∷ []) (x' ∷ ys) (inl u) =
-- -- -- -- -- --    inr (x , (refl , refl) , u)
-- -- -- -- -- --  hasRedexSplitCases++ (x₁ ∷ x₂ ∷ xs) ys (inl u) =
-- -- -- -- -- --    inl (inl (inl u))

-- -- -- -- -- --  HasRedexSplitCases∷ : (Bool × A) → (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- --  HasRedexSplitCases∷ (b , a) (b' , a') xs =
-- -- -- -- -- --    (WillReduce b a xs ⊎ WillReduceʳ b' a' xs)
-- -- -- -- -- --     ⊎ (HasRedex xs ⊎ (xs ≡ []))
 
-- -- -- -- -- --  hasRedexSplitCases∷ : ∀ b x b' x' xs →
-- -- -- -- -- --    HasRedex ((b , x) ∷ (xs ∷ʳ (b' , x'))) →
-- -- -- -- -- --        HasRedexSplitCases∷ (b , x) (b' , x') xs
-- -- -- -- -- --  hasRedexSplitCases∷ b x b' x' [] u = inr (inr refl)
-- -- -- -- -- --  hasRedexSplitCases∷ b x b' x' (x₁ ∷ xs) (inl x₂) = inl (inl x₂)
-- -- -- -- -- --  hasRedexSplitCases∷ b x b' x' (x₁ ∷ []) (inr (inl (p , q))) =
-- -- -- -- -- --    inl (inr (( sym (notnot b') ∙ sym (cong not p)) , sym q))
-- -- -- -- -- --  hasRedexSplitCases∷ b x b' x' (x₁ ∷ []) (inr (inr (inl ())))
-- -- -- -- -- --  hasRedexSplitCases∷ b x b' x' (x₁ ∷ []) (inr (inr (inr ())))
-- -- -- -- -- --  hasRedexSplitCases∷ _ _ b' x' ((b , x) ∷ xs@(_ ∷ _)) (inr u) =
-- -- -- -- -- --    ⊎.rec (⊎.rec (inr ∘ inl ∘ inl) (inl ∘ inr))
-- -- -- -- -- --          (⊎.rec (inr ∘ inl ∘ inr) (⊥.rec ∘ ¬cons≡nil))
-- -- -- -- -- --      (hasRedexSplitCases∷ b x b' x' xs u)

-- -- -- -- -- --  HasRedexSplitCases : (r : Red) → Type ℓ
-- -- -- -- -- --  HasRedexSplitCases [] = ⊥*
-- -- -- -- -- --  HasRedexSplitCases ((b , a) cj∷ r) = 
-- -- -- -- -- --    HasRedexSplitCases∷ (b , a) (not b , a) (evRed r) 
-- -- -- -- -- --  HasRedexSplitCases (x ·∷ r) = HasRedexSplitCases++ (evRed x) (evRed r)

-- -- -- -- -- --  hasRedexSplitCases : ∀ r → HasRedex (evRed r) → HasRedexSplitCases r
-- -- -- -- -- --  hasRedexSplitCases (x₁ cj∷ r) = hasRedexSplitCases∷ _ _ _ _ _
-- -- -- -- -- --  hasRedexSplitCases (x₁ ·∷ r) = hasRedexSplitCases++ _ _

-- -- -- -- -- --  -- RedViewR : ∀ (r : Red) xs (x : Bool × A) → Type ℓ
-- -- -- -- -- --  -- RedViewR r xs x = Σ (Red × Red)
-- -- -- -- -- --  --    λ (rl , rr) →
-- -- -- -- -- --  --      evRed (rl ·∷ (not₁ x cj∷ rr)) ≡ xs ∷ʳ x



-- -- -- -- -- --  RedViewR : ∀ (r : Red) (x : Bool × A) → Type ℓ
-- -- -- -- -- --  RedViewR r x = Σ (Red × Red)
-- -- -- -- -- --     λ (rl , rr) →
-- -- -- -- -- --       evRed (rl ·∷ (not₁ x cj∷ rr)) ≡ evRed r


-- -- -- -- -- --  redViewR : ∀ r x → WillReduceʳ (not (fst x)) (snd x) (evRed r)
-- -- -- -- -- --                → RedViewR r x 
-- -- -- -- -- --  redViewR (x cj∷ r) x' x₁ =
-- -- -- -- -- --   let x₁' = WillReduceʳ[∷ʳ] _ _ (x ∷ evRed r) (not₁ x)  x₁  
-- -- -- -- -- --   in ([] , r) ,
-- -- -- -- -- --       cong (evRed ∘ (_cj∷ r)) (ΣPathP x₁' ∙ not₁not₁ _)
-- -- -- -- -- --  redViewR (x ·∷ r) x' u = {!!}
-- -- -- -- -- --  --   let (w , q) = redViewR x x'
-- -- -- -- -- --  --        (subst (λ x →  WillReduceʳ (not (fst x')) (snd x') x)
-- -- -- -- -- --  --         (++-unit-r (evRed x))
-- -- -- -- -- --  --         u)
-- -- -- -- -- --  --   in w , q ∙ sym (++-unit-r (evRed x))
-- -- -- -- -- --  -- redViewR (x ·∷ r'@(x₁ ∷ r)) x' u = {!!}
-- -- -- -- -- --   -- let ((rL , rR) , p) = redViewR r x'
-- -- -- -- -- --   --            {!!} 
-- -- -- -- -- --   -- in {!!}

-- -- -- -- -- -- --  -- redViewR : ∀ r xs x → evRed r ≡ xs ∷ʳ x
-- -- -- -- -- -- --  --    → RedViewR r xs x
-- -- -- -- -- -- --  -- redViewR [] xs x = ⊥.rec ∘ ¬nil≡snoc
-- -- -- -- -- -- --  -- redViewR ((b' , a') cj∷ r) xs (b , a) p =
-- -- -- -- -- -- --  --  ([] , r) , cong {x = not b , a}
-- -- -- -- -- -- --  --               {y = b' , a'}
-- -- -- -- -- -- --  --               (λ x' → x' ∷ evRed r ++ not₁ x' ∷ [])
-- -- -- -- -- -- --  --                (cong not₁ (sym
-- -- -- -- -- -- --  --                  (snoc-inj₂ {xs = (b' , a') ∷ evRed r} {ys = xs} p))
-- -- -- -- -- -- --  --                  ∙ not₁not₁ (b' , a')) ∙ p

-- -- -- -- -- -- --  -- redViewR (rll ·∷ r) xs x x₁ = 
-- -- -- -- -- -- --  --  let ((rl , rr) , z) = redViewR r (drop (length (evRed rll)) xs) x (
-- -- -- -- -- -- --  --            sym (drop++ (evRed rll) _)
-- -- -- -- -- -- --  --              ∙∙ cong (drop (length (evRed rll))) x₁
-- -- -- -- -- -- --  --                 ∙∙ {!!})
-- -- -- -- -- -- --  --  in ((rll ·∷ rl) , rr) , (
-- -- -- -- -- -- --  --       ++-assoc (evRed rll) _ _
-- -- -- -- -- -- --  --        ∙∙ (cong (evRed rll ++_) z) ∙∙
-- -- -- -- -- -- --  --       {!!} )

-- -- -- -- -- --  RedViewL : ∀ (r : Red) (x : Bool × A) → Type ℓ
-- -- -- -- -- --  RedViewL r x = Σ (Red × Red)
-- -- -- -- -- --     λ (rl , rr) →
-- -- -- -- -- --       evRed ((not₁ x cj∷ rl) ·∷ rr) ≡ evRed r

-- -- -- -- -- --  redViewL : ∀ r x → WillReduce ((fst x)) (snd x) (evRed r)
-- -- -- -- -- --     → RedViewL r x
-- -- -- -- -- --  redViewL (x₂ cj∷ r) x (p₁ , p₂) =
-- -- -- -- -- --    (r , []) , ++-unit-r _ ∙ cong (evRed ∘ (_cj∷ r))
-- -- -- -- -- --       (ΣPathP (cong not p₁ ∙ notnot _ , p₂)) 
-- -- -- -- -- --  redViewL (x₂ ·∷ r) x q =
-- -- -- -- -- --    ⊎.rec (λ (p , q) →
-- -- -- -- -- --            let ((rL , rR) , p') = redViewL r x q
-- -- -- -- -- --             in (rL , rR) , p' ∙ cong (_++ evRed r) (sym p))
-- -- -- -- -- --          (λ q → 
-- -- -- -- -- --            let ((rL , rR) , p) = redViewL x₂ x q
-- -- -- -- -- --            in (rL , (rR ·∷ r)) ,
-- -- -- -- -- --                  cong (not₁ x ∷_)
-- -- -- -- -- --                    (sym (++-assoc _ (evRed rR) (evRed r)))
-- -- -- -- -- --                   ∙ cong (_++ evRed r) p)
-- -- -- -- -- --     (casesWillReduce++
-- -- -- -- -- --       (fst x , snd x)
-- -- -- -- -- --       (evRed x₂)
-- -- -- -- -- --       (evRed r)
-- -- -- -- -- --       q) 

-- -- -- -- -- --  reduceRed' : ∀ r → (u : HasRedex (evRed r)) → HasRedexSplitCases r → Red
-- -- -- -- -- --  reduceRed' (x' cj∷ r) u (inl (inl x)) =
-- -- -- -- -- --   let ((rl , rr) , p) = redViewL r x' x  
-- -- -- -- -- --   in rl ·∷ (x' cj∷ rr)
-- -- -- -- -- --  reduceRed' (x' cj∷ r) u (inl (inr x)) = 
-- -- -- -- -- --   let ((rl , rr) , p) = redViewR r x' x  
-- -- -- -- -- --   in (x' cj∷ rl) ·∷ rr
-- -- -- -- -- --  reduceRed' (x₁ cj∷ r) u (inr (inl x)) =
-- -- -- -- -- --    x₁ cj∷ reduceRed' r x (hasRedexSplitCases r x)
-- -- -- -- -- --  reduceRed' (x₁ cj∷ r) u (inr (inr x)) = []
-- -- -- -- -- --  reduceRed' (x₁ ·∷ r) u (inl (inl x)) =
-- -- -- -- -- --   reduceRed' x₁ x (hasRedexSplitCases x₁ x) ·∷ r
-- -- -- -- -- --  reduceRed' (x₁ ·∷ r) u (inl (inr x)) =
-- -- -- -- -- --    x₁ ·∷ reduceRed' r x (hasRedexSplitCases r x)
-- -- -- -- -- --  reduceRed' (x₁ ·∷ r) u (inr (x' , wrL , wrR)) =
-- -- -- -- -- --   let ((rl , rr) , p) = redViewR x₁ x' wrL  
-- -- -- -- -- --       ((rl' , rr') , p') = redViewL r x' wrR  
-- -- -- -- -- --   in rl ·∷ (x' cj∷ (rr ·∷ rr')) ·∷ rr'


-- -- -- -- -- -- -- --  -- reduceRed' : ∀ r → (u : HasRedex (evRed r)) → HasRedexSplitCases r
-- -- -- -- -- -- -- --  --   → Σ _ λ r' → (reduce _ u ≡ evRed r')
-- -- -- -- -- -- -- --  -- reduceRed' (x₁ cj∷ r) u x = {!!}
-- -- -- -- -- -- -- --  -- reduceRed' (x₁ ·∷ r) u (inl (inl x)) = {!!}
-- -- -- -- -- -- -- --  -- reduceRed' (x₁ ·∷ r) u (inl (inr x)) = {!!}
-- -- -- -- -- -- -- --  -- reduceRed' (x₁ ·∷ r) u (inr x) = {!x!}
 

-- -- -- -- -- -- -- --  -- hasRedexSplitCases∷ b x [] x₁ = inr (inr refl)
-- -- -- -- -- -- -- --  -- hasRedexSplitCases∷ b x (x₂ ∷ xs) (inl x₁) = inl (inl x₁)
-- -- -- -- -- -- -- --  -- hasRedexSplitCases∷ b x (x₂ ∷ []) (inr (inl (p , q))) =
-- -- -- -- -- -- -- --  --    inl (inr (cong not (sym (notnot b) ∙ sym p) , sym q))
-- -- -- -- -- -- -- --  -- hasRedexSplitCases∷ b x (x₂ ∷ []) (inr (inr (inl ())))
-- -- -- -- -- -- -- --  -- hasRedexSplitCases∷ b x (x₂ ∷ []) (inr (inr (inr ())))
-- -- -- -- -- -- -- --  -- hasRedexSplitCases∷ b x (x₂ ∷ x₃ ∷ xs) (inr (inl x₁)) =
-- -- -- -- -- -- -- --  --   inr (inl (inl x₁))
-- -- -- -- -- -- -- --  -- hasRedexSplitCases∷ b x (x₂ ∷ x₃ ∷ xs) (inr (inr x₁)) =
-- -- -- -- -- -- -- --  --  let z = hasRedexSplitCases∷ b x (x₃ ∷ xs) (inr x₁) 
-- -- -- -- -- -- -- --  --  in ⊎.map {!idfun _!} {!!} z

-- -- -- -- -- -- -- -- --  reduceRed : ∀ r → (u : HasRedex (evRed r)) →
-- -- -- -- -- -- -- -- --     Σ _ λ r' → (reduce _ u ≡ evRed r') 
-- -- -- -- -- -- -- -- --  reduceRed (x cj∷ r) u = {!!}
-- -- -- -- -- -- -- -- --  reduceRed (x ·∷ r) u = {!!}
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   w : HasRedex (evRed x ++ evRed r) →
-- -- -- -- -- -- -- -- --        HasRedexSplitCases (evRed x) (evRed r) →
-- -- -- -- -- -- -- -- --         (Σ Red (λ r' → reduce (evRed x ++ evRed r) u ≡ evRed r'))
-- -- -- -- -- -- -- -- --   w x x₁ = {!x !}
-- -- -- -- -- -- -- -- --   -- ⊎.rec (⊎.rec
-- -- -- -- -- -- -- -- --   --   (λ u →
-- -- -- -- -- -- -- -- --   --    let (x' , p) = reduceRed x u
-- -- -- -- -- -- -- -- --   --    in (x' ·∷ r) , {!cong (_++ (evRed r)) p!})
-- -- -- -- -- -- -- -- --   --   λ u →
-- -- -- -- -- -- -- -- --   --    let z = reduceRed r u
-- -- -- -- -- -- -- -- --   --    in {!!}) {!!}
-- -- -- -- -- -- -- -- --   --  (hasRedexSplitCases (evRed x) (evRed r) u)


-- -- -- -- -- -- -- -- -- -- --  [_]_≺_ : ∀ {ℓX} {X} r → Idx {ℓX} {X} r → Idx r → ((Σ Type Dec) × (Σ Type Dec))
-- -- -- -- -- -- -- -- -- -- --  [_]_≺_ (a cj∷ r) (inl x) (inl x₁) = (Unit , yes tt) , (⊥ , no λ ())
-- -- -- -- -- -- -- -- -- -- --  [_]_≺_ (a cj∷ r) (inl x) (inr x₁) = (⊥ , no λ ()) , (⊥ , no λ ())
-- -- -- -- -- -- -- -- -- -- --  [_]_≺_ (a cj∷ r) (inr x) (inl x₁) = (Unit , yes tt) , (Unit , yes tt)
-- -- -- -- -- -- -- -- -- -- --  [_]_≺_ (a cj∷ r) (inr x) (inr x₁) = [ r ] x ≺ x₁
-- -- -- -- -- -- -- -- -- -- --  [_]_≺_ (r ·∷ r') (inl x) (inl x₁) = [ r ] x ≺ x₁
-- -- -- -- -- -- -- -- -- -- --  [_]_≺_ (r ·∷ r') (inl x) (inr x₁) = (⊥ , no λ ()) , (⊥ , no λ ())
-- -- -- -- -- -- -- -- -- -- --  [_]_≺_ (r ·∷ r') (inr x) (inl x₁) = (⊥ , no λ ()) , (⊥ , no λ ())
-- -- -- -- -- -- -- -- -- -- --  [_]_≺_ (r ·∷ r') (inr x) (inr x₁) = [ r' ] x ≺ x₁



-- -- -- -- -- -- -- -- -- -- --  MarkedRed = Red* (Bool × (Bool × A))

-- -- -- -- -- -- -- -- -- -- --  toMarkedFresh : Red → MarkedRed
-- -- -- -- -- -- -- -- -- -- --  toMarkedFresh = mapRed (false ,_) 

-- -- -- -- -- -- -- -- -- -- --  _⊰_ : {r : Red} → Idx×𝟚 r → Idx×𝟚 r → Type  
-- -- -- -- -- -- -- -- -- -- --  _⊰_ {r} x y = 
-- -- -- -- -- -- -- -- -- -- --    fst (Iso.fun (IsoIdxFin·2 r) x)
-- -- -- -- -- -- -- -- -- -- --     < fst (Iso.fun (IsoIdxFin·2 r) y)

-- -- -- -- -- -- -- -- -- -- --  ⊰←≺ : {r : Red} → (x y : Idx r)
-- -- -- -- -- -- -- -- -- -- --             → fst (snd ([ r ] x ≺ y))
-- -- -- -- -- -- -- -- -- -- --             → (y , false) ⊰ (x , false)
-- -- -- -- -- -- -- -- -- -- --             × (x , true) ⊰ (y , true)
      
-- -- -- -- -- -- -- -- -- -- --  ⊰←≺ {x cj∷ r} (inr x₂) (inl x₃) x₁ =
-- -- -- -- -- -- -- -- -- -- --    _ , snd (IsoIdxFin·2 r .Iso.fun (x₂ , true))
-- -- -- -- -- -- -- -- -- -- --  ⊰←≺ {x cj∷ r} (inr x₂) (inr x₃) x₁ = ⊰←≺ {r} x₂ x₃ x₁
-- -- -- -- -- -- -- -- -- -- --  ⊰←≺ {x ·∷ r} (inl x₂) (inl x₃) x₁ = 
-- -- -- -- -- -- -- -- -- -- --   let (z , z') = ⊰←≺ {x} x₂ x₃ x₁
-- -- -- -- -- -- -- -- -- -- --   in {!z!} , {!!}
-- -- -- -- -- -- -- -- -- -- --  ⊰←≺ {x ·∷ r} (inr x₂) (inr x₃) x₁ = 
-- -- -- -- -- -- -- -- -- -- --    let (z , z') = ⊰←≺ {r} x₂ x₃ x₁
-- -- -- -- -- -- -- -- -- -- --    in {!z!}
 
-- -- -- -- -- -- -- -- -- -- --  ⊰→≺ : {r : Red} → (x y : Idx r)
-- -- -- -- -- -- -- -- -- -- --             → (y , false) ⊰ (x , false)
-- -- -- -- -- -- -- -- -- -- --             → (x , true) ⊰ (y , true)
-- -- -- -- -- -- -- -- -- -- --             → fst (snd ([ r ] x ≺ y))  
-- -- -- -- -- -- -- -- -- -- --  ⊰→≺ = {!!}

-- -- -- -- -- -- -- -- -- -- --  -- Mark' : ∀ {ℓ} {A : Type ℓ}
          
-- -- -- -- -- -- -- -- -- -- --  --          (B? : ∀ a → Bool ) → List A
-- -- -- -- -- -- -- -- -- -- --  --          → Bool → ℕ → Bool
-- -- -- -- -- -- -- -- -- -- --  -- Mark' B? [] b0 _ = b0
-- -- -- -- -- -- -- -- -- -- --  -- Mark' B? (x ∷ xs) b0 zero = b0
-- -- -- -- -- -- -- -- -- -- --  -- Mark' B? (x ∷ xs) b0 (suc k) =
-- -- -- -- -- -- -- -- -- -- --  --  Mark' B? (xs) (B? x ⊕ b0) k
  

-- -- -- -- -- -- -- -- -- -- --  ∫⊕ : (ℕ → Bool) → ℕ → Bool 
-- -- -- -- -- -- -- -- -- -- --  ∫⊕ f zero = false
-- -- -- -- -- -- -- -- -- -- --  ∫⊕ f (suc k) = f k ⊕ ∫⊕ f k

-- -- -- -- -- -- -- -- -- -- --  ∫⊕F' : ∀ {n} → ((Σ _ λ k → (k < n)) → Bool) → ∀ k → (k < n) → Bool 
-- -- -- -- -- -- -- -- -- -- --  ∫⊕F' {suc n} f (zero) k< = false
-- -- -- -- -- -- -- -- -- -- --  ∫⊕F' {suc n} f (suc k) k< =
-- -- -- -- -- -- -- -- -- -- --    f (k , <-weaken {n = n} k<) ⊕ ∫⊕F' {suc n} f k (<-weaken {n = n} k<)


-- -- -- -- -- -- -- -- -- -- --  ∫⊕F : ∀ {n} → ((Σ _ λ k → (k < n)) → Bool) → (Σ _ λ k → (k < n)) → Bool 
-- -- -- -- -- -- -- -- -- -- --  ∫⊕F {n} f = uncurry (∫⊕F' {n} f) 


-- -- -- -- -- -- -- -- -- -- --  ∫fromIx' : ∀ (r : Red) → (Idx r → Bool) → Bool → Idx×𝟚 r → Bool
-- -- -- -- -- -- -- -- -- -- --  ∫fromIx' (x₁ cj∷ r) f b' = uncurry $
-- -- -- -- -- -- -- -- -- -- --    let f? = f (inl _)
-- -- -- -- -- -- -- -- -- -- --    in ⊎.rec (λ _ bSide → if bSide then (f? ⊕ b') else b' )
-- -- -- -- -- -- -- -- -- -- --         (curry (∫fromIx' r (f ∘ inr) (f? ⊕ b')))
-- -- -- -- -- -- -- -- -- -- --  ∫fromIx' (x₁ ·∷ r) f b' =
-- -- -- -- -- -- -- -- -- -- --    uncurry $ ⊎.rec ((curry (∫fromIx' x₁ (f ∘ inl) b' ))) (curry (∫fromIx' r (f ∘ inr) b' ))




-- -- -- -- -- -- -- -- -- -- --  -- ∫fromIx : ∀ (r : Red) → (Idx r → Bool) → Idx×𝟚 r → Bool
-- -- -- -- -- -- -- -- -- -- --  -- ∫fromIx r f = ∫fromIx' r f false

-- -- -- -- -- -- -- -- -- -- --  -- ∫fromIxLem : ∀ (r : Red) → (f : Idx r → Bool) →
-- -- -- -- -- -- -- -- -- -- --  --  (ixA ixB : Idx r) → (∀ ix → fst (snd ([ r ] ixA ≺ ix))
-- -- -- -- -- -- -- -- -- -- --  --                   → fst (snd ([ r ] ix ≺ ixB)) → f ix ≡ false)
-- -- -- -- -- -- -- -- -- -- --  --   → {!!}
-- -- -- -- -- -- -- -- -- -- --  -- ∫fromIxLem = {!!}

-- -- -- -- -- -- -- -- -- -- -- --  -- f : ℕ → Bool
-- -- -- -- -- -- -- -- -- -- -- --  -- f 0 = false
-- -- -- -- -- -- -- -- -- -- -- --  -- f 1 = false
-- -- -- -- -- -- -- -- -- -- -- --  -- f 2 = true
-- -- -- -- -- -- -- -- -- -- -- --  -- f 3 = false
-- -- -- -- -- -- -- -- -- -- -- --  -- f 4 = false
-- -- -- -- -- -- -- -- -- -- -- --  -- f 5 = true
-- -- -- -- -- -- -- -- -- -- -- --  -- f _ = false

-- -- -- -- -- -- -- -- -- -- -- --  range : ℕ → List ℕ
-- -- -- -- -- -- -- -- -- -- -- --  range zero = []
-- -- -- -- -- -- -- -- -- -- -- --  range (suc k) = zero ∷ Li.map suc (range k)
 
-- -- -- -- -- -- -- -- -- -- -- --  -- fx = Li.map {B = Bool × Bool} (λ k → f k , ∫⊕ f k) (range 8)

 
-- -- -- -- -- -- -- -- -- -- -- --  -- fx' = (false , false) ∷
-- -- -- -- -- -- -- -- -- -- -- --  --         (false , false) ∷
-- -- -- -- -- -- -- -- -- -- -- --  --         (true , false) ∷
-- -- -- -- -- -- -- -- -- -- -- --  --         (false , true) ∷
-- -- -- -- -- -- -- -- -- -- -- --  --         (false , true) ∷
-- -- -- -- -- -- -- -- -- -- -- --  --         (true , true) ∷ (false , false) ∷ (false , false) ∷ []



-- -- -- -- -- -- -- -- -- -- -- --  module _ (r : Red) (q : Idx r → Bool) where

-- -- -- -- -- -- -- -- -- -- -- --   markIx : Idx×𝟚 r → Bool
-- -- -- -- -- -- -- -- -- -- -- --   markIx = ∫fromIx r (q)

-- -- -- -- -- -- -- -- -- -- -- --   markK : Fin·2 (redLen r) → Bool
-- -- -- -- -- -- -- -- -- -- -- --   markK =
-- -- -- -- -- -- -- -- -- -- -- --    let f = q ∘ fst ∘ Iso.inv (IsoIdxFin·2 r) 
-- -- -- -- -- -- -- -- -- -- -- --    in ∫⊕F {n = redLen r ℕ.· 2} f

-- -- -- -- -- -- -- -- -- -- -- --  lemFinInl : ∀ x r b u →
-- -- -- -- -- -- -- -- -- -- -- --     fst (Iso.fun (IsoIdxFin·2 x) (u , b))
-- -- -- -- -- -- -- -- -- -- -- --       ≡  fst (Iso.fun (IsoIdxFin·2 (x ·∷ r)) (inl u , b))
-- -- -- -- -- -- -- -- -- -- -- --  lemFinInl (x ∷ x₁) r b u = {!!}

-- -- -- -- -- -- -- -- -- -- -- --  markLem'·∷ : ∀ x r q u b → 
-- -- -- -- -- -- -- -- -- -- -- --    markK x (q ∘ inl) (Iso.fun (IsoIdxFin·2 x) (u , b))
-- -- -- -- -- -- -- -- -- -- -- --       ≡ markK (x ·∷ r) q (Iso.fun (IsoIdxFin·2 (x ·∷ r)) (inl u , b)) 
-- -- -- -- -- -- -- -- -- -- -- --  markLem'·∷ = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- --  markLem' : ∀ r q k → markIx r q k ≡ markK r q (Iso.fun (IsoIdxFin·2 r) k) 
-- -- -- -- -- -- -- -- -- -- -- --  markLem' (x cj∷ r) q (inl u , false) = refl
-- -- -- -- -- -- -- -- -- -- -- --  markLem' (x cj∷ r) q (inl u , true) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  markLem' (x ·∷ r) q (inl u , b) =
-- -- -- -- -- -- -- -- -- -- -- --   let z = markLem' x (q ∘ inl) (u , b)
-- -- -- -- -- -- -- -- -- -- -- --   in z ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- --  markLem' (x cj∷ r) q (inr u , b) = {!!} 
-- -- -- -- -- -- -- -- -- -- -- --  markLem' (x ·∷ r) q (inr u , b) = 
-- -- -- -- -- -- -- -- -- -- -- --   let z = markLem' r (q ∘ inr) (u , b)
-- -- -- -- -- -- -- -- -- -- -- --   in z ∙ {!!}


-- -- -- -- -- -- -- -- -- -- -- --  -- markLem : ∀ r q k → markIx r q (Iso.inv (IsoIdxFin·2 r) k) ≡ markK r q k 
-- -- -- -- -- -- -- -- -- -- -- --  -- markLem (x ∷ r) q k = {!!}

-- -- -- -- -- -- -- -- -- -- -- --  record ChainCtx : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- --    aR bR : Red
-- -- -- -- -- -- -- -- -- -- -- --    l : List (Bool × A)
-- -- -- -- -- -- -- -- -- -- -- --    0<lenL : 0 < length l 
-- -- -- -- -- -- -- -- -- -- -- --    aR++l=bR : evRed aR ++ l ≡ evRed bR

-- -- -- -- -- -- -- -- -- -- -- --   lenB≡lenA+lenL : (redLen bR) ℕ.· 2 ≡ 
-- -- -- -- -- -- -- -- -- -- -- --       ((redLen aR ℕ.· 2) + (length l))
-- -- -- -- -- -- -- -- -- -- -- --   lenB≡lenA+lenL =
-- -- -- -- -- -- -- -- -- -- -- --     lenEvRed≡redLen·2 bR ∙∙
-- -- -- -- -- -- -- -- -- -- -- --       cong length (sym aR++l=bR) ∙∙
-- -- -- -- -- -- -- -- -- -- -- --        (length++ (evRed aR) l ∙ cong (_+ length l)
-- -- -- -- -- -- -- -- -- -- -- --          (sym (lenEvRed≡redLen·2 aR)))
      
  
-- -- -- -- -- -- -- -- -- -- -- --   IsoIxBIxA⊎F : Iso (Idx×𝟚 bR) (Idx×𝟚 aR ⊎ Σ _ (_< (length l)))
-- -- -- -- -- -- -- -- -- -- -- --   IsoIxBIxA⊎F = 
-- -- -- -- -- -- -- -- -- -- -- --     compIso (IsoIdxFin·2 bR)
-- -- -- -- -- -- -- -- -- -- -- --       (compIso (compIso
-- -- -- -- -- -- -- -- -- -- -- --         (FinRec≡Iso lenB≡lenA+lenL)
-- -- -- -- -- -- -- -- -- -- -- --          (invIso (IsoFin⊎ (redLen aR ℕ.· 2) (length l))))
-- -- -- -- -- -- -- -- -- -- -- --        (⊎Iso (invIso (IsoIdxFin·2 aR)) idIso)) 

-- -- -- -- -- -- -- -- -- -- -- --   ixB∈aR : Idx bR × Bool → Type
-- -- -- -- -- -- -- -- -- -- -- --   ixB∈aR x = isInl (Iso.fun IsoIxBIxA⊎F x)

-- -- -- -- -- -- -- -- -- -- -- --   ixB∉aR : Idx bR × Bool → Type
-- -- -- -- -- -- -- -- -- -- -- --   ixB∉aR x = isInr (Iso.fun IsoIxBIxA⊎F x)

-- -- -- -- -- -- -- -- -- -- -- --   overEdgeBidx : Idx bR → Type
-- -- -- -- -- -- -- -- -- -- -- --   overEdgeBidx idx =
-- -- -- -- -- -- -- -- -- -- -- --     ixB∈aR (idx , false)
-- -- -- -- -- -- -- -- -- -- -- --      × ixB∉aR (idx , true)

-- -- -- -- -- -- -- -- -- -- -- --   _b↔a_ : Idx×𝟚 bR → Idx×𝟚 aR → Type
-- -- -- -- -- -- -- -- -- -- -- --   _b↔a_ bIx aIx = Iso.fun IsoIxBIxA⊎F bIx ≡ inl aIx



-- -- -- -- -- -- -- -- -- -- -- --   data Chain : Type

-- -- -- -- -- -- -- -- -- -- -- --   headCh : Chain → Idx×𝟚 bR

-- -- -- -- -- -- -- -- -- -- -- --   _↖↙_ : Idx×𝟚 bR → Idx×𝟚 bR → Type 
-- -- -- -- -- -- -- -- -- -- -- --   (ixB , b) ↖↙ ixB'  =
-- -- -- -- -- -- -- -- -- -- -- --    Σ (ixB∈aR ixB') λ p → 
-- -- -- -- -- -- -- -- -- -- -- --     ((ixB , not b) ≡
-- -- -- -- -- -- -- -- -- -- -- --       Iso.inv IsoIxBIxA⊎F (inl (map-snd not (fromIsInl _ p))))

-- -- -- -- -- -- -- -- -- -- -- --   record ChainStep (xs : Chain) : Type where
-- -- -- -- -- -- -- -- -- -- -- --    pattern
-- -- -- -- -- -- -- -- -- -- -- --    constructor cs[_,_]
-- -- -- -- -- -- -- -- -- -- -- --    field
-- -- -- -- -- -- -- -- -- -- -- --     ixB : _
-- -- -- -- -- -- -- -- -- -- -- --     link : ixB ↖↙ (headCh xs)

-- -- -- -- -- -- -- -- -- -- -- --   open ChainStep

-- -- -- -- -- -- -- -- -- -- -- --   data Chain where
-- -- -- -- -- -- -- -- -- -- -- --    [_,_] : ∀ ixB → overEdgeBidx ixB → Chain
-- -- -- -- -- -- -- -- -- -- -- --    _∷_ : ∀ xs → ChainStep xs → Chain

-- -- -- -- -- -- -- -- -- -- -- --   headCh [ ixB , x ] = ixB , false
-- -- -- -- -- -- -- -- -- -- -- --   headCh (xs ∷ cs[ ixB , x₁ ]) = ixB

-- -- -- -- -- -- -- -- -- -- -- --   startCh : Chain → Idx×𝟚 bR
-- -- -- -- -- -- -- -- -- -- -- --   startCh [ ixB , x ] = ixB , true
-- -- -- -- -- -- -- -- -- -- -- --   startCh (xs ∷ cs[ ixB , x₁ ]) = startCh xs


-- -- -- -- -- -- -- -- -- -- -- --   chainStep? : ∀ xs → Dec (ChainStep xs)
-- -- -- -- -- -- -- -- -- -- -- --   chainStep? xs = w (_ , refl)
-- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- --    w : ((x , _) : singl (Iso.fun IsoIxBIxA⊎F (headCh xs)))
-- -- -- -- -- -- -- -- -- -- -- --           → Dec (ChainStep xs)
-- -- -- -- -- -- -- -- -- -- -- --    w (inl x , p) = yes cs[
-- -- -- -- -- -- -- -- -- -- -- --           map-snd not
-- -- -- -- -- -- -- -- -- -- -- --            (Iso.inv IsoIxBIxA⊎F (inl (map-snd not
-- -- -- -- -- -- -- -- -- -- -- --              (fromIsInl (Iso.fun IsoIxBIxA⊎F (headCh xs))
-- -- -- -- -- -- -- -- -- -- -- --               (subst isInl (sym p) _)))))
-- -- -- -- -- -- -- -- -- -- -- --           , ((subst isInl (sym p) _) , ΣPathP (refl , notnot _)) ]
-- -- -- -- -- -- -- -- -- -- -- --    w (inr x , p) = no ((subst isInl p ∘ fst) ∘ link)

-- -- -- -- -- -- -- -- -- -- -- --   IsCompleted : Chain → Type
-- -- -- -- -- -- -- -- -- -- -- --   IsCompleted xs = ¬ (ChainStep xs)

-- -- -- -- -- -- -- -- -- -- -- --   bIsInCh : Chain → Idx bR → Σ Type Dec
-- -- -- -- -- -- -- -- -- -- -- --   bIsInCh [ ixB , _ ] ixB' = _ , discreteIdx bR ixB ixB'
-- -- -- -- -- -- -- -- -- -- -- --   bIsInCh (xs ∷ cs[ (ixB , _) , _ ]) ixB' =
-- -- -- -- -- -- -- -- -- -- -- --    let (t , t?) = bIsInCh xs ixB'
-- -- -- -- -- -- -- -- -- -- -- --    in ((ixB ≡ ixB') ⊎ t) ,
-- -- -- -- -- -- -- -- -- -- -- --         ⊎Dec (discreteIdx bR ixB ixB') t? 

-- -- -- -- -- -- -- -- -- -- -- --   -- aIsInCh : Chain → Idx aR → Σ Type Dec
-- -- -- -- -- -- -- -- -- -- -- --   -- aIsInCh = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   -- -- inCh? : Chain → Idx bR → Bool
-- -- -- -- -- -- -- -- -- -- -- --   -- -- inCh? [ ixB , _ ] ixB' = {!ixB!}
-- -- -- -- -- -- -- -- -- -- -- --   -- -- inCh? (x ∷ x₂) x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   -- markF : ℕ → Bool
-- -- -- -- -- -- -- -- -- -- -- --   -- markF k = {!!}


-- -- -- -- -- -- -- -- -- -- -- --   markB : Chain → Idx×𝟚 bR → Bool
-- -- -- -- -- -- -- -- -- -- -- --   markB ch = ∫fromIx bR (Dec→Bool ∘ snd ∘ bIsInCh ch)

-- -- -- -- -- -- -- -- -- -- -- --   -- markA : Chain → Idx×𝟚 aR → Bool
-- -- -- -- -- -- -- -- -- -- -- --   -- markA ch = ∫fromIx aR (Dec→Bool ∘ snd ∘ aIsInCh ch)
  
-- -- -- -- -- -- -- -- -- -- -- --   mark : Chain → Fin·2 (redLen bR) → Bool
-- -- -- -- -- -- -- -- -- -- -- --   mark ch =
-- -- -- -- -- -- -- -- -- -- -- --    let f = (Dec→Bool ∘ snd ∘ bIsInCh ch ∘ fst) ∘ Iso.inv (IsoIdxFin·2 bR) 
-- -- -- -- -- -- -- -- -- -- -- --    in ∫⊕F {n = redLen bR ℕ.· 2} f

-- -- -- -- -- -- -- -- -- -- -- --   markB= : (ch : Chain) → (ix : Idx×𝟚 bR) → 
-- -- -- -- -- -- -- -- -- -- -- --           markB ch ix ≡
-- -- -- -- -- -- -- -- -- -- -- --             mark ch (Iso.fun (IsoIdxFin·2 bR) ix)
-- -- -- -- -- -- -- -- -- -- -- --   markB= ch = markLem' bR (Dec→Bool ∘ snd ∘ bIsInCh ch)


-- -- -- -- -- -- -- -- -- -- -- --   insCh0-lem :
-- -- -- -- -- -- -- -- -- -- -- --     ∀ ch x → IsCompleted ch →
-- -- -- -- -- -- -- -- -- -- -- --        (fst (Iso.fun (IsoIdxFin·2 bR) (startCh ch))
-- -- -- -- -- -- -- -- -- -- -- --        < fst (Iso.fun (IsoIdxFin·2 bR) (x , true)))
-- -- -- -- -- -- -- -- -- -- -- --        ×  (fst (Iso.fun (IsoIdxFin·2 bR) (x , true))
-- -- -- -- -- -- -- -- -- -- -- --            < fst (Iso.fun (IsoIdxFin·2 bR) (headCh ch)))
-- -- -- -- -- -- -- -- -- -- -- --         → ¬ fst (bIsInCh ch x)
-- -- -- -- -- -- -- -- -- -- -- --   insCh0-lem [ ixB₁ , x₁ ] x _ (u , v) =
-- -- -- -- -- -- -- -- -- -- -- --      <→≢ {n = fst (Iso.fun (IsoIdxFin·2 bR) (ixB₁ , true))}
-- -- -- -- -- -- -- -- -- -- -- --       {fst (Iso.fun (IsoIdxFin·2 bR) (x , true))} u
-- -- -- -- -- -- -- -- -- -- -- --        ∘ cong (λ x → fst (Iso.fun (IsoIdxFin·2 bR) (x , true)))
-- -- -- -- -- -- -- -- -- -- -- --   insCh0-lem (ch ∷ cs[ ixB₁ , link₁ ]) x _ (u , v) =
-- -- -- -- -- -- -- -- -- -- -- --     ⊎.rec (<→≢ {n = fst (Iso.fun (IsoIdxFin·2 bR) (x , true))}
-- -- -- -- -- -- -- -- -- -- -- --       {fst (Iso.fun (IsoIdxFin·2 bR) ixB₁)} v ∘
-- -- -- -- -- -- -- -- -- -- -- --         {!!})
-- -- -- -- -- -- -- -- -- -- -- --       {!!}
  
-- -- -- -- -- -- -- -- -- -- -- --   -- chainInChainLem0< : ∀ ch x → IsCompleted ch →
-- -- -- -- -- -- -- -- -- -- -- --   --     fst (Iso.fun (IsoIdxFin·2 bR) (startCh ch))
-- -- -- -- -- -- -- -- -- -- -- --   --      < fst (Iso.fun (IsoIdxFin·2 bR) (headCh ch))
-- -- -- -- -- -- -- -- -- -- -- --   --      → fst (Iso.fun (IsoIdxFin·2 bR) (headCh ch)) <
-- -- -- -- -- -- -- -- -- -- -- --   --         fst (Iso.fun (IsoIdxFin·2 bR) (x , true))
-- -- -- -- -- -- -- -- -- -- -- --   --       → ¬ fst (bIsInCh ch x) 
-- -- -- -- -- -- -- -- -- -- -- --   -- chainInChainLem0< = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --   chainInChainLem0 : ∀ ch x' → IsCompleted ch →
-- -- -- -- -- -- -- -- -- -- -- -- --      fst (Iso.fun (IsoIdxFin·2 bR) x')
-- -- -- -- -- -- -- -- -- -- -- -- --        < fst (Iso.fun (IsoIdxFin·2 bR) (headCh ch))
-- -- -- -- -- -- -- -- -- -- -- -- --      → fst (Iso.fun (IsoIdxFin·2 bR) (startCh ch))
-- -- -- -- -- -- -- -- -- -- -- -- --         < fst (Iso.fun (IsoIdxFin·2 bR) x')
-- -- -- -- -- -- -- -- -- -- -- -- --         → markB ch x' ≡ true 
-- -- -- -- -- -- -- -- -- -- -- -- --   chainInChainLem0 = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --   chainInChainLem : ∀ ch ch' → IsCompleted ch → IsCompleted ch' →
-- -- -- -- -- -- -- -- -- -- -- -- --      fst (Iso.fun (IsoIdxFin·2 bR) (startCh ch'))
-- -- -- -- -- -- -- -- -- -- -- -- --        < fst (Iso.fun (IsoIdxFin·2 bR) (headCh ch))
-- -- -- -- -- -- -- -- -- -- -- -- --      → fst (Iso.fun (IsoIdxFin·2 bR) (startCh ch))
-- -- -- -- -- -- -- -- -- -- -- -- --         < fst (Iso.fun (IsoIdxFin·2 bR) (startCh ch'))
-- -- -- -- -- -- -- -- -- -- -- -- --         → ∀ x → fst (bIsInCh ch' (fst x)) →
-- -- -- -- -- -- -- -- -- -- -- -- --           markB ch x ≡ true 
-- -- -- -- -- -- -- -- -- -- -- -- --   chainInChainLem = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   ixB∈aR→ixA : ∀ idxB → ixB∈aR idxB → Idx aR × Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- --   ixB∈aR→ixA = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- --   infixr 5 _b∷_[_,_] _a∷_[_,_]


-- -- -- -- -- -- -- -- -- -- -- -- -- --   data ChainA : Type
-- -- -- -- -- -- -- -- -- -- -- -- -- --   data ChainB : Type 

-- -- -- -- -- -- -- -- -- -- -- -- -- --   _B∉chA_ : Idx×𝟚 bR → ChainA → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- --   _B∉chB_ : Idx×𝟚 bR → ChainB → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- --   _A∉chB_ : Idx×𝟚 aR → ChainB → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- --   _A∉chA_ : Idx×𝟚 aR → ChainA → Type


-- -- -- -- -- -- -- -- -- -- -- -- -- --   _a←b_ : Idx×𝟚 aR → Idx×𝟚 bR → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- --   _b←a_ : Idx×𝟚 bR → Idx×𝟚 aR → Type

-- -- -- -- -- -- -- -- -- -- -- -- -- --   headA : ChainA → Idx×𝟚 aR
-- -- -- -- -- -- -- -- -- -- -- -- -- --   headB : ChainB → Idx×𝟚 bR

-- -- -- -- -- -- -- -- -- -- -- -- -- --   data ChainB where 
-- -- -- -- -- -- -- -- -- -- -- -- -- --    [_,_] : ∀ ixB → overEdgeBidx ixB → ChainB
-- -- -- -- -- -- -- -- -- -- -- -- -- --    _b∷_[_,_] : ∀ ixB → (chA : ChainA)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      → ixB b←a (headA chA) → ixB B∉chA chA  → ChainB
   
-- -- -- -- -- -- -- -- -- -- -- -- -- --   data ChainA  where 
-- -- -- -- -- -- -- -- -- -- -- -- -- --    _a∷_[_,_] : ∀ ixA → (chB : ChainB)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      → ixA a←b (headB chB) → ixA A∉chB chB  → ChainA


-- -- -- -- -- -- -- -- -- -- -- -- -- --   headA (ixA a∷ chB [ _ , _ ]) = ixA

-- -- -- -- -- -- -- -- -- -- -- -- -- --   headB [ ixB , x ] = ixB , false
-- -- -- -- -- -- -- -- -- -- -- -- -- --   headB (ixB b∷ chA [ _ , _ ]) = ixB

-- -- -- -- -- -- -- -- -- -- -- -- -- --   (ixA , bA) a←b ixB = ixB b↔a (ixA , not bA)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   (ixB , bB) b←a ixA = (ixB , not bB) b↔a ixA
  
  
  
-- -- -- -- -- -- -- -- -- -- -- -- -- --   x B∉chA (ixA a∷ chB [ _ , _ ]) = x B∉chB chB
-- -- -- -- -- -- -- -- -- -- -- -- -- --   x B∉chB [ ixB , x₁ ] = ¬ (fst x ≡ ixB)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   x B∉chB (ixB b∷ chA [ _ , _ ]) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --     (¬ (fst x ≡ fst ixB)) × (x B∉chA chA) 
-- -- -- -- -- -- -- -- -- -- -- -- -- --   x A∉chA (ixA a∷ chB [ _ , _ ]) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --     (¬ (fst x ≡ fst ixA)) × (x A∉chB chB) 
-- -- -- -- -- -- -- -- -- -- -- -- -- --   x A∉chB [ ixB  , _ ] = Unit
-- -- -- -- -- -- -- -- -- -- -- -- -- --   x A∉chB (ixB b∷ chA [ _ , _ ]) = x A∉chA chA

-- -- -- -- -- -- -- -- -- -- -- -- -- --   Completed : ChainB → Type  
-- -- -- -- -- -- -- -- -- -- -- -- -- --   Completed chB = overEdgeBidx (fst  (headB chB)) × (snd (headB chB) ≡ true)

-- -- -- -- -- -- -- -- -- -- -- -- -- --   stepA∉ : ∀ chA → map-snd not (Iso.inv IsoIxBIxA⊎F (inl (headA chA))) B∉chA chA
-- -- -- -- -- -- -- -- -- -- -- -- -- --   stepA∉ (ixA a∷ [ ixB , (inlIxbF , inrIxbR )  ] [ x , x₁ ]) p =
-- -- -- -- -- -- -- -- -- -- -- -- -- --     let z : snd (Iso.inv IsoIxBIxA⊎F (inl ixA)) ≡ true
-- -- -- -- -- -- -- -- -- -- -- -- -- --         z = ¬false→true _
-- -- -- -- -- -- -- -- -- -- -- -- -- --            λ p' →
-- -- -- -- -- -- -- -- -- -- -- -- -- --              let q : Iso.inv IsoIxBIxA⊎F (inl ixA) ≡ (ixB , false)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                  q = ΣPathP (p , p')
-- -- -- -- -- -- -- -- -- -- -- -- -- --                  q' = cong (Iso.fun IsoIxBIxA⊎F) q
-- -- -- -- -- -- -- -- -- -- -- -- -- --              in not≢const _
-- -- -- -- -- -- -- -- -- -- -- -- -- --                   (sym
-- -- -- -- -- -- -- -- -- -- -- -- -- --                    (cong snd (isEmbedding→Inj
-- -- -- -- -- -- -- -- -- -- -- -- -- --                     ⊎.isEmbedding-inl _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- --                     (sym (Iso.rightInv IsoIxBIxA⊎F (inl ixA)) ∙∙ q' ∙∙ x))))
-- -- -- -- -- -- -- -- -- -- -- -- -- --         zz :  (ixB , true) ≡ Iso.inv IsoIxBIxA⊎F (inl ixA)
-- -- -- -- -- -- -- -- -- -- -- -- -- --         zz = ΣPathP (sym p , (sym z))
-- -- -- -- -- -- -- -- -- -- -- -- -- --     in subst {y = inl ixA} isInr
-- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong (Iso.fun IsoIxBIxA⊎F) zz ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- --           Iso.rightInv IsoIxBIxA⊎F (inl ixA)) inrIxbR
        
-- -- -- -- -- -- -- -- -- -- -- -- -- --   stepA∉ (ixA a∷ ixB b∷ chA [ x₂ , x₃ ] [ x , x₁ ]) = {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- --   stepA : (chA : ChainA) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Σ _ λ ixB → ixB b←a (headA chA) × ixB B∉chA chA
-- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (stepA chA) = map-snd not (Iso.inv IsoIxBIxA⊎F (inl (headA chA)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (snd (stepA chA)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --     cong (Iso.fun IsoIxBIxA⊎F) (ΣPathP (refl , notnot _))
-- -- -- -- -- -- -- -- -- -- -- -- -- --      ∙ Iso.rightInv IsoIxBIxA⊎F (inl (headA chA))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   snd (snd (stepA chA)) = stepA∉ chA
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ChainCtx a b l = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Hlp : ∀ (a b : Red) (l : List (Bool × A)) →  0 < length l →  evRed a ++ l ≡ evRed b →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ¬ (IsNormalised l)   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Hlp = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- [_,_,_]subRed_ : _ → Red →  _ → Red → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- [ ls , xs , rs ]subRed ys = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --    ls ++ evRed xs ++ rs ≡ evRed ys


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- AtomRdxAt : (r : Red) → Idx r → Bool → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- AtomRdxAt r idx b = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- subRedsEndL : ∀ ls xs ys rs → [ ls , xs , rs ]subRed ys →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --                 Σ Red λ r → evRed r ≡ ls ++ rs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- subRedsEndL = {!!}




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- infixr 5 _∷↔_ 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- Red : (R : Type ℓ) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- Red R = ((Bool × A) × Maybe (Bool × R))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  data Red : Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  data Red[] : Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  data Red where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   red· : Red[] → Red
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ·A : (Bool × A) → Red

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  data Red[] where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ↔ : Red[]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    _∷↔_ : Red → Red[] → Red[]

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- red[]→List : Red[] → List Red
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- red[]→List (↔ x) = [ x ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- red[]→List (x ∷↔ xs) = x ∷ red[]→List xs

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  evRed : Red → List (Bool × A) → List (Bool × A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  evRed[] : Red[] → List (Bool × A)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  red[]Length/2 : Red[] → ℕ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redLength/2 : Red → ℕ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redLength/2 (red· x) = red[]Length/2 x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redLength/2 (·A x) = 1


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  red[]Length/2 ↔ = zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  red[]Length/2 (x ∷↔ x₁) = redLength/2 x + red[]Length/2 x₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  evRed (red· x) xs = evRed[] x ++ xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- evRed (·red x) xs = xs ++ evRed[] x 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  evRed (·A (b , a)) xs = (b , a) ∷ (xs ∷ʳ (not b , a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  evRed[] (↔) = []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  evRed[] (x ∷↔ xs) = evRed x (evRed[] xs)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  evRedLen : ∀ r → length (evRed[] r) ≡ red[]Length/2 r ℕ.· 2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  evRedLen ↔ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  evRedLen (red· x ∷↔ r) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    let x' = evRedLen x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        r' = evRedLen r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    in length++ (evRed[] x) (evRed[] r) ∙∙ cong₂ _+_ x' r'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ∙∙ ·-distribʳ (red[]Length/2 x) (red[]Length/2 r)  2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  evRedLen (·A x ∷↔ r) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong suc (length++ (evRed[] r) _ ∙ +-comm _ 1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ∙ cong (2 +_) (evRedLen r)    

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  [_,_,_]subRed_ : _ → Red[] →  _ → Red[] → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  [ ls , xs , rs ]subRed ys = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ls ++ evRed[] xs ++ rs ≡ evRed[] ys

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexAt : List (Bool × A) → ℕ → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexAt xs k = HeadIsRedex (drop k xs) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexAt<length : ∀ xs k → atomRedexAt xs k → suc k < length xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexAt<length (x₁ ∷ x₂ ∷ xs) zero x = tt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexAt<length (x₁ ∷ xs) (suc k) x = atomRedexAt<length xs k x
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedex : List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedex xs =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Σ _ (atomRedexAt xs)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ++atomRedexAt : ∀ k xs ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → atomRedexAt ys k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → atomRedexAt (xs ++ ys) (length xs + k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ++atomRedexAt k [] ys x = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ++atomRedexAt k (x₁ ∷ xs) ys x = ++atomRedexAt k xs ys x
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ++atomRedex : ∀ xs ys → atomRedex ys → atomRedex (xs ++ ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ++atomRedex xs ys (k , u) = length xs + k , ++atomRedexAt k xs ys u 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexAt++ : ∀ k xs ys → atomRedexAt xs k → atomRedexAt (xs ++ ys) k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexAt++ zero [] ys ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexAt++ (suc k) [] ys ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexAt++ (suc k) (x₁ ∷ xs) ys u = atomRedexAt++ k xs ys u
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexAt++ zero (x₁ ∷ x₂ ∷ xs) ys x = x
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedex++ : ∀ xs ys → atomRedex xs → atomRedex (xs ++ ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedex++ xs ys (k , u) = k , atomRedexAt++ k xs ys u

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexRed[]Ev : ∀ r → atomRedex (evRed[] r) ⊎ (evRed[] r ≡ []) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexRed[]Ev ↔ = inr refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexRed[]Ev (red· x ∷↔ r) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ⊎.rec (λ u → inl (atomRedex++ _ _ u))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ p → ⊎.rec
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (λ u → inl (++atomRedex _ _ u))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (λ p' → inr (cong₂ _++_ p p'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (atomRedexRed[]Ev r) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (atomRedexRed[]Ev x) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  atomRedexRed[]Ev (·A x ∷↔ r) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ⊎.rec ((λ u → inl (++atomRedex [ x ] _ (atomRedex++ _ _ u))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ p → inl (subst (λ xs →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              atomRedex (x ∷ xs ++ (not (fst x) , snd x) ∷ []))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (sym p) ((0) , (sym (notnot (fst x))) , refl)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (atomRedexRed[]Ev r) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- pairIn : ∀ (Bool × A) (Bool × A) → List (Bool × A) → {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- pairIn = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- subRedsAtomRedex : ∀ ls xs ys rs → [ ls , xs , rs ]subRed ys 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --                 → atomRedex (evRed[] xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --                 → atomRedex (evRed[] ys) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- subRedsAtomRedex ls xs ys rs p u =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --    subst atomRedex p ((++atomRedex ls _ (atomRedex++ _ rs u)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  subRedsAtomRedexAt : ∀ ls xs ys rs k → [ ls , xs , rs ]subRed ys 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → atomRedexAt (evRed[] xs) k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → atomRedexAt (evRed[] ys) (length ls + k) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  subRedsAtomRedexAt ls xs ys rs k u v =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    let z = ++atomRedexAt k ls (evRed[] xs ++ rs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (atomRedexAt++ k (evRed[] xs) rs v)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    in subst (flip atomRedexAt (length ls + k))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         u z


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  removePairAt : ℕ → List (Bool × A) → List (Bool × A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  removePairAt k xs = (take k xs) ++ (drop (2 + k) xs)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ++removePairAt : ∀ k xs ys →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    removePairAt (length xs + k) (xs ++ ys) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      xs ++ removePairAt k ys 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ++removePairAt k [] ys = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ++removePairAt k (x ∷ xs) ys =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cong (x ∷_) (++removePairAt k xs ys)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  removePairAt++ : ∀ k xs ys → suc k < length xs → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    removePairAt k (xs ++ ys) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      removePairAt k xs ++ ys 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  removePairAt++ zero (_ ∷ _ ∷ _) _ _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  removePairAt++ (suc k) (x ∷ xs) ys v =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong (x ∷_) (removePairAt++ k xs ys v)
 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  removePairAt-len : ∀ xs k → suc k < length xs → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    2 + length (removePairAt k xs) ≡ length xs 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  removePairAt-len (x₁ ∷ xs) (suc k) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong suc (removePairAt-len xs k x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  removePairAt-len (x₁ ∷ x₂ ∷ xs) zero x = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redexSpan : List (Σ Bool (λ _ → A)) → Bool × A → Bool × A → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redexSpan xs x x' =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Σ (_ × _ × _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        λ (ls , cs , rs) → ls ++ [ x ] ++ cs ++ [ x' ] ++ rs ≡ xs

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redexSpan' : _ → _ → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redexSpan' xs x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        redexSpan xs x (map-fst not x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ⊎ redexSpan xs (map-fst not x) x


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  lookup : (xs : List (Bool × A)) → ∀ k → k < length xs → (Bool × A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  lookup (x ∷ _) zero _ = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  lookup (_ ∷ xs) (suc k) = lookup xs k

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _∈_ : (Bool × A) → List (Bool × A) → Type ℓ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  x ∈ xs = Σ (Σ _ _) λ (k , k<) → lookup xs k k< ≡ x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ∈red→span' : ∀ x r  → x ∈ evRed[] r → redexSpan' (evRed[] r) x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ∈red→span'-uc : ∀ x r k k< → lookup (evRed[] r) k k< ≡ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   → redexSpan' (evRed[] r) x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ∈red→span'-uc = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ∈red→span'-uc x (red· x₁ ∷↔ r) zero k< p = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ∈red→span'-uc x (·A x₁ ∷↔ r) zero k< p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   inl (([] , (evRed[] r , [])) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     cong evRed[] λ i → (·A (p (~ i)) ∷↔ r))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ∈red→span'-uc x (red· x₁ ∷↔ r) (suc k) k< p = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ∈red→span'-uc x (·A x₁ ∷↔ r) (suc k) k< p = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RedIdx : Red → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Red[]Idx : Red[] → Type
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RedIdx (red· x) = Red[]Idx x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RedIdx (·A x) = Bool
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Red[]Idx ↔ = ⊥
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Red[]Idx (x ∷↔ r) = RedIdx x ⊎ Red[]Idx r

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  lookupRed[] : ∀ r → Red[]Idx r → Bool × A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  lookupRed : ∀ r → RedIdx r → Bool × A
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  lookupRed (red· x₁) x = lookupRed[] x₁ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  lookupRed (·A (b , a)) x = x ⊕ b , a
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  lookupRed[] (r ∷↔ _) (inl x) = lookupRed r x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  lookupRed[] (_ ∷↔ r) (inr x) = lookupRed[] r x


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  adjRed[]Idx : ∀ r → Red[]Idx r → Red[]Idx r
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  adjRedIdx : ∀ r → RedIdx r → RedIdx r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  adjRedIdx (red· x₁) x = adjRed[]Idx x₁ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  adjRedIdx (·A x₁) = not

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  adjRed[]Idx (x₁ ∷↔ r) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ⊎.map (adjRedIdx x₁) (adjRed[]Idx r)
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RedIdx/2 : Red → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Red[]Idx/2 : Red[] → Type

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RedIdx/2 (red· x) = Red[]Idx/2 x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RedIdx/2 (·A x) = Unit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Red[]Idx/2 ↔ = ⊥
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Red[]Idx/2 (x ∷↔ y) = RedIdx/2 x ⊎ Red[]Idx/2 y



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Idx[]→Fin : ∀ r → (Red[]Idx r) → (Σ ℕ (_< red[]Length/2 r ℕ.· 2))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Idx[]→Fin (x₁ ∷↔ r) x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsoIdx[]Fin : ∀ r → Iso (Red[]Idx r) (Σ ℕ (_< red[]Length/2 r ℕ.· 2)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsoIdx[]Fin ↔ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsoIdx[]Fin (red· x ∷↔ r) = compIso (⊎Iso (IsoIdx[]Fin x) (IsoIdx[]Fin r))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsoIdx[]Fin (·A x ∷↔ r) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- compIso (⊎Iso {!!} (IsoIdx[]Fin r)) {!!} 



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Iso[Bool×RedIdx/2]RedIdx : ∀ r → Iso (Bool × Red[]Idx/2 r) (Red[]Idx r)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Iso[Bool×RedIdx/2]RedIdx r = w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   w→ : (Red[]Idx/2 r × Bool) → (Red[]Idx r)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   w→ = {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   w : Iso _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.fun w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv w = {!!}
  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- AtomRedexSpansCases : ∀ r k → atomRedexAt (evRed[] r) k →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --            {!? ⊎ ?!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- AtomRedexSpansCases = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  removeAtomRedex : ∀ r k → atomRedexAt (evRed[] r) k →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       Σ _ λ r' → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        evRed[] r' ≡ (removePairAt k (evRed[] r)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  removeAtomRedex = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  subRedsEndL : ∀ ls xs ys rs → [ ls , xs , rs ]subRed ys →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  Σ Red[] λ r → evRed[] r ≡ ls ++ rs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  subRedsEndL ls xs ys rs x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    h (red[]Length/2 xs) ls xs ys rs (evRedLen xs) x (atomRedexRed[]Ev xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   h : ∀ n ls xs ys rs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → length (evRed[] xs) ≡ n ℕ.· 2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → [ ls , xs , rs ]subRed ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → atomRedex (evRed[] xs) ⊎ (evRed[] xs ≡ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → Σ Red[] λ r → evRed[] r ≡ ls ++ rs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   h zero ls xs ys rs x x₁ _ = ys ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     sym x₁ ∙  cong (ls ++_) (cong (_++ rs) (lengthZero (evRed[] xs) x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   h (suc n) ls xs ys rs x x₁ (inl (k , rat)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    let (xs' , pXs') = removeAtomRedex xs k rat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (ys' , pYs') = removeAtomRedex ys _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (subRedsAtomRedexAt ls xs ys rs k x₁ rat)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        k< = atomRedexAt<length (evRed[] xs) k rat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        l= = removePairAt-len (evRed[] xs) k k< ∙ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    in h n ls xs' ys' rs (cong length pXs' ∙ injSuc (injSuc l=))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((cong (λ zs → ls ++ zs ++ rs) pXs'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ∙∙ cong (ls ++_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (sym (removePairAt++ k  (evRed[] xs) rs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             k<))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          sym (++removePairAt k ls (evRed[] xs ++ rs)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∙∙ cong (removePairAt (length ls + k)) x₁ ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         sym pYs')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (atomRedexRed[]Ev xs')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   h (suc n) ls xs ys rs x x₁ (inr x₂) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ⊥.rec (znots (cong length (sym x₂) ∙ x)) 
    


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsNormalisedEvRed[]→≡[] : ∀ x → (IsNormalised (evRed[] x)) → evRed[] x ≡ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsNormalisedEvRed[]→≡[] ↔ x₁ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsNormalisedEvRed[]→≡[] (red· x ∷↔ y) u =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    let (x* , y*) = IsNormalised++ (evRed[] x) (evRed[] y) u
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        x' = IsNormalisedEvRed[]→≡[] x x*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        y' = IsNormalisedEvRed[]→≡[] y y*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    in cong₂ _++_ x' y'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsNormalisedEvRed[]→≡[] (·A x ∷↔ x₂) (u , v) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let z = IsNormalisedEvRed[]→≡[] x₂ (IsNormalised∷ᵣ _ _ v)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in ⊥.rec ( u (subst (WillReduce (fst x) (snd x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong (_++ [ (not (fst x) , snd x) ]) (sym z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ((sym (notnot _)) , refl)))
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- RED = (Bool × A) × List Red

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- evRED : RED → List (Bool × A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- evRED (x , y) = evRed (·A x) (flatten (Li.map (flip evRed []) y))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  infix 3 _↓_ _↓∷_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _↓∷_ : (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _↓∷_ x xs =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Σ (_ × _)  λ (redL , xsR) → ((evRed[] redL) ++ (x ∷ xsR) ≡ xs)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓[] : List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓[] xs = Σ _ λ r → evRed[] r ≡ xs

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- _↓_∷_ : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- _↓_∷_ = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  xs ↓ [] = ↓[] xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  xs ↓ (x ∷ ys) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Σ (x ↓∷ xs) λ ((_ , xsR) , _) → xsR ↓ ys 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ¬[]↓∷ : ∀ x xs  → [] ↓ x ∷ xs → ⊥ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ¬[]↓∷ x xs (((l , r) , p) , _) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ¬cons≡nil (++=[] (evRed[] l) (x ∷ r) p) 
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓[][] : ↓[] []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fst ↓[][] = ↔
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  snd ↓[][] = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓refl : ∀ x → x ↓ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓refl [] = ↓[][]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓refl (x ∷ xs) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ((↔ , _) , refl) , ↓refl xs


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓[]++↓ : ∀ xs ys → evRed[] xs ++ ys ↓ ys 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓[]++↓ xs [] = xs , sym (++-unit-r _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓[]++↓ xs (x ∷ ys) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ((xs , ys) , refl) , ↓refl ys

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓++↓[] : ∀ xs ys → xs ++ evRed[] ys ↓ xs 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓++↓[] [] ys = ys , refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓++↓[] (x ∷ xs) ys =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ((↔ , _) , refl) , ↓++↓[] xs ys 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open BinaryRelation

 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  []↓ : ∀ xs → [] ↓ xs → xs ≡ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  []↓ [] q = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  []↓ (x ∷ xs) (((lL , lR) , p) , q) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           let w = ++=[] _ (x ∷ lR) p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            in ⊥.rec (¬cons≡nil w)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓++ : ∀ xs ysL ysR → xs ↓ ysL ++ ysR →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ (_ × _) λ (xsL ,  xsR) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (xsL ++ xsR ≡ xs) × (xsL ↓ ysL) × (xsR ↓ ysR) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓++ xs [] ysR x = ([] , xs) , refl ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ↓[][] , x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓++ xs (y ∷ ysL) ysR (((wL , wR) , w) , x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let ((xsL' , xsR') , (p , (q , r))) = ↓++ _ ysL ysR x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in (evRed[] wL ++ y ∷ xsL' , xsR') ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ++-assoc (evRed[] wL) _ _ ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           cong ((evRed[] wL ++_) ∘ (y ∷_))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             p ∙∙ w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         , (((((wL) , xsL') , refl) , q) , r)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓trans[] : ∀ xs r → xs ↓ (evRed[] r) → ↓[] xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓trans[] xs ↔ q = q
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓trans[] xs (red· x ∷↔ r) q =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     let ((x' , r') , (x'++r'≡xs , x'↓x , r'↓r)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ↓++ xs (evRed[] x) (evRed[] r) q
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (x'' , x='') = ↓trans[] x' x x'↓x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (r'' , r='') = ↓trans[] r' r r'↓r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     in (red· x'' ∷↔ r'') ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        cong₂ _++_ x='' r='' ∙ x'++r'≡xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓trans[] xs (·A x ∷↔ r) q = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let ¬x = not (fst x) , snd x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (([x] , r*++¬[x]*) , (v , v' , v'')) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ↓++ xs [ x ] (evRed[] r ++ [ ¬x ]) q
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((r* , ¬[x]*) , (u , u' , u'')) = ↓++ r*++¬[x]* (evRed[] r) [ ¬x ] v''
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (((rL , _) , f'') , (rR , f')) = u'' 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (r' , p') = ↓trans[] r* r u'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       eq1 : evRed[] rL ++ ¬x ∷ evRed[] rR ≡ ¬[x]*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       eq1 = cong (λ s → evRed[] rL ++ ¬x ∷ s) (f') ∙ f''
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       e : [x] ++ r*++¬[x]* ↓ []      
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       e = (red· (fst (fst (fst v'))) ∷↔
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              red· (·A x ∷↔ (red· r' ∷↔ rL)) ∷↔
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                rR) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ((cong (evRed[] (fst (fst (fst q))) ++_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (cong (x ∷_) (
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       cong (_++ evRed[] rR)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (++-assoc _ (evRed[] rL) [ ¬x ] ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            cong (_++ (evRed[] rL ++ [ ¬x ])) p')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             ∙ ++-assoc ([] ++ r*)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              (evRed[] rL ++ [ ¬x ]) (evRed[] rR)))  ∙ sym (++-assoc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (evRed[] (fst (fst (fst q)))) ([ x ] ++ r*)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ((evRed[] rL ++ [ ¬x ]) ++ (evRed[] rR))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       cong₂ (_++_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (sym (++-assoc (evRed[] (fst (fst (fst q)))) [ x ] r*))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (++-assoc (evRed[] rL) [ ¬x ] _))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       ∙∙

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     cong₂ _++_ refl eq1 ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (++-assoc (evRed[] (fst (fst (fst q))) ++ [ x ])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        r* _ ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       cong ((evRed[] (fst (fst (fst q))) ++ x ∷ []) ++_) u)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in subst ↓[] v e
 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓trans : isTrans _↓_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓trans xs ys [] u (r , p) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↓trans[] xs r (subst (xs ↓_) (sym p) u)
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓trans xs ys (x ∷ zs) u (((ysL , ysR) , p) , q) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    let ((xsL , xsR) , xsL++xsR≡xs , ysL↓[] , xsR↓x∷ysR) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ↓++ xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (evRed[] ysL)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (x ∷ ysR)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (subst (xs ↓_) (sym p) u)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (((ysL' , ysR') , p') , q') = xsR↓x∷ysR
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (xsL' , xsL'≡) = ↓trans[] xsL ysL ysL↓[]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        qq' = ↓trans ysR' ysR zs q' q
       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    in ((red· xsL' ∷↔ ysL' , ysR') ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ++-assoc (evRed[] xsL') (evRed[] ysL') (x ∷ ysR') ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             cong₂ {x = evRed[] xsL'} _++_ xsL'≡ p' ∙ xsL++xsR≡xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         , qq'

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _↓++↓_ : ∀ {xsL xsR ysL ysR} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     xsL ↓ ysL → xsR ↓ ysR →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       xsL ++ xsR ↓ ysL ++ ysR
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _↓++↓_ {xsL = []} {ysL = []} _ v = v
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _↓++↓_ {xsL = []} {xsR} {(x ∷ ysL)} {ysR} u v = ⊥.rec (¬[]↓∷ _ _ u)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _↓++↓_ {xsL = (x ∷ xsL)} {xsR} {[]} {ysR} (r , p) v =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    let w = ↓[]++↓ r xsR
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        w' = subst (λ w' → w' ++ xsR ↓ xsR) p w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    in ↓trans _ _ _ w' v
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _↓++↓_ {xsL = (x ∷ xsL)} {xsR} {(y ∷ ysL)} {ysR} (((uL , uR) , u) , u') v' =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let q = u' ↓++↓ v'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in ((uL , uR ++ xsR) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     sym (++-assoc (evRed[] uL) (y ∷ uR) xsR)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∙  cong (_++ xsR) u) , q

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- rev↓rev : ∀ xs ys → xs ↓ ys → rev xs ↓ rev ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- rev↓rev = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- rev↓rev [] [] x = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- rev↓rev [] (x₁ ∷ ys) x = ⊥.rec (¬[]↓∷ _ _ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- rev↓rev (x₁ ∷ xs) [] x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- rev↓rev (x₁ ∷ xs) (x₂ ∷ ys) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --  let z = ↓++↓ _ _ _ _ (rev↓rev xs ys {!!}) {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --  in {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _↙_↘_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  xs ↙ zs ↘ ys = (zs ↓ xs) × (zs ↓ ys)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  infix 3 _↙↘_


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _↙↘_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  xs ↙↘ ys = Σ _ (xs ↙_↘ ys)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↙↘sym : ∀ x y → x ↙↘ y → y ↙↘ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↙↘sym x y = map-snd λ (x , y) → y , x



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↙↘refl : ∀ x → x ↙↘ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↙↘refl = λ x → x , ↓refl x , ↓refl x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↘[]↙→↙↘ : ∀ x y → ↓[] x → ↓[] y → x ↙↘ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↘[]↙→↙↘ x y (x' , px) (y' , py) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (x ++ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , subst (λ y → x ++ y ↓ x) py (↓++↓[] x y')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , subst (λ x → x ++ y ↓ y) px (↓[]++↓ x' y)
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↘↙→↙↘ : ∀ x y z → x ↓ z → y ↓ z → x ↙↘ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↘↙→↙↘ x y [] = ↘[]↙→↙↘ x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↘↙→↙↘ xs ys (z ∷ zs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (((xsL , xsR) , pX) , qX)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (((ysL , ysR) , pY) , qY) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (w , w↓xsL , w↓ysL)  = ↘[]↙→↙↘ _ _ (xsL , refl) (ysL , refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (ws , ws↓xsR , ws↓ysR ) = ↘↙→↙↘ _ _ _ qX qY
      
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in w ++ z ∷ ws
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       , subst (w ++ z ∷ ws ↓_) pX
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (w↓xsL ↓++↓ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (_↓++↓_ {[ z ]} {_} {[ z ]} (↓refl [ z ]) (ws↓xsR))) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       , subst (w ++ z ∷ ws ↓_) pY
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ((w↓ysL ↓++↓ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (_↓++↓_ {[ z ]} {_} {[ z ]} (↓refl [ z ]) (ws↓ysR))))
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↙↘trans : ∀ x y z → x ↙↘ y → y ↙↘ z → x ↙↘ z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↙↘trans x y z (x' , p , q) (z' , r , s) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (y' , p' , q') = ↘↙→↙↘ x' z' y q r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in y' , (↓trans y' x' x p' p  , ↓trans y' z' z q' s)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  isEquivRel↙↘ : isEquivRel _↙↘_ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  isEquivRel.reflexive isEquivRel↙↘ = ↙↘refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  isEquivRel.symmetric isEquivRel↙↘ = ↙↘sym
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  isEquivRel.transitive isEquivRel↙↘ = ↙↘trans


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  _↙↘++↙↘_ : ∀ {xsL xsR ysL ysR} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     xsL ↙↘ ysL → xsR ↙↘ ysR →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       xsL ++ xsR ↙↘ ysL ++ ysR
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (_ , xl , yl) ↙↘++↙↘ (_ , xr , yr) = _ , (xl ↓++↓ xr) , (yl ↓++↓ yr)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  List/↙↘ : Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  List/↙↘ = _ /₂ _↙↘_


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  List/↙↘· : List/↙↘ → List/↙↘ → List/↙↘
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  List/↙↘· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ _ _ c → eq/ _ _ ∘ _↙↘++↙↘ (↙↘refl c))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ a _ _ → eq/ _ _ ∘ (↙↘refl a) ↙↘++↙↘_ )


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  rev-fst-not : List (Bool × A) → List (Bool × A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  rev-fst-not = rev ∘ Li.map (map-fst not)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  invol-rev-fst-not : isInvolution rev-fst-not
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  invol-rev-fst-not xs =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   sym (rev-map-comm (map-fst not) (rev-fst-not xs)) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     cong (Li.map (map-fst not))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (rev-rev (Li.map (map-fst not) xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ∙ map-∘ (map-fst not) (map-fst not) xs ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ i → Li.map (map-fst (λ x → notnot x i) ) xs) ∙ map-id xs
    

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  rev-fst-not-↓ : ∀ xs ys → xs ↓ ys → rev-fst-not xs ↓ rev-fst-not ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  rev-fst-not-↓ xs ys =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  XS++rev-fst-notXS↓[] : ∀ xs → xs ++ rev-fst-not xs ↓ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  XS++rev-fst-notXS↓[] [] = ↔ , refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  XS++rev-fst-notXS↓[] (x ∷ xs) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (r , p) = XS++rev-fst-notXS↓[] xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in (·A x ∷↔ r ) , 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        cong (λ xs → x  ∷ (xs ∷ʳ (not (fst x) , snd x))) p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∙ cong (x ∷_) (++-assoc xs (rev-fst-not xs) _ ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          cong (xs ++_) ((
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (sym (cong rev (map++ (map-fst not) [ x ] xs)))) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          sym (rev-++ (Li.map (map-fst not) [ x ])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                               (Li.map (map-fst not) xs))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  rev-fst-notXS++XS↓[] : ∀ xs → rev-fst-not xs ++ xs ↓ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  rev-fst-notXS++XS↓[] xs =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    subst (λ xs' → rev-fst-not xs ++ xs' ↓ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (invol-rev-fst-not xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (XS++rev-fst-notXS↓[] (rev-fst-not xs))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓→↙↘ : ∀ {xs ys} → xs ↓ ys → xs ↙↘ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ↓→↙↘ x = _ , ↓refl _ , x
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  rev-fst-not-↙↘ : ∀ xs ys →  xs ↙↘ ys → rev-fst-not xs ↙↘ rev-fst-not ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  rev-fst-not-↙↘ xs ys (zs , ↓xs , ↓ys) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    _ , rev-fst-not-↓ _ _ ↓xs , rev-fst-not-↓ _ _ ↓ys

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  List/↙↘Group : GroupStr List/↙↘
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  GroupStr.1g List/↙↘Group = SQ.[ [] ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  GroupStr._·_ List/↙↘Group = List/↙↘·

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  GroupStr.inv List/↙↘Group =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    SQ.rec squash/ (SQ.[_] ∘ rev-fst-not)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ _ _ → eq/ _ _ ∘ rev-fst-not-↙↘ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  GroupStr.isGroup List/↙↘Group = makeIsGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    squash/ (SQ.elimProp3
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ _ _ _ → squash/ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ xs ys zs → cong SQ.[_] (sym (++-assoc xs ys zs)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (SQ.elimProp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ _ → squash/ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ xs → cong SQ.[_] (++-unit-r xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (SQ.elimProp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ _ → squash/ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (SQ.elimProp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ _ → squash/ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ xs → eq/ _ _ (↓→↙↘ {ys = []} (XS++rev-fst-notXS↓[] xs)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (SQ.elimProp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ _ → squash/ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ xs → eq/ _ _ (↓→↙↘ {ys = []} (rev-fst-notXS++XS↓[] xs)))



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- ↙↘[]lem : ∀ r xs → IsNormalised xs → evRed[] r ↓ xs → xs ≡ [] 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- ↙↘[]lem = {!!}


 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- ↙↘-norm-uniq : ∀ xs ys zs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --    → IsNormalised xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --    → IsNormalised ys 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --    → xs ↙ zs ↘ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --    → xs ≡ ys  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- ↙↘-norm-uniq [] ys zs nX nY (rX , rY) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --   sym (↙↘[]lem (fst rX) ys nY (subst (_↓ ys) (sym (snd rX)) rY)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- ↙↘-norm-uniq xs@(_ ∷ _) [] zs nX nY (rX , rY) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --     ⊥.rec
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --      (¬cons≡nil (↙↘[]lem (fst rY) xs nX (subst (_↓ xs) (sym (snd rY)) rX))) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- ↙↘-norm-uniq (x ∷ xs) (y ∷ ys) zs nX nY
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --    ((((rX , zLX) , pX) , qX) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --     (((rY , zLY) , pY) , qY)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --   decRec
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --     (λ lenRX≡lenRY →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --       let z = congP (λ i → drop (((evRedLen rX ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --             (cong (ℕ._· 2) lenRX≡lenRY) ∙∙ sym (evRedLen rY)) i))) (pX ∙ (sym pY))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --           z' = (sym (drop++ (evRed[] rX) _) ∙∙ z ∙∙ drop++ (evRed[] rY) _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --       in cong₂ _∷_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --            (cons-inj₁ z')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --            (↙↘-norm-uniq xs ys zLX
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --               (snd nX) (snd nY)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --               (qX , subst (_↓ ys) (sym (cons-inj₂ z')) qY)) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --     (⊥.rec ∘ ⊎.rec {!!} {!!} ∘ ≢-split
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --       )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --    (ℕ.discreteℕ (red[]Length/2 rX)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --                  (red[]Length/2 rY))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --    h : red[]Length/2 rX < red[]Length/2 rY → ⊥
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- --    h = {!!}
   

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- _↘_↙_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- xs ↘ zs ↙ ys = (xs ↓ zs) × (ys ↓ zs)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- _↘↙_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- xs ↘↙ ys = Σ _ (xs ↘_↙ ys)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- ↘↙sym : ∀ x y → x ↘↙ y → y ↘↙ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- ↘↙sym x y = map-snd λ (x , y) → y , x



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- ↘↙refl : ∀ x → x ↘↙ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- ↘↙refl = λ x → x , ↓refl x , ↓refl x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- ↘[]↙→↘↙ : ∀ x y → ↓[] x → ↓[] y → x ↘↙ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- ↘[]↙→↘↙ _ _ u v = [] , u , v 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- ↙↘→↘↙ : ∀ x y z → z ↓ x → z ↓ y → x ↘ z ↙ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- ↙↘→↘↙ = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- ↘↙→↙↘ : ∀ x y z → x ↓ z → y ↓ z → x ↙↘ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- ↘↙→↙↘ x y [] = ↘[]↙→↙↘ x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- ↘↙→↙↘ xs ys (z ∷ zs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --   (((xsL , xsR) , pX) , qX)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --   (((ysL , ysR) , pY) , qY) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  let (w , w↓xsL , w↓ysL)  = ↘[]↙→↙↘ _ _ (xsL , refl) (ysL , refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --      (ws , ws↓xsR , ws↓ysR ) = ↘↙→↙↘ _ _ _ qX qY
      
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  in w ++ z ∷ ws
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --      , subst (w ++ z ∷ ws ↓_) pX
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --         (↓++↓ _ _ _ _ w↓xsL
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --           (↓++↓ [ z ] _ [ z ] _ (↓refl [ z ]) (ws↓xsR))) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --      , subst (w ++ z ∷ ws ↓_) pY
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --         ((↓++↓ _ _ _ _ w↓ysL
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --           (↓++↓ [ z ] _ [ z ] _ (↓refl [ z ]) (ws↓ysR))))
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- ↙↘trans : ∀ x y z → x ↙↘ y → y ↙↘ z → x ↙↘ z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- ↙↘trans x y z (x' , p , q) (z' , r , s) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  let (y' , p' , q') = ↘↙→↙↘ x' z' y q r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  in y' , (↓trans y' x' x p' p  , ↓trans y' z' z q' s)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- isEquivRel↙↘ : isEquivRel _↙↘_ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- isEquivRel.reflexive isEquivRel↙↘ = ↙↘refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- isEquivRel.symmetric isEquivRel↙↘ = ↙↘sym
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- isEquivRel.transitive isEquivRel↙↘ = ↙↘trans




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- List/↓ : Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- List/↓ = _ /₂ _↓_


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- List/↓· : List/↓ → List/↓ → List/↓
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- List/↓· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --    (λ a b c → eq/ _ _ ∘ flip (↓++↓ _ _ _ _) (↓refl c))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --    (λ a b c → eq/ _ _ ∘ ↓++↓ _ _ _ _ (↓refl a))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- List/↓Group : GroupStr List/↓
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- GroupStr.1g List/↓Group = SQ.[ [] ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- GroupStr._·_ List/↓Group = List/↓·

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- GroupStr.inv List/↓Group =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --   SQ.rec squash/ (SQ.[_] ∘ rev)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- GroupStr.isGroup List/↓Group = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- module FG (freeGroupGroup : Group ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --           (η : A → ⟨ freeGroupGroup ⟩) where 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  FreeGroup = ⟨ freeGroupGroup ⟩

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  open GroupStr (snd freeGroupGroup)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  open GroupTheory freeGroupGroup

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  η* : Bool × A → FreeGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  η* (b , a) = (if b then idfun _ else inv) (η a)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  fromList' : FreeGroup → List (Bool × A) → FreeGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  fromList' = foldr (_·_ ∘ η*) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  fromList : List (Bool × A) → FreeGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  fromList = fromList' 1g

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  fromList· : ∀ xs ys → fromList (xs ++ ys) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --                            fromList xs · fromList ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  fromList· [] _ = sym (·IdL _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  fromList· (_ ∷ xs) _ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --   cong (_ ·_) (fromList· xs _) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --    ·Assoc _ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  redex-ε-η* : ∀ x x' → IsRedex x x' → η* x · η* x' ≡ 1g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  redex-ε-η* (false , _) (false , _) (p , _) = ⊥.rec (false≢true p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  redex-ε-η* (false , x) (true , _) (_ , q) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --    cong (inv (η x) ·_) (cong (η) (sym q)) ∙ ·InvL (η x) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  redex-ε-η* (true , x) (false , _) (_ , q) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --    cong (η x ·_) (cong (inv ∘ η) (sym q)) ∙ ·InvR (η x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- --  redex-ε-η* (true , _) (true , _) (p , _) = ⊥.rec (true≢false p)







-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- ↓trans : isTrans _↓_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- ↓trans xs [] zs u v = subst (xs ↓_) (sym ([]↓ zs v)) u
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- ↓trans xs (x ∷ ys) zs u v = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- infix 3 [_]_↓'_ [_]_∷↓'_ [_]_↓∷'_ _↓∷Fst_


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- _↓∷Fst_ : List (Bool × A) → List (Bool × A) → Type ℓ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- xs ↓∷Fst ys = Σ (_ × _)  λ (redL , xsR) → ((evRED redL) ++ xsR ≡ xs)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷Snd : (xs ys : List (Bool × A)) → xs ↓∷Fst ys → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷Snd = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷Fst  = Σ (_ × _)  λ (redL , xsR) → ((evRED redL) ++ xsR ≡ xs)
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- [_]_↓∷'_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- [_]_↓'_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- [_]_∷↓'_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- [ [] ] xs ↓∷' ys = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- [ x ∷ tx ] xs ↓∷' ys =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --   Σ (xs ↓∷Fst ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --      λ q → [ tx ] snd (fst q) ↓' ys 
 

 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- [ _ ] [] ∷↓' [] = Unit*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- [ _ ] [] ∷↓' _ ∷ _ = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- [ _ ] _ ∷ _ ∷↓' [] = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- [ [] ] x₁ ∷ xs ∷↓' y ∷ ys = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- [ _ ∷ tx ] x ∷ xs ∷↓' y ∷ ys =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --    (x ≡ y) × ([ tx ] xs ↓' ys)
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- [ tx ] xs ↓' ys =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --   ([ tx ] xs ↓∷' ys) ⊎.⊎
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --     ([ tx ] xs ∷↓' ys)  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- ↓∷'→len≥2 : ∀ ts xs ys → [ ts ] xs ↓∷' ys → 2 ≤ length xs  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- ↓∷'→len≥2 (_ ∷ _) xs ys (((redL , xsR) , p) , _) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --   let p' =  cong suc (cong (_+ length xsR)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --              (sym (+-suc _ _) ∙ sym (length++ (flatten (Li.map (λ x₁ → evRed x₁ []) (snd redL)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                [ (not (fst (fst redL)) , snd (fst redL)) ])) ∙ sym (length++
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --             ((flatten (Li.map (λ x₁ → evRed x₁ []) (snd redL)) ++
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                (not (fst (fst redL)) , snd (fst redL)) ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                ) xsR)) ∙ cong length p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --   in subst (2 ≤_) p' tt   
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- open BinaryRelation

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [[]]↓'→⊥ : ∀ xs ys → [ [] ] xs ↓' ys → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [[]]↓'→⊥ [] [] (inr x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [[]]↓'→⊥ (x₁ ∷ xs) [] (inr ())
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [[]]↓'→⊥ (x₁ ∷ xs) (x₂ ∷ ys) (inr ())

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- isTrans-↓∷' : ∀ tx → isTrans [ tx ]_↓∷'_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- isTrans-∷↓' : ∀ tx → isTrans [ tx ]_∷↓'_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' : ∀ tx tx' → ∀ a b c →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx ] a ↓' b) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx' ] b ↓' c) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx ] a ↓' c)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- isTrans-↓∷' (x ∷ tx) xs ys zs p q = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷'-lem : ∀ tx → ∀ a x bL bR →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx ] (x ∷ a) ∷↓' (evRED (x , bL)) ++ bR) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                       Σ (List Red × List (Bool × A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                        λ (aL , aR) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                          {!!} × ([ tx ] aR ↓' bR )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷'-lem = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷' : ∀ tx tx' → ∀ a x bL bR c →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx ] (x ∷ a) ∷↓' (evRED (x , bL)) ++ bR) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx' ] (evRED (x , bL)) ++ bR ↓∷' c) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx ] (x ∷ a) ↓∷' c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷' tx tx' a x bL bR c = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- tx tx' (x ∷ a) (fst₁ , []) bR [] p q = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷' tx tx' (x ∷ a) (fst₁ , []) bR (x₁ ∷ c) p q = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷' tx tx' (x₁ ∷ a) (fst₁ , x ∷ snd₁) bR c p q = {!c!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' tx [] a b c (inr x) (inl ())
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' tx tx'@(_ ∷ _) a [] c (inr x) (inl x'@(((bL , bR) , p) , q)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --   ⊥.rec (¬cons≡nil p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' tx@(_ ∷ _) tx'@(_ ∷ _) (ha ∷ a) (x ∷ b) c (inr u) (inl x'@((((_ , bL) , bR) , p) , q)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --  let pp = sym p ∙ cong (λ h → evRED (h , bL) ++ bR)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --             (cons-inj₁ p ∙ sym (fst u))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --  in inl (isTrans-∷↓'-↓∷' tx tx' a ha bL bR c
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --     (subst ([ tx ] (ha ∷ a) ∷↓'_) pp u)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --     (subst ( [ tx' ]_↓∷' c) pp x')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --    )

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' tx tx' [] [] [] (inr x) (inr _) = inr _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' (_ ∷ tx) [] (x₂ ∷ xs) (x₃ ∷ ys) (x₄ ∷ zs) (inr (p , q)) (inr ())
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' (_ ∷ tx) (_ ∷ tx') (x₂ ∷ xs) (x₃ ∷ ys) (x₄ ∷ zs) (inr (p , q)) (inr (p' , q'))  = inr (p ∙ p' , isTrans-↓' tx tx' xs ys zs q q')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' (_ ∷ tx) tx' xs ys zs (inl ((((rL , rs) , w) , q))) v =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --  let u = isTrans-↓' tx tx' rs ys zs q v
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- --  in inl (((rL , rs) , w) , u)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- infix 3 _↓_ _∷↓_ _↓∷_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- xs ↓ ys = [ xs ] xs ↓' ys

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- _↓∷_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- _∷↓_ : List (Bool × A) → List (Bool × A) → Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷H : ∀ n → (l : List (Bool × A)) → length l ≤ n  → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓H : ∀ n → (l : List (Bool × A)) → length l ≤ n  → List (Bool × A) → Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷H zero _ _ _ = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷H (suc n) xs l≤sn xs'  =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- --      Σ (_ × _)  λ (redL , xsR) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- --     (((evRED redL) ++ xsR ≡ xs) ×
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- --       (↓∷H n {!!} {!!} {!!} ⊎ ↓H n xsR {!!} xs') )

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓H n l x x₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- --   {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- xs ↓∷ xs' = ↓∷H (length xs) xs (≤-refl (length xs)) xs'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- --   -- Σ (_ × _)  λ (redL , xsR) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- --   --   (((evRED redL) ++ xsR ≡ xs) × {!? ↓ ?!} )
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [] ∷↓ [] = Unit*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [] ∷↓ _ ∷ _ = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- _ ∷ _ ∷↓ [] = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- x ∷ xs ∷↓ x' ∷ xs' = (x ≡ x') × (xs ↓ xs')
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- xs ↓ xs' = (xs ↓∷ xs') ⊎ (xs ∷↓ xs')

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- module FG (freeGroupGroup : Group ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --           (η : A → ⟨ freeGroupGroup ⟩) where 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  FreeGroup = ⟨ freeGroupGroup ⟩

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  open GroupStr (snd freeGroupGroup)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  open GroupTheory freeGroupGroup

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  η* : Bool × A → FreeGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  η* (b , a) = (if b then idfun _ else inv) (η a)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList' : FreeGroup → List (Bool × A) → FreeGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList' = foldr (_·_ ∘ η*) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList : List (Bool × A) → FreeGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList = fromList' 1g

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList· : ∀ xs ys → fromList (xs ++ ys) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --                            fromList xs · fromList ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList· [] _ = sym (·IdL _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList· (_ ∷ xs) _ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --   cong (_ ·_) (fromList· xs _) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --    ·Assoc _ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* : ∀ x x' → IsRedex x x' → η* x · η* x' ≡ 1g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (false , _) (false , _) (p , _) = ⊥.rec (false≢true p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (false , x) (true , _) (_ , q) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --    cong (inv (η x) ·_) (cong (η) (sym q)) ∙ ·InvL (η x) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (true , x) (false , _) (_ , q) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --    cong (η x ·_) (cong (inv ∘ η) (sym q)) ∙ ·InvR (η x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (true , _) (true , _) (p , _) = ⊥.rec (true≢false p)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- infix 3 _↓_ _∷↓_ _↓∷_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- _↓∷_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- _∷↓_ : List (Bool × A) → List (Bool × A) → Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- [] ↓∷ xs' = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ []) ↓∷ xs' = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ x' ∷ xs) ↓∷ xs' = IsRedex x x' × (xs ↓ xs')

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- [] ∷↓ [] = Unit*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- [] ∷↓ _ ∷ _ = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- _ ∷ _ ∷↓ [] = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- x ∷ xs ∷↓ x' ∷ xs' = (x ≡ x') × (xs ↓ xs')

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- xs ↓ xs' = (xs ↓∷ xs') ⊎ (xs ∷↓ xs')


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓refl : ∀ x → x ∷↓ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓refl : ∀ x → x ↓ x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓refl [] = tt*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓refl (_ ∷ xs) = refl , ↓refl xs
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓refl x = ⊎.inr (∷↓refl x)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓trans : ∀ x y z → x ∷↓ y → y ∷↓ z → x ∷↓ z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓trans = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans-∷↓-↓∷ :  ∀ x y z → x ∷↓ y → y ↓∷ z → x ↓ z

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans : ∀ x y z → x ↓ y → y ↓ z → x ↓ z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans x y z (inr p) (inl q) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ []) (x' ∷ x₂ ∷ ys) zs (inr (fst₁ , inl ())) (inl x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ []) (x' ∷ x₂ ∷ ys) zs (inr (fst₁ , inr ())) (inl x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ x₃ ∷ x₄ ∷ xs) (x' ∷ x₂ ∷ ys) zs (inr (p , inl x₁)) (inl (q , r)) =    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ x₃ ∷ xs) (x' ∷ x₂ ∷ ys) zs (inr (p , inr (p' , p''))) (inl (q , r)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --   inl (subst2 IsRedex {!!} {!!} q
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --     , (↓trans _ _ _ p'' r))
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans [] [] _ (inr _) (inr x) = inr x
    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ xs) (x' ∷ ys) [] (inr p) (inr ())
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ xs) (x' ∷ ys) (z' ∷ zs) (inr (p , q)) (inr (p' , q')) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --   inr (p ∙ p' , ↓trans _ _ _ q q' )
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ x₂ ∷ x₃) _ _ (inl (p , q)) r =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --    inl (p , ↓trans _ _ _ q r)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans-∷↓-↓∷ (x ∷ []) (x₃ ∷ x₄ ∷ y) z (fst₁ , inl ()) x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans-∷↓-↓∷ (x ∷ []) (x₃ ∷ x₄ ∷ y) z (fst₁ , inr ()) x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans-∷↓-↓∷ (x ∷ y ∷ xs) (x' ∷ y' ∷ ys) z (p , inr (p' , q')) (r , s) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --    inl (subst2 IsRedex (sym p) (sym p') r ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --        ↓trans _ _ _ q' s)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans-∷↓-↓∷ (x ∷ y ∷ u ∷ xs) (x' ∷ y' ∷ ys) z (p , inl (r' , s')) (r , s) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --   inl (subst2 IsRedex (sym p) {!!} r ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --     {!!} )
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓→≤length : ∀ xs ys → xs ↓ ys → length ys ≤ length xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷→<length : ∀ xs ys → xs ↓∷ ys → length ys < length xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓→≤length : ∀ xs ys → xs ∷↓ ys → length ys ≤ length xs

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓→≤length [] [] x = tt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓→≤length (x₁ ∷ xs) (x₂ ∷ ys) x = ↓→≤length xs ys (snd x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷→<length (x₁ ∷ x₂ ∷ xs) ys x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --   <-weaken {length ys} (↓→≤length xs ys (snd x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓→≤length xs ys = ⊎.rec
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --   (<-weaken {length ys} ∘ ↓∷→<length xs ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --   (∷↓→≤length xs ys)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷asym : ∀ xs ys → xs ↓∷ ys → ys ↓∷ xs → ⊥
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷asym xs ys p p' =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --  <-asym {length ys} (↓∷→<length xs ys p) (↓∷→<length ys xs p')

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓antisym : ∀ x y → x ∷↓ y → y ∷↓ x → x ≡ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓antisym : ∀ x y → x ↓ y → y ↓ x → x ≡ y


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓antisym [] [] p q = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓antisym (_ ∷ xs) (_ ∷ ys) (p , q) (p' , q') = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --   cong₂ _∷_ p (↓antisym xs ys q q')


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓antisym xs ys (inl x) (inl x₁) = ⊥.rec (↓∷asym _ _ x x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓antisym xs ys (inl x) (inr x₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓antisym xs ys (inr x) (inl x₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓antisym xs ys (inr x) (inr x₁) = ∷↓antisym xs ys x x₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↙_↘_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- xs ↙ zs ↘ ys = (zs ↓ xs) × (zs ↓ ys)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↙↘_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- xs ↙↘ ys = Σ _ (xs ↙_↘ ys)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘sym : ∀ x y → x ↙↘ y → y ↙↘ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘sym x y = map-snd λ (x , y) → y , x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘refl : ∀ x → x ↙↘ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘refl = λ x → x , ↓refl x , ↓refl x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↘↙→↙↘ : ∀ x y z → x ↓ z → y ↓ z → x ↙↘ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↘↙→↙↘ = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘trans : ∀ x y z → x ↙↘ y → y ↙↘ z → x ↙↘ z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘trans x y z (x' , p , q) (z' , r , s) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --  let (y' , p' , q') = ↘↙→↙↘ x' z' y q r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --  in y' , (↓trans y' x' x p' p  , ↓trans y' z' z q' s)
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open BinaryRelation _↓_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓EquivRel : isEquivRel
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isEquivRel.reflexive ↓EquivRel = ↓refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isEquivRel.symmetric ↓EquivRel = ↓sym
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isEquivRel.transitive ↓EquivRel = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↓∷_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- [] ↓∷ xs' = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ []) ↓∷ xs' = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ x' ∷ xs) ↓∷ xs' = IsRedex x x' × (xs ≡ xs')
 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- [] ↓ xs' = ⊥*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ xs) ↓ [] = (x ∷ xs) ↓∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ xs) ↓ (x' ∷ xs') =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ((x ∷ xs) ↓∷ (x' ∷ xs'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⊎ ((x ≡ x') × (xs ↓ xs'))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- redex∷↓ : ∀ x x' xs → IsRedex x x' → x ∷ x' ∷ xs ↓ xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- redex∷↓ x x' [] p = p , refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- redex∷↓ x x' (x₁ ∷ xs) p = inl (p , refl)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷++ : ∀ {a b x x'} c → (x ∷ a) ↓∷ (x' ∷ b) → (x ∷ a ++ c) ↓∷ (x' ∷ b ++ c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷++ {x₁ ∷ []} c (_ , q) = ⊥.rec (¬nil≡cons q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷++ {x₁ ∷ x₂ ∷ a} c = map-snd (cong (_++ c))
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++L↓ : ∀ a b c → a ↓ b → a ++ c ↓ b ++ c
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++L↓ (x₁ ∷ a) (x₂ ∷ b) c =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ⊎.map (↓∷++ c) (map-snd (++L↓ a b c))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++L↓ (x ∷ x' ∷ []) [] xs (p , _) = redex∷↓ x x' xs p 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++L↓ (x₁ ∷ x₂ ∷ x₃ ∷ a) [] c (_ , q) = ⊥.rec (¬cons≡nil q)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++R↓ : ∀ a b c → b ↓ c → a ++ b ↓ a ++ c
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++R↓ [] b c p = p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++R↓ (x ∷ a) b c p = inr (refl , ++R↓ a b c p)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓ : Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓ = _ /₂ _↓_


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (isSetA : isSet A) where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsPropIsNormalised : ∀ x → isProp (IsNormalised x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsPropIsNormalised = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  𝑵 : ℙ (List (Bool × A)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  𝑵 x = IsNormalised x , IsPropIsNormalised x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  isSet[𝟚×A] : isSet _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  isSet[𝟚×A] = isOfHLevelList 0 (isSet× 𝟚.isSetBool isSetA)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ηInj : ∀ a a' → Path List/↓ [ [ (true , a) ] ]/ [ [ (true , a') ] ]/ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             a ≡ a' 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ηInj a a' = PT.rec (isSetA _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!} ∘' Iso.fun (SQ.TC.IsoTcTc' _↓_ _ _) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w : ∀ a a' → TC.tc _↓_ ((true , a) ∷ []) ((true , a') ∷ []) → a ≡ a'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.here (inl ()))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.here (inr ()))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.there [] x x₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.there ((false , a'') ∷ []) x x₁) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.there ((true , a'') ∷ []) x x₁) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      w _ _ x ∙ w _ _ x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.there (x₂ ∷ x₃ ∷ a'') x x₁) = {!!}
      
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.tcsym x) = sym (w a' a x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.tcrefl x) = cong snd (cons-inj₁ x)
    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓· : List/↓ → List/↓ → List/↓
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++L↓ a b c))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++R↓ a b c))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓ : List/↓ → List/↓ → List/↓
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++L↓ a b c))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++R↓ a b c))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓Group : GroupStr List/↓
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.1g List/↓Group = SQ.[ [] ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr._·_ List/↓Group = List/↓·

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.inv List/↓Group =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SQ.rec squash/ (SQ.[_] ∘ rev)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.isGroup List/↓Group = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module FG (freeGroupGroup : Group ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (η : A → ⟨ freeGroupGroup ⟩) where 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  FreeGroup = ⟨ freeGroupGroup ⟩

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open GroupStr (snd freeGroupGroup)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open GroupTheory freeGroupGroup

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  η* : Bool × A → FreeGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  η* (b , a) = (if b then idfun _ else inv) (η a)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList' : FreeGroup → List (Bool × A) → FreeGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList' = foldr (_·_ ∘ η*) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList : List (Bool × A) → FreeGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList = fromList' 1g

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList· : ∀ xs ys → fromList (xs ++ ys) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            fromList xs · fromList ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList· [] _ = sym (·IdL _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList· (_ ∷ xs) _ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cong (_ ·_) (fromList· xs _) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ·Assoc _ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* : ∀ x x' → IsRedex x x' → η* x · η* x' ≡ 1g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (false , _) (false , _) (p , _) = ⊥.rec (false≢true p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (false , x) (true , _) (_ , q) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong (inv (η x) ·_) (cong (η) (sym q)) ∙ ·InvL (η x) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (true , x) (false , _) (_ , q) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong (η x ·_) (cong (inv ∘ η) (sym q)) ∙ ·InvR (η x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (true , _) (true , _) (p , _) = ⊥.rec (true≢false p)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- 𝑵𝑭 : ⟨ freeGroupGroup ⟩ → ℙ (List (Bool × A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- 𝑵𝑭 a l = ((fromList l ≡ a) , is-set _ _) L.⊓
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --             𝑵 l
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- NF : ⟨ freeGroupGroup ⟩ → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- NF a = ∃ (List (Bool × A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   λ l → (fromList l ≡ a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     × IsNormalised l 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module FGAlt where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open import Cubical.HITs.FreeGroup.Alt 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open FG (freeGroupGroup A) η

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- hh : ∀ x b xs → ∀ l → {!NonEmpty (NF ((x , b) ∷ l)) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --          !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- hh = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   non∅NF : ∀ x → NonEmpty (NF x) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   non∅NF = ElimProp.go w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    open ElimProp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w : ElimProp _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    εB (elim₁ w) q = q ∣ [] , refl , tt* ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∷B (elim₁ w) false a x x₁ = x₁ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∷B (elim₁ w) true a x x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    isPropB w = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (_≟_ : Discrete A) where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsRedex? : ∀ x x' → Dec (IsRedex x x')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsRedex? (b , x) (b' , x') =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    subst Dec (sym ΣPathP≡PathPΣ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (discreteΣ 𝟚._≟_ (λ _ → _≟_) (b , x) (not b' , x'))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  WillReduce? : ∀ x xs → Dec (WillReduce (fst x) (snd x) xs)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  WillReduce? _ [] = no λ ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  WillReduce? _ (_ ∷ xs) = IsRedex? _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsNormalised? : ∀ xs → Dec (IsNormalised xs)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsNormalised? [] = yes _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsNormalised? (x ∷ xs) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Dec× (Dec¬ (WillReduce? _ _)) (IsNormalised? _) 


