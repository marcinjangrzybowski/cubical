{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.NormalForm.Base where

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
import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Binary.Base


private
  variable
    ℓ : Level

[𝟚×_] : (A : Type ℓ) → Type ℓ
[𝟚×_] = List ∘' (Bool ×_) 

module NormalForm (A : Type ℓ) where


 not₁ : (Bool × A) → (Bool × A)
 not₁ = map-fst not

 not₁not₁ : ∀ x → not₁ (not₁ x) ≡ x 
 not₁not₁ (x , y) = cong (_, y) (notnot x) 

 IsRedex : Bool × A → Bool × A → Type ℓ
 IsRedex x x' = x ≡ not₁ x'

 symIsRedex : ∀ x y → IsRedex x y → IsRedex y x
 symIsRedex x y p = sym (not₁not₁ _) ∙ cong not₁ (sym p)
 
 WillReduce : Bool → A → (xs : [𝟚× A ]) → Type ℓ
 WillReduce _ _ [] = ⊥* 
 WillReduce b x (h ∷ _) = IsRedex (b , x) h
 
 HeadIsRedex : [𝟚× A ] → Type ℓ
 HeadIsRedex [] = ⊥*
 HeadIsRedex ((b , a) ∷ xs) = WillReduce b a xs

 HasRedex : [𝟚× A ] → Type ℓ
 HasRedex [] = ⊥*
 HasRedex xs@(_ ∷ xs') = HeadIsRedex xs ⊎ HasRedex xs'

 HasRedex∷ʳ : ∀ {xs} {x} → HasRedex xs → HasRedex (xs ∷ʳ x) 
 HasRedex∷ʳ {x₂ ∷ xs} (inr x₁) = inr (HasRedex∷ʳ x₁)
 HasRedex∷ʳ {x₂ ∷ x₃ ∷ xs} (inl x₁) = inl x₁

 HasRedex++ : ∀ xs ys → HasRedex xs → HasRedex (xs ++ ys)  
 HasRedex++ (x₁ ∷ xs) ys (inr x) = inr (HasRedex++ xs ys x)
 HasRedex++ (x₁ ∷ x₂ ∷ xs) ys (inl x) = inl x

 ++HasRedex : ∀ xs ys → HasRedex ys → HasRedex (xs ++ ys)  
 ++HasRedex [] ys x = x
 ++HasRedex (x₁ ∷ xs) ys x =
   inr (++HasRedex xs ys x)

 IsNormalised : [𝟚× A ] → hProp ℓ
 IsNormalised xs = (¬ HasRedex xs) , isProp¬ _

 IsNormalised[] : ⟨ IsNormalised [] ⟩
 IsNormalised[] = lower

 IsNormalised[x] : ∀ x → ⟨ IsNormalised [ x ] ⟩
 IsNormalised[x] _ = ⊎.rec lower lower

 IsNormalisedTail : ∀ xs → ⟨ IsNormalised xs ⟩ → ⟨ IsNormalised (tail xs) ⟩ 
 IsNormalisedTail [] n = n
 IsNormalisedTail (x ∷ xs) = _∘ inr

 ¬IsRedex→IsNormalisedPair :
   ∀ {x x'} → ¬ IsRedex x x' → ⟨ IsNormalised (x ∷ [ x' ]) ⟩ 
 ¬IsRedex→IsNormalisedPair {x' = x'} ¬ir = ⊎.rec ¬ir (IsNormalised[x] x')
 
 invLi : [𝟚× A ] → [𝟚× A ]
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

 HasRedexInvLi : ∀ {xs} → HasRedex xs → HasRedex (invLi xs)
 HasRedexInvLi {_ ∷ []} x = x
 HasRedexInvLi {x₁ ∷ x₂ ∷ xs} = ⊎.rec
  (subst HasRedex (sym (++-assoc (invLi xs) _ _))
     ∘' ++HasRedex (invLi xs) (_ ∷ _)
     ∘' inl ∘' cong not₁  ∘' symIsRedex _ _ )
  (HasRedex∷ʳ ∘' HasRedexInvLi)
     
 
 IsNormalisedInvLi : ∀ {xs} → 
                   ⟨ IsNormalised xs
                         L.⇔ IsNormalised (invLi xs) ⟩
 IsNormalisedInvLi = _∘' subst HasRedex (invol-invLi _) ∘' HasRedexInvLi
   , _∘' HasRedexInvLi 

 HasRedexSplit++ : ∀ {xs ys} → HasRedex (xs ++ ys) →
        HasRedex (take 1 (rev xs) ++ take 1 ys) ⊎
            (HasRedex xs ⊎ HasRedex ys)
 HasRedexSplit++ {[]} = inr ∘ inr
 HasRedexSplit++ {x ∷ []} {[]} r = ⊥.rec (IsNormalised[x] x r)
 HasRedexSplit++ {x ∷ []} {x₁ ∷ ys} = ⊎.rec (inl ∘ inl) (inr ∘ inr)
 HasRedexSplit++ {x ∷ x₁ ∷ xs} {ys} = 
   ⊎.rec (inr ∘ inl ∘ inl)
    (⊎.rec (inl ∘ subst (λ zz → HasRedex (zz ++ take 1 ys))
     (w _ (subst (0 <_) (+-comm 1 _ ∙ sym (length++ (rev xs) _)) _)))
      (⊎.rec (inr ∘ inl ∘ inr) (inr ∘ inr) ) ∘' HasRedexSplit++ {x₁ ∷ xs} {ys})
  where
  w : ∀ xs → 0 < length xs → take 1 xs ≡ take 1 (xs ++ [ x ])
  w (x ∷ xs) _ = refl


 module NF {ℓ'} (G : Group ℓ') (η : A → ⟨ G ⟩) where

  open GroupStr (snd G) renaming (_·_ to _·fg_) public

  η* : Bool × A → ⟨ G ⟩
  η* (b , a) = (if b then idfun _ else inv) (η a)

  fromList : [𝟚× A ] → ⟨ G ⟩
  fromList = foldr (_·fg_ ∘ η*) 1g

  record NF (g : _) : Type (ℓ-max ℓ ℓ') where
   constructor _nf_,_
   field
    𝒘 : [𝟚× A ]
    fromList𝒘≡ : fromList 𝒘 ≡ g
    isNormalised𝒘 : ⟨ IsNormalised 𝒘 ⟩


  fromList· : ∀ xs ys → fromList (xs ++ ys) ≡
                            fromList xs ·fg fromList ys
  fromList· [] _ = sym (·IdL _)
  fromList· (_ ∷ xs) _ =
   cong (_ ·fg_) (fromList· xs _) ∙
    ·Assoc _ _ _

  redex-ε-η* : ∀ x x' → IsRedex x x' → η* x ·fg η* x' ≡ 1g
  redex-ε-η* (false , _) (false , _) = ⊥.rec ∘ false≢true ∘ cong fst
  redex-ε-η* (false , x) (true , _) q = 
    cong (inv (η x) ·fg_) (cong (η) (sym (cong snd q))) ∙ ·InvL (η x) 
  redex-ε-η* (true , x) (false , _) q =
    cong (η x ·fg_) (cong (inv ∘ η) (sym (cong snd q))) ∙ ·InvR (η x)
  redex-ε-η* (true , _) (true , _) = ⊥.rec ∘ true≢false ∘ cong fst
