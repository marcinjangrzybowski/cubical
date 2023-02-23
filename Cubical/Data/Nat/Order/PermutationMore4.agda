{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.PermutationMore4 where

open import Cubical.Data.Nat.Base as ℕ hiding (_·_)
open import Cubical.Data.Nat.Properties


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution

open import Cubical.Foundations.Everything
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group

open import Cubical.Algebra.SymmetricGroup

import Cubical.Functions.Logic as L

open import Cubical.Functions.Embedding

open import Cubical.Data.List as Li

import Cubical.Data.Nat.FinGenAut2 as A

import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SequentialColimit as SC

open import Cubical.Data.Nat.Order.Permutation

-- open import Cubical.Data.FinData.GTrun

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)

open import Cubical.HITs.ListedFiniteSet.Base2

private
  variable
    ℓ : Level
    A : Type ℓ




-- -- mkCube' : ∀ {ℓ} {A A' : Type ℓ}
-- --    {a₀₀₋ : A ≡ A}
-- --    {a₀₁₋ : A ≡ A}
-- --    {a₀₋₀ : A ≡ A} {a₀₋₁ : A ≡ A}
-- --    (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- --    {a₁₀₋ : A' ≡ A'}
-- --    {a₁₁₋ : A' ≡ A'}
-- --    {a₁₋₀ : A' ≡ A'} {a₁₋₁ : A' ≡ A'}
-- --    (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- --    {a₋₀₀ : A ≡ A'} {a₋₀₁ : A ≡ A'}
-- --    (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- --    {a₋₁₀ : A ≡ A'} {a₋₁₁ : A ≡ A'}
-- --    (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- --    (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- --    (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- --    → _
-- --    → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
-- -- mkCube' a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ x =
-- --  toPathP (invEq (congEquiv (PathP≃Path _ _ _))
-- --     (invEq (congEquiv ((congEquiv (
-- --       (PathP≃Path (λ i → Type _) (a₋₋₀ i1 i1) _)
-- --        ∙ₑ univalence))))
-- --      (ΣSquareSet (isProp→isSet ∘ isPropIsEquiv)
-- --       (comm→PathP
-- --        (invEq (congEquiv (invEquiv funExtEquiv))
-- --         (funExt x))))))

-- -- mkCube :
-- --  ∀ {a₀₀₋ : A ≡ A}
-- --    {a₀₁₋ : A ≡ A}
-- --    {a₀₋₀ : A ≡ A} {a₀₋₁ : A ≡ A}
-- --    (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- --    {a₁₀₋ : A ≡ A}
-- --    {a₁₁₋ : A ≡ A}
-- --    {a₁₋₀ : A ≡ A} {a₁₋₁ : A ≡ A}
-- --    (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- --    {a₋₀₀ : A ≡ A} {a₋₀₁ : A ≡ A}
-- --    (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- --    {a₋₁₀ : A ≡ A} {a₋₁₁ : A ≡ A}
-- --    (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- --    (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- --    (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- --    → SquareP (λ i j → (a₀₋₋ i j) → (a₁₋₋ i j))
-- --        (λ j → transport (flipSquare a₋₀₋ j))
-- --        (λ j → transport (flipSquare a₋₁₋ j))
-- --        (λ i → transport (flipSquare a₋₋₀ i))
-- --        (λ i → transport (flipSquare a₋₋₁ i))
-- --    → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
-- -- mkCube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ x k i j =
-- --   hcomp
-- --    (λ l → λ {
-- --      (i = i0) → {!!}
-- --     ;(i = i1) → {!!}
-- --     ;(j = i0) → {!!}
-- --     ;(j = i1) → {!!}
-- --     ;(k = i0) → a₀₋₋ i j
-- --     ;(k = i1) → a₁₋₋ i j
-- --     })
-- --    (ua (x i j , {!!}) k)

ℙrm' : ℕ → Type
ℙrm' n = EM₁ (PermG n)



Flooop : ∀ n (k l : Σ ℕ  λ k → (suc k < n)) → Fin n ≡ Fin n
Flooop n k l i =
  Glue (Fin n)
    λ {(i = i0) → _ , adjT'≃ {n = n} k
      ;(i = i1) → _ , adjT'≃ {n = n} l
       }

-- ℕlooop' : ℕ → ℕ → ℕ ≡ ℕ
-- ℕlooop' n k i = 
--   Glue ℕ
--     λ {(i = i0) → _ , {!A.adjTransposition≃ k!}
--       ;(i = i1) → _ , {!!}
--        }


Flooop-comp : ∀ n (k l : Σ ℕ  λ k → (suc k < n))
  → Square
       (ua (adjT'≃ {n = n} k))
       (ua (adjT'≃ {n = n} l))
       (Flooop n k l)
       refl
Flooop-comp n k l i j =
    Glue (Fin n)
    λ {(j = i0) (i = i0) → _ , adjT'≃ {n = n} k
      ;(j = i0) (i = i1) → _ , adjT'≃ {n = n} l
      ;(j = i1) → _ , idEquiv _
       }

Flooop-comm-sqL' : ∀ n k l → commT (fst k) (fst l)
  → (x : Fin n) →
      PathP (λ z₁ → ua (adjT'≃ {n = n} l ∙ₑ adjT'≃ {n = n}  k) z₁)
        (fst (adjT'≃ {n = n} k) x)
      (fst (adjT'≃ {n = n} l) x)
Flooop-comm-sqL' n k l z x i =
  glue (λ {(i = i0) → (fst (adjT'≃ {n = n} k) x)
         ; (i = i1) → (fst (adjT'≃ {n = n} l) x) })           
       (≡Fin {n = n}
         {(fst (adjT'≃ {n = n} k ∙ₑ adjT'≃ {n = n} l ∙ₑ adjT'≃ {n = n} k) x)}
         {(fst (adjT'≃ {n = n} l) x)}
             (funExt⁻ (A.adjTranspositionComm' (fst k) (fst l) z) (fst x)) i)

Flooop-comm-sqL : ∀ n (k l : Σ ℕ  λ k → (suc k < n))
   → commT (fst k) (fst l)
   → PathP (λ j → Fin n ≃ ua (adjT'≃ {n = n} l ∙ₑ adjT'≃ {n = n} k) j)
      (adjT'≃ {n = n} k)
      (adjT'≃ {n = n} l)
Flooop-comm-sqL n k l z =
 ΣPathPProp isPropIsEquiv
   (funExt (Flooop-comm-sqL' n k l z ))  

Flooop-comm-sqR : ∀ n (k l : Σ ℕ  λ k → (suc k < n))
   → PathP (λ j → Fin n ≃ ua (adjT'≃ {n = n} l ∙ₑ adjT'≃ {n = n} k) j)
      (adjT'≃ {n = n} l)
      (adjT'≃ {n = n} k)
Flooop-comm-sqR n k l =
   ΣPathPProp isPropIsEquiv
   (λ i x →
       glue (λ {(i = i0) → (fst (adjT'≃ {n = n} l) x)
               ; (i = i1) → (fst (adjT'≃ {n = n} k) x) })
           (fst (adjT'≃ {n = n} k)
             (isInvolution-adjT n l x i)))
  


Flooop-comm : ∀ n (k l : Σ ℕ  λ k → (suc k < n))
   → commT (fst k) (fst l)
   → Square (Flooop n k l) (Flooop n l k)  refl refl
Flooop-comm n k l z j i =
    Glue (ua (adjT'≃ {n = n} l ∙ₑ adjT'≃ {n = n} k) j)
    λ {(i = i0) → Fin n , Flooop-comm-sqL n k l z j
      ;(i = i1) → Fin n , Flooop-comm-sqR n k l j }


-- floop-braid-0 : ∀ n k k< → 
--    PathP (λ j → ua (adjT'≃ {n = n} (suc k , k<)) j ≃
--         (ua ((adjT'≃ {n = n} (suc k , k<)) ∙ₑ
--                   (adjT'≃ {n = n} ((k , <-weaken {n = n} k<))) ∙ₑ
--                   (adjT'≃ {n = n} (suc k , k<))) (~ j)))
--       (adjT'≃ {n = n} (k , <-weaken {n = n} k<))
--       (adjT'≃ {n = n} (k , <-weaken {n = n} k<))
-- floop-braid-0 n k k< =
--    ΣPathPProp isPropIsEquiv 
--               ( {!!}
--      ◁ (λ j →
--        ua-gluePathExt (((adjT'≃ {n = n} (suc k , k<)) ∙ₑ
--                   (adjT'≃ {n = n} ((k , <-weaken {n = n} k<))) ∙ₑ
--                   (adjT'≃ {n = n} (suc k , k<)))) (~ j) ∘'
--          ua-ungluePathExt ((adjT'≃ {n = n} (suc k , k<))) j) ▷
--          {!!})


-- floop-braid-1 : ∀ n k k< → 
--    PathP (λ j → ua (adjT'≃ {n = n} (k , <-weaken {n = n} k<)) j ≃ {!!})
--       (adjT'≃ {n = n} (suc k , k<))
--       (adjT'≃ {n = n} (suc k , k<))
-- floop-braid-1 n k k< j = {!!}

Flooop-sq : ∀ n {k₀} {k₁} {k₂} {k₃} →
    Square
      (Flooop n k₀ k₁)
      (Flooop n k₂ k₃)
      (Flooop n k₀ k₂)
      (Flooop n k₁ k₃)
Flooop-sq n {k₀} {k₁} {k₂} {k₃} i j =
  Glue (Fin n)
   λ {  (i = i0)(j = i0) → _ , adjT'≃ {n = n} k₀
      ; (i = i0)(j = i1) → _ , adjT'≃ {n = n} k₁
      ; (i = i1)(j = i0) → _ , adjT'≃ {n = n} k₂
      ; (i = i1)(j = i1) → _ , adjT'≃ {n = n} k₃
      }

data ℙrm (n : ℕ) : Type₀ where 
  𝕡base : ℙrm n
  𝕡loop : (Σ ℕ  λ k → (suc k < n)) → 𝕡base ≡ 𝕡base  
  𝕡looop : (k l : Σ ℕ  λ k → (suc k < n)) → 𝕡base ≡ 𝕡base
  -- 𝕡comp : (k l : Σ ℕ  λ k → (suc k < n)) →
  --    Square
  --      (𝕡loop k)
  --      (𝕡loop l)
  --      refl
  --      (𝕡looop k l)

  𝕡comp : (k l : Σ ℕ  λ k → (suc k < n)) →
     Square
       (𝕡loop k)
       (𝕡loop l)
       (𝕡looop k l)
       refl
         
  𝕡invol : ∀ k → 𝕡loop k ≡ sym (𝕡loop k)
  𝕡comm : (k l : Σ ℕ  λ k → (suc k < n)) →
     commT (fst k) (fst l) →
       Square
         refl
         refl
       (𝕡looop k l)
       (𝕡looop l k)

  𝕡braid : ∀ k k<  →        
         Square
         (𝕡loop (suc k , k<))
         (𝕡loop (k , <-weaken {n = n} k<))
         (𝕡looop (k , <-weaken {n = n} k<) (suc k , k<))
         (𝕡looop (k , <-weaken {n = n} k<) (suc k , k<))


  𝕡squash : isGroupoid (ℙrm n)

𝕡comp' : ∀ {n} → (k l : Σ ℕ  λ k → (suc k < n)) →
   Square {A = ℙrm n}
     (𝕡loop k)
     (𝕡loop l)
     refl
     (𝕡looop k l)
𝕡comp' k l =
   (𝕡invol k) ◁
   (λ i j → (𝕡comp k l i (~ j)))
   ▷ sym (𝕡invol l)

𝕡looop-invol : ∀ n → (k l : Σ ℕ  λ k → (suc k < n)) →
    𝕡looop {n = n} k l ≡ sym (𝕡looop l k)
𝕡looop-invol n k l i j =
   hcomp
      (λ l' → λ {
        (i = i0) → 𝕡comp k l j (~ l')
       ;(i = i1) → 𝕡comp l k (~ j) (~ l')
       ;(j = i0) → 𝕡loop k (~ l')
       ;(j = i1) → 𝕡loop l (~ l')
       }) 𝕡base

record R𝕡rec {n} (A : Type ℓ) : Type ℓ where
 no-eta-equality
 field
   abase : A
   aloop : (Σ ℕ  λ k → (suc k < n)) → abase ≡ abase
   alooop : (k l : Σ ℕ  λ k → (suc k < n)) → abase ≡ abase
   acomp : (k l : Σ ℕ  λ k → (suc k < n)) →
      Square
        (aloop k)
        (aloop l)
        (alooop k l)
        refl

   ainvol : ∀ k → aloop k ≡ sym (aloop k)
   acomm : (k l : Σ ℕ  λ k → (suc k < n)) →
      commT (fst k) (fst l) →
        Square
          refl
          refl
        (alooop k l)
        (alooop l k)

   abraid : ∀ k k<  →        
          Square
          (aloop (suc k , k<))
          (aloop (k , <-weaken {n = n} k<))
          (alooop (k , <-weaken {n = n} k<) (suc k , k<))
          (alooop (k , <-weaken {n = n} k<) (suc k , k<))
   asquash : isGroupoid A


 f : ℙrm n → A
 f 𝕡base = abase
 f (𝕡loop x i) = aloop x i
 f (𝕡looop k l i) = alooop k l i
 f (𝕡comp k l i i₁) = acomp k l i i₁
 -- f (𝕡comp' k l i i₁) = acomp' k l i i₁
 f (𝕡invol k i i₁) = ainvol k i i₁
 f (𝕡comm k l x i i₁) = acomm k l x i i₁
 f (𝕡braid k k< i i₁) = abraid k k< i i₁
 f (𝕡squash _ _ _ _ r s i₀ i₁ i₂) =
   asquash _ _ _ _
     (λ i j → (f (r i j)))
     (λ i j → (f (s i j)))
     i₀ i₁ i₂

record R𝕡elim {n} (A : ℙrm n → Type ℓ) : Type ℓ where
 no-eta-equality
 field
   isGroupoidA : ∀ x → isGroupoid (A x)
   abase : A 𝕡base
   aloop : (k : Σ ℕ  λ k → (suc k < n)) →
     PathP (λ i → A (𝕡loop k i)) abase abase
   alooop : (k l : Σ ℕ  λ k → (suc k < n)) →
     PathP (λ i → A (𝕡looop k l i)) abase abase
   acomp : ∀ k l →
     SquareP (λ j i → A (𝕡comp k l j i))
       (aloop k)
       (aloop l)
       (alooop k l)
       refl
   ainvol : ∀ k →
     SquareP (λ i j → A (𝕡invol k i j))
       (aloop k)
       (symP (aloop k))
       refl refl
   acomm : (k l : Σ ℕ  λ k → (suc k < n)) → ∀ x →     
       SquareP (λ i j → A (𝕡comm k l x i j))
         refl
         refl
       (alooop k l)
       (alooop l k)
   abraid : ∀ k k<  →        
         SquareP (λ i j → A (𝕡braid k k< i j))
         (aloop (suc k , k<))
         (aloop (k , <-weaken {n = n} k<))
         (alooop (k , <-weaken {n = n} k<) (suc k , k<))
         (alooop (k , <-weaken {n = n} k<) (suc k , k<))
  


 f : ∀ x → A x
 f 𝕡base = abase
 f (𝕡loop x i) = aloop x i
 f (𝕡looop k l i) = alooop k l i
 f (𝕡comp k l j i) = acomp k l j i
   
 f (𝕡invol k i j) = ainvol k i j
 
 f (𝕡comm k l x i j) = acomm k l x i j
    
 
 f (𝕡braid k k< i j) = abraid k k< i j
 f (𝕡squash x y p q r s i j k) =
   isOfHLevel→isOfHLevelDep 3 isGroupoidA
     _ _ _ _
     (λ j k → f (r j k)) (λ j k → f (s j k))
     (𝕡squash x y p q r s) i j k


record R𝕡elimSet {n} (A : ℙrm n → Type ℓ) : Type ℓ where
 no-eta-equality
 field
   isSetA : ∀ x → isSet (A x)
   abase : A 𝕡base
   aloop : (k : Σ ℕ  λ k → (suc k < n)) →
     PathP (λ i → A (𝕡loop k i)) abase abase
   alooop : (k l : Σ ℕ  λ k → (suc k < n)) →
     PathP (λ i → A (𝕡looop k l i)) abase abase
   -- (k l : Σ ℕ  λ k → (suc k < n)) → abase ≡ abase

 fR : R𝕡elim (λ z → A z)
 R𝕡elim.isGroupoidA fR = isSet→isGroupoid ∘ isSetA
 R𝕡elim.abase fR = abase
 R𝕡elim.aloop fR = aloop
 R𝕡elim.alooop fR = alooop
 R𝕡elim.acomp fR k l = 
   isSet→SquareP (λ j i → isSetA (𝕡comp k l j i)) _ _ _ _
 R𝕡elim.ainvol fR k =
  isSet→SquareP (λ j i → isSetA (𝕡invol k j i)) _ _ _ _
 R𝕡elim.acomm fR k l x =
  isSet→SquareP (λ j i → isSetA (𝕡comm k l x j i)) _ _ _ _
 R𝕡elim.abraid fR k k< =
  isSet→SquareP (λ j i → isSetA (𝕡braid k k< j i)) _ _ _ _

 f : ∀ x → A x
 f = R𝕡elim.f fR

record R𝕡elimSet' {n} (A : ℙrm n → Type ℓ) : Type ℓ where
 no-eta-equality
 field
   isSetA : ∀ x → isSet (A x)
   abase : A 𝕡base
   aloop : (k : Σ ℕ  λ k → (suc k < n)) →
     PathP (λ i → A (𝕡loop k i)) abase abase

 fR : R𝕡elimSet (λ z → A z)
 R𝕡elimSet.isSetA fR = isSetA
 R𝕡elimSet.abase fR = abase
 R𝕡elimSet.aloop fR = aloop
 R𝕡elimSet.alooop fR k l i =
   comp (λ j → A (𝕡comp k l i (~ j)))
     (λ j → λ { (i = i0) → aloop k (~ j) ; (i = i1) → aloop l (~ j) })
     abase

 f : ∀ x → A x
 f = R𝕡elimSet.f fR



record R𝕡elimProp {n} (A : ℙrm n → Type ℓ) : Type ℓ where
 no-eta-equality
 field
   isPropA : ∀ x → isProp (A x)
   abase : A 𝕡base

 fR : R𝕡elimSet (λ z → A z)
 R𝕡elimSet.isSetA fR = isProp→isSet ∘ isPropA
 R𝕡elimSet.abase fR = abase
 R𝕡elimSet.aloop fR k = isProp→PathP (λ _ → isPropA _) _ _
 R𝕡elimSet.alooop fR k l = isProp→PathP (λ _ → isPropA _) _ _

 f : ∀ x → A x
 f = R𝕡elimSet.f fR



toℙrmR≡ : ∀ n → Rrec {n = n} (Path (ℙrm n) 𝕡base 𝕡base)
Rrec.isSetA (toℙrmR≡ n) = 𝕡squash _ _
Rrec.εA (toℙrmR≡ n) = refl
Rrec.∷A (toℙrmR≡ n) k = 𝕡loop k ∙_ 
Rrec.invoA (toℙrmR≡ n) k x i j = 
  hcomp (λ l →
       λ { (i = i1) → x (j ∧ l)
         ; (j = i0) → 𝕡base
         ; (j = i1) → (hcomp (λ l' →
                 λ { (i = i1) → x (l' ∧ l)
                   ; (l = i0) → 𝕡invol k l' i
                   ; (l = i1) → x l'
                   }) (𝕡loop k (l ∨ i)))
         }) (𝕡loop k (~ i ∧ j))

Rrec.braidA (toℙrmR≡ n) k k< x i =
    𝕡comp' (k , <-weaken {n = n} k<) (suc k , k<) i
  ∙ 𝕡braid k k< i
  ∙ 𝕡comp (k , <-weaken {n = n} k<) (suc k , k<) i ∙ x

Rrec.commA (toℙrmR≡ n) k l z x i =
    𝕡comp' k l i
    ∙ (𝕡comm k l z i ∙∙ 𝕡comp l k i ∙∙ x)
  

toℙrmRsq : ∀ n → (h : Perm n) → RelimProp
      (λ z →
         
         Square (Rrec.f (toℙrmR≡ n) z)
         (Rrec.f (toℙrmR≡ n) ((snd (PermG n) GroupStr.· z) h)) refl
         (Rrec.f (toℙrmR≡ n) h))
RelimProp.isPropA (toℙrmRsq n h) _ =
  isOfHLevelRetractFromIso
    1 (invIso PathP→comm-Iso) (𝕡squash _ _ _ _)
RelimProp.εA (toℙrmRsq n h) i j = (Rrec.f (toℙrmR≡ n) h) (i ∧ j)
RelimProp.∷A (toℙrmRsq n h) k x i = 𝕡loop k ∙ x i

toℙrmR : ∀ n → EMrec (PermG n) {B = ℙrm n} 𝕡squash
EMrec.b (toℙrmR n) = 𝕡base
EMrec.bloop (toℙrmR n) = Rrec.f (toℙrmR≡ n)
EMrec.bComp (toℙrmR n) g h = RelimProp.f (toℙrmRsq n h) g 


toℙrm : ∀ n → ℙrm' n → ℙrm n
toℙrm n = EMrec.f (toℙrmR n)


commSq : ∀ n → ∀ k xs → Square {A = ℙrm' n}
           (emloop (η k))
           (emloop xs)
           refl
           (emloop (η k · xs))
commSq n k xs i j =
  hcomp (λ l' → λ {
       (i = i0) → emloop (η k) j
      ;(i = i1) → emloop (invo k xs l') j
      ;(j = i0) → embase
      ;(j = i1) → emloop (k ∷ xs) i
      }) (emcomp (η k) (η k · xs) i j)

-- commSq' : ∀ n → ∀ k l → Square {A = ℙrm' n}
--            (emloop (η l))
--            (emloop (η k))
--            refl
--            (emloop (η l · η k))
           
-- commSq' n k l i j = {!!}
--   -- hcomp (λ l' → λ {
--   --      (i = i0) → emloop (η k) j
--   --     ;(i = i1) → emloop (invo k (η l) l') j
--   --     ;(j = i0) → embase
--   --     ;(j = i1) → emloop (k ∷ η l) i
--   --     }) (emcomp (η k) (η k · η l) i j)

involSq : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
      emloop (η {n = n} k) ≡ sym (emloop (η k))
involSq n k i j =
  hcomp (λ l → λ {
       (i = i0) → emcomp (η k) (η k) j l
      ;(i = i1) → emcomp ε (η k) (~ j) l
      ;(j = i0) → emloop (k ∷ ε) l
      ;(j = i1) → emloop {Group = PermG n} ((invo {n = n} k ε) i) l
      }) embase


braidSq : ∀ n k l →
   Square {A = ℙrm' n}
     (emloop (η k))
     (emloop (η k))
     (emloop (η l))
     (emloop (k  ∷ l ∷ k ∷ ε))
braidSq n k l =
    (involSq n k) ◁
      emloop-doubleCompFill (PermG n) (η k) (η l) (η k)
braidSq' : ∀ n k l →
   Square {A = ℙrm' n}
     (sym (emloop (η l)))
     (sym (emloop (η l)))
     (emloop (l ∷ k ∷ l ∷ ε))
     (emloop (η k))
braidSq' n k l =
  (sym (involSq n l)) ◁
     λ i j → emloop-doubleCompFill (PermG n) (η l) (η k) (η l) i (~ j)


braidSqC : ∀ n k k< →
   Square {A = ℙrm' n}
     refl
     refl
     (emloop ((k , <-weaken {n = n} k<)
         ∷ (suc k , k<) ∷ (k , <-weaken  {n = n} k<) ∷ ε))
     (emloop ((suc k , k<) ∷ (k , <-weaken  {n = n} k<) ∷ (suc k , k<) ∷ ε))
      
braidSqC n k k< i j = emloop (braid k k< ε j ) i
  -- (braidSqC0 n k k< j
  --   ∙∙ (λ i → emloop (braid k k< ε i ) j)
  --   ∙∙
  --   braidSqC1 n k k< j) i

Rfromℙrm : ∀ n → R𝕡rec {n = n} (ℙrm' n)
R𝕡rec.abase (Rfromℙrm n) = embase
R𝕡rec.aloop (Rfromℙrm n) = emloop ∘ η
R𝕡rec.alooop (Rfromℙrm n) k l i =
  hcomp (λ z → λ {(i = i0) → emloop (η k) (~ z)
                ; (i = i1) → emloop (η l) (~ z)} ) embase

R𝕡rec.acomp (Rfromℙrm n) k l i j =
  doubleCompPath-filler (emloop (η k)) refl (sym (emloop (η l))) (~ j) i
R𝕡rec.ainvol (Rfromℙrm n) = involSq n
    
R𝕡rec.acomm (Rfromℙrm n) k l x i j =
  (commSq n k (η l) j ∙∙
    (λ i → emloop (comm k l x ε i ) j)
   ∙∙ sym (commSq n l (η k) j)) i
R𝕡rec.abraid (Rfromℙrm n) k k< i j =
  (braidSq n (k , (<-weaken {n = n} k<) ) (suc k , k<) j ∙∙
   (braidSqC n k k< j)
   ∙∙ braidSq' n (k , (<-weaken {n = n} k<) ) (suc k , k<) j) i

R𝕡rec.asquash (Rfromℙrm n) = emsquash

fromℙrm : ∀ n → ℙrm n → ℙrm' n
fromℙrm n = R𝕡rec.f (Rfromℙrm n)

emloop-ε : ∀ n → refl ≡ emloop {Group = PermG n} ε 
emloop-ε n i j =
  hcomp (λ l →
    primPOr i (~ i ∨ j ∨ ~ j)
      (λ _ → emcomp ε ε j l)
       λ _ → emloop ε l)
    embase 

RelimProp≡ : ∀ n → RelimProp
      λ z →
        Square
         (λ j → fromℙrm n (Rrec.f (toℙrmR≡ n) z j))
         (emloop z)
        refl
        refl
RelimProp.isPropA (RelimProp≡ n) x = emsquash _ _ _ _
RelimProp.εA (RelimProp≡ n) = emloop-ε n
RelimProp.∷A (RelimProp≡ n) k {xs} X =
  (cong-∙ (fromℙrm n) (𝕡loop k) (cong (toℙrm n) (emloop xs))
    ∙ cong (emloop (η k) ∙_) X) ∙ sym (emloop-comp _ (η k) xs)
   
RfromToℙrm : ∀ n → EMelimSet (PermG n) (λ z → fromℙrm n (toℙrm n z) ≡ z)
EMelimSet.isSetB (RfromToℙrm n) x = emsquash _ _
EMelimSet.b (RfromToℙrm n) = refl
EMelimSet.bPathP (RfromToℙrm n) = flipSquare ∘ RelimProp.f (RelimProp≡ n)

fromToℙrm : ∀ n → section (fromℙrm n) (toℙrm n)
fromToℙrm n = EMelimSet.f (RfromToℙrm n)


RtoFromℙrm : ∀ n → 
     R𝕡elimSet {n = n} (λ z → toℙrm n (fromℙrm n z) ≡ z)
R𝕡elimSet.isSetA (RtoFromℙrm n) _ = 𝕡squash _ _
R𝕡elimSet.abase (RtoFromℙrm n) = refl
R𝕡elimSet.aloop (RtoFromℙrm n) k i j =
   (compPath-filler (𝕡loop k) refl) (~ j) i
R𝕡elimSet.alooop (RtoFromℙrm n) k l i j = 
  
   hcomp (λ l' → λ {
       (i = i0) → compPath-filler (𝕡loop k) refl (~ j) (~ l')
      ;(i = i1) → compPath-filler (𝕡loop l) refl (~ j) (~ l')
      ;(j = i0) → toℙrm n
         (doubleCompPath-filler
            (emloop (η k)) refl
             (sym (emloop (η l))) l' i)
      ;(j = i1) → 𝕡comp k l i (~ l')
      }) 𝕡base

toFromℙrm : ∀ n → retract (fromℙrm n) (toℙrm n)
toFromℙrm n = R𝕡elimSet.f (RtoFromℙrm n)

IsoEmℙrm : ∀ n →  Iso (ℙrm n) (ℙrm' n)
Iso.fun (IsoEmℙrm n) = fromℙrm n
Iso.inv (IsoEmℙrm n) = toℙrm n
Iso.rightInv (IsoEmℙrm n) = fromToℙrm n
Iso.leftInv (IsoEmℙrm n) = toFromℙrm n

R𝔽in : ∀ n → R𝕡rec {n = n} (hSet ℓ-zero)
R𝕡rec.abase (R𝔽in n) = Fin n , isSetFin {n = n}
R𝕡rec.aloop (R𝔽in n) k =
  Σ≡Prop (λ _ → isPropIsOfHLevel 2) (ua (adjT'≃ {n = n} k))
R𝕡rec.alooop (R𝔽in n) k l =
  Σ≡Prop (λ _ → isPropIsOfHLevel 2) (Flooop n k l)
R𝕡rec.acomp (R𝔽in n) k l =
      ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
        (Flooop-comp n k l)

R𝕡rec.ainvol (R𝔽in n) k =
    ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
        (involPathSym _)

R𝕡rec.acomm (R𝔽in n) k l x =
      ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
       (flipSquare (Flooop-comm n k l x))
R𝕡rec.abraid (R𝔽in n) k k< =
  ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
    (comm→PathP (isInjectiveTransport
      (funExt λ x → ≡Fin {n = n}
        (funExt⁻ (A.adjTranspositionBraid k ) (fst x) ))))
R𝕡rec.asquash (R𝔽in n) = isGroupoidHSet

𝔽inH : ∀ n → ℙrm n → hSet ℓ-zero
𝔽inH n = R𝕡rec.f {n = n} (R𝔽in n)

𝔽in : ∀ {n} → ℙrm n → Type
𝔽in {n} = fst ∘' 𝔽inH n

Rsucℙrm : ∀ n → R𝕡rec {n = n} (ℙrm (suc n))
R𝕡rec.abase (Rsucℙrm n) = 𝕡base
R𝕡rec.aloop (Rsucℙrm n) k = 𝕡loop (suc (fst k) , (snd k))
R𝕡rec.alooop (Rsucℙrm n) k l =
  𝕡looop _ _
R𝕡rec.acomp (Rsucℙrm n) k l =
  𝕡comp _ _
R𝕡rec.ainvol (Rsucℙrm n) k =
  𝕡invol _
R𝕡rec.acomm (Rsucℙrm n) k l x =
  𝕡comm _ _ (suc-commT (fst k) (fst l) x)
R𝕡rec.abraid (Rsucℙrm n) k k< =
  𝕡braid _ _
R𝕡rec.asquash (Rsucℙrm n) = 𝕡squash

sucℙrm : ∀ n → ℙrm n → ℙrm (suc n)
sucℙrm n = R𝕡rec.f {n = n} (Rsucℙrm n)

fm2base : ℕ → FMSet2 Unit
fm2base zero = []
fm2base (suc x) = _ ∷2 (fm2base x)

fm2loop : ∀ n → ℕ → fm2base n ≡ fm2base n
fm2loop (suc n) (suc x) = cong (tt ∷2_) (fm2loop n x)
fm2loop zero x = refl
fm2loop (suc zero) zero = refl
fm2loop (suc (suc n)) zero = comm _ _ _

RtoFM2⊤ : ∀ n → R𝕡rec {n = n} (FMSet2 Unit)
R𝕡rec.abase (RtoFM2⊤ n) = fm2base n
R𝕡rec.aloop (RtoFM2⊤ n) (k , _) = fm2loop n k
--   cong (tt ∷2_) (R𝕡rec.aloop (RtoFM2⊤ n) (k , k<) )
-- R𝕡rec.aloop (RtoFM2⊤ (suc (suc n))) (zero , k<) = comm _ _ _

R𝕡rec.alooop (RtoFM2⊤ n) (zero , k<) (zero , l<) = refl
R𝕡rec.alooop (RtoFM2⊤ (suc n)) (suc k , k<) (suc l , l<) =
    cong (tt ∷2_) (R𝕡rec.alooop (RtoFM2⊤ n) (k , k<) (l , l<))
R𝕡rec.alooop (RtoFM2⊤ (suc (suc n))) (zero , k<) (suc (suc l) , l<) i =
  comm _ _ (R𝕡rec.aloop (RtoFM2⊤ n) (l , l<) (~ i)) (i)
R𝕡rec.alooop (RtoFM2⊤ (suc (suc n))) (suc (suc k) , k<) (zero , l<) i =
  comm _ _ (R𝕡rec.aloop (RtoFM2⊤ n) (k , k<) i) (~ i)
  
R𝕡rec.alooop (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc zero , l<) =
   comm _ _ _ ∙∙ refl ∙∙ cong (_ ∷2_) (sym (comm _ _ _)) 
R𝕡rec.alooop (RtoFM2⊤ (suc (suc (suc n)))) (suc zero , k<) (zero , l<) =
  cong (_ ∷2_) (comm _ _ _) ∙∙ refl ∙∙ sym (comm _ _ _)
  
R𝕡rec.acomp (RtoFM2⊤ (suc n)) (zero , k<) (zero , l<) i j =
  R𝕡rec.aloop (RtoFM2⊤ (suc n)) (0 , isProp≤ {m = 1} {n = n} k< l< i) j
 
R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc zero , l<) i j =
    doubleCompPath-filler  (comm _ _ _) refl
      (sym (cong (_ ∷2_) (comm _ _ (R𝕡rec.abase (RtoFM2⊤ n))))) (~ j) i
R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc (suc l) , l<) i j =
  comm _ _ ((R𝕡rec.aloop (RtoFM2⊤ (suc n)) (l , l<) (~ i ∨ j))) (i ∨ j)
R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (suc zero , k<) (zero , l<) i j =
  doubleCompPath-filler (cong (_ ∷2_) (comm _ _
    (R𝕡rec.abase (RtoFM2⊤ n))))
      refl (sym (comm _ _ _)) (~ j) i
R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (suc (suc k) , k<) (zero , l<) i j =
    comm _ _ (R𝕡rec.aloop (RtoFM2⊤ (suc n)) (k , k<) (i ∨ j)) (~ i ∨  j)

R𝕡rec.acomp (RtoFM2⊤ (suc n)) (suc k , k<) (suc l , l<) i j =
 tt ∷2 R𝕡rec.acomp (RtoFM2⊤ n) (k , k<) (l , l<) i j
R𝕡rec.ainvol (RtoFM2⊤ (suc (suc n))) (zero , k<) = comm-inv _ _ _
R𝕡rec.ainvol (RtoFM2⊤ (suc (suc (suc n)))) (suc k , k<) =
  cong (cong (tt  ∷2_)) (R𝕡rec.ainvol (RtoFM2⊤ (suc (suc n))) (k , k<))
R𝕡rec.acomm (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc (suc l) , l<) x i j =
  comm-inv tt tt
    (R𝕡rec.ainvol (RtoFM2⊤ (suc n)) (l , l<) (~ j) i) (~ j) (~ i)
R𝕡rec.acomm (RtoFM2⊤ (suc n)) (suc k , k<) (suc l , l<) x i j = 
  tt ∷2 R𝕡rec.acomm (RtoFM2⊤ (n)) (k , k<) (l , l<)
    (pred-commT k l x) i j

R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc n)))) zero k< i j =
  ((λ i → hexU _ _ _ ((R𝕡rec.abase (RtoFM2⊤ n))) i j)
    ∙∙ refl ∙∙
     (sym (cong (cong (tt ∷2_)) (comm-inv _ _ _))
       ◁ flipSquare (hexL _ _ _ (R𝕡rec.abase (RtoFM2⊤ n))) ▷
       cong (cong (tt ∷2_)) (comm-inv _ _ _)) j
       ) i 

R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc (suc n))))) (suc k) k< i j =
 tt ∷2 R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc n)))) k k< i j
R𝕡rec.asquash (RtoFM2⊤ n) = trunc


toFM2⊤ : Σ _ ℙrm → FMSet2 Unit
toFM2⊤ x = R𝕡rec.f {n = (fst x)} (RtoFM2⊤ (fst x)) (snd x)


comp0 : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
     Square
       (𝕡looop {n = suc (suc n)}(zero , tt) (suc (suc (fst k)) , snd k))
       (𝕡loop (zero , tt))
       (sym (𝕡loop (suc (suc (fst k)) , snd k)))
       refl
comp0 n k i j =
  hcomp
    (λ l → λ {
       (i = i0) → 𝕡comm (zero , tt) (suc (suc (fst k)) , snd k) _ j (~ l)
     ; (i = i1) → 𝕡loop (zero , tt) (j ∧ l)
     ; (j = i0) → 𝕡invol (suc (suc (fst k)) , snd k) l i
     ; (j = i1) → 𝕡loop (0 , tt) (~ i ∨ l)
     }) ((𝕡comp (suc (suc (fst k)) , snd k) (zero , tt) ▷ 𝕡invol (zero , tt)) j i)

comp1 : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
     Square
       (𝕡looop {n = n} k l)
       (𝕡loop k)
       refl
       (𝕡loop l)
comp1 n k l i j =
  hcomp
    (λ l' → λ {
       (i = i0) → (𝕡looop {n = n} k l) j
     ; (i = i1) → (𝕡loop k) (j ∨ ~ l')
     ; (j = i0) → 𝕡loop k (~ l' ∧ i)
     ; (j = i1) → (𝕡loop l) i
     }) ((𝕡comp {n = n} k l) j i)


aloopcommm : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
      PathP
      (λ i →
         sucℙrm (suc n) (sucℙrm n (𝕡loop k i)) ≡
         sucℙrm (suc n) (sucℙrm n (𝕡loop k i)))
      (𝕡loop (zero , tt)) (𝕡loop (zero , tt)) 
aloopcommm n (k , k<) i j =
     hcomp (λ l → λ {
    (i = i0) → comp0 n (k , k<) l j
   ;(i = i1) → comp1 (suc (suc n)) (zero , _) (suc (suc k) , k<) l j
   ;(j = i0) → 𝕡loop (suc (suc k) , k<) (i ∨ ~ l)
   ;(j = i1) → 𝕡loop (suc (suc k) , k<) (i ∧ l)
   }) (𝕡looop (zero , _) (suc (suc k) , k<) j)

fromFM2comm-diag : ∀ n → ∀ l l< → Square {A = ℙrm (2 + n)}
       (λ i →
         aloopcommm n (l , l<) (~ i) i)
      (𝕡looop (zero , _) (suc (suc l) , l<))
      refl
      refl
fromFM2comm-diag n l l< =
  symP-fromGoal (compPath-filler (𝕡looop (zero , _) (suc (suc l) , l<)) refl)

fromFM2comm-diag' : ∀ n → ∀ l l< → Square {A = ℙrm (2 + n)}
       (λ i →
         aloopcommm n (l , l<) (i) (~ i))
      (𝕡looop (suc (suc l) , l<) (zero , _))
      refl
      refl
fromFM2comm-diag' n k k< =
  congP (λ _ → sym) (fromFM2comm-diag n k k<) ∙
   sym (𝕡looop-invol _ _ _)





fromFM2comm : (n : ℕ) → R𝕡elimSet {n = n} (λ (y : ℙrm n) →
      (sucℙrm (suc n) (sucℙrm n y)) ≡
      (sucℙrm (suc n) (sucℙrm n y)))
R𝕡elimSet.isSetA (fromFM2comm n) _ = 𝕡squash _ _
R𝕡elimSet.abase (fromFM2comm n) = 𝕡loop (zero , _)
R𝕡elimSet.aloop (fromFM2comm n) = aloopcommm n
R𝕡elimSet.alooop (fromFM2comm n) k l i j =
 hcomp
   (λ l' → λ {
     (i = i0) → aloopcommm n k (~ l') j
    ;(i = i1) → aloopcommm n l (~ l') j
    ;(j = i0) → sucℙrm (suc n) (sucℙrm n (𝕡comp k l i (~ l')))
    ;(j = i1) → sucℙrm (suc n) (sucℙrm n (𝕡comp k l i (~ l')))
     }) (𝕡loop (zero , tt) j)


fromFM2comm-inv : (n : ℕ) → R𝕡elimProp {n = n}
  (λ (p : ℙrm n) →
     R𝕡elimSet.f (fromFM2comm n) p
  ≡ sym (R𝕡elimSet.f (fromFM2comm n) p))
R𝕡elimProp.isPropA (fromFM2comm-inv n) _ = 𝕡squash _ _ _ _
R𝕡elimProp.abase (fromFM2comm-inv n) = 𝕡invol _


-- hex-lem : ∀ n → R𝕡elimProp {n = n}
--       (λ z₁ →
--          Square
--          {!!}
--          {!!}
--          {!!}
--          {!!})
-- hex-lem = {!!}

RfromFM2⊤' : RElim {A = Unit} λ xs → ℙrm (len2 xs)
RElim.[]* RfromFM2⊤' = 𝕡base
RElim._∷*_ RfromFM2⊤' _ = sucℙrm _
RElim.comm* RfromFM2⊤' _ _ = (R𝕡elimSet.f (fromFM2comm _))
RElim.comm-inv* RfromFM2⊤' _ _ = R𝕡elimProp.f (fromFM2comm-inv _)
RElim.hexDiag* RfromFM2⊤' _ _ _ p =
      (cong′ (sucℙrm _) (((R𝕡elimSet.f (fromFM2comm _)) p))
      ∙∙ ((R𝕡elimSet.f (fromFM2comm _)) (sucℙrm _ p))
      ∙∙ cong′ (sucℙrm _) (sym ((R𝕡elimSet.f (fromFM2comm _)) p)) )
RElim.hexU* RfromFM2⊤' _ _ _ =
  R𝕡elimProp.f (record { isPropA =
    λ _ → isOfHLevelRetractFromIso 1 (invIso PathP→comm-Iso)
      (𝕡squash _ _ _ _) ;
    abase = λ i j →
      hcomp (λ l →
        primPOr (~ i) (j ∨ ~ j) (λ _ → 𝕡loop (1 , tt) j)
          λ _ → hcomp
              (λ l' → λ {
                  (i = i0) → 𝕡loop (zero , tt) (~ l' ∧ l)
                 ;(i = i1) → 𝕡invol (1 , tt) l' l
                 ;(l = i0) → 𝕡looop (zero , tt) (1 , tt) i
                 ;(l = i1) → 𝕡loop (zero , tt) (i ∨ (~ l'))
                 }) (𝕡comp (zero , tt) (1 , tt) i l))
       (𝕡braid zero tt i j) })
  
RElim.hexL* RfromFM2⊤' _ _ _ p =
  symP-fromGoal (doubleCompPath-filler _ _ _)
RElim.trunc* RfromFM2⊤' _ = 𝕡squash

fromFM2⊤ : FMSet2 Unit → Σ ℕ ℙrm
fromFM2⊤ xs = (len2 xs) , (RElim.f RfromFM2⊤' xs )


Rsucℙrm-lem : ∀ n → R𝕡elimSet {n = n}
  λ p → toFM2⊤ (suc n , sucℙrm n p) ≡ tt ∷2 toFM2⊤ (n , p)
R𝕡elimSet.isSetA (Rsucℙrm-lem n) _ = trunc _ _
R𝕡elimSet.abase (Rsucℙrm-lem n) = refl
R𝕡elimSet.aloop (Rsucℙrm-lem n) k _ = refl
R𝕡elimSet.alooop (Rsucℙrm-lem n) k l _ = refl

sucℙrm-lem : ∀ n p → toFM2⊤ (suc n , sucℙrm n p) ≡ tt ∷2 toFM2⊤ (n , p)
sucℙrm-lem n = R𝕡elimSet.f (Rsucℙrm-lem n)

comm*-lem : ∀ n → R𝕡elimProp {n = n}
               (λ p → Square {A = FMSet2 Unit}
        (sucℙrm-lem (suc n) (sucℙrm n p) ∙ cong′ (tt ∷2_) (sucℙrm-lem n p))
        (sucℙrm-lem (suc n) (sucℙrm n p) ∙ cong′ (tt ∷2_) (sucℙrm-lem n p))
        (λ i → toFM2⊤ (suc (suc n) , (R𝕡elimSet.f {n = n} (fromFM2comm n)) p i))
        (comm tt tt (toFM2⊤ (n , p))))
R𝕡elimProp.isPropA (comm*-lem n) _ =
   isOfHLevelRetractFromIso 1 (invIso PathP→comm-Iso) (trunc _ _ _ _)
R𝕡elimProp.abase (comm*-lem n) i = refl ∙∙ refl ∙∙ refl

RfromToFM2⊤ : RElimSet' (λ z → toFM2⊤ (fromFM2⊤ z) ≡ z) 
RElimSet'.[]* RfromToFM2⊤ = refl
(RfromToFM2⊤ RElimSet'.∷* tt) {xs} X =
  uncurry sucℙrm-lem (fromFM2⊤ xs) ∙ cong (tt ∷2_) X
  
RElimSet'.comm* RfromToFM2⊤ tt tt {xs} X i j =
 hcomp
   (λ l → primPOr (j ∨ ~ j) ((i ∨ ~ i))
      (primPOr j (~ j) (λ _ → comm tt tt (X l) i)
        λ _ → toFM2⊤ (fromFM2⊤ (comm tt tt xs i)))
      λ _ → (uncurry sucℙrm-lem (fromFM2⊤ (tt ∷2 xs)) ∙
         cong′ (tt ∷2_) (compPath-filler (uncurry sucℙrm-lem (fromFM2⊤ xs))
                    (cong′ (tt ∷2_) X) l)) j)

  (R𝕡elimProp.f {n = (fst (fromFM2⊤ xs))}
    (comm*-lem (fst (fromFM2⊤ xs))) (snd (fromFM2⊤ xs)) i j)

-- RElimSet.hexDiag* RfromToFM2⊤ _ _ _ b i j = 
--   hcomp
--     (λ l → λ {
--       (i = i0) → {!!}
--      ;(i = i1) → {!!}
--      ;(j = i0) → {!!}
--      ;(j = i1) → hexDiag _ _ _ (b l) i
--        })
--     {!!}

-- i = i0 ⊢ (uncurry sucℙrm-lem (fromFM2⊤ (y ∷2 z ∷2 xs)) ∙
--           (λ i₁ →
--              tt ∷2
--              (uncurry sucℙrm-lem (fromFM2⊤ (z ∷2 xs)) ∙
--               (λ i₂ →
--                  tt ∷2 (uncurry sucℙrm-lem (fromFM2⊤ xs) ∙ (λ i₃ → tt ∷2 b i₃)) i₂))
--              i₁))
--          j
-- i = i1 ⊢ (uncurry sucℙrm-lem (fromFM2⊤ (y ∷2 x ∷2 xs)) ∙
--           (λ i₁ →
--              tt ∷2
--              (uncurry sucℙrm-lem (fromFM2⊤ (x ∷2 xs)) ∙
--               (λ i₂ →
--                  tt ∷2 (uncurry sucℙrm-lem (fromFM2⊤ xs) ∙ (λ i₃ → tt ∷2 b i₃)) i₂))
--              i₁))
--          j
-- j = i0 ⊢ toFM2⊤ (fromFM2⊤ (hexDiag x y z xs i))
-- j = i1 ⊢ hexDiag x y z xs i
-- b  : toFM2⊤ (fromFM2⊤ xs) ≡ xs

RElimSet'.trunc* RfromToFM2⊤ _ = trunc _ _

fromToFM2⊤ : retract fromFM2⊤ toFM2⊤
fromToFM2⊤ = RElimSet'.f RfromToFM2⊤

dccf-lem : ∀ {a a' : A} → (p : a ≡ a') →
             Square p p (refl ∙∙ refl ∙∙ refl) refl
dccf-lem {a = a} {a'} p i j = 
   hcomp
     (λ l → λ {
       (i = i0) → p j
      ;(i = i1) → p j
      ;(j = i1) → a'
       })
     (p j)



RtoFromFM2⊤-fst : ∀ n → R𝕡elimSet {n = n} (λ z → len2 (toFM2⊤ (n , z)) ≡ n)
R𝕡elimSet.isSetA (RtoFromFM2⊤-fst n) _ = isProp→isSet (isSetℕ _ _)
R𝕡elimSet.abase (RtoFromFM2⊤-fst zero) = refl
R𝕡elimSet.abase (RtoFromFM2⊤-fst (suc n)) =
  cong suc (R𝕡elimSet.abase (RtoFromFM2⊤-fst n))
R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc n)) (suc k , k<) i j =
  suc (R𝕡elimSet.aloop (RtoFromFM2⊤-fst (n)) (k , k<) i j)
R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc (suc n))) (zero , k<) = refl

R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc n)) (suc k , k<) (suc l , l<) i j =
  suc (R𝕡elimSet.alooop (RtoFromFM2⊤-fst n) (k , k<) (l , l<) i j)
R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc n)) (zero , k<) (zero , l<) = refl
R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc n)))) (zero , k<) (suc zero , l<) i j =
 suc (suc (suc (dccf-lem (R𝕡elimSet.abase (RtoFromFM2⊤-fst n)) i j)))
R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc (suc n))))) (zero , k<) (suc (suc l) , l<) i j = suc (suc (R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc (suc n))) (l , l<) (~ i) j))
R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc n)))) (suc zero , k<) (zero , l<) i j =
  suc (suc (suc (dccf-lem (R𝕡elimSet.abase (RtoFromFM2⊤-fst n)) i j)))
R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc (suc n))))) (suc (suc k) , k<) (zero , l<) i j = suc (suc ((R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc (suc n))) (k , k<) i j)))


-- ∷2-lem-fst : ∀ xs → (fromFM2⊤ (tt ∷2 xs)) ≡
--    (suc (fst (fromFM2⊤ xs)) , uncurry sucℙrm (fromFM2⊤ xs))

base≡ : ∀ n → PathP (λ i → ℙrm (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) i))
      (RElim.f RfromFM2⊤' (fm2base n)) 𝕡base
base≡ zero _ = 𝕡base
base≡ (suc n) = congP (λ _ → sucℙrm _) (base≡ n)



loop≡ : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
      PathP
      (λ i →
         PathP (λ i₁ → ℙrm (R𝕡elimSet.f (RtoFromFM2⊤-fst n) (𝕡loop k i) i₁))
         (snd (fromFM2⊤ (toFM2⊤ (n , 𝕡loop k i)))) (𝕡loop k i))
      (base≡ n) (base≡ n)
loop≡ (suc n) (suc k , k<) i j = sucℙrm _ (loop≡ n (k , k<) i j) 
loop≡ (suc (suc n)) (zero , k<) i j =
        (R𝕡elim.f
          (R𝕡elimSet.fR (fromFM2comm (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j)))
         ((base≡ n) j ) i)

looop≡ : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
      PathP
      (λ i →
         PathP
         (λ i₁ → ℙrm (R𝕡elimSet.f (RtoFromFM2⊤-fst n) (𝕡looop k l i) i₁))
                           (snd (fromFM2⊤ (toFM2⊤ (n , 𝕡looop k l i))))
         (𝕡looop k l i))
      (base≡ n) (base≡ n)
looop≡ (suc n) (suc k , k<) (suc l , l<) i j =
   sucℙrm _ (looop≡ n (k , k<) (l , l<) i j)      
looop≡ (suc (suc n)) (zero , k<) (zero , l<) i j =
  hcomp (λ l' → primPOr j (i ∨ ~ i ∨ ~ j)
             (λ _ → 𝕡comp (zero , _) (zero , _) i (~ l'))
             λ _ → loop≡ (suc (suc n)) (zero , _) (~ l') j)
        (sucℙrm _ (sucℙrm _ (base≡ n j)))
looop≡ (suc (suc (suc n))) (zero , k<) (suc zero , l<) i j = 
  comp (λ l' →  ℙrm (3 +
           hfill
          (λ { l (i = i0) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
             ; l (i = i1) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
             ; l (j = i1) → n
             }) (inS (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j)) l'))
     (λ l' → λ {
         (i = i0) → loop≡ (suc (suc (suc n))) (zero , _) (~ l') j
        ;(i = i1) → loop≡ (suc (suc (suc n))) (1 , _) (~ l') j
        ;(j = i1) → 𝕡comp (zero , _) (1 , _) i (~ l')
        })
        ((sucℙrm _ (sucℙrm _ (sucℙrm _ (base≡ n j)))))

looop≡ (suc (suc (suc (suc n)))) kk@(zero , k<) ll@(suc (suc l) , l<) =
  flipSquareP ((λ j i →
      (((R𝕡elim.f
            (R𝕡elimSet.fR (fromFM2comm _))
            (loop≡ (suc (suc n)) (l , l<) (~ i) j) i))) ) ▷
             fromFM2comm-diag (suc (suc n)) l l<)
   
looop≡ (suc (suc (suc n))) (suc zero , k<) (zero , l<) i j =
     comp (λ l' →  ℙrm (3 +
           hfill
          (λ { l (i = i1) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
             ; l (i = i0) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
             ; l (j = i1) → n
             }) (inS (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j)) l'))
     (λ l' → λ {
         (i = i1) → loop≡ (suc (suc (suc n))) (zero , _) (~ l') j
        ;(i = i0) → loop≡ (suc (suc (suc n))) (1 , _) (~ l') j
        ;(j = i1) → 𝕡comp (1 , _) (zero , _) i (~ l')
        })
        ((sucℙrm _ (sucℙrm _ (sucℙrm _ (base≡ n j)))))

looop≡ (suc (suc (suc (suc n)))) (suc (suc k) , k<) (zero , l<) =
    flipSquareP ((λ j i →
      (((R𝕡elim.f
            (R𝕡elimSet.fR (fromFM2comm _))
            (loop≡ (suc (suc n)) (k , k<) (i) j) (~ i)))) ) ▷
             fromFM2comm-diag' (suc (suc n)) k k<)


RtoFromFM2⊤ : ∀ n → R𝕡elimSet {n = n} (λ z →
       PathP (λ i → ℙrm ((R𝕡elimSet.f (RtoFromFM2⊤-fst n) z i)))
           (snd (fromFM2⊤ (toFM2⊤ (n , z)))) z)
R𝕡elimSet.isSetA (RtoFromFM2⊤ n) _ =
 isOfHLevelRetractFromIso 2 (PathPIsoPath _ _ _) (𝕡squash _ _)
R𝕡elimSet.abase (RtoFromFM2⊤ n) = base≡ n
R𝕡elimSet.aloop (RtoFromFM2⊤ n) = loop≡ n
R𝕡elimSet.alooop (RtoFromFM2⊤ n) = looop≡ n

toFromFM2⊤ : section fromFM2⊤ toFM2⊤
toFromFM2⊤ (n , p) = ΣPathP (_  , R𝕡elimSet.f {n = n} (RtoFromFM2⊤ n) p)

Iso-FM2⊤-Σℙrm : Iso (FMSet2 Unit) (Σ _ ℙrm)
Iso.fun Iso-FM2⊤-Σℙrm = fromFM2⊤
Iso.inv Iso-FM2⊤-Σℙrm = toFM2⊤
Iso.rightInv Iso-FM2⊤-Σℙrm = toFromFM2⊤
Iso.leftInv Iso-FM2⊤-Σℙrm = fromToFM2⊤


module _ {A : Type ℓ} where


-- --  -- pci = preCompInvol.e' {f = f} (B j i) fInvol
--  →adjT : ∀ n (k : Σ ℕ (λ k₁ → suc k₁ < n))  → (Fin n → A) ≃ (Fin n → A)
--  →adjT n k = preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k)
 
--  𝔽→looop : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n))  → (Fin n → A) ≡ (Fin n → A)
--  𝔽→looop n k l i =
--    Glue (Fin n → A)
--      λ { (i = i0) → (Fin n → A) , →adjT n k
--        ; (i = i1) → (Fin n → A) , →adjT n l } 

--  𝔽→looop-comp-si : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
--       Square
--          (λ i → Flooop n k l i → A)
--          (𝔽→looop n k l)
--          refl
--          refl
--  𝔽→looop-comp-si n k l j i =
--    Glue (Flooop n k l (i ∨ j) → A)
--      λ { (i = i0) → {!!}
--        ; (i = i1) → {!!}
--        ; (j = i0) → _ , idEquiv _
--        }

--  𝔽→looop-comp : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
--      Square
--        (ua (→adjT n k))
--        (ua (→adjT n l))
--        (𝔽→looop n k l)
--        refl
--  𝔽→looop-comp = {!!}

--  R𝔽→ : ∀ n → R𝕡elim {n = n} λ p → singl (𝔽in p → A)
--  R𝕡elim.isGroupoidA (R𝔽→ n) _ = isOfHLevelPlus 3 (isContrSingl _)
--  R𝕡elim.abase (R𝔽→ n) = _ , refl
--  R𝕡elim.aloop (R𝔽→ n) k i = _ ,
--    λ j → preCompInvol.eq {f = adjT n k} A (isInvolution-adjT n  k) j i   
--  fst (R𝕡elim.alooop (R𝔽→ n) k l i) = 𝔽→looop n k l i
--  snd (R𝕡elim.alooop (R𝔽→ n) k l i) j = 𝔽→looop-comp-si n k l j i
--  R𝕡elim.acomp (R𝔽→ n) = {!!}
--  R𝕡elim.ainvol (R𝔽→ n) = {!!}
--  R𝕡elim.acomm (R𝔽→ n) = {!!}
--  R𝕡elim.abraid (R𝔽→ n) = {!!}
--  -- R𝕡elim.isGroupoidA (R𝕍 n) p =
--  --    isOfHLevelPlus 3 (isContrSingl _)
--  -- R𝕡elim.abase (R𝔽→ n) = (𝔽in p → A) , ua (tabEquiv n)
--  -- R𝕡elim.aloop (R𝕍 n) k = ΣPathP (ua (adjT×^≃ (fst k)) , ua-adj-law n k)
--  -- R𝕡elim.alooop (R𝕍 n) k l = ΣPathP (𝕍looop n (fst k) (fst l) , 𝕍loopSi n k l )
--  -- fst (R𝕡elim.acomp (R𝕍 n) (k , _) (l , _) i j) = 𝕍comp n k l i j

--  -- snd (R𝕡elim.acomp (R𝕍 n) k l i j) m = 𝕍compSi n k l m i j
--  -- fst (R𝕡elim.ainvol (R𝕍 n) k i j) = 𝕍invol n (fst k) i j
--  -- snd (R𝕡elim.ainvol (R𝕍 n) k i j) = {!!}
--  -- R𝕡elim.acomm (R𝕍 n) = {!!}
--  -- R𝕡elim.abraid (R𝕍 n) = {!!}


sucF'-fst : ∀ n k k< → PathP (λ i → ua (adjT'≃ {n = n} (k , k<)) i → ℕ)
                  (fst ∘ fst (adjT'≃ {suc n} (suc k , k<)) ∘ sucF)
                  (suc ∘ fst)
sucF'-fst n k k< i x = suc (fst (unglue (i ∨ ~ i) x))

sucF'-snd : ∀ n k k< → PathP (λ i → (x : ua (adjT'≃ {n = n} (k , k<)) i) →
                                (sucF'-fst n k k< i x) ≤ n)
                 (λ x → adjT< (suc n) (suc k) (fst (sucF {n = n} x))
                         k< (snd (sucF {n = n} x)))
                 λ x → snd x
sucF'-snd n k k< =
  isProp→PathP (λ i → isPropΠ λ x → isProp≤ {m = sucF'-fst n k k< i x} {n = n})
    (λ x → adjT< (suc n) (suc k) (suc (fst x)) k< (snd x)) snd

sucF' : ∀ n k k< → PathP (λ i → ua (adjT'≃ {n = n} (k , k<)) i → Fin (suc n))
                  (fst (adjT'≃ {suc n} (suc k , k<)) ∘ sucF)
                  sucF
sucF' n k k< i x =
  sucF'-fst n k k< i x ,
   sucF'-snd n k k< i x


-- module _ {A : Type ℓ} where

 
--  swap-01-× : ∀ {n} → (A ×^ n) → (A ×^ n)
--  swap-01-× {zero} = idfun _
--  swap-01-× {suc zero} = idfun _
--  swap-01-× {suc (suc n)} = swap-01

--  invo-swap-01-× : ∀ n → isInvolution (swap-01-× {n})
--  invo-swap-01-× zero x = refl
--  invo-swap-01-× (suc zero) x = refl
--  invo-swap-01-× (suc (suc n)) x = refl

--  adjT×^ : ∀ {n} → ℕ →
--               (A ×^ n) → (A ×^ n)
--  adjT×^ zero = swap-01-×
--  adjT×^ {suc n} (suc k) (x , xs) = x , (adjT×^ k xs)
--  adjT×^ {zero} (suc k) = idfun _
 
--  isEquiv-adjT×^ : ∀ n k → isEquiv (adjT×^ {n} k)
--  isEquiv-adjT×^ (suc n) (suc k) =
--    snd (≃-× (_ , idIsEquiv _) (_ , isEquiv-adjT×^ n k))
--  isEquiv-adjT×^ zero zero = idIsEquiv _
--  isEquiv-adjT×^ (suc zero) zero = idIsEquiv _
--  isEquiv-adjT×^ (suc (suc n)) zero = snd Σ-swap-01-≃
--  isEquiv-adjT×^ zero (suc k) = idIsEquiv _

--  adjT×^≃ : ∀ {n} → ℕ → (A ×^ n) ≃ (A ×^ n)
--  adjT×^≃ k = adjT×^ k , isEquiv-adjT×^ _ k

--  isInvo-adjT×^ : ∀ {n} → ∀ k → isInvolution (adjT×^ {n} k)
--  isInvo-adjT×^ zero = invo-swap-01-× _
--  isInvo-adjT×^ {zero} (suc k) _ = refl
--  isInvo-adjT×^ {suc n} (suc k) (x , xs) =
--    cong′ (x ,_) (isInvo-adjT×^ {n} k xs)

--  braid-adjT×^ : ∀ {n} → ∀ k →  suc (suc k) < n → ∀ v → 
--    (adjT×^  {n} k ∘ adjT×^  {n} (suc k) ∘ adjT×^  {n} (k)) v
--    ≡ (adjT×^  {n} (suc k) ∘ adjT×^  {n} (k) ∘ adjT×^  {n} (suc k)) v
--  braid-adjT×^ {suc n} (suc k) x (v , vs) = cong′ (v ,_) (braid-adjT×^ {n} k x vs)
--  braid-adjT×^ {suc (suc (suc n))} zero x v = refl
 

--  comm-adjT×^ : ∀ {n} → ∀ k l → (k< : (suc k) < n) (l< : (suc l) < n) → 
--    A.commT k l → ∀ v →  
--    (adjT×^  {n} l
--      ∘ adjT×^  {n} k ) v
--    ≡ (adjT×^  {n} k
--      ∘ adjT×^  {n} l ) v
--  comm-adjT×^ {n = suc n} (suc k) (suc l) k< l< x (v , vs) =
--     cong (v ,_) (comm-adjT×^ {n = n} k l k< l< (A.pred-commT k l x) vs)
--  comm-adjT×^ {n = suc (suc n)} zero (suc (suc l)) k< l< x v = refl



--  tabEquiv : ∀ n → (Fin n → A) ≃ (A ×^ n)
--  tabEquiv n = isoToEquiv (invIso (Iso-×^-F→ n))

    
--  zz : ∀ n k → PathP (λ i → (ua (adjT'≃ {n} k) i → A) → (A ×^ n))
--         (adjT×^ (fst k) ∘ tabulate)
--         (tabulate)           

--  zz (suc n) (suc k , k<) i x =
--    x (glue (λ { (i = i0) → zero , tt ; (i = i1) → zero , tt }) (0 , tt)) ,
--    zz n (k , k<) i
--        (x ∘ (λ y → glue (λ { (i = i0) → sucF y ; (i = i1) → sucF y })
--          (sucF' n k k< i y)))   
--  zz (suc (suc n)) (zero , k<) i x =
--    (x (glue (λ { (i = i0) → suc zero , tt ; (i = i1) → zero , tt }) (0 , tt)) ,
--     x (glue (λ { (i = i0) → zero , tt ; (i = i1) → suc zero , tt }) (1 , tt)) ,
--    tabulate λ y → x (glue (λ { (i = i0) → sucF (sucF y)
--                              ; (i = i1) → sucF (sucF y) })
--                (sucF (sucF y))))

--  ua-adj-lawP : ∀ n k →
--        PathP (λ i → (ua (adjT'≃ {n = n} k) i → A) ≃ ua (adjT×^≃ {n = n} (fst k)) i)
--                  (tabEquiv n)
--                  (tabEquiv n)
--  ua-adj-lawP n k = ΣPathPProp isPropIsEquiv
--    λ i x → glue (λ { (i = i0) → tabulate x
--                    ; (i = i1) → tabulate x }) (zz n k i x) 

--  ua-adj-law : ∀ n k →
--    Square
--        (ua (tabEquiv n))
--        (ua (tabEquiv n))
--        (λ i → ua (adjT'≃ {n = n} k) i → A)
--        (ua (adjT×^≃ {n = n} (fst k)))
       
--  ua-adj-law n k i j =
--    Glue (ua (adjT×^≃ {n = n} (fst k)) i)
--         λ {  (j = i0) → (ua (adjT'≃ {n = n} k) i → A) , ua-adj-lawP n k i
--            ; (j = i1) → ua (adjT×^≃ {n = n} (fst k)) i , idEquiv _
--            }


-- -- -- -- --  braid-adjT×^ : ∀ {n} → ∀ k →  suc (suc k) < n → ∀ v → 
-- -- -- -- --    (adjT×^  {n} k ∘ adjT×^  {n} (suc k) ∘ adjT×^  {n} (k)) v
-- -- -- -- --    ≡ (adjT×^  {n} (suc k) ∘ adjT×^  {n} (k) ∘ adjT×^  {n} (suc k)) v
-- -- -- -- --  braid-adjT×^ {n = suc (suc (suc n))} zero x _ = refl
-- -- -- -- --  braid-adjT×^ {n = suc (suc n)} (suc k) x (v , vs) =
-- -- -- -- --    cong (v ,_) (braid-adjT×^ k x vs)

-- -- -- -- --  comm-adjT×^ : ∀ {n} → ∀ k l → (k< : (suc k) < n) (l< : (suc l) < n) → 
-- -- -- -- --    A.commT k l → ∀ v →  
-- -- -- -- --    (adjT×^  {n} l
-- -- -- -- --      ∘ adjT×^  {n} k ) v
-- -- -- -- --    ≡ (adjT×^  {n} k
-- -- -- -- --      ∘ adjT×^  {n} l ) v
-- -- -- -- --  comm-adjT×^ {n = suc (suc (suc n))} zero (suc (suc l)) k< l< x v = refl
-- -- -- -- --  comm-adjT×^ {n = suc (suc n)} (suc k) (suc (suc l)) k< l< x (v , vs) =
-- -- -- -- --     cong (v ,_) (comm-adjT×^
-- -- -- -- --      {n = suc n} k (suc l) k< l< x vs)


-- -- -- -- --  adjT×^ : ∀ {n} → ℕ →
-- -- -- -- --    Iso (A ×^ n)
-- -- -- -- --        (A ×^ n)
-- -- -- -- --  adjT×^ {n} k =
-- -- -- -- --   involIso {f = adjT×^ {n} k} (isInvo-adjT×^ {n} k)

-- -- -- -- --  adjT×^≃ : ∀ {n} → ℕ →
-- -- -- -- --        (A ×^ n) ≃ (A ×^ n)
-- -- -- -- --  adjT×^≃ {n} k =
-- -- -- -- --   involEquiv {f = adjT×^ {n} k} (isInvo-adjT×^ {n} k)



-- -- -- -- --  tabEquiv : ∀ n → (Fin n → A) ≃ (A ×^ n)
-- -- -- -- --  tabEquiv n = isoToEquiv (invIso (Iso-×^-F→ n))

-- -- -- -- --  -- zz' : ∀ n k k< → PathP (λ i → ua (adjT'≃ {n = n} (k , k<)) i →
-- -- -- -- --  --                               ua (adjT'≃ {n = suc n} (suc k , k<)) i)
-- -- -- -- --  --         sucF
-- -- -- -- --  --         sucF
-- -- -- -- --  -- zz' (suc (suc n)) k k< i x =
-- -- -- -- --  --   glue (λ { (i = i0) → sucF x ; (i = i1) → sucF x }) (sucF (unglue (i ∨ ~ i) x))
   
-- -- -- -- --  zz : ∀ n k → PathP (λ i → (ua (adjT'≃ {n} k) i → A) → (A ×^ n))
-- -- -- -- --         (adjT×^ (fst k) ∘ tabulate)
-- -- -- -- --         (tabulate)           
-- -- -- -- --  zz (suc (suc n)) (zero , k<) i x =
-- -- -- -- --    (x (glue (λ { (i = i0) → suc zero , tt ; (i = i1) → zero , tt }) (0 , tt)) ,
-- -- -- -- --     x (glue (λ { (i = i0) → zero , tt ; (i = i1) → suc zero , tt }) (1 , tt)) ,
-- -- -- -- --    tabulate λ y → x (glue (λ { (i = i0) → sucF (sucF y)
-- -- -- -- --                              ; (i = i1) → sucF (sucF y) })
-- -- -- -- --                (sucF (sucF y))) )
-- -- -- -- --  zz (suc (suc (suc n))) (suc k , k<) i x =
-- -- -- -- --    x (glue (λ { (i = i0) → zero , tt ; (i = i1) → zero , tt }) (0 , tt)) ,
-- -- -- -- --    zz (suc (suc n)) (k , k<) i
-- -- -- -- --        (x ∘ (λ y → glue (λ { (i = i0) → sucF y ; (i = i1) → sucF y })
-- -- -- -- --          (sucF (unglue (i ∨ ~ i) y))))   

-- -- -- -- --  ua-adj-lawP : ∀ n k →
-- -- -- -- --        PathP (λ i → (ua (adjT'≃ {n = n} k) i → A) ≃ ua (adjT×^≃ {n = n} (fst k)) i)
-- -- -- -- --                  (tabEquiv n)
-- -- -- -- --                  (tabEquiv n)
-- -- -- -- --  ua-adj-lawP n k = ΣPathPProp isPropIsEquiv
-- -- -- -- --    λ i x → glue (λ { (i = i0) → tabulate x
-- -- -- -- --                    ; (i = i1) → tabulate x }) (zz n k i x) 

-- -- -- -- --  ua-adj-law : ∀ n k →
-- -- -- -- --    Square
-- -- -- -- --        (ua (tabEquiv n))
-- -- -- -- --        (ua (tabEquiv n))
-- -- -- -- --        (λ i → ua (adjT'≃ {n = n} k) i → A)
-- -- -- -- --        (ua (adjT×^≃ {n = n} (fst k)))
       
-- -- -- -- --  ua-adj-law n k i j =
-- -- -- -- --    Glue (ua (adjT×^≃ {n = n} (fst k)) i)
-- -- -- -- --         λ {  (j = i0) → (ua (adjT'≃ {n = n} k) i → A) , ua-adj-lawP n k i
-- -- -- -- --            ; (j = i1) → ua (adjT×^≃ {n = n} (fst k)) i , idEquiv _
-- -- -- -- --            }

-- -- -- -- --  𝕍looop : ∀ n → (k l : ℕ) →
-- -- -- -- --     (A ×^ n) ≡ (A ×^ n)
-- -- -- -- --  𝕍looop n k l i =
-- -- -- -- --    Glue (A ×^ n)
-- -- -- -- --       λ { (i = i0) → _ , adjT×^≃ k
-- -- -- -- --         ; (i = i1) → _ , adjT×^≃ l
-- -- -- -- --          }

-- -- -- -- --  zz-oo-lem : ∀ n l l< → PathP (λ i → ua (adjT'≃ {n = suc (suc n)} (l , l<)) (~ i) →
-- -- -- -- --       Flooop (suc (suc (suc (suc n)))) (zero , tt) (suc (suc l) , l<) i)
-- -- -- -- --         (sucF ∘ sucF)
-- -- -- -- --         (sucF ∘ sucF)
-- -- -- -- --  zz-oo-lem n l l< i x =
-- -- -- -- --    glue (λ { (i = i0) → sucF (sucF x) ; (i = i1) → sucF (sucF x) })
-- -- -- -- --      (sucF (sucF (unglue (i ∨ ~ i) x)))

-- -- -- -- --  zz-oo : ∀ n k l → PathP (λ i → (Flooop n k l i → A) → (A ×^ n))
-- -- -- -- --         (adjT×^ (fst k) ∘ tabulate)
-- -- -- -- --         (adjT×^ (fst l) ∘ tabulate)
-- -- -- -- --  zz-oo (suc (suc n)) (zero , k<) (zero , l<) i x =
-- -- -- -- --    (x (glue (λ { (i = i0) → suc zero , tt ; (i = i1) → suc zero , tt }) (0 , tt)) ,
-- -- -- -- --     x (glue (λ { (i = i0) → zero , tt ; (i = i1) → zero , tt }) (1 , tt)) ,
-- -- -- -- --    tabulate λ y → x (glue (λ { (i = i0) → sucF (sucF y)
-- -- -- -- --                              ; (i = i1) → sucF (sucF y) })
-- -- -- -- --                (sucF (sucF y))) )
 
-- -- -- -- --  zz-oo (suc (suc (suc n))) (zero , k<) (suc zero , l<) i x =
-- -- -- -- --    (x (glue (λ { (i = i0) → 1 , tt ; (i = i1) → zero , tt }) (zero , tt)) ,
-- -- -- -- --      x (glue (λ { (i = i0) → zero , tt ; (i = i1) → 2 , tt }) (1 , tt)) ,
-- -- -- -- --      x (glue (λ { (i = i0) → 2 , tt ; (i = i1) → 1 , tt }) (2 , tt)) ,
-- -- -- -- --    tabulate λ y → x (glue (λ { (i = i0) → sucF (sucF (sucF y))
-- -- -- -- --                              ; (i = i1) → sucF (sucF (sucF y)) })
-- -- -- -- --                (sucF (sucF (sucF y)))) )
-- -- -- -- --  zz-oo (suc (suc (suc (suc n)))) (zero , k<) (suc (suc l) , l<) i x =
-- -- -- -- --    (x (glue (λ { (i = i0) → suc zero , tt ; (i = i1) → zero , tt }) (0 , tt)) ,
-- -- -- -- --     x (glue (λ { (i = i0) → zero , tt ; (i = i1) → suc zero , tt }) (1 , tt)) ,
-- -- -- -- --     zz (suc (suc n)) (l , l<) (~ i) (x ∘' zz-oo-lem n l l< i))
-- -- -- -- --  zz-oo (suc (suc (suc n))) (suc zero , k<) (zero , l<) i x =
-- -- -- -- --     (x (glue (λ { (i = i1) → 1 , tt ; (i = i0) → zero , tt }) (zero , tt)) ,
-- -- -- -- --      x (glue (λ { (i = i1) → zero , tt ; (i = i0) → 2 , tt }) (1 , tt)) ,
-- -- -- -- --      x (glue (λ { (i = i1) → 2 , tt ; (i = i0) → 1 , tt }) (2 , tt)) ,
-- -- -- -- --    tabulate λ y → x (glue (λ { (i = i0) → sucF (sucF (sucF y))
-- -- -- -- --                              ; (i = i1) → sucF (sucF (sucF y)) })
-- -- -- -- --                (sucF (sucF (sucF y)))) )
-- -- -- -- --  zz-oo (suc (suc (suc (suc n)))) (suc (suc k) , k<) (zero , l<) i x =
-- -- -- -- --       (x (glue (λ { (i = i1) → suc zero , tt ; (i = i0) → zero , tt }) (0 , tt)) ,
-- -- -- -- --     x (glue (λ { (i = i1) → zero , tt ; (i = i0) → suc zero , tt }) (1 , tt)) ,
-- -- -- -- --     zz (suc (suc n)) (k , k<) (i) (x ∘' zz-oo-lem n k k< (~ i)))
-- -- -- -- --  zz-oo (suc (suc (suc n))) (suc k , k<) (suc l , l<) i x =
-- -- -- -- --   x (glue (λ { (i = i0) → zero , tt ; (i = i1) → zero , tt }) (0 , tt)) ,
-- -- -- -- --    zz-oo (suc (suc n)) (k , k<) (l , l<) i
-- -- -- -- --        (x ∘ (λ y → glue (λ { (i = i0) → sucF y ; (i = i1) → sucF y })
-- -- -- -- --          (sucF (unglue (i ∨ ~ i) y))))   



-- -- -- -- --  adj-lawP-oo : ∀ n k l →
-- -- -- -- --        PathP (λ i → (Flooop n k l i → A) ≃ 𝕍looop n (fst k) (fst l) i)
-- -- -- -- --                  (tabEquiv n)
-- -- -- -- --                  (tabEquiv n)
-- -- -- -- --  adj-lawP-oo n k l = ΣPathPProp isPropIsEquiv
-- -- -- -- --    λ i x → glue (λ { (i = i0) → tabulate x
-- -- -- -- --                    ; (i = i1) → tabulate x }) (zz-oo n k l i x) 


-- -- -- -- --  𝕍looopSi : ∀ n k l → Square
-- -- -- -- --      (ua (tabEquiv n))
-- -- -- -- --      (ua (tabEquiv n))
-- -- -- -- --      (λ i → Flooop n k l i → A)
-- -- -- -- --      (𝕍looop n (fst k) (fst l))
-- -- -- -- --  𝕍looopSi n k l i j =
-- -- -- -- --     Glue (𝕍looop n (fst k) (fst l) i)
-- -- -- -- --         λ { (j = i0) → (Flooop n k l i → A) , adj-lawP-oo n k l i
-- -- -- -- --           ; (j = i1) → 𝕍looop n (fst k) (fst l) i , idEquiv _ }

-- -- -- -- --  𝕍comp : ∀ n k l → Square {A = Type ℓ}
-- -- -- -- --                  (ua (adjT×^≃ k))
-- -- -- -- --                  (ua (adjT×^≃ l))
-- -- -- -- --                  (𝕍looop n k l)
-- -- -- -- --                  refl 
-- -- -- -- --  𝕍comp n k l i j =
-- -- -- -- --   Glue (A ×^ n) {(~ i ∧ ~ j) ∨ (i ∧ ~ j) ∨ j}
-- -- -- -- --     λ {(j = i0) (i = i0) → _ , adjT×^≃ (k)
-- -- -- -- --       ;(j = i0) (i = i1) → _ , adjT×^≃ (l)
-- -- -- -- --       ;(j = i1) → _ , idEquiv _ }
      
-- -- -- -- --  postulate
-- -- -- -- --   𝕍compSi : ∀ n k l → Cube {A = Type ℓ}
-- -- -- -- --                     (λ i j → Flooop-comp n k l i j → A)
-- -- -- -- --                     (𝕍comp n (fst k) (fst l))
-- -- -- -- --                     (flipSquare (ua-adj-law n k))
-- -- -- -- --                     (flipSquare (ua-adj-law n l))
-- -- -- -- --                     (flipSquare (𝕍looopSi n k l))
-- -- -- -- --                     (λ i → refl {x = ua (tabEquiv n) i})

-- -- -- -- --   -- 𝕍compSi = {!!}

-- -- -- -- -- -- mkCube' _ _ _ _ _ _
-- -- -- -- -- --    {!!}
  
-- -- -- -- --   -- w : {!!}
-- -- -- -- --   -- w = {!!}
-- -- -- -- --    -- Glue (A ×^ n)
-- -- -- -- --    --  (λ { (i = i0) → ua-adj-law n k j m , {!!}
-- -- -- -- --    --     ; (i = i1) → ua-adj-law n l j m , {!!}
-- -- -- -- --    --     ; (j = i0) → 𝕍loopSi n k l i m , {!!}
-- -- -- -- --    --     ; (j = i1) → ua (tabEquiv n) m , {!!} --ua-unglueEquiv (tabEquiv n) m
-- -- -- -- --    --     ; (m = i0) → (𝔽in (𝕡comp {n = n} k l i j) → A) , {!!}
-- -- -- -- --    --     ; (m = i1) → 𝕍comp n (fst k) (fst l) i j ,
-- -- -- -- --    --          unglueEquiv _ ((~ i ∧ ~ j) ∨ (i ∧ ~ j) ∨ j)
-- -- -- -- --    --            (λ {(j = i0) (i = i0) → _ , adjT×^≃ (fst k)
-- -- -- -- --    --               ;(j = i0) (i = i1) → _ , adjT×^≃ (fst l)
-- -- -- -- --    --               ;(j = i1) → _ , idEquiv _ }) 
-- -- -- -- --    --     })

-- -- -- -- --  𝕍invol : ∀ n k → Square
-- -- -- -- --          (ua (adjT×^≃ {n = n} k))
-- -- -- -- --          (sym (ua (adjT×^≃ {n = n} k)))
-- -- -- -- --          refl refl
-- -- -- -- --  𝕍invol n k = involPathSym (isInvo-adjT×^ k) 

-- -- -- -- --  postulate
-- -- -- -- --   𝕍involSi : ∀ n k → Cube
-- -- -- -- --           (λ i j → involPathSym {f = adjT n k} (isInvolution-adjT n k) i j → A)
-- -- -- -- --           (𝕍invol n (fst k))
-- -- -- -- --           (flipSquare (ua-adj-law n k))
-- -- -- -- --           (λ i j → (ua-adj-law n k) (~ j) i)
-- -- -- -- --           (λ _ → refl)
-- -- -- -- --           (λ _ → refl)



-- -- -- -- --  𝕍comm-sideF : ∀ n k l 
-- -- -- -- --      → (x : A ×^ n) →
-- -- -- -- --       PathP (λ z → ua (adjT×^≃ {n = n} k ∙ₑ adjT×^≃ {n = n} l) z)
-- -- -- -- --       (fst (adjT×^≃ {n = n} k) x)
-- -- -- -- --       (fst (adjT×^≃ {n = n} l) x)
-- -- -- -- --  𝕍comm-sideF n k l x =
-- -- -- -- --     ua-gluePath ((adjT×^≃ {n = n} k ∙ₑ adjT×^≃ {n = n} l))
-- -- -- -- --      (cong (adjT×^ l) (isInvo-adjT×^ {n} k x))

-- -- -- -- --  𝕍comm-side : ∀ n k l 
-- -- -- -- --     → PathP (λ i →  (A ×^ n) ≃ ua (adjT×^≃ {n = n} k ∙ₑ adjT×^≃ {n = n} l) i)
-- -- -- -- --         (adjT×^≃ {n = n} k)
-- -- -- -- --         (adjT×^≃ {n = n} l)
-- -- -- -- --  𝕍comm-side n k l =
-- -- -- -- --    ΣPathPProp
-- -- -- -- --    isPropIsEquiv (funExt (𝕍comm-sideF n k l))

-- -- -- -- --  𝕍comm : ∀ n k l (k< : (suc k) < n) (l< : (suc l) < n) → (x : A.commT k l)
-- -- -- -- --      → 𝕍looop n k l ≡ 𝕍looop n l k
-- -- -- -- --  𝕍comm n k l k< l< x i j =
-- -- -- -- --    Glue (ua (equivEq
-- -- -- -- --                 {e = (adjT×^≃ {n = n} k) ∙ₑ (adjT×^≃ {n = n} l)}
-- -- -- -- --                 {f = (adjT×^≃ {n = n} l) ∙ₑ (adjT×^≃ {n = n} k)}
-- -- -- -- --                 (funExt (comm-adjT×^ {n} k l k< l< x)) j) i)
-- -- -- -- --         λ { (j = i0) → (A ×^ n) , 𝕍comm-side n k l i
-- -- -- -- --           ; (j = i1) → (A ×^ n) , 𝕍comm-side n l k i }

-- -- -- -- --  postulate
-- -- -- -- --   𝕍commSi : ∀ n k l (k< : (suc k) < n) (l< : (suc l) < n) → (x : A.commT k l)
-- -- -- -- --           →  Cube
-- -- -- -- --           (λ i j → Flooop-comm n (k , k<) (l , l<) x i j → A)
-- -- -- -- --           (𝕍comm n k l k< l< x)
-- -- -- -- --           (flipSquare (𝕍looopSi n (k , k<) (l , l<)))
-- -- -- -- --           (flipSquare (𝕍looopSi n (l , l<) (k , k<)))
-- -- -- -- --           (λ _ → refl)
-- -- -- -- --           (λ _ → refl)
          


-- -- -- -- --  𝕍braid-side-f : ∀ n k l →
-- -- -- -- --    PathP (λ j → ua (adjT×^≃ {n = n} l) j →
-- -- -- -- --      ua (adjT×^≃ {n = n} k ∙ₑ adjT×^≃ l ∙ₑ adjT×^≃ k) j)
-- -- -- -- --      (fst (adjT×^≃ k))
-- -- -- -- --      (fst (adjT×^≃ k))
-- -- -- -- --  𝕍braid-side-f n k l =
-- -- -- -- --     λ i x → glue (λ { (i = i0) → adjT×^ k x
-- -- -- -- --                     ; (i = i1) → adjT×^ {n = n} k x
-- -- -- -- --            })
-- -- -- -- --     (zzzz i x)
-- -- -- -- --   where
-- -- -- -- --    zzzz : PathP (λ j → ua (adjT×^≃ {n = n} l) j → A ×^ n)
-- -- -- -- --            (fst (adjT×^≃ {n = n} k ∙ₑ adjT×^≃ {n = n} k ∙ₑ
-- -- -- -- --                     adjT×^≃ l ∙ₑ adjT×^≃ k)
-- -- -- -- --                    ) (adjT×^ {n = n} k)
-- -- -- -- --    zzzz = 
-- -- -- -- --       funExt (λ x → cong ((adjT×^ k ∘ (adjT×^ l)))
-- -- -- -- --         (isInvo-adjT×^ {n} k x)) ◁ (λ j → fst (adjT×^≃ k)
-- -- -- -- --     ∘ ua-ungluePathExt (adjT×^≃ {n = n} l) j)
      
     

-- -- -- -- --  𝕍braid-side : ∀ n k l →
-- -- -- -- --    PathP (λ j → ua (adjT×^≃ {n = n} l) j ≃
-- -- -- -- --         ua (adjT×^≃ {n = n} k ∙ₑ adjT×^≃ l ∙ₑ adjT×^≃ k) j)
-- -- -- -- --      (adjT×^≃ k)
-- -- -- -- --      (adjT×^≃ k)
-- -- -- -- --  𝕍braid-side n k l = ΣPathPProp
-- -- -- -- --    isPropIsEquiv (𝕍braid-side-f n k l)
 
-- -- -- -- --  𝕍braid : ∀ n k (k< : (suc (suc k)) < n) 
-- -- -- -- --      → Square
-- -- -- -- --           (ua (adjT×^≃ {n = n} (suc k)))
-- -- -- -- --           (ua (adjT×^≃ {n = n} k))
-- -- -- -- --           (𝕍looop n k (suc k))
-- -- -- -- --           (𝕍looop n k (suc k))
-- -- -- -- --  𝕍braid n k k< i j =
-- -- -- -- --     Glue (ua (equivEq
-- -- -- -- --            {e = adjT×^≃ {n = n} k ∙ₑ adjT×^≃ (suc k) ∙ₑ adjT×^≃ k}
-- -- -- -- --            {f = adjT×^≃ {n = n} (suc k) ∙ₑ adjT×^≃ k ∙ₑ adjT×^≃ (suc k) }
-- -- -- -- --              (funExt (braid-adjT×^ {n} k k<)) i) j)
-- -- -- -- --       λ { (i = i0) → ua (adjT×^≃ {n = n} (suc k)) j
-- -- -- -- --           , 𝕍braid-side n k (suc k) j
-- -- -- -- --         ; (i = i1) → ua (adjT×^≃ {n = n} k) j
-- -- -- -- --           , 𝕍braid-side n (suc k) k j 
-- -- -- -- --          }

-- -- -- -- --  postulate
-- -- -- -- --   𝕍braidSi : ∀ n k (k< : (suc (suc k)) < n) 
-- -- -- -- --           → Cube
-- -- -- -- --           (λ i j → 𝔽in {n = n} (𝕡braid k k< i j) → A)
-- -- -- -- --           (𝕍braid n k k<)
-- -- -- -- --           (flipSquare (ua-adj-law n (suc k , k<)))
-- -- -- -- --           (flipSquare (ua-adj-law n (k , <-weaken {n = n} k<) ))
-- -- -- -- --           (flipSquare (𝕍looopSi n (k , <-weaken {n = n} k<) (suc k , k<)))
-- -- -- -- --           (flipSquare (𝕍looopSi n (k , <-weaken {n = n} k<) (suc k , k<)))
          

-- -- -- -- --  -- 𝕍braid (suc (suc (suc n))) zero k< = {!!}
-- -- -- -- --  -- 𝕍braid (suc (suc n)) (suc k) k< = 
-- -- -- -- --  --   comm→PathP (isInjectiveTransport
-- -- -- -- --  --        (funExt λ a → ΣPathP (refl , {!!})))

-- -- -- -- --   -- ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- --   --   (comm→PathP (isInjectiveTransport
-- -- -- -- --   --     (funExt λ x → ≡Fin {n = n}
-- -- -- -- --   --       (funExt⁻ (A.adjTranspositionBraid k ) (fst x) ))))

-- -- -- -- --  R𝕍 : ∀ n → R𝕡elim {n = n} λ p → singl (𝔽in p → A)
-- -- -- -- --  R𝕡elim.isGroupoidA (R𝕍 n) p =
-- -- -- -- --     isOfHLevelPlus 3 (isContrSingl _)
-- -- -- -- --  R𝕡elim.abase (R𝕍 n) = (A ×^ n) , ua (tabEquiv n)
-- -- -- -- --  R𝕡elim.aloop (R𝕍 n) k = ΣPathP (ua (adjT×^≃ (fst k)) , ua-adj-law n k)
-- -- -- -- --  R𝕡elim.alooop (R𝕍 n) k l = ΣPathP (𝕍looop n (fst k) (fst l) , 𝕍looopSi n k l )
-- -- -- -- --  fst (R𝕡elim.acomp (R𝕍 n) (k , _) (l , _) i j) = 𝕍comp n k l i j

-- -- -- -- --  snd (R𝕡elim.acomp (R𝕍 n) k l i j) m = 𝕍compSi n k l m i j
-- -- -- -- --  fst (R𝕡elim.ainvol (R𝕍 n) k i j) = 𝕍invol n (fst k) i j
-- -- -- -- --  snd (R𝕡elim.ainvol (R𝕍 n) k i j) m = 𝕍involSi n k m i j
-- -- -- -- --  fst (R𝕡elim.acomm (R𝕍 n) k l x i j) =
-- -- -- -- --     𝕍comm n (fst k) (fst l) (snd k) (snd l) x j i
-- -- -- -- --  snd (R𝕡elim.acomm (R𝕍 n) k l x i j) m =
-- -- -- -- --    𝕍commSi n (fst k) (fst l) (snd k) (snd l) x m j i
-- -- -- -- --  fst (R𝕡elim.abraid (R𝕍 n) k k< i j) = 𝕍braid n k k< i j
-- -- -- -- --  snd (R𝕡elim.abraid (R𝕍 n) k k< i j) m = 𝕍braidSi n k k< m i j

-- -- -- -- --  𝕍 : ∀ n → ℙrm n → Type ℓ
-- -- -- -- --  𝕍 n = fst ∘ R𝕡elim.f (R𝕍 n) 


-- -- -- -- --  shp : (xs : FMSet2 A) → ℙrm _
-- -- -- -- --  shp xs = snd (fromFM2⊤ (fm2Map (λ _ → tt) xs))

-- -- -- -- --  𝕍' : FMSet2 A → Type ℓ
-- -- -- -- --  𝕍' xs = uncurry 𝕍 (fromFM2⊤ (fm2Map (λ _ → tt) xs) ) 



-- -- -- -- --  ∷𝕍R : ∀ n → A → R𝕡elim {n = n} λ (p : ℙrm n) → 𝕍 n p → 𝕍 (suc n) (sucℙrm n p) 
-- -- -- -- --  R𝕡elim.isGroupoidA (∷𝕍R n a) = {!!}
-- -- -- -- --  R𝕡elim.abase (∷𝕍R n a) = a ,_
-- -- -- -- --  R𝕡elim.aloop (∷𝕍R (suc (suc n)) a) (k , k<) i x =
-- -- -- -- --    ua-glue (adjT×^≃ {n = 3 + n} (suc k)) i (λ { (i = i0) → a , x })
-- -- -- -- --     (inS (a , ua-unglue (adjT×^≃ {n = 2 + n} k) i x))
-- -- -- -- --  R𝕡elim.alooop (∷𝕍R (suc n) a) k l i x =
-- -- -- -- --     glue (λ { (i = i0) → a , x
-- -- -- -- --             ; (i = i1) → a , x
-- -- -- -- --             }) (a , unglue (i ∨ ~ i) x) 
-- -- -- -- --  R𝕡elim.acomp (∷𝕍R (suc (suc n)) a) k l i j x =
-- -- -- -- --     glue (λ { (i = i0) (j = i0) → a , x
-- -- -- -- --             ; (i = i1) (j = i0) → a , x
-- -- -- -- --             ; (j = i1) → a , x
-- -- -- -- --             }) (a , unglue ((i ∧ ~ j) ∨ (~ i ∧ ~ j) ∨ j) x)
-- -- -- -- --  R𝕡elim.ainvol (∷𝕍R n a) = {!!}
-- -- -- -- --  R𝕡elim.acomm (∷𝕍R n a) = {!!}
-- -- -- -- --  R𝕡elim.abraid (∷𝕍R n a) = {!!}

-- -- -- -- --  ∷𝕍 : ∀ n → A → (p : ℙrm n) → 𝕍 n p → 𝕍 (suc n) (sucℙrm n p) 
-- -- -- -- --  ∷𝕍 n a = R𝕡elim.f (∷𝕍R n a)

-- -- -- -- --  module _ (isGroupoidA : isGroupoid A) where

-- -- -- -- --   FMto𝕍'R : RElim 𝕍'
-- -- -- -- --   RElim.[]* FMto𝕍'R = tt*
-- -- -- -- --   RElim._∷*_ FMto𝕍'R a {xs} = ∷𝕍 _ a (shp xs) 
-- -- -- -- --   RElim.comm* FMto𝕍'R x y b = {!!}
-- -- -- -- --   RElim.comm-inv* FMto𝕍'R = {!!}
-- -- -- -- --   RElim.hexDiag* FMto𝕍'R = {!!}
-- -- -- -- --   RElim.hexU* FMto𝕍'R = {!!}
-- -- -- -- --   RElim.hexL* FMto𝕍'R = {!!}
-- -- -- -- --   RElim.trunc* FMto𝕍'R = {!!}

-- -- -- -- --   FMto𝕍 : (xs : FMSet2 A) → 𝕍' xs 
-- -- -- -- --   FMto𝕍 = {!!}


-- -- -- -- -- -- -- fromℙrm n 𝕡base = embase
-- -- -- -- -- -- -- fromℙrm n (𝕡loop x i) = emloop (η x) i
-- -- -- -- -- -- -- fromℙrm n (𝕡looop k l i) = emloop (η k · η l) i
-- -- -- -- -- -- -- fromℙrm n (𝕡comp k l i j) =
-- -- -- -- -- -- --     hcomp (λ l' → λ {
-- -- -- -- -- -- --        (i = i0) → {!!} --emloop (η k) j
-- -- -- -- -- -- --       ;(i = i1) → emloop (η l) (l' ∧ j)
-- -- -- -- -- -- --       ;(j = i0) → embase 
-- -- -- -- -- -- --       ;(j = i1) → emcomp (η k) (η l) l' i 
-- -- -- -- -- -- --       }) (emloop (η k) (i ∨ ~ j))


-- -- -- -- -- -- -- -- i = i0 ⊢ emloop (η k) j
-- -- -- -- -- -- -- -- i = i1 ⊢ emloop (η l) j
-- -- -- -- -- -- -- -- j = i0 ⊢ embase
-- -- -- -- -- -- -- -- j = i1 ⊢ emloop (k ∷ η l) i

-- -- -- -- -- -- -- fromℙrm n (𝕡comp' k l i j) =
-- -- -- -- -- -- --       hcomp (λ l' → λ {
-- -- -- -- -- -- --        (i = i0) → {!emloop (η k) (l' ∧ j)!} --emloop (η k) j
-- -- -- -- -- -- --       ;(i = i1) → {!emloop (η l) (l' ∨ j) !}
-- -- -- -- -- -- --       ;(j = i0) → emcomp (η k) (η l) l' i  
-- -- -- -- -- -- --       ;(j = i1) → embase
-- -- -- -- -- -- --       }) {!!}


-- -- -- -- -- -- -- -- i = i0 ⊢ emloop (η k) j
-- -- -- -- -- -- -- -- i = i1 ⊢ emloop (η l) j
-- -- -- -- -- -- -- -- j = i0 ⊢ emloop (k ∷ η l) i
-- -- -- -- -- -- -- -- j = i1 ⊢ embase

-- -- -- -- -- -- -- fromℙrm n (𝕡invol k i j) = 
-- -- -- -- -- -- --   hcomp (λ l → λ {
-- -- -- -- -- -- --        (i = i0) → emcomp (η k) (η k) j l
-- -- -- -- -- -- --       ;(i = i1) → emcomp ε (η k) (~ j) l
-- -- -- -- -- -- --       ;(j = i0) → emloop (k ∷ ε) l
-- -- -- -- -- -- --       ;(j = i1) → emloop ((invo k ε) i) l
-- -- -- -- -- -- --       }) embase

-- -- -- -- -- -- -- fromℙrm n (𝕡comm k l x i i₁) = emloop (comm k l x ε i₁) i
-- -- -- -- -- -- -- fromℙrm n (𝕡braid k k< i i₁) = {!!}
-- -- -- -- -- -- -- fromℙrm n (𝕡squash _ _ _ _ r s i i₁ i₂) =
-- -- -- -- -- -- --   emsquash _ _ _ _
-- -- -- -- -- -- --     (λ i j → fromℙrm n (r i j))
-- -- -- -- -- -- --     (λ i j → fromℙrm n (s i j))
-- -- -- -- -- -- --      i i₁ i₂

-- -- -- -- -- -- -- -- -- -- -- infixr 30 _ₑ∙ₚ_

-- -- -- -- -- -- -- -- -- -- -- _ₑ∙ₚ_ : ∀ {ℓ} {A B C : Type ℓ} → A ≃ B → B ≡ C → A ≡ C 
-- -- -- -- -- -- -- -- -- -- -- (e ₑ∙ₚ p) i = Glue (p i) 
-- -- -- -- -- -- -- -- -- -- --     λ { (i = i0) → _ , e
-- -- -- -- -- -- -- -- -- -- --       ; (i = i1) → _ , idEquiv _
-- -- -- -- -- -- -- -- -- -- --       }

-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-ua : ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) → (p : B ≡ C) →
-- -- -- -- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- -- -- -- --              (ua e)
-- -- -- -- -- -- -- -- -- -- --              (e ₑ∙ₚ p)             
-- -- -- -- -- -- -- -- -- -- --              refl
-- -- -- -- -- -- -- -- -- -- --              p
-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-ua  e p j i =
-- -- -- -- -- -- -- -- -- -- --   Glue (p (j ∧ i) ) 
-- -- -- -- -- -- -- -- -- -- --     λ { (i = i0) → A , e 
-- -- -- -- -- -- -- -- -- -- --       ; (i = i1) → p j , idEquiv (p j)
-- -- -- -- -- -- -- -- -- -- --       }

-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-fill : ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) → (p : B ≡ C) →
-- -- -- -- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- -- -- -- --              (e ₑ∙ₚ p)
-- -- -- -- -- -- -- -- -- -- --              p
-- -- -- -- -- -- -- -- -- -- --              (ua e)
-- -- -- -- -- -- -- -- -- -- --              refl
-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-fill  e p j i =
-- -- -- -- -- -- -- -- -- -- --     Glue
-- -- -- -- -- -- -- -- -- -- --        (p i)
-- -- -- -- -- -- -- -- -- -- --        λ { (j = i0)(i = i0) → _ , e
-- -- -- -- -- -- -- -- -- -- --           ; (i = i1) → _ , idEquiv (p i1)
-- -- -- -- -- -- -- -- -- -- --           ; (j = i1) → _ , idEquiv (p i)
-- -- -- -- -- -- -- -- -- -- --           }
  
-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-compSq :  ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) → (f : B ≃ C)
-- -- -- -- -- -- -- -- -- -- --             → PathP (λ j → A ≃ ua f j)
-- -- -- -- -- -- -- -- -- -- --                    e
-- -- -- -- -- -- -- -- -- -- --                   (e ∙ₑ f)
-- -- -- -- -- -- -- -- -- -- -- fst (ₑ∙ₚ-compSq e f j) = ua-gluePathExt f j ∘ fst e
-- -- -- -- -- -- -- -- -- -- -- snd (ₑ∙ₚ-compSq e f j) = isProp→PathP (λ j → isPropIsEquiv (ua-gluePathExt f j ∘ fst e))
-- -- -- -- -- -- -- -- -- -- --     (snd e) (snd (e ∙ₑ f)) j

-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp :  ∀ {ℓ} {A B C D : Type ℓ} → (e : A ≃ B) → (f : B ≃ C) → (p : C ≡ D) →
-- -- -- -- -- -- -- -- -- -- --                   e ₑ∙ₚ f ₑ∙ₚ p ≡ (e ∙ₑ f) ₑ∙ₚ p  
-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp  {B} {C} {D} e f p j i =
-- -- -- -- -- -- -- -- -- -- --    Glue (ₑ∙ₚ-fill f p j i) 
-- -- -- -- -- -- -- -- -- -- --     λ { (i = i0) → A , ₑ∙ₚ-compSq e f j
-- -- -- -- -- -- -- -- -- -- --       ; (i = i1) → D , idEquiv D
-- -- -- -- -- -- -- -- -- -- --       }


-- -- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp³eq-fill :  ∀ {ℓ} {A B : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- --             → (e : A ≃ A) → (f : A ≃ A) → (p : A ≡ B)
-- -- -- -- -- -- -- -- -- -- -- --             → e ∙ₑ f ∙ₑ e ≡ f ∙ₑ e ∙ₑ f 
-- -- -- -- -- -- -- -- -- -- -- --             → Square (f ₑ∙ₚ e ₑ∙ₚ p)
-- -- -- -- -- -- -- -- -- -- -- --                       (e ₑ∙ₚ f ₑ∙ₚ p)
-- -- -- -- -- -- -- -- -- -- -- --                       {!ua!}
-- -- -- -- -- -- -- -- -- -- -- --                       {!!}
            
-- -- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp³eq-fill = {!!}


-- -- -- -- -- -- -- -- -- -- -- unglue-ₑ∙p : ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) → (X : B ≡ C)
-- -- -- -- -- -- -- -- -- -- --                 → PathP (λ i → (e ₑ∙ₚ X) i ≃ X i) e (idEquiv _) 
-- -- -- -- -- -- -- -- -- -- -- unglue-ₑ∙p e X =
-- -- -- -- -- -- -- -- -- -- --   ΣPathPProp (λ _ → isPropIsEquiv _)
-- -- -- -- -- -- -- -- -- -- --    λ i x → unglue (i ∨ ~ i) x 

-- -- -- -- -- -- -- -- -- -- -- glue-ₑ∙p-comp : ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) (f : B ≃ C) 
-- -- -- -- -- -- -- -- -- -- --                 → PathP (λ i → A → (e ₑ∙ₚ (f ₑ∙ₚ refl)) i) (idfun _)
-- -- -- -- -- -- -- -- -- -- --                     (fst  (e ∙ₑ f)) 
-- -- -- -- -- -- -- -- -- -- -- glue-ₑ∙p-comp e f i x =
-- -- -- -- -- -- -- -- -- -- --   glue (λ { (i = i0) → x
-- -- -- -- -- -- -- -- -- -- --            ; (i = i1) → fst (e ∙ₑ f) x }  )
-- -- -- -- -- -- -- -- -- -- --               (glue (λ { (i = i0) → fst e x
-- -- -- -- -- -- -- -- -- -- --                         ; (i = i1) → fst (e ∙ₑ f) x }  ) (fst (e ∙ₑ f) x))


-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp²eq-sides :
-- -- -- -- -- -- -- -- -- -- --    ∀ {ℓ} {A B : Type ℓ}
-- -- -- -- -- -- -- -- -- -- --             → (e : A ≃ A) → (f : A ≃ A) → (p : A ≡ B) 
-- -- -- -- -- -- -- -- -- -- --             → f ∙ₑ e ≡ e ∙ₑ f → ∀ j i
-- -- -- -- -- -- -- -- -- -- --             → Partial (j ∨ ~ j ∨ i ∨ ~ i) (Σ (Type ℓ) (λ T → T ≃ p i))
-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp²eq-sides  {B} e f p x j i =
-- -- -- -- -- -- -- -- -- -- --       λ {
-- -- -- -- -- -- -- -- -- -- --         (i = i0) → A , x j
-- -- -- -- -- -- -- -- -- -- --       ; (i = i1) → B , (idEquiv B ∙ₑ idEquiv B)
-- -- -- -- -- -- -- -- -- -- --       ; (j = i0) → (f ₑ∙ₚ e ₑ∙ₚ p) i ,
-- -- -- -- -- -- -- -- -- -- --               unglue-ₑ∙p f (e ₑ∙ₚ p) i
-- -- -- -- -- -- -- -- -- -- --             ∙ₑ unglue-ₑ∙p e p i
-- -- -- -- -- -- -- -- -- -- --       ; (j = i1) → ( e ₑ∙ₚ f ₑ∙ₚ p) i ,
-- -- -- -- -- -- -- -- -- -- --             unglue-ₑ∙p e (f ₑ∙ₚ p) i
-- -- -- -- -- -- -- -- -- -- --             ∙ₑ unglue-ₑ∙p f p i
-- -- -- -- -- -- -- -- -- -- --       }


-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp²eq :  ∀ {ℓ} {A B : Type ℓ}
-- -- -- -- -- -- -- -- -- -- --             → (e : A ≃ A) → (f : A ≃ A) → (p : A ≡ B) 
-- -- -- -- -- -- -- -- -- -- --             → f ∙ₑ e ≡ e ∙ₑ f 
-- -- -- -- -- -- -- -- -- -- --             →  f ₑ∙ₚ e ₑ∙ₚ p ≡ e ₑ∙ₚ f ₑ∙ₚ p  
-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp²eq  {B} e f p x j i =
-- -- -- -- -- -- -- -- -- -- --    Glue (p i) (ₑ∙ₚ-comp²eq-sides e f p x j i)


-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp³eq-sides :
-- -- -- -- -- -- -- -- -- -- --    ∀ {ℓ} {A B : Type ℓ}
-- -- -- -- -- -- -- -- -- -- --             → (e : A ≃ A) → (f : A ≃ A) → (p : A ≡ B) 
-- -- -- -- -- -- -- -- -- -- --             → e ∙ₑ f ∙ₑ e ≡ f ∙ₑ e ∙ₑ f  → ∀ j i
-- -- -- -- -- -- -- -- -- -- --             → Partial (j ∨ ~ j ∨ i ∨ ~ i) (Σ (Type ℓ) (λ T → T ≃ p i))
-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp³eq-sides  {B} e f p x j i =
-- -- -- -- -- -- -- -- -- -- --       λ {
-- -- -- -- -- -- -- -- -- -- --         (i = i0) → A , x j
-- -- -- -- -- -- -- -- -- -- --       ; (i = i1) → B , compEquiv (idEquiv B) (idEquiv B ∙ₑ idEquiv B)
-- -- -- -- -- -- -- -- -- -- --       ; (j = i0) → ( e ₑ∙ₚ f ₑ∙ₚ e ₑ∙ₚ p) i ,
-- -- -- -- -- -- -- -- -- -- --               unglue-ₑ∙p e (f ₑ∙ₚ e ₑ∙ₚ p) i
-- -- -- -- -- -- -- -- -- -- --             ∙ₑ unglue-ₑ∙p f (e ₑ∙ₚ p) i
-- -- -- -- -- -- -- -- -- -- --             ∙ₑ unglue-ₑ∙p e p i
-- -- -- -- -- -- -- -- -- -- --       ; (j = i1) → ( f ₑ∙ₚ e ₑ∙ₚ f ₑ∙ₚ p) i ,
-- -- -- -- -- -- -- -- -- -- --             unglue-ₑ∙p f (e ₑ∙ₚ f ₑ∙ₚ p) i
-- -- -- -- -- -- -- -- -- -- --             ∙ₑ unglue-ₑ∙p e (f ₑ∙ₚ p) i
-- -- -- -- -- -- -- -- -- -- --             ∙ₑ unglue-ₑ∙p f p i
-- -- -- -- -- -- -- -- -- -- --       }


-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp³eq :  ∀ {ℓ} {A B : Type ℓ}
-- -- -- -- -- -- -- -- -- -- --             → (e : A ≃ A) → (f : A ≃ A) → (p : A ≡ B) 
-- -- -- -- -- -- -- -- -- -- --             → e ∙ₑ f ∙ₑ e ≡ f ∙ₑ e ∙ₑ f 
-- -- -- -- -- -- -- -- -- -- --             →  e ₑ∙ₚ f ₑ∙ₚ e ₑ∙ₚ p ≡ f ₑ∙ₚ e ₑ∙ₚ f ₑ∙ₚ p  
-- -- -- -- -- -- -- -- -- -- -- ₑ∙ₚ-comp³eq  {B} e f p x j i =
-- -- -- -- -- -- -- -- -- -- --    Glue (p i)
-- -- -- -- -- -- -- -- -- -- --      (ₑ∙ₚ-comp³eq-sides  {B} e f p x j i)




-- -- -- -- -- -- -- -- -- -- -- -- glue-invol-ₑ∙ₚ : ∀ {ℓ} {A B : Type ℓ} → (f : A → A) →
-- -- -- -- -- -- -- -- -- -- -- --     (fInvol : isInvolution f)  → (X : A ≡ B)
-- -- -- -- -- -- -- -- -- -- -- --         → PathP (λ i → X i ≃ (involEquiv {f = f} fInvol ₑ∙ₚ X) i)
           
-- -- -- -- -- -- -- -- -- -- -- --            (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- -- --            (idEquiv _)
-- -- -- -- -- -- -- -- -- -- -- -- glue-invol-ₑ∙ₚ f fInvol X =
-- -- -- -- -- -- -- -- -- -- -- --    ΣPathP ( ({!!} ◁
-- -- -- -- -- -- -- -- -- -- -- --               λ i → λ x → glue (λ {(i = i0) → f x ; (i = i1) → x })
-- -- -- -- -- -- -- -- -- -- -- --                 {!x!})
-- -- -- -- -- -- -- -- -- -- -- --     , {!!})
-- -- -- -- -- -- -- -- -- -- --   -- e' i ,
-- -- -- -- -- -- -- -- -- -- --   --        isProp→PathP (λ i → isPropIsEquiv (e' i))
-- -- -- -- -- -- -- -- -- -- --   --          (snd e)
-- -- -- -- -- -- -- -- -- -- --   --          (idIsEquiv _) i


-- -- -- -- -- -- -- -- -- -- -- glue-invol-ₑ∙p : ∀ {ℓ} {A B : Type ℓ} → (e : A ≃ A) →
-- -- -- -- -- -- -- -- -- -- --     (fInvol : isInvolution (fst e))  → (X : A ≡ B)
-- -- -- -- -- -- -- -- -- -- --         → PathP (λ i → X i ≃ (e ₑ∙ₚ X) i) e (idEquiv _)
-- -- -- -- -- -- -- -- -- -- -- glue-invol-ₑ∙p e eInvol X i =
-- -- -- -- -- -- -- -- -- -- --   e' i ,
-- -- -- -- -- -- -- -- -- -- --          isProp→PathP (λ i → isPropIsEquiv (e' i))
-- -- -- -- -- -- -- -- -- -- --            (snd e)
-- -- -- -- -- -- -- -- -- -- --            (idIsEquiv _) i

-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --     e' : ∀ i → X i → (e ₑ∙ₚ X) i
-- -- -- -- -- -- -- -- -- -- --     e' i = (λ x → glue (λ { (i = i0) → _
-- -- -- -- -- -- -- -- -- -- --           ; (i = i1) → _ })
-- -- -- -- -- -- -- -- -- -- --        (hcomp (λ k → λ {(i = i0) → eInvol x (~ k)
-- -- -- -- -- -- -- -- -- -- --                        ;(i = i1) → x
-- -- -- -- -- -- -- -- -- -- --             }) x))




-- -- -- -- -- -- -- -- -- -- -- invol-ₑ∙pSides : ∀ {ℓ} {A B : Type ℓ} → (e : A ≃ A) →
-- -- -- -- -- -- -- -- -- -- --     (fInvol : isInvolution (fst e))  → (X : A ≡ B)
-- -- -- -- -- -- -- -- -- -- --                 → ∀ j i → Partial (j ∨ ~ j ∨ i ∨ ~ i)
-- -- -- -- -- -- -- -- -- -- --                  (Σ (Type ℓ) (λ T → T ≃ X i))
-- -- -- -- -- -- -- -- -- -- -- invol-ₑ∙pSides  {B = B} e eInvol X j i =
-- -- -- -- -- -- -- -- -- -- --          (λ { (i = i0) → A ,
-- -- -- -- -- -- -- -- -- -- --                 equivEq {e = e ∙ₑ e} {f = idEquiv _} (funExt eInvol) j

-- -- -- -- -- -- -- -- -- -- --           ; (i = i1) → B , equivEq
-- -- -- -- -- -- -- -- -- -- --                {e = idEquiv _ ∙ₑ idEquiv _}
-- -- -- -- -- -- -- -- -- -- --                {f = idEquiv _} refl j
-- -- -- -- -- -- -- -- -- -- --           ; (j = i0) → _ ,
-- -- -- -- -- -- -- -- -- -- --              (unglue-ₑ∙p e (e ₑ∙ₚ X) i) ∙ₑ (unglue-ₑ∙p e X i)

-- -- -- -- -- -- -- -- -- -- --           ; (j = i1) → X i , idEquiv _
-- -- -- -- -- -- -- -- -- -- --           })


-- -- -- -- -- -- -- -- -- -- -- invol-ₑ∙p : ∀ {ℓ} {A B : Type ℓ} → (e : A ≃ A) →
-- -- -- -- -- -- -- -- -- -- --     (fInvol : isInvolution (fst e))  → (X : A ≡ B)
-- -- -- -- -- -- -- -- -- -- --                 → Square
-- -- -- -- -- -- -- -- -- -- --                    (e ₑ∙ₚ e ₑ∙ₚ X )
-- -- -- -- -- -- -- -- -- -- --                    X
-- -- -- -- -- -- -- -- -- -- --                    (λ _ → A)
-- -- -- -- -- -- -- -- -- -- --                    (λ _ → B)
-- -- -- -- -- -- -- -- -- -- -- invol-ₑ∙p  {B = B} e eInvol X j i =
-- -- -- -- -- -- -- -- -- -- --  Glue (X i) (invol-ₑ∙pSides e eInvol X j i)


-- -- -- -- -- -- -- -- -- -- -- invol-ₑ∙pSq-reflTy : ∀ {ℓ} {A : Type ℓ} → (f : A → A) →
-- -- -- -- -- -- -- -- -- -- --     (fInvol : isInvolution f)
-- -- -- -- -- -- -- -- -- -- --      → Type (ℓ-suc ℓ)
-- -- -- -- -- -- -- -- -- -- -- invol-ₑ∙pSq-reflTy  f fInvol =
-- -- -- -- -- -- -- -- -- -- --  let e = (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- --  in Cube
-- -- -- -- -- -- -- -- -- -- --      (invol-ₑ∙p e fInvol refl)
-- -- -- -- -- -- -- -- -- -- --      (ua-CompFill∙ₑ e e)
-- -- -- -- -- -- -- -- -- -- --      (symP-fromGoal (ₑ∙ₚ-ua e (e ₑ∙ₚ refl)))
-- -- -- -- -- -- -- -- -- -- --      (λ i j → Glue A
-- -- -- -- -- -- -- -- -- -- --        λ {  (j = i0) → A , equivEq {e = idEquiv _} {f = e ∙ₑ e} (sym (funExt fInvol)) i
-- -- -- -- -- -- -- -- -- -- --           ; (j = i1) → A , idEquiv _
-- -- -- -- -- -- -- -- -- -- --           ; (i = i0) → A , idEquiv _
-- -- -- -- -- -- -- -- -- -- --           })
-- -- -- -- -- -- -- -- -- -- --      (λ _ _ → A)
-- -- -- -- -- -- -- -- -- -- --      λ j i → ua (involEquiv {f = f} fInvol) (i ∨ ~ j)

   


-- -- -- -- -- -- -- -- -- -- -- -- sqInv : (e : A ≃ A) → isInvolution (fst e) →
-- -- -- -- -- -- -- -- -- -- -- --            PathP (λ j → A ≃ ua e j) e (idEquiv A)
-- -- -- -- -- -- -- -- -- -- -- -- sqInv e eInvol j = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- invol-ₑ∙p-refl : (e : A ≃ A) →
-- -- -- -- -- -- -- -- -- -- -- --     (fInvol : isInvolution (fst e))
-- -- -- -- -- -- -- -- -- -- -- --                 → Square
-- -- -- -- -- -- -- -- -- -- -- --                    (e ₑ∙ₚ e ₑ∙ₚ refl)
-- -- -- -- -- -- -- -- -- -- -- --                    refl
-- -- -- -- -- -- -- -- -- -- -- --                    (λ _ → A)
-- -- -- -- -- -- -- -- -- -- -- --                    (λ _ → A)
-- -- -- -- -- -- -- -- -- -- -- -- invol-ₑ∙p-refl  e fInvol j i =
-- -- -- -- -- -- -- -- -- -- -- --    Glue (ₑ∙ₚ-fill e refl j i)
-- -- -- -- -- -- -- -- -- -- -- --      λ {(i = i0) → A , ₑ∙ₚ-compSq e e j
-- -- -- -- -- -- -- -- -- -- -- --        ;(i = i1) → A , idEquiv A
-- -- -- -- -- -- -- -- -- -- -- --        ;(j = i1) → A , equivEq {e = (e ∙ₑ e)} {idEquiv A} (funExt fInvol) i
-- -- -- -- -- -- -- -- -- -- -- --         }

-- -- -- -- -- -- -- -- -- -- -- invol-ₑ∙pSq : ∀ {ℓ} {A B : Type ℓ} → (e : A ≃ A) →
-- -- -- -- -- -- -- -- -- -- --     (eInvol : isInvolution (fst e))  → (X : A ≡ B)
-- -- -- -- -- -- -- -- -- -- --                 → PathP (λ l →
-- -- -- -- -- -- -- -- -- -- --                      Square
-- -- -- -- -- -- -- -- -- -- --                    (e ₑ∙ₚ e ₑ∙ₚ λ i → X (i ∧ l))
-- -- -- -- -- -- -- -- -- -- --                    (λ i → X (i ∧ l))
-- -- -- -- -- -- -- -- -- -- --                    (λ _ → A)
-- -- -- -- -- -- -- -- -- -- --                    (λ _ → X l))
-- -- -- -- -- -- -- -- -- -- --                      (invol-ₑ∙p e eInvol refl) (invol-ₑ∙p e eInvol X)
-- -- -- -- -- -- -- -- -- -- -- invol-ₑ∙pSq  {B = B} e eInvol X
-- -- -- -- -- -- -- -- -- -- --   = λ l → invol-ₑ∙p e eInvol λ i → X (i ∧ l)



-- -- -- -- -- -- -- -- -- -- -- unglue-invol-ₑ∙p : ∀ {ℓ} {A B : Type ℓ} → (e : A ≃ A) →
-- -- -- -- -- -- -- -- -- -- --     (fInvol : isInvolution (fst e))  → (X : A ≡ B)
-- -- -- -- -- -- -- -- -- -- --                 →  SquareP (λ j i → invol-ₑ∙p e fInvol X j i ≃ X i)
-- -- -- -- -- -- -- -- -- -- --                      (λ i → unglue-ₑ∙p e (e ₑ∙ₚ X) i ∙ₑ unglue-ₑ∙p e X i)
-- -- -- -- -- -- -- -- -- -- --                      (λ _ → idEquiv _)
-- -- -- -- -- -- -- -- -- -- --                      (equivEq (funExt fInvol))
-- -- -- -- -- -- -- -- -- -- --                      (equivEq refl)
                     
-- -- -- -- -- -- -- -- -- -- -- fst (unglue-invol-ₑ∙p e eInvol X j i) x =
-- -- -- -- -- -- -- -- -- -- --  unglue (j ∨ ~ j ∨ i ∨ ~ i)
-- -- -- -- -- -- -- -- -- -- --    {e = λ o → snd (invol-ₑ∙pSides e eInvol X j i o)} x
 
-- -- -- -- -- -- -- -- -- -- -- snd (unglue-invol-ₑ∙p e eInvol X j i) =
-- -- -- -- -- -- -- -- -- -- --  let z = (λ j i → isPropIsEquiv
-- -- -- -- -- -- -- -- -- -- --          (λ x → unglue (j ∨ ~ j ∨ i ∨ ~ i)
-- -- -- -- -- -- -- -- -- -- --             {e = λ o → snd (invol-ₑ∙pSides e eInvol X j i o)} x))

-- -- -- -- -- -- -- -- -- -- --  in isProp→SquareP z
-- -- -- -- -- -- -- -- -- -- --     (isProp→PathP (λ j → z j i0) _ _)
-- -- -- -- -- -- -- -- -- -- --     (isProp→PathP (λ j → z j i1) _ _)
-- -- -- -- -- -- -- -- -- -- --     (λ i → snd (unglue-ₑ∙p e (e ₑ∙ₚ X) i ∙ₑ unglue-ₑ∙p e X i))
-- -- -- -- -- -- -- -- -- -- --     (λ i → idIsEquiv _)
-- -- -- -- -- -- -- -- -- -- --     j i



-- -- -- -- -- -- -- -- -- -- -- w∷ : ∀ n → Σ ℕ (λ k → suc k < n) → Fin n ≡ Fin n → Fin n ≡ Fin n
-- -- -- -- -- -- -- -- -- -- -- w∷ n k = (adjT'≃ {n = n} k) ₑ∙ₚ_

-- -- -- -- -- -- -- -- -- -- -- w∷≃ : ∀ n k → (X : Fin n ≡ Fin n) 
-- -- -- -- -- -- -- -- -- -- --        → ∀ j → w∷ n k X j ≃ X j
-- -- -- -- -- -- -- -- -- -- -- w∷≃ n k X j = unglue-ₑ∙p (adjT'≃ {n = n} k) X j


-- -- -- -- -- -- -- -- -- -- -- w∷invo : ∀ n k X → w∷ n k (w∷ n k X) ≡ X  
-- -- -- -- -- -- -- -- -- -- -- w∷invo n k X i j = invol-ₑ∙p (adjT'≃ {n = n} k) (isInvolution-adjT n k) X i j 

-- -- -- -- -- -- -- -- -- -- -- w∷invo-unglue≃ : ∀ n k X → ∀ i j → w∷invo n k X i j ≃ X j
-- -- -- -- -- -- -- -- -- -- -- w∷invo-unglue≃ n k X i j =
-- -- -- -- -- -- -- -- -- -- --    unglue-invol-ₑ∙p (adjT'≃ {n = n} k) (isInvolution-adjT n k) X i j 

-- -- -- -- -- -- -- -- -- -- -- permFin : ∀ n → Perm n → Fin n ≡ Fin n 
-- -- -- -- -- -- -- -- -- -- -- permFin n = Rrec.f (w)
-- -- -- -- -- -- -- -- -- -- --  where


-- -- -- -- -- -- -- -- -- -- --  w : Rrec {n = n} (Fin n ≡ Fin n)
-- -- -- -- -- -- -- -- -- -- --  Rrec.isSetA (w) = isOfHLevel≡ 2 (isSetFin {n = n}) (isSetFin {n = n})
-- -- -- -- -- -- -- -- -- -- --  Rrec.εA w = refl
-- -- -- -- -- -- -- -- -- -- --  Rrec.∷A (w) = w∷ n
-- -- -- -- -- -- -- -- -- -- --  Rrec.invoA (w) = w∷invo n      
-- -- -- -- -- -- -- -- -- -- --  Rrec.braidA (w) k k< _ =
-- -- -- -- -- -- -- -- -- -- --        ₑ∙ₚ-comp³eq _ _ _
-- -- -- -- -- -- -- -- -- -- --     (equivEq (cong (Iso.fun ∘ permuteIso n) (braid k k< ε)))
-- -- -- -- -- -- -- -- -- -- --  Rrec.commA w k l x X =
-- -- -- -- -- -- -- -- -- -- --      ₑ∙ₚ-comp²eq _ _ _
-- -- -- -- -- -- -- -- -- -- --        ((equivEq (cong (Iso.fun ∘ permuteIso n) (comm k l x ε))))

-- -- -- -- -- -- -- -- -- -- -- ℙrm : ℕ → Type
-- -- -- -- -- -- -- -- -- -- -- ℙrm n = EM₁ (Symmetric-Group (Fin n) (isSetFin {n}))

-- -- -- -- -- -- -- -- -- -- -- ℙrm' : ℕ → Type
-- -- -- -- -- -- -- -- -- -- -- ℙrm' n = EM₁ (PermG n)



-- -- -- -- -- -- -- -- -- -- -- h𝔽in' : ∀ n → ℙrm' n → hSet ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- h𝔽in' n = EMrec.f w
-- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- --   w : EMrec _ isGroupoidHSet
-- -- -- -- -- -- -- -- -- -- --   EMrec.b w = _ , isSetFin {n}
-- -- -- -- -- -- -- -- -- -- --   EMrec.bloop w g = 
-- -- -- -- -- -- -- -- -- -- --     TypeOfHLevel≡ 2 (permFin n g)
-- -- -- -- -- -- -- -- -- -- --   EMrec.bComp w g h = 
-- -- -- -- -- -- -- -- -- -- --     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- --       (RelimProp.f {n = n} w∷compR g)

-- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- --    w∷compR : RelimProp
-- -- -- -- -- -- -- -- -- -- --       (λ z → Square (permFin n z) (permFin n (z · h)) refl (permFin n h))
-- -- -- -- -- -- -- -- -- -- --    RelimProp.isPropA w∷compR _ =
-- -- -- -- -- -- -- -- -- -- --       isOfHLevelRetractFromIso
-- -- -- -- -- -- -- -- -- -- --          1
-- -- -- -- -- -- -- -- -- -- --          (invIso PathP→comm-Iso)
-- -- -- -- -- -- -- -- -- -- --            (isOfHLevel≡ 2 (isSetFin {n = n}) (isSetFin {n = n})
-- -- -- -- -- -- -- -- -- -- --              _ _ )
-- -- -- -- -- -- -- -- -- -- --    RelimProp.εA w∷compR i j = permFin n h (i ∧ j)
-- -- -- -- -- -- -- -- -- -- --    RelimProp.∷A w∷compR k {xs} X j = (adjT'≃ {n = n} k) ₑ∙ₚ (X j)


-- -- -- -- -- -- -- -- -- -- -- 𝔽in' : ∀ n → ℙrm' n → Type ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- 𝔽in'  n = fst ∘ h𝔽in' n 

-- -- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙p : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : ∀ j i → Type ℓ'}
-- -- -- -- -- -- -- -- -- -- -- --               → (f : A → A) → (fInvol : isInvolution f)
-- -- -- -- -- -- -- -- -- -- -- --                 {X : (A → B i1 i0) ≡ (A' → B i1 i1)}
-- -- -- -- -- -- -- -- -- -- -- --                 {X' : A ≡ A'} 
                                
-- -- -- -- -- -- -- -- -- -- -- --               → (P : Square
-- -- -- -- -- -- -- -- -- -- -- --                       (λ i → X' i → B i0 i)
-- -- -- -- -- -- -- -- -- -- -- --                       X
-- -- -- -- -- -- -- -- -- -- -- --                       (λ j → A → B j i0)-
-- -- -- -- -- -- -- -- -- -- -- --                       (λ j → A' → B j i1))
-- -- -- -- -- -- -- -- -- -- -- --               → Square  
-- -- -- -- -- -- -- -- -- -- -- --                   (λ i →
-- -- -- -- -- -- -- -- -- -- -- --                     {!!} → B i0 i)
-- -- -- -- -- -- -- -- -- -- -- --                   (λ i → ((preCompInvol.e' {f = f} (B i1 i) fInvol) ₑ∙ₚ λ i' → {!X i'!}) i)
-- -- -- -- -- -- -- -- -- -- -- --                   {!!}
-- -- -- -- -- -- -- -- -- -- -- --                   {!!}
-- -- -- -- -- -- -- -- -- -- -- --               -- → (λ i →  ((involEquiv {f = f} fInvol) ₑ∙ₚ X') i → B )
-- -- -- -- -- -- -- -- -- -- -- --               --   ≡ ((preCompInvol.e' {f = f} B fInvol) ₑ∙ₚ X)
-- -- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙p  {A'} {B = B} f fInvol {X} {X' = X'} P j i = {!!}



-- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙p-sides : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : ∀ j i → Type ℓ'}
-- -- -- -- -- -- -- -- -- -- --               → (f : A → A) → (fInvol : isInvolution f)
-- -- -- -- -- -- -- -- -- -- --                 {X : (A → B i1 i0) ≡ (A' → B i1 i1)}
-- -- -- -- -- -- -- -- -- -- --                 {X' : A ≡ A'} 
                                
-- -- -- -- -- -- -- -- -- -- --               → (P : Square
-- -- -- -- -- -- -- -- -- -- --                       (λ i → X' i → B i0 i)
-- -- -- -- -- -- -- -- -- -- --                       X
-- -- -- -- -- -- -- -- -- -- --                       (λ j → A → B j i0)
-- -- -- -- -- -- -- -- -- -- --                       (λ j → A' → B j i1))
-- -- -- -- -- -- -- -- -- -- --               → ∀ j i
-- -- -- -- -- -- -- -- -- -- --               → Partial (~ j ∨ i ∨ ~ i)
-- -- -- -- -- -- -- -- -- -- --                   (Σ (Type (ℓ-max ℓ ℓ')) (λ T → T ≃ P j i)) 
-- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙p-sides  {A'} {B = B} f fInvol {X} {X' = X'} P j i = 
-- -- -- -- -- -- -- -- -- -- --    let e = (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- --   in λ {
-- -- -- -- -- -- -- -- -- -- --       (i = i0) → (A → B j i0) , preCompInvol.e' {f = f} (B j i) fInvol
-- -- -- -- -- -- -- -- -- -- --     ; (i = i1) → (A' → B j i1) , idEquiv _
-- -- -- -- -- -- -- -- -- -- --     ; (j = i0) → ((e ₑ∙ₚ X') i → B i0 i) ,
-- -- -- -- -- -- -- -- -- -- --             (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)) ,
-- -- -- -- -- -- -- -- -- -- --             isProp→PathP
-- -- -- -- -- -- -- -- -- -- --               (λ i → isPropIsEquiv {A = (e ₑ∙ₚ X') i → B j i} {B = X' i → B i0 i}
-- -- -- -- -- -- -- -- -- -- --                 (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)))
-- -- -- -- -- -- -- -- -- -- --               (snd (preCompInvol.e' {f = f} (B j i0) fInvol))
-- -- -- -- -- -- -- -- -- -- --               (idIsEquiv _) i
-- -- -- -- -- -- -- -- -- -- --       }


-- -- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙p-sides : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : Type ℓ'}
-- -- -- -- -- -- -- -- -- -- -- --               → (f : A → A) → (fInvol : isInvolution f) 
-- -- -- -- -- -- -- -- -- -- -- --                 {X : (A → B) ≡ (A' → B)}
-- -- -- -- -- -- -- -- -- -- -- --                 {X' : A ≡ A'}
-- -- -- -- -- -- -- -- -- -- -- --               → (P : (λ i → X' i → B) ≡ X)
-- -- -- -- -- -- -- -- -- -- -- --               → ∀ j i
-- -- -- -- -- -- -- -- -- -- -- --               → Partial (~ j ∨ i ∨ ~ i)
-- -- -- -- -- -- -- -- -- -- -- --                   (Σ (Type (ℓ-max ℓ ℓ')) (λ T → T ≃ P j i)) 
-- -- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙p-sides  {A'} {B = B} f fInvol {X} {X' = X'} P j i =
-- -- -- -- -- -- -- -- -- -- -- --    let e = (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- -- --   in λ {
-- -- -- -- -- -- -- -- -- -- -- --       (i = i0) → (A → B) , preCompInvol.e' {f = f} B fInvol
-- -- -- -- -- -- -- -- -- -- -- --     ; (i = i1) → (A' → B) , idEquiv _
-- -- -- -- -- -- -- -- -- -- -- --     ; (j = i0) → ((e ₑ∙ₚ X') i → B) ,
-- -- -- -- -- -- -- -- -- -- -- --             (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)) ,
-- -- -- -- -- -- -- -- -- -- -- --             isProp→PathP
-- -- -- -- -- -- -- -- -- -- -- --               (λ i → isPropIsEquiv {A = (e ₑ∙ₚ X') i → B} {B = X' i → B}
-- -- -- -- -- -- -- -- -- -- -- --                 (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)))
-- -- -- -- -- -- -- -- -- -- -- --               (snd (preCompInvol.e' {f = f} B fInvol))
-- -- -- -- -- -- -- -- -- -- -- --               (idIsEquiv _) i
-- -- -- -- -- -- -- -- -- -- -- --       }

-- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙p : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : Type ℓ'}
-- -- -- -- -- -- -- -- -- -- --               → (f : A → A) → (fInvol : isInvolution f) 
-- -- -- -- -- -- -- -- -- -- --                 {X : (A → B) ≡ (A' → B)}
-- -- -- -- -- -- -- -- -- -- --                 {X' : A ≡ A'}
-- -- -- -- -- -- -- -- -- -- --               → (P : (λ i → X' i → B) ≡ X)
-- -- -- -- -- -- -- -- -- -- --               → (λ i →  ((involEquiv {f = f} fInvol) ₑ∙ₚ X') i → B )
-- -- -- -- -- -- -- -- -- -- --                 ≡ ((preCompInvol.e' {f = f} B fInvol) ₑ∙ₚ X)
-- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙p  {A'} {B = B} f fInvol {X} {X' = X'} P j i = 
-- -- -- -- -- -- -- -- -- -- --   let e = (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- --   in Glue (P j i) (dom-ₑ∙p-sides  {A'} {B = λ _ _ → B} f fInvol {X} {X' = X'} P j i)



-- -- -- -- -- -- -- -- -- -- -- unglue-dom-ₑ∙p : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : Type ℓ'}
-- -- -- -- -- -- -- -- -- -- --               → (f : A → A) → (fInvol : isInvolution f) 
-- -- -- -- -- -- -- -- -- -- --                 {X : (A → B) ≡ (A' → B)}
-- -- -- -- -- -- -- -- -- -- --                 {X' : A ≡ A'}
-- -- -- -- -- -- -- -- -- -- --               → (P : (λ i → X' i → B) ≡ X)
-- -- -- -- -- -- -- -- -- -- --               → SquareP
-- -- -- -- -- -- -- -- -- -- --                 (λ j i →
-- -- -- -- -- -- -- -- -- -- --                 dom-ₑ∙p  {A'} {B = B} f fInvol {X} {X' = X'} P j i
-- -- -- -- -- -- -- -- -- -- --                  ≃  P j i)
-- -- -- -- -- -- -- -- -- -- --                      (λ i → (λ x y → x (fst (glue-invol-ₑ∙p
-- -- -- -- -- -- -- -- -- -- --                           (involEquiv {f = f} fInvol) fInvol X' i) y))
-- -- -- -- -- -- -- -- -- -- --                        , unglueIsEquiv (X' i → B) i1
-- -- -- -- -- -- -- -- -- -- --                           (dom-ₑ∙p-sides {B = λ _ _ → B} f fInvol {X} {X'} P i0 i))
-- -- -- -- -- -- -- -- -- -- --                      (λ i → 
-- -- -- -- -- -- -- -- -- -- --                         fst (unglue-ₑ∙p (preCompInvol.e' {f = f} B fInvol) X i) ,
-- -- -- -- -- -- -- -- -- -- --                        unglueIsEquiv (X i) (i ∨ ~ i)
-- -- -- -- -- -- -- -- -- -- --                           (dom-ₑ∙p-sides {B = λ _ _ → B} f fInvol {X} {X'} P i1 i) )
-- -- -- -- -- -- -- -- -- -- --                      refl 
-- -- -- -- -- -- -- -- -- -- --                      refl

-- -- -- -- -- -- -- -- -- -- -- unglue-dom-ₑ∙p  {A'} {B = B} f fInvol {X} {X' = X'} P j i =
-- -- -- -- -- -- -- -- -- -- --   unglueEquiv (P j i) _
-- -- -- -- -- -- -- -- -- -- --     (dom-ₑ∙p-sides  {A'} {B = λ _ _ → B} f fInvol {X} {X' = X'} P j i)


-- -- -- -- -- -- -- -- -- -- -- -- unglue-dom-ₑ∙p : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : Type ℓ'}
-- -- -- -- -- -- -- -- -- -- -- --               → (f : A → A) → (fInvol : isInvolution f) 
-- -- -- -- -- -- -- -- -- -- -- --                 {X : (A → B) ≡ (A' → B)}
-- -- -- -- -- -- -- -- -- -- -- --                 {X' : A ≡ A'}
-- -- -- -- -- -- -- -- -- -- -- --               → (P : (λ i → X' i → B) ≡ X)
-- -- -- -- -- -- -- -- -- -- -- --               → SquareP
-- -- -- -- -- -- -- -- -- -- -- --                 (λ j i →
-- -- -- -- -- -- -- -- -- -- -- --                 dom-ₑ∙p  {A'} {B = B} f fInvol {X} {X' = X'} P j i
-- -- -- -- -- -- -- -- -- -- -- --                  → P j i)
-- -- -- -- -- -- -- -- -- -- -- --                      ((λ i x y → x (fst (glue-invol-ₑ∙p
-- -- -- -- -- -- -- -- -- -- -- --                           (involEquiv {f = f} fInvol) fInvol X' i) y)))
-- -- -- -- -- -- -- -- -- -- -- --                      (congP (λ _ → fst)
-- -- -- -- -- -- -- -- -- -- -- --                       (unglue-ₑ∙p (preCompInvol.e' {f = f} B fInvol) X))
-- -- -- -- -- -- -- -- -- -- -- --                      refl
-- -- -- -- -- -- -- -- -- -- -- --                      refl

-- -- -- -- -- -- -- -- -- -- -- -- unglue-dom-ₑ∙p  {A'} {B = B} f fInvol {X} {X' = X'} P j i =
-- -- -- -- -- -- -- -- -- -- -- --   let e = (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- -- --   in fst (unglueEquiv (P j i) _
-- -- -- -- -- -- -- -- -- -- -- --          {!!})
-- -- -- -- -- -- -- -- -- -- -- --     -- λ {
-- -- -- -- -- -- -- -- -- -- -- --     --   (i = i0) → (A → B) , preCompInvol.e' {f = f} B fInvol
-- -- -- -- -- -- -- -- -- -- -- --     -- ; (i = i1) → (A' → B) , idEquiv _
-- -- -- -- -- -- -- -- -- -- -- --     -- ; (j = i0) → ((e ₑ∙ₚ X') i → B) ,
-- -- -- -- -- -- -- -- -- -- -- --     --         (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)) ,
-- -- -- -- -- -- -- -- -- -- -- --     --         isProp→PathP
-- -- -- -- -- -- -- -- -- -- -- --     --           (λ i → isPropIsEquiv {A = (e ₑ∙ₚ X') i → B} {B = X' i → B}
-- -- -- -- -- -- -- -- -- -- -- --     --             (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)))
-- -- -- -- -- -- -- -- -- -- -- --     --           (snd (preCompInvol.e' {f = f} B fInvol))
-- -- -- -- -- -- -- -- -- -- -- --     --           (idIsEquiv _) i
-- -- -- -- -- -- -- -- -- -- -- --     --   })


-- -- -- -- -- -- -- -- -- -- -- dom-invol-ₑ∙p : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (isSetA : isSet A)
-- -- -- -- -- -- -- -- -- -- --               → (f : A → A) → (fInvol : isInvolution f) 
-- -- -- -- -- -- -- -- -- -- --                 {X : (A → B) ≡ (A → B)}
-- -- -- -- -- -- -- -- -- -- --                 {X' : A ≡ A}
-- -- -- -- -- -- -- -- -- -- --               → (P : (λ i → X' i → B) ≡ X)
-- -- -- -- -- -- -- -- -- -- --               → Cube

-- -- -- -- -- -- -- -- -- -- --                   (λ l j → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P ) l j)
-- -- -- -- -- -- -- -- -- -- --                   P
-- -- -- -- -- -- -- -- -- -- --                   (λ i j → invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X' i j
-- -- -- -- -- -- -- -- -- -- --                           → B)
-- -- -- -- -- -- -- -- -- -- --                   (λ i j → invol-ₑ∙p (preCompInvol.e' {f = f} B fInvol)
-- -- -- -- -- -- -- -- -- -- --                       (λ x → funExt λ y → cong x (fInvol y)) X i j)
-- -- -- -- -- -- -- -- -- -- --                   (refl {x = λ l → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P) l i0})
-- -- -- -- -- -- -- -- -- -- --                   (refl {x = λ l → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P) l i1})
-- -- -- -- -- -- -- -- -- -- -- dom-invol-ₑ∙p {ℓ = ℓ} {ℓ'}  {B} isSetA f fInvol {X} {X'} P i l j =
-- -- -- -- -- -- -- -- -- -- --    Glue (P l j ) {i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l}
-- -- -- -- -- -- -- -- -- -- --       λ o → T i l j o , e i l j o , isEqE i l j o

-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --     T : ∀ i l j → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l) (Type (ℓ-max ℓ ℓ'))
-- -- -- -- -- -- -- -- -- -- --     T i l j =
-- -- -- -- -- -- -- -- -- -- --      λ { (i = i0) → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P ) l j 
-- -- -- -- -- -- -- -- -- -- --        ; (i = i1) → P l j
-- -- -- -- -- -- -- -- -- -- --        ; (l = i0) → (invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X' i j → B) 
-- -- -- -- -- -- -- -- -- -- --        ; (l = i1) → invol-ₑ∙p (preCompInvol.e' {f = f} B fInvol)
-- -- -- -- -- -- -- -- -- -- --                       (λ x → funExt λ y → cong x (fInvol y)) X i j
-- -- -- -- -- -- -- -- -- -- --        ; (j = i0) → (A → B)
-- -- -- -- -- -- -- -- -- -- --        ; (j = i1) → (A → B) }

-- -- -- -- -- -- -- -- -- -- --     isSetX' : ∀ j → isSet (X' j)
-- -- -- -- -- -- -- -- -- -- --     isSetX' j = isProp→PathP (λ j → isPropIsSet {A = X' j})
-- -- -- -- -- -- -- -- -- -- --       isSetA isSetA j

-- -- -- -- -- -- -- -- -- -- --     isSetInvol : ∀ i j →
-- -- -- -- -- -- -- -- -- -- --           isSet (invol-ₑ∙p (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- --                          fInvol X' i j)
-- -- -- -- -- -- -- -- -- -- --     isSetInvol i j =
-- -- -- -- -- -- -- -- -- -- --       isOfHLevelRespectEquiv 2
-- -- -- -- -- -- -- -- -- -- --         (invEquiv (unglue-invol-ₑ∙p (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- --                          fInvol X' i j))
-- -- -- -- -- -- -- -- -- -- --         (isSetX' j)

-- -- -- -- -- -- -- -- -- -- --     ∘f = preCompInvol.e' {f = f} B fInvol

-- -- -- -- -- -- -- -- -- -- --     e : ∀ i l j → PartialP (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l)
-- -- -- -- -- -- -- -- -- -- --             λ o → T i l j o → P l j 
-- -- -- -- -- -- -- -- -- -- --     e i l j =  λ { (i = i0) → fst (unglue-dom-ₑ∙p f fInvol P l j) ∘
-- -- -- -- -- -- -- -- -- -- --                fst (unglue-dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P) l j) 
-- -- -- -- -- -- -- -- -- -- --        ; (i = i1) → idfun _
-- -- -- -- -- -- -- -- -- -- --        ; (l = i0) → _∘ 
-- -- -- -- -- -- -- -- -- -- --                (isSet→SquareP {A = λ i j → X' j → 
-- -- -- -- -- -- -- -- -- -- --                 invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X' i j} (λ i j →
-- -- -- -- -- -- -- -- -- -- --                     isSetΠ λ _ → isSetInvol i j)
-- -- -- -- -- -- -- -- -- -- --                   (λ j → (fst (glue-invol-ₑ∙p
-- -- -- -- -- -- -- -- -- -- --                           (involEquiv {f = f} fInvol) fInvol
-- -- -- -- -- -- -- -- -- -- --                            (involEquiv {f = f} fInvol ₑ∙ₚ X') j))
-- -- -- -- -- -- -- -- -- -- --                            ∘' (fst (glue-invol-ₑ∙p
-- -- -- -- -- -- -- -- -- -- --                           (involEquiv {f = f} fInvol) fInvol X' j)))
-- -- -- -- -- -- -- -- -- -- --                   (λ _ → idfun _)
-- -- -- -- -- -- -- -- -- -- --                   (λ i y → fInvol y i)
-- -- -- -- -- -- -- -- -- -- --                   (λ _ → idfun _) i j)

-- -- -- -- -- -- -- -- -- -- --        ; (l = i1) → fst (unglue-invol-ₑ∙p ∘f
-- -- -- -- -- -- -- -- -- -- --                       (λ x → funExt λ y → cong x (fInvol y)) X i j)
-- -- -- -- -- -- -- -- -- -- --        ; (j = i0) → λ x y → x (fInvol y i)
-- -- -- -- -- -- -- -- -- -- --        ; (j = i1) → idfun _
-- -- -- -- -- -- -- -- -- -- --        }

-- -- -- -- -- -- -- -- -- -- --     isEqEJ0 : (i l : I) → isEquiv {A = A → B} {B = A → B} (λ x y → x (fInvol y i))
-- -- -- -- -- -- -- -- -- -- --     isEqEJ0 i l = isProp→PathP
-- -- -- -- -- -- -- -- -- -- --            (λ i → isPropIsEquiv (λ x y → x (fInvol y i)))
-- -- -- -- -- -- -- -- -- -- --            (snd (∘f ∙ₑ ∘f))
-- -- -- -- -- -- -- -- -- -- --             (idIsEquiv _) i

-- -- -- -- -- -- -- -- -- -- --     isEqEJ1 : (i l : I) → isEquiv {A = A → B} (λ x → x)
-- -- -- -- -- -- -- -- -- -- --     isEqEJ1 _ _ = idIsEquiv _

-- -- -- -- -- -- -- -- -- -- --     isEqI0L0 : _
-- -- -- -- -- -- -- -- -- -- --     isEqI0L0 = isProp→PathP (λ j → isPropIsEquiv (e i0 i0 j 1=1)) _ _

-- -- -- -- -- -- -- -- -- -- --     isEqI0L1 : _
-- -- -- -- -- -- -- -- -- -- --     isEqI0L1 = isProp→PathP (λ j → isPropIsEquiv (e i0 i1 j 1=1)) _ _


-- -- -- -- -- -- -- -- -- -- --     isEqE : ∀ i l j → PartialP (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l)
-- -- -- -- -- -- -- -- -- -- --             λ o → isEquiv (e i l j o) 
-- -- -- -- -- -- -- -- -- -- --     isEqE i l j =
-- -- -- -- -- -- -- -- -- -- --      λ { (i = i0) →
-- -- -- -- -- -- -- -- -- -- --             isProp→SquareP
-- -- -- -- -- -- -- -- -- -- --             (λ l j → isPropIsEquiv (e i0 l j 1=1))
-- -- -- -- -- -- -- -- -- -- --                  (λ _ → snd (compEquiv ∘f ∘f))
-- -- -- -- -- -- -- -- -- -- --                  (λ _ → idIsEquiv _)
-- -- -- -- -- -- -- -- -- -- --                  isEqI0L0
-- -- -- -- -- -- -- -- -- -- --                  isEqI0L1 l j 
-- -- -- -- -- -- -- -- -- -- --        ; (i = i1) → idIsEquiv _
-- -- -- -- -- -- -- -- -- -- --        ; (l = i0) →
-- -- -- -- -- -- -- -- -- -- --             isProp→SquareP
-- -- -- -- -- -- -- -- -- -- --             (λ i j → isPropIsEquiv (e i i0 j 1=1))
-- -- -- -- -- -- -- -- -- -- --                  (λ i → isEqEJ0 i i0)
-- -- -- -- -- -- -- -- -- -- --                  (λ _ → idIsEquiv _)
-- -- -- -- -- -- -- -- -- -- --                  isEqI0L0
-- -- -- -- -- -- -- -- -- -- --                  (λ _ → idIsEquiv _) i j
-- -- -- -- -- -- -- -- -- -- --        ; (l = i1) →
-- -- -- -- -- -- -- -- -- -- --                       isProp→SquareP
-- -- -- -- -- -- -- -- -- -- --             (λ i j → isPropIsEquiv (e i i1 j 1=1))
-- -- -- -- -- -- -- -- -- -- --                  (λ i → isEqEJ0 i i1)
-- -- -- -- -- -- -- -- -- -- --                  (λ i → isEqEJ1 i i1)
-- -- -- -- -- -- -- -- -- -- --                  isEqI0L1
-- -- -- -- -- -- -- -- -- -- --                  (λ _ → idIsEquiv _) i j
-- -- -- -- -- -- -- -- -- -- --        ; (j = i0) → isEqEJ0 i l            
-- -- -- -- -- -- -- -- -- -- --        ; (j = i1) → isEqEJ1 i l      
-- -- -- -- -- -- -- -- -- -- --        }

-- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙ₚ-comp²eq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (isSetA : isSet A)
-- -- -- -- -- -- -- -- -- -- --               → (f : A → A) → (fInvol : isInvolution f)
-- -- -- -- -- -- -- -- -- -- --               → (g : A → A) → (gInvol : isInvolution g)
-- -- -- -- -- -- -- -- -- -- --               → (fg-comm : f ∘ g ≡ g ∘ f) → 
-- -- -- -- -- -- -- -- -- -- --                 {X : (A → B) ≡ (A → B)}
-- -- -- -- -- -- -- -- -- -- --                 {X' : A ≡ A}
-- -- -- -- -- -- -- -- -- -- --               → (P : (λ i → X' i → B) ≡ X)
-- -- -- -- -- -- -- -- -- -- --               → Cube
-- -- -- -- -- -- -- -- -- -- --                   (dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol P ))
-- -- -- -- -- -- -- -- -- -- --                   (dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol P ))
-- -- -- -- -- -- -- -- -- -- --                   (λ i j → ₑ∙ₚ-comp²eq
-- -- -- -- -- -- -- -- -- -- --                      (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- --                      (involEquiv {f = g} gInvol) X' (equivEq (fg-comm)) i j → B)
-- -- -- -- -- -- -- -- -- -- --                   (ₑ∙ₚ-comp²eq _ _ X (equivEq
-- -- -- -- -- -- -- -- -- -- --                     (funExt λ x → cong (x ∘'_) (sym fg-comm))) )
-- -- -- -- -- -- -- -- -- -- --                   refl
-- -- -- -- -- -- -- -- -- -- --                   refl

-- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙ₚ-comp²eq {ℓ} {ℓ'} {B = B} isSetA f fInvol g gInvol fg-comm {X} {X'} P =
-- -- -- -- -- -- -- -- -- -- --    λ i l j →
-- -- -- -- -- -- -- -- -- -- --         Glue (P l j) λ o → T i l j o , E i l j o ,
-- -- -- -- -- -- -- -- -- -- --           isEquivE i l j o  

-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --    T : ∀ i l j → Partial (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
-- -- -- -- -- -- -- -- -- -- --                (Type (ℓ-max ℓ ℓ'))
-- -- -- -- -- -- -- -- -- -- --    T i l j = λ {
-- -- -- -- -- -- -- -- -- -- --      (i = i0) → _
-- -- -- -- -- -- -- -- -- -- --     ;(i = i1) → _
-- -- -- -- -- -- -- -- -- -- --     ;(l = i0) → _
-- -- -- -- -- -- -- -- -- -- --     ;(l = i1) → _
-- -- -- -- -- -- -- -- -- -- --     ;(j = i0) → _
-- -- -- -- -- -- -- -- -- -- --     ;(j = i1) → _
-- -- -- -- -- -- -- -- -- -- --     }

-- -- -- -- -- -- -- -- -- -- --    isSetX' : ∀ j → isSet (X' j)
-- -- -- -- -- -- -- -- -- -- --    isSetX' j = isProp→PathP (λ j → isPropIsSet {A = X' j})
-- -- -- -- -- -- -- -- -- -- --      isSetA isSetA j

-- -- -- -- -- -- -- -- -- -- --    isSet-ₑ∙ₚ-comp²eq : ∀ i j →
-- -- -- -- -- -- -- -- -- -- --          isSet
-- -- -- -- -- -- -- -- -- -- --      (ₑ∙ₚ-comp²eq (involEquiv {f = f} fInvol) (involEquiv {f = g} gInvol) X'
-- -- -- -- -- -- -- -- -- -- --       (equivEq fg-comm) i j)
-- -- -- -- -- -- -- -- -- -- --    isSet-ₑ∙ₚ-comp²eq i j =
-- -- -- -- -- -- -- -- -- -- --      isOfHLevelRespectEquiv 2
-- -- -- -- -- -- -- -- -- -- --        (invEquiv (unglueEquiv (X' j) (i ∨ ~ i ∨ j ∨ ~ j)
-- -- -- -- -- -- -- -- -- -- --          (ₑ∙ₚ-comp²eq-sides
-- -- -- -- -- -- -- -- -- -- --           (involEquiv {f = f} fInvol) (involEquiv {f = g} gInvol) X'
-- -- -- -- -- -- -- -- -- -- --       (equivEq fg-comm) i j)))
-- -- -- -- -- -- -- -- -- -- --        (isSetX' j)


-- -- -- -- -- -- -- -- -- -- --    El0 : ∀ i j → T i i0 j 1=1 → X' j → B
-- -- -- -- -- -- -- -- -- -- --    El0 i j = _∘' 
-- -- -- -- -- -- -- -- -- -- --                (isSet→SquareP {A = λ i j → X' j → 
-- -- -- -- -- -- -- -- -- -- --                 ₑ∙ₚ-comp²eq
-- -- -- -- -- -- -- -- -- -- --                      (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- --                      (involEquiv {f = g} gInvol) X' (equivEq (fg-comm)) i j}
-- -- -- -- -- -- -- -- -- -- --                       (λ i j →
-- -- -- -- -- -- -- -- -- -- --                     isSetΠ λ _ → isSet-ₑ∙ₚ-comp²eq i j)
-- -- -- -- -- -- -- -- -- -- --                     (λ j → (fst (glue-invol-ₑ∙p
-- -- -- -- -- -- -- -- -- -- --                           (involEquiv {f = g} gInvol) gInvol
-- -- -- -- -- -- -- -- -- -- --                            (involEquiv {f = f} fInvol ₑ∙ₚ X') j))
-- -- -- -- -- -- -- -- -- -- --                            ∘' (fst (glue-invol-ₑ∙p
-- -- -- -- -- -- -- -- -- -- --                           (involEquiv {f = f} fInvol) fInvol X' j)))
-- -- -- -- -- -- -- -- -- -- --                   (λ j → (fst (glue-invol-ₑ∙p
-- -- -- -- -- -- -- -- -- -- --                           (involEquiv {f = f} fInvol) fInvol
-- -- -- -- -- -- -- -- -- -- --                            (involEquiv {f = g} gInvol ₑ∙ₚ X') j))
-- -- -- -- -- -- -- -- -- -- --                            ∘' (fst (glue-invol-ₑ∙p
-- -- -- -- -- -- -- -- -- -- --                           (involEquiv {f = g} gInvol) gInvol X' j)))
-- -- -- -- -- -- -- -- -- -- --                   (sym fg-comm)
-- -- -- -- -- -- -- -- -- -- --                   (λ _ → idfun _) i j)

-- -- -- -- -- -- -- -- -- -- --    El1 : ∀ i j → T i i1 j 1=1 → X j
-- -- -- -- -- -- -- -- -- -- --    El1 i j = unglue (j ∨ ~ j ∨ i ∨ ~ i)
-- -- -- -- -- -- -- -- -- -- --        {e = λ o → snd (ₑ∙ₚ-comp²eq-sides
-- -- -- -- -- -- -- -- -- -- --           (preCompInvol.e' {f = f} B fInvol)
-- -- -- -- -- -- -- -- -- -- --           (preCompInvol.e' {f = g} B gInvol) X
-- -- -- -- -- -- -- -- -- -- --        (equivEq
-- -- -- -- -- -- -- -- -- -- --                     (funExt λ x → cong (x ∘'_) (sym fg-comm))) i j o)} 


-- -- -- -- -- -- -- -- -- -- --    E : ∀ i l j → PartialP (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
-- -- -- -- -- -- -- -- -- -- --                (λ o → T i l j o → P l j)
-- -- -- -- -- -- -- -- -- -- --    E i l j = λ {
-- -- -- -- -- -- -- -- -- -- --      (i = i0) →
-- -- -- -- -- -- -- -- -- -- --        fst (unglue-dom-ₑ∙p f fInvol P l j) ∘
-- -- -- -- -- -- -- -- -- -- --                fst (unglue-dom-ₑ∙p g gInvol ((dom-ₑ∙p f fInvol P)) l j)
-- -- -- -- -- -- -- -- -- -- --     ;(i = i1) →
-- -- -- -- -- -- -- -- -- -- --        fst (unglue-dom-ₑ∙p g gInvol P l j) ∘
-- -- -- -- -- -- -- -- -- -- --                fst (unglue-dom-ₑ∙p f fInvol ((dom-ₑ∙p g gInvol P)) l j)
-- -- -- -- -- -- -- -- -- -- --     ;(l = i0) → El0 i j
-- -- -- -- -- -- -- -- -- -- --     ;(l = i1) → El1 i j
-- -- -- -- -- -- -- -- -- -- --     ;(j = i0) → λ x → x ∘ (fg-comm (~ i))
-- -- -- -- -- -- -- -- -- -- --     ;(j = i1) → idfun _
-- -- -- -- -- -- -- -- -- -- --     }

-- -- -- -- -- -- -- -- -- -- --    isEquivEi0 : ∀ l j → isEquiv (E i0 l j 1=1)
-- -- -- -- -- -- -- -- -- -- --    isEquivEi0 l j =
-- -- -- -- -- -- -- -- -- -- --       snd (unglue-dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol P) l j
-- -- -- -- -- -- -- -- -- -- --           ∙ₑ unglue-dom-ₑ∙p f fInvol P l j)

-- -- -- -- -- -- -- -- -- -- --    isEquivEi1 : ∀ l j → isEquiv (E i1 l j 1=1)
-- -- -- -- -- -- -- -- -- -- --    isEquivEi1 l j =
-- -- -- -- -- -- -- -- -- -- --       snd (unglue-dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol P) l j
-- -- -- -- -- -- -- -- -- -- --           ∙ₑ unglue-dom-ₑ∙p g gInvol P l j)



-- -- -- -- -- -- -- -- -- -- --    isEquivE : ∀ i l j → PartialP (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
-- -- -- -- -- -- -- -- -- -- --                (λ o → isEquiv (E i l j o))
-- -- -- -- -- -- -- -- -- -- --    isEquivE i l j =
-- -- -- -- -- -- -- -- -- -- --        λ {
-- -- -- -- -- -- -- -- -- -- --      (i = i0) → isEquivEi0 l j
-- -- -- -- -- -- -- -- -- -- --     ;(i = i1) → isEquivEi1 l j
-- -- -- -- -- -- -- -- -- -- --     ;(l = i0) → isProp→PathP
-- -- -- -- -- -- -- -- -- -- --          (λ i → isPropIsEquiv (E i l j 1=1))
-- -- -- -- -- -- -- -- -- -- --               (isEquivEi0 l j)
-- -- -- -- -- -- -- -- -- -- --               (isEquivEi1 l j) i
-- -- -- -- -- -- -- -- -- -- --     ;(l = i1) → isProp→PathP
-- -- -- -- -- -- -- -- -- -- --          (λ i → isPropIsEquiv (E i l j 1=1))
-- -- -- -- -- -- -- -- -- -- --               (isEquivEi0 l j)
-- -- -- -- -- -- -- -- -- -- --               (isEquivEi1 l j) i
-- -- -- -- -- -- -- -- -- -- --     ;(j = i0) → isProp→PathP
-- -- -- -- -- -- -- -- -- -- --          (λ i → isPropIsEquiv (E i l j 1=1))
-- -- -- -- -- -- -- -- -- -- --               (isEquivEi0 l j)
-- -- -- -- -- -- -- -- -- -- --               (isEquivEi1 l j) i
-- -- -- -- -- -- -- -- -- -- --     ;(j = i1) → isProp→PathP
-- -- -- -- -- -- -- -- -- -- --          (λ i → isPropIsEquiv (E i l j 1=1))
-- -- -- -- -- -- -- -- -- -- --               (isEquivEi0 l j)
-- -- -- -- -- -- -- -- -- -- --               (isEquivEi1 l j) i
-- -- -- -- -- -- -- -- -- -- --               }

-- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙ₚ-comp³eq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (isSetA : isSet A)
-- -- -- -- -- -- -- -- -- -- --    → (f : A → A) → (fInvol : isInvolution f)
-- -- -- -- -- -- -- -- -- -- --    → (g : A → A) → (gInvol : isInvolution g)
-- -- -- -- -- -- -- -- -- -- --    → (fg-braid : (f ∘' g ∘' f) ≡ (g ∘' f ∘' g)) 
-- -- -- -- -- -- -- -- -- -- --    →   {X : (A → B) ≡ (A → B)}
-- -- -- -- -- -- -- -- -- -- --                 {X' : A ≡ A}
-- -- -- -- -- -- -- -- -- -- --               → (P : (λ i → X' i → B) ≡ X)
-- -- -- -- -- -- -- -- -- -- --               → Cube
-- -- -- -- -- -- -- -- -- -- --                    ((dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol P ))))
-- -- -- -- -- -- -- -- -- -- --                    ((dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol P ))))
                   
-- -- -- -- -- -- -- -- -- -- --                   (λ i j → ₑ∙ₚ-comp³eq
-- -- -- -- -- -- -- -- -- -- --                      (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- --                      (involEquiv {f = g} gInvol) X' (equivEq fg-braid) i j → B)
-- -- -- -- -- -- -- -- -- -- --                    (ₑ∙ₚ-comp³eq _ _ X
-- -- -- -- -- -- -- -- -- -- --                      (equivEq (funExt λ x → cong (x ∘'_) (fg-braid))))

-- -- -- -- -- -- -- -- -- -- --                   refl
-- -- -- -- -- -- -- -- -- -- --                   refl
-- -- -- -- -- -- -- -- -- -- -- dom-ₑ∙ₚ-comp³eq {ℓ} {ℓ'} {A} {B} isSetA f fInvol g gInvol fg-braid {X} {X'} P = 
-- -- -- -- -- -- -- -- -- -- --      λ i l j → Glue (P l j) λ o → T i l j o , E i l j o 

-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --    T : ∀ i l j → Partial (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
-- -- -- -- -- -- -- -- -- -- --                (Type (ℓ-max ℓ ℓ'))
-- -- -- -- -- -- -- -- -- -- --    T i l j = λ {
-- -- -- -- -- -- -- -- -- -- --      (i = i0) → _
-- -- -- -- -- -- -- -- -- -- --     ;(i = i1) → _
-- -- -- -- -- -- -- -- -- -- --     ;(l = i0) → _
-- -- -- -- -- -- -- -- -- -- --     ;(l = i1) → _
-- -- -- -- -- -- -- -- -- -- --     ;(j = i0) → _
-- -- -- -- -- -- -- -- -- -- --     ;(j = i1) → _
-- -- -- -- -- -- -- -- -- -- --     }

-- -- -- -- -- -- -- -- -- -- --    isSetX' : ∀ j → isSet (X' j)
-- -- -- -- -- -- -- -- -- -- --    isSetX' j = isProp→PathP (λ j → isPropIsSet {A = X' j})
-- -- -- -- -- -- -- -- -- -- --      isSetA isSetA j

-- -- -- -- -- -- -- -- -- -- --    isSet-ₑ∙ₚ-comp³eq : ∀ i j →
-- -- -- -- -- -- -- -- -- -- --          isSet
-- -- -- -- -- -- -- -- -- -- --      (ₑ∙ₚ-comp³eq (involEquiv {f = f} fInvol) (involEquiv {f = g} gInvol) X'
-- -- -- -- -- -- -- -- -- -- --       (equivEq fg-braid) i j)
-- -- -- -- -- -- -- -- -- -- --    isSet-ₑ∙ₚ-comp³eq i j =
-- -- -- -- -- -- -- -- -- -- --      isOfHLevelRespectEquiv 2
-- -- -- -- -- -- -- -- -- -- --        (invEquiv (unglueEquiv (X' j) (i ∨ ~ i ∨ j ∨ ~ j)
-- -- -- -- -- -- -- -- -- -- --          (ₑ∙ₚ-comp³eq-sides
-- -- -- -- -- -- -- -- -- -- --           (involEquiv {f = f} fInvol) (involEquiv {f = g} gInvol) X'
-- -- -- -- -- -- -- -- -- -- --       (equivEq fg-braid) i j)))
-- -- -- -- -- -- -- -- -- -- --        (isSetX' j)

-- -- -- -- -- -- -- -- -- -- --    f' : (X : A ≡ A) → ∀ j → X j ≃ (involEquiv {f = f} fInvol ₑ∙ₚ X) j
-- -- -- -- -- -- -- -- -- -- --    f' X j = glue-invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X j

-- -- -- -- -- -- -- -- -- -- --    g' : (X : A ≡ A) → ∀ j → X j ≃ (involEquiv {f = g} gInvol ₑ∙ₚ X) j
-- -- -- -- -- -- -- -- -- -- --    g' X j = glue-invol-ₑ∙p (involEquiv {f = g} gInvol) gInvol X j


-- -- -- -- -- -- -- -- -- -- --    Ei0 : ∀ l j → T i0 l j 1=1 ≃ P l j
-- -- -- -- -- -- -- -- -- -- --    Ei0 l j =     
-- -- -- -- -- -- -- -- -- -- --         (unglue-dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol P)) l j)
-- -- -- -- -- -- -- -- -- -- --      ∙ₑ (unglue-dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol P) l j)
-- -- -- -- -- -- -- -- -- -- --      ∙ₑ (unglue-dom-ₑ∙p f fInvol P l j)


-- -- -- -- -- -- -- -- -- -- --    Ei1 : ∀ l j → T i1 l j 1=1 ≃ P l j
-- -- -- -- -- -- -- -- -- -- --    Ei1 l j =     
-- -- -- -- -- -- -- -- -- -- --         (unglue-dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol P)) l j)
-- -- -- -- -- -- -- -- -- -- --      ∙ₑ (unglue-dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol P) l j)
-- -- -- -- -- -- -- -- -- -- --      ∙ₑ (unglue-dom-ₑ∙p g gInvol P l j)

-- -- -- -- -- -- -- -- -- -- --    El0 : ∀ i j → T i i0 j 1=1 → X' j → B
-- -- -- -- -- -- -- -- -- -- --    El0 i j = _∘' 
-- -- -- -- -- -- -- -- -- -- --                (isSet→SquareP {A = λ i j → X' j → 
-- -- -- -- -- -- -- -- -- -- --                 ₑ∙ₚ-comp³eq
-- -- -- -- -- -- -- -- -- -- --                      (involEquiv {f = f} fInvol)
-- -- -- -- -- -- -- -- -- -- --                      (involEquiv {f = g} gInvol) X' (equivEq (fg-braid)) i j}
-- -- -- -- -- -- -- -- -- -- --                       (λ i j →
-- -- -- -- -- -- -- -- -- -- --                     isSetΠ λ _ → isSet-ₑ∙ₚ-comp³eq i j)
-- -- -- -- -- -- -- -- -- -- --                     (λ j →  fst (f' X' j ∙ₑ g' (λ j → ua (f' X' j) i1) j
-- -- -- -- -- -- -- -- -- -- --                                 ∙ₑ f' (λ j → ua (g' (λ j → ua (f' X' j) i1) j) i1) j) )
-- -- -- -- -- -- -- -- -- -- --                     (λ j →  fst (g' X' j ∙ₑ f' (λ j → ua (g' X' j) i1) j
-- -- -- -- -- -- -- -- -- -- --                                 ∙ₑ g' (λ j → ua (f' (λ j → ua (g' X' j) i1) j) i1) j) )
-- -- -- -- -- -- -- -- -- -- --                   fg-braid
-- -- -- -- -- -- -- -- -- -- --                   (λ _ → idfun _)
-- -- -- -- -- -- -- -- -- -- --                   i j)

-- -- -- -- -- -- -- -- -- -- --    El1 : ∀ i j → T i i1 j 1=1 → X j
-- -- -- -- -- -- -- -- -- -- --    El1 i j = unglue (j ∨ ~ j ∨ i ∨ ~ i)
-- -- -- -- -- -- -- -- -- -- --        {e = λ o → snd (ₑ∙ₚ-comp³eq-sides
-- -- -- -- -- -- -- -- -- -- --           (preCompInvol.e' {f = f} B fInvol)
-- -- -- -- -- -- -- -- -- -- --           (preCompInvol.e' {f = g} B gInvol) X
-- -- -- -- -- -- -- -- -- -- --        (equivEq
-- -- -- -- -- -- -- -- -- -- --                     (funExt λ x → cong (x ∘'_) (fg-braid))) i j o)} 


-- -- -- -- -- -- -- -- -- -- --    E : ∀ i l j → PartialP (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
-- -- -- -- -- -- -- -- -- -- --                (λ o → T i l j o ≃ P l j)
-- -- -- -- -- -- -- -- -- -- --    E i l j = λ {
-- -- -- -- -- -- -- -- -- -- --      (i = i0) → Ei0 l j
-- -- -- -- -- -- -- -- -- -- --     ;(i = i1) → Ei1 l j
-- -- -- -- -- -- -- -- -- -- --     ;(l = i0) → El0 i j ,
-- -- -- -- -- -- -- -- -- -- --          isProp→PathP
-- -- -- -- -- -- -- -- -- -- --          (λ i → isPropIsEquiv (El0 i j))
-- -- -- -- -- -- -- -- -- -- --               (snd (Ei0 l j))
-- -- -- -- -- -- -- -- -- -- --               (snd (Ei1 l j)) i
-- -- -- -- -- -- -- -- -- -- --     ;(l = i1) → El1 i j ,
-- -- -- -- -- -- -- -- -- -- --         isProp→PathP
-- -- -- -- -- -- -- -- -- -- --          (λ i → isPropIsEquiv (El1 i j))
-- -- -- -- -- -- -- -- -- -- --               (snd (Ei0 l j))
-- -- -- -- -- -- -- -- -- -- --               (snd (Ei1 l j)) i
-- -- -- -- -- -- -- -- -- -- --     ;(j = i0) → (_∘' (fg-braid i)) ,
-- -- -- -- -- -- -- -- -- -- --        isProp→PathP
-- -- -- -- -- -- -- -- -- -- --          (λ i → isPropIsEquiv (_∘' (fg-braid i)))
-- -- -- -- -- -- -- -- -- -- --               (snd (Ei0 l j))
-- -- -- -- -- -- -- -- -- -- --               (snd (Ei1 l j)) i
-- -- -- -- -- -- -- -- -- -- --     ;(j = i1) → idfun _ ,
-- -- -- -- -- -- -- -- -- -- --               isProp→PathP
-- -- -- -- -- -- -- -- -- -- --          (λ i → isPropIsEquiv (idfun _))
-- -- -- -- -- -- -- -- -- -- --               (snd (Ei0 l j))
-- -- -- -- -- -- -- -- -- -- --               (snd (Ei1 l j)) i
-- -- -- -- -- -- -- -- -- -- --     }





-- -- -- -- -- -- -- -- -- -- -- -- h𝔽in : ∀ n → ℙrm n → hSet ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- h𝔽in n = EMrec.f w
-- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- --   w : EMrec (Symmetric-Group (Fin n) (isSetFin {n})) isGroupoidHSet
-- -- -- -- -- -- -- -- -- -- -- --   EMrec.b w = Fin n , isSetFin {n}
-- -- -- -- -- -- -- -- -- -- -- --   EMrec.bloop w g = TypeOfHLevel≡ 2 (ua g)
-- -- -- -- -- -- -- -- -- -- -- --   EMrec.bComp w g h =
-- -- -- -- -- -- -- -- -- -- -- --      ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- --         λ i j →
-- -- -- -- -- -- -- -- -- -- -- --           Glue (ua {!ua !} i)
-- -- -- -- -- -- -- -- -- -- -- --             λ { (j = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- --               ; (j = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- --               }




-- -- -- -- -- -- -- -- -- -- -- -- 𝔽in : ∀ n → ℙrm n → Type ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- 𝔽in  n = fst ∘ h𝔽in n


-- -- -- -- -- -- -- -- -- -- -- -- 𝔽h : (A : Type ℓ) → ∀ n → ℙrm n → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- 𝔽h A n em = 𝔽in n em → A 





-- -- -- -- -- -- -- -- -- -- -- -- uaDom≃ : ∀ {ℓ ℓ'} {A B : Type ℓ} (C : Type ℓ') → (e : A ≃ B) →  
-- -- -- -- -- -- -- -- -- -- -- --      ua (preCompEquiv {C = C} (invEquiv e))
-- -- -- -- -- -- -- -- -- -- -- --        ≡ cong (λ X → X → C) (ua e)
-- -- -- -- -- -- -- -- -- -- -- -- uaDom≃ C e = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   -- invEq≡→equivFun≡ (invEquiv univalence)
-- -- -- -- -- -- -- -- -- -- -- --   --  (equivEq (funExt (λ x →
-- -- -- -- -- -- -- -- -- -- -- --   --    fromPathP (funTypeTransp' (idfun _) C ((ua (isoToEquiv e))) x)
-- -- -- -- -- -- -- -- -- -- -- --   --     ∙ funExt λ y → cong x (cong (Iso.inv e) (transportRefl y)))))

-- -- -- -- -- -- -- -- -- -- -- -- 𝔽h* : (A : Type ℓ) → ∀ n → (p : ℙrm n) → singl (𝔽h A n p )
-- -- -- -- -- -- -- -- -- -- -- -- 𝔽h* A n = EMelim.f w
-- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- --  w : EMelim _ λ z → singl (𝔽h A n z)
-- -- -- -- -- -- -- -- -- -- -- --  EMelim.isGrpB w = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  EMelim.b w = _ , refl
-- -- -- -- -- -- -- -- -- -- -- --  EMelim.bPathP w g = ΣPathP
-- -- -- -- -- -- -- -- -- -- -- --    ((ua (preCompEquiv {C = A} (invEquiv g))) ,
-- -- -- -- -- -- -- -- -- -- -- --      flipSquare (sym (uaDom≃ A g)))
-- -- -- -- -- -- -- -- -- -- -- --  EMelim.bSqP w = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- 𝔽-≡ : (A : Type ℓ) → ∀ n (g : Fin n ≃ Fin n) →
-- -- -- -- -- -- -- -- -- -- -- --       PathP (λ i → singl (𝔽h A n (emloop g i)))
-- -- -- -- -- -- -- -- -- -- -- --       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- -- -- -- -- -- -- -- -- -- --       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- -- -- -- -- -- -- -- -- -- -- 𝔽-≡ A n g = ΣPathP
-- -- -- -- -- -- -- -- -- -- -- --     (ua ({!!} ∙ₑ preCompEquiv (invEquiv g) ∙ₑ {!Iso-×^-F→ n!})
-- -- -- -- -- -- -- -- -- -- -- --    , flipSquare (symP-fromGoal {!  uaDom≃ A g!}))
-- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- --  s : {!!}
-- -- -- -- -- -- -- -- -- -- -- --  s = (uaDomIso A {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕍 : (A : Type ℓ) → ∀ n em → singl (𝔽h A n em)
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕍 A n = EMelim.f w
-- -- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- -- --  w : EMelim _
-- -- -- -- -- -- -- -- -- -- -- -- --                      (λ z → singl (𝔽h A n z))
-- -- -- -- -- -- -- -- -- -- -- -- --  EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
-- -- -- -- -- -- -- -- -- -- -- -- --  EMelim.b w = (A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n)))
-- -- -- -- -- -- -- -- -- -- -- -- --  EMelim.bPathP w = 𝔽-≡ A n
-- -- -- -- -- -- -- -- -- -- -- -- --  fst (EMelim.bSqP w g h i j) = 𝔽-sq-fst A n g h i j
-- -- -- -- -- -- -- -- -- -- -- -- --  snd (EMelim.bSqP w g h i j) k = {!!}

-- -- -- -- -- -- -- -- -- -- -- ism : ∀ n → Iso (Perm n) (Iso (Fin n) (Fin n))
-- -- -- -- -- -- -- -- -- -- -- ism n = (fst (PermGIsoIso n))

-- -- -- -- -- -- -- -- -- -- -- lookTab≡ : ∀ n → (Fin n → A) ≡ (A ×^ n)
-- -- -- -- -- -- -- -- -- -- -- lookTab≡ n = ua (isoToEquiv (invIso (Iso-×^-F→ n)))



-- -- -- -- -- -- -- -- -- -- -- perm𝔽≡ : ∀ n → (g : Perm n) →
-- -- -- -- -- -- -- -- -- -- --              singl {A = (Fin n → A) ≡ (Fin n → A) }
-- -- -- -- -- -- -- -- -- -- --              (λ i → permFin n g i → A) 
-- -- -- -- -- -- -- -- -- -- -- perm𝔽≡ {ℓ}  n = Relim.f (w {n})
-- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- --  open Relim

-- -- -- -- -- -- -- -- -- -- --  ∘T : ∀ {n} → (Σ ℕ  λ k → (suc k < n)) → _
-- -- -- -- -- -- -- -- -- -- --  ∘T {n} k = preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k) 


-- -- -- -- -- -- -- -- -- -- --  w : ∀ {n} → Relim (λ z → singl (λ i → permFin n z i → A))
-- -- -- -- -- -- -- -- -- -- --  isSetA w _ = isOfHLevelPlus 2 (isContrSingl _)
-- -- -- -- -- -- -- -- -- -- --  εA w = refl , refl
-- -- -- -- -- -- -- -- -- -- --  fst (∷A (w {n}) k (X , _)) = ∘T {n} k ₑ∙ₚ X
-- -- -- -- -- -- -- -- -- -- --  snd (∷A (w {n}) k (X , P)) =
-- -- -- -- -- -- -- -- -- -- --    dom-ₑ∙p
-- -- -- -- -- -- -- -- -- -- --      (fst (isoToEquiv (adjTIso' {n = n} k)))
-- -- -- -- -- -- -- -- -- -- --      (isInvolution-adjT n k)
-- -- -- -- -- -- -- -- -- -- --      P  
-- -- -- -- -- -- -- -- -- -- --  invoA (w {n}) k (X , P) = ΣPathP
-- -- -- -- -- -- -- -- -- -- --     ((invol-ₑ∙p _ _ X) ,
-- -- -- -- -- -- -- -- -- -- --       dom-invol-ₑ∙p (isSetFin {n = n}) _ _ P)

-- -- -- -- -- -- -- -- -- -- --  braidA (w {n}) k k< (X , P) =
-- -- -- -- -- -- -- -- -- -- --    ΣPathP (ₑ∙ₚ-comp³eq _ _ _
-- -- -- -- -- -- -- -- -- -- --         (equivEq (funExt λ x →
-- -- -- -- -- -- -- -- -- -- --                 cong (x ∘'_) 
-- -- -- -- -- -- -- -- -- -- --                   (cong (Iso.fun ∘ permuteIso n) (braid k k< ε))))
-- -- -- -- -- -- -- -- -- -- --       , dom-ₑ∙ₚ-comp³eq (isSetFin {n = n}) _ _ _ _
-- -- -- -- -- -- -- -- -- -- --             (cong (Iso.fun ∘ permuteIso n) (braid k k< ε)) P)
 
-- -- -- -- -- -- -- -- -- -- --  commA (w {n}) k l z (X , P) =
-- -- -- -- -- -- -- -- -- -- --     ΣPathP (
-- -- -- -- -- -- -- -- -- -- --          ₑ∙ₚ-comp²eq _ _ _
-- -- -- -- -- -- -- -- -- -- --              (equivEq (funExt λ x →
-- -- -- -- -- -- -- -- -- -- --                 cong (x ∘'_) 
-- -- -- -- -- -- -- -- -- -- --                   (sym ((cong (Iso.fun ∘ permuteIso n) (comm k l z ε))))
-- -- -- -- -- -- -- -- -- -- --          ))

-- -- -- -- -- -- -- -- -- -- --       , dom-ₑ∙ₚ-comp²eq (isSetFin {n = n}) _ _ _ _
-- -- -- -- -- -- -- -- -- -- --             (cong (Iso.fun ∘ permuteIso n) (comm k l z ε)) P)




-- -- -- -- -- -- -- -- -- -- -- perm𝔽sq : isGroupoid A → ∀ n → (g h : Perm n)
-- -- -- -- -- -- -- -- -- -- --              → Square
-- -- -- -- -- -- -- -- -- -- --                (fst (perm𝔽≡  n g))
-- -- -- -- -- -- -- -- -- -- --                (fst (perm𝔽≡ n (g · h)))
-- -- -- -- -- -- -- -- -- -- --                refl
-- -- -- -- -- -- -- -- -- -- --                (fst (perm𝔽≡ n h))
-- -- -- -- -- -- -- -- -- -- -- perm𝔽sq  isGroupoid-A n g h = Relim.f (w h) g
-- -- -- -- -- -- -- -- -- -- --  module QQQ where
-- -- -- -- -- -- -- -- -- -- --  open Relim

-- -- -- -- -- -- -- -- -- -- --  ∘T : (Σ ℕ  λ k → (suc k < n)) → _
-- -- -- -- -- -- -- -- -- -- --  ∘T k = preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k) 

-- -- -- -- -- -- -- -- -- -- --  isGpdFin→A : isGroupoid (Fin n → A) 
-- -- -- -- -- -- -- -- -- -- --  isGpdFin→A = isGroupoidΠ λ _ → isGroupoid-A

-- -- -- -- -- -- -- -- -- -- --  w : (h : Perm n) → Relim (λ g → 
-- -- -- -- -- -- -- -- -- -- --                Square
-- -- -- -- -- -- -- -- -- -- --                (fst (perm𝔽≡  n g))
-- -- -- -- -- -- -- -- -- -- --                (fst (perm𝔽≡ n (g · h)))
-- -- -- -- -- -- -- -- -- -- --                refl
-- -- -- -- -- -- -- -- -- -- --                (fst (perm𝔽≡ n h)))
-- -- -- -- -- -- -- -- -- -- --  isSetA (w h) _ =
-- -- -- -- -- -- -- -- -- -- --    isOfHLevelRetractFromIso 2
-- -- -- -- -- -- -- -- -- -- --      (invIso PathP→comm-Iso)
-- -- -- -- -- -- -- -- -- -- --      (isOfHLevel≡ 3 isGpdFin→A isGpdFin→A _ _)
-- -- -- -- -- -- -- -- -- -- --  εA (w h) j i = (fst (perm𝔽≡  n h)) (i ∧ j)
-- -- -- -- -- -- -- -- -- -- --  ∷A (w h) k X j i = (∘T k ₑ∙ₚ X j) i 
-- -- -- -- -- -- -- -- -- -- --  invoA (w h) k {xs} X l j i =
-- -- -- -- -- -- -- -- -- -- --     invol-ₑ∙p ((λ z x → z (adjT n k x)) ,
-- -- -- -- -- -- -- -- -- -- --                   involIsEquiv (λ x i b → x (isInvolution-adjT n k b i)))
-- -- -- -- -- -- -- -- -- -- --                   (λ x i z → x (isInvolution-adjT n k z i)) (X j) l i
-- -- -- -- -- -- -- -- -- -- --  braidA (w h) k k< X l j i =
-- -- -- -- -- -- -- -- -- -- --      ₑ∙ₚ-comp³eq
-- -- -- -- -- -- -- -- -- -- --         (((λ z x → z (adjT n (k , <-weaken {n = n} k<) x)) ,
-- -- -- -- -- -- -- -- -- -- --                   involIsEquiv
-- -- -- -- -- -- -- -- -- -- --                    (λ x i b → x (isInvolution-adjT n (k , <-weaken {n = n} k<) b i))))
-- -- -- -- -- -- -- -- -- -- --         (((λ z x → z (adjT n (suc k , k<) x)) ,
-- -- -- -- -- -- -- -- -- -- --                   involIsEquiv (λ x i b → x (isInvolution-adjT n (suc k , k<) b i))))
-- -- -- -- -- -- -- -- -- -- --         (X j)
-- -- -- -- -- -- -- -- -- -- --          (equivEq (funExt λ x →
-- -- -- -- -- -- -- -- -- -- --         cong (x ∘'_) 
-- -- -- -- -- -- -- -- -- -- --           (cong (Iso.fun ∘ permuteIso n) (braid k k< ε))))
-- -- -- -- -- -- -- -- -- -- --           l i 


-- -- -- -- -- -- -- -- -- -- --  commA (w h) k l' z X l j i =
-- -- -- -- -- -- -- -- -- -- --     ₑ∙ₚ-comp²eq
-- -- -- -- -- -- -- -- -- -- --       (((λ z x → z (adjT n l' x)) ,
-- -- -- -- -- -- -- -- -- -- --                   involIsEquiv (λ x i b → x (isInvolution-adjT n l' b i))))
-- -- -- -- -- -- -- -- -- -- --       (((λ z x → z (adjT n k x)) ,
-- -- -- -- -- -- -- -- -- -- --                   involIsEquiv (λ x i b → x (isInvolution-adjT n k b i))))
-- -- -- -- -- -- -- -- -- -- --       (X j)
-- -- -- -- -- -- -- -- -- -- --        (equivEq (funExt (λ x → cong (x ∘'_)
-- -- -- -- -- -- -- -- -- -- --         (sym ((cong (Iso.fun ∘ permuteIso n) (comm k l' z ε)))) )))
-- -- -- -- -- -- -- -- -- -- --        l i


-- -- -- -- -- -- -- -- -- -- -- perm𝔽sq-Snd : (isGroupoid-A : isGroupoid A) → ∀ n → (g h : Perm n)
-- -- -- -- -- -- -- -- -- -- --              → SquareP
-- -- -- -- -- -- -- -- -- -- --                   (λ i j → (𝔽in' n (emcomp g h i j) → A) ≡
-- -- -- -- -- -- -- -- -- -- --                             perm𝔽sq isGroupoid-A n g h i j)
-- -- -- -- -- -- -- -- -- -- --                (flipSquare (snd (perm𝔽≡  n g)))
-- -- -- -- -- -- -- -- -- -- --                (flipSquare (snd (perm𝔽≡  n (g · h))))
-- -- -- -- -- -- -- -- -- -- --                refl
-- -- -- -- -- -- -- -- -- -- --                (flipSquare (snd (perm𝔽≡  n h)))
-- -- -- -- -- -- -- -- -- -- -- perm𝔽sq-Snd  isGroupoid-A n g h = RelimProp.f (w h) g
-- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- --  open RelimProp

-- -- -- -- -- -- -- -- -- -- --  ∘T : (Σ ℕ  λ k → (suc k < n)) → _
-- -- -- -- -- -- -- -- -- -- --  ∘T k = preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k) 

-- -- -- -- -- -- -- -- -- -- --  isGpdFin→A : isGroupoid (Fin n → A) 
-- -- -- -- -- -- -- -- -- -- --  isGpdFin→A = isGroupoidΠ λ _ → isGroupoid-A

-- -- -- -- -- -- -- -- -- -- --  w : (h : Perm n) → RelimProp (λ g → 
-- -- -- -- -- -- -- -- -- -- --                SquareP
-- -- -- -- -- -- -- -- -- -- --                   (λ i j → (𝔽in' n (emcomp g h i j) → A) ≡
-- -- -- -- -- -- -- -- -- -- --                             perm𝔽sq isGroupoid-A n g h i j)
-- -- -- -- -- -- -- -- -- -- --                (flipSquare (snd (perm𝔽≡  n g)))
-- -- -- -- -- -- -- -- -- -- --                (flipSquare (snd (perm𝔽≡  n (g · h))))
-- -- -- -- -- -- -- -- -- -- --                (refl)
-- -- -- -- -- -- -- -- -- -- --                (flipSquare (snd (perm𝔽≡  n h))))
-- -- -- -- -- -- -- -- -- -- --  isPropA (w h) x =
-- -- -- -- -- -- -- -- -- -- --    isOfHLevelRespectEquiv 1
-- -- -- -- -- -- -- -- -- -- --     (invEquiv (PathP≃Path _ _ _))
-- -- -- -- -- -- -- -- -- -- --       (isOfHLevelRespectEquiv 2
-- -- -- -- -- -- -- -- -- -- --         (invEquiv (PathP≃Path _ _ _))
-- -- -- -- -- -- -- -- -- -- --          ((isOfHLevelRespectEquiv 3
-- -- -- -- -- -- -- -- -- -- --         (invEquiv (PathP≃Path _ _ _))
-- -- -- -- -- -- -- -- -- -- --          (isOfHLevel≡ 3 isGpdFin→A isGpdFin→A ) _ _)) _ _)
-- -- -- -- -- -- -- -- -- -- --  εA (w h) i j l = (snd (perm𝔽≡  n h)) l (i ∧ j)
-- -- -- -- -- -- -- -- -- -- --  ∷A (w h) k {xs} X i j l =    
-- -- -- -- -- -- -- -- -- -- --    Glue (X i j l) {i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l}
-- -- -- -- -- -- -- -- -- -- --     λ o → T i j l o , (E i j l o) , isEqE i j l o
-- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- --     T : ∀ i j l → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l) (Type _)
-- -- -- -- -- -- -- -- -- -- --     T i j l = λ {
-- -- -- -- -- -- -- -- -- -- --          (i = i0) → _
-- -- -- -- -- -- -- -- -- -- --         ;(i = i1) → _
-- -- -- -- -- -- -- -- -- -- --         ;(j = i0) → _ 
-- -- -- -- -- -- -- -- -- -- --         ;(j = i1) → _
-- -- -- -- -- -- -- -- -- -- --         ;(l = i0) → _ 
-- -- -- -- -- -- -- -- -- -- --         ;(l = i1) → _
-- -- -- -- -- -- -- -- -- -- --         }
-- -- -- -- -- -- -- -- -- -- --     Ei0 : ∀ l j →  T i0 j l 1=1 ≃ X i0 j l
-- -- -- -- -- -- -- -- -- -- --     Ei0 l j = (unglue-dom-ₑ∙p
-- -- -- -- -- -- -- -- -- -- --                (fst (isoToEquiv (adjTIso' {n = n} k)))
-- -- -- -- -- -- -- -- -- -- --                (isInvolution-adjT n k)
-- -- -- -- -- -- -- -- -- -- --              (snd (perm𝔽≡ n xs)) l j)

-- -- -- -- -- -- -- -- -- -- --     Ei1 : ∀ l j →  T i1 j l 1=1 ≃ X i1 j l
-- -- -- -- -- -- -- -- -- -- --     Ei1 l j = (unglue-dom-ₑ∙p
-- -- -- -- -- -- -- -- -- -- --                (fst (isoToEquiv (adjTIso' {n = n} k)))
-- -- -- -- -- -- -- -- -- -- --                (isInvolution-adjT n k)
-- -- -- -- -- -- -- -- -- -- --              (snd (perm𝔽≡ n (xs · h))) l j)

-- -- -- -- -- -- -- -- -- -- --     li0Sq : SquareP (λ i j → 𝔽in' n (emcomp xs h i j) → 𝔽in' n (emcomp (k ∷ xs) h i j))
-- -- -- -- -- -- -- -- -- -- --                 _ _ _ _
-- -- -- -- -- -- -- -- -- -- --     li0Sq =
-- -- -- -- -- -- -- -- -- -- --        isSet→SquareP (λ i j → isSet→ (snd (h𝔽in' n (emcomp (k ∷ xs) h i j))))
-- -- -- -- -- -- -- -- -- -- --           (λ j x₁ → (fst
-- -- -- -- -- -- -- -- -- -- --                   (glue-invol-ₑ∙p (involEquiv {f = adjT n k} (isInvolution-adjT n k))
-- -- -- -- -- -- -- -- -- -- --                    (isInvolution-adjT n k) (λ i₂ → permFin n (xs) i₂) j)
-- -- -- -- -- -- -- -- -- -- --                   x₁))
-- -- -- -- -- -- -- -- -- -- --                 (λ j x₁ → (fst
-- -- -- -- -- -- -- -- -- -- --                   (glue-invol-ₑ∙p (involEquiv {f = adjT n k} (isInvolution-adjT n k))
-- -- -- -- -- -- -- -- -- -- --                    (isInvolution-adjT n k) (λ i₂ → permFin n (xs · h) i₂) j)
-- -- -- -- -- -- -- -- -- -- --                   x₁))
-- -- -- -- -- -- -- -- -- -- --                 (λ _ → adjT n k)
-- -- -- -- -- -- -- -- -- -- --                 λ _ → idfun _

-- -- -- -- -- -- -- -- -- -- --     E : ∀ i j l → PartialP (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l) (λ o → T i j l o → X i j l)
-- -- -- -- -- -- -- -- -- -- --     E i j l = λ {
-- -- -- -- -- -- -- -- -- -- --          (i = i0) → fst (Ei0 l j)
-- -- -- -- -- -- -- -- -- -- --         ;(i = i1) →  fst (unglue-dom-ₑ∙p
-- -- -- -- -- -- -- -- -- -- --                (fst (isoToEquiv (adjTIso' {n = n} k)))
-- -- -- -- -- -- -- -- -- -- --                (isInvolution-adjT n k)
-- -- -- -- -- -- -- -- -- -- --              (snd (perm𝔽≡ n (xs · h))) l j)
-- -- -- -- -- -- -- -- -- -- --         ;(j = i0) → _∘' (adjT n k)
-- -- -- -- -- -- -- -- -- -- --         ;(j = i1) → idfun _
-- -- -- -- -- -- -- -- -- -- --         ;(l = i0) → _∘' (li0Sq i j)  
-- -- -- -- -- -- -- -- -- -- --         ;(l = i1) → fst (unglue-ₑ∙p (∘T k) (perm𝔽sq isGroupoid-A n (xs) h i) j ) 
-- -- -- -- -- -- -- -- -- -- --         }

-- -- -- -- -- -- -- -- -- -- --     isEqE : ∀ i j l → PartialP (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l) (λ o →
-- -- -- -- -- -- -- -- -- -- --          isEquiv (E i j l o))
-- -- -- -- -- -- -- -- -- -- --     isEqE i j l = λ {
-- -- -- -- -- -- -- -- -- -- --          (i = i0) → snd (Ei0 l j)
-- -- -- -- -- -- -- -- -- -- --         ;(i = i1) → snd (Ei1 l j)
-- -- -- -- -- -- -- -- -- -- --         ;(j = i0) → isProp→PathP
-- -- -- -- -- -- -- -- -- -- --             (λ i → isPropIsEquiv (E i j l 1=1))
-- -- -- -- -- -- -- -- -- -- --             (snd (Ei0 l j))
-- -- -- -- -- -- -- -- -- -- --             (snd (Ei1 l j)) i
-- -- -- -- -- -- -- -- -- -- --         ;(j = i1) → isProp→PathP
-- -- -- -- -- -- -- -- -- -- --             (λ i → isPropIsEquiv (E i j l 1=1))
-- -- -- -- -- -- -- -- -- -- --             (snd (Ei0 l j))
-- -- -- -- -- -- -- -- -- -- --             (snd (Ei1 l j)) i
-- -- -- -- -- -- -- -- -- -- --         ;(l = i0) → isProp→PathP
-- -- -- -- -- -- -- -- -- -- --             (λ i → isPropIsEquiv (E i j l 1=1))
-- -- -- -- -- -- -- -- -- -- --             (snd (Ei0 l j))
-- -- -- -- -- -- -- -- -- -- --             (snd (Ei1 l j)) i  
-- -- -- -- -- -- -- -- -- -- --         ;(l = i1) → isProp→PathP
-- -- -- -- -- -- -- -- -- -- --             (λ i → isPropIsEquiv (E i j l 1=1))
-- -- -- -- -- -- -- -- -- -- --             (snd (Ei0 l j))
-- -- -- -- -- -- -- -- -- -- --             (snd (Ei1 l j)) i 
-- -- -- -- -- -- -- -- -- -- --         }


-- -- -- -- -- -- -- -- -- -- -- perm𝔽Si : (isGroupoid A) → ∀ n →  (em : ℙrm' n) →
-- -- -- -- -- -- -- -- -- -- --              singl (𝔽in' n em → A) 
-- -- -- -- -- -- -- -- -- -- -- perm𝔽Si  isGroupoid-A n = EMelim.f w
-- -- -- -- -- -- -- -- -- -- --  where

-- -- -- -- -- -- -- -- -- -- --  w : EMelim (PermG n) (λ z → singl (𝔽in' n z → _))
-- -- -- -- -- -- -- -- -- -- --  EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
-- -- -- -- -- -- -- -- -- -- --  EMelim.b w = (𝔽in' n embase → A) , refl
-- -- -- -- -- -- -- -- -- -- --  EMelim.bPathP w g =  
-- -- -- -- -- -- -- -- -- -- --   let z = perm𝔽≡ n g
-- -- -- -- -- -- -- -- -- -- --   in ΣPathP (fst z , flipSquare (snd z))
-- -- -- -- -- -- -- -- -- -- --  fst (EMelim.bSqP w g h i j) = perm𝔽sq   isGroupoid-A n g h i j
-- -- -- -- -- -- -- -- -- -- --  snd (EMelim.bSqP w g h i j) = perm𝔽sq-Snd  isGroupoid-A n g h i j



-- -- -- -- -- -- -- -- -- -- -- perm𝔽 : {A : Type ℓ} → (isGroupoid A) → ∀ n → (em : ℙrm' n) → Type ℓ 
-- -- -- -- -- -- -- -- -- -- -- perm𝔽 isGA n = fst ∘ perm𝔽Si isGA n



-- -- -- -- -- -- -- -- -- -- -- adjT×^ : ∀ {n} → ℕ →
-- -- -- -- -- -- -- -- -- -- --              (A ×^ n) → (A ×^ n)
-- -- -- -- -- -- -- -- -- -- -- adjT×^ {n = zero} _ x = x
-- -- -- -- -- -- -- -- -- -- -- adjT×^ {n = suc zero} _ x = x
-- -- -- -- -- -- -- -- -- -- -- adjT×^ {n = suc (suc n)} zero (x , x' , xs) = (x' , x , xs)
-- -- -- -- -- -- -- -- -- -- -- adjT×^ {n = suc (suc n)} (suc k) (x , xs) =
-- -- -- -- -- -- -- -- -- -- --    x , adjT×^ k xs

-- -- -- -- -- -- -- -- -- -- -- isInvo-adjT×^ : ∀ {n} → ∀ k → isInvolution (adjT×^  {n} k) 
-- -- -- -- -- -- -- -- -- -- -- isInvo-adjT×^ {n = zero} k x = refl
-- -- -- -- -- -- -- -- -- -- -- isInvo-adjT×^ {n = suc zero} k x = refl
-- -- -- -- -- -- -- -- -- -- -- isInvo-adjT×^ {n = suc (suc n)} zero x = refl
-- -- -- -- -- -- -- -- -- -- -- isInvo-adjT×^ {n = suc (suc n)} (suc k) (x , xs) =
-- -- -- -- -- -- -- -- -- -- --  cong (x ,_) (isInvo-adjT×^ k xs)


-- -- -- -- -- -- -- -- -- -- -- braid-adjT×^ : ∀ {n} → ∀ k →  suc (suc k) < n → ∀ v → 
-- -- -- -- -- -- -- -- -- -- --   (adjT×^  {n} k ∘ adjT×^  {n} (suc k) ∘ adjT×^  {n} (k)) v
-- -- -- -- -- -- -- -- -- -- --   ≡ (adjT×^  {n} (suc k) ∘ adjT×^  {n} (k) ∘ adjT×^  {n} (suc k)) v
-- -- -- -- -- -- -- -- -- -- -- braid-adjT×^ {n = suc (suc (suc n))} zero x _ = refl
-- -- -- -- -- -- -- -- -- -- -- braid-adjT×^ {n = suc (suc n)} (suc k) x (v , vs) =
-- -- -- -- -- -- -- -- -- -- --   cong (v ,_) (braid-adjT×^ k x vs)

-- -- -- -- -- -- -- -- -- -- -- comm-adjT×^ : ∀ {n} → ∀ k l → (k< : (suc k) < n) (l< : (suc l) < n) → 
-- -- -- -- -- -- -- -- -- -- --   A.commT k l → ∀ v →  
-- -- -- -- -- -- -- -- -- -- --   (adjT×^  {n} l
-- -- -- -- -- -- -- -- -- -- --     ∘ adjT×^  {n} k ) v
-- -- -- -- -- -- -- -- -- -- --   ≡ (adjT×^  {n} k
-- -- -- -- -- -- -- -- -- -- --     ∘ adjT×^  {n} l ) v
-- -- -- -- -- -- -- -- -- -- -- comm-adjT×^ {n = suc (suc (suc n))} zero (suc (suc l)) k< l< x v = refl
-- -- -- -- -- -- -- -- -- -- -- comm-adjT×^ {n = suc (suc n)} (suc k) (suc (suc l)) k< l< x (v , vs) =
-- -- -- -- -- -- -- -- -- -- --    cong (v ,_) (comm-adjT×^
-- -- -- -- -- -- -- -- -- -- --     {n = suc n} k (suc l) k< l< x vs)


-- -- -- -- -- -- -- -- -- -- -- adjT×^ : ∀ {n} → ℕ →
-- -- -- -- -- -- -- -- -- -- --   Iso (A ×^ n)
-- -- -- -- -- -- -- -- -- -- --       (A ×^ n)
-- -- -- -- -- -- -- -- -- -- -- adjT×^ {n} k =
-- -- -- -- -- -- -- -- -- -- --  involIso {f = adjT×^ {n} k} (isInvo-adjT×^ {n} k)

-- -- -- -- -- -- -- -- -- -- -- adjT×^≃ : ∀ {n} → ℕ →
-- -- -- -- -- -- -- -- -- -- --       (A ×^ n) ≃ (A ×^ n)
-- -- -- -- -- -- -- -- -- -- -- adjT×^≃ {n} k =
-- -- -- -- -- -- -- -- -- -- --  involEquiv {f = adjT×^ {n} k} (isInvo-adjT×^ {n} k)


-- -- -- -- -- -- -- -- -- -- -- glue-adjT≃' : ∀ {ℓ} {A : Type ℓ} → ∀ n k
-- -- -- -- -- -- -- -- -- -- --            →
-- -- -- -- -- -- -- -- -- -- --            PathP (λ i → (A ×^ n) → (adjT×^≃  {n = n} k ₑ∙ₚ refl) i)
-- -- -- -- -- -- -- -- -- -- --              (adjT×^ {n = n} k)
-- -- -- -- -- -- -- -- -- -- --              (idfun _)
-- -- -- -- -- -- -- -- -- -- -- glue-adjT≃'  zero k =
-- -- -- -- -- -- -- -- -- -- --    ua-gluePathExt (adjT×^  {n = zero} k ,
-- -- -- -- -- -- -- -- -- -- --      involIsEquiv (isInvo-adjT×^  {n = zero} k))
-- -- -- -- -- -- -- -- -- -- -- glue-adjT≃'  (suc zero) k =
-- -- -- -- -- -- -- -- -- -- --       ua-gluePathExt (adjT×^  {n = suc zero} k ,
-- -- -- -- -- -- -- -- -- -- --      involIsEquiv (isInvo-adjT×^  {n = suc zero} k))
-- -- -- -- -- -- -- -- -- -- -- -- glue-adjT≃'  (suc (suc n)) k i x =
-- -- -- -- -- -- -- -- -- -- -- --   glue (λ { (i = i0) → {!!} ;
-- -- -- -- -- -- -- -- -- -- -- --     (i = i1) → {!!} }) {!!}
-- -- -- -- -- -- -- -- -- -- -- glue-adjT≃'  (suc (suc n)) zero i x =
-- -- -- -- -- -- -- -- -- -- --   glue (λ { (i = i0) → fst (snd x) , fst x , snd (snd x) ;
-- -- -- -- -- -- -- -- -- -- --     (i = i1) → x }) x
-- -- -- -- -- -- -- -- -- -- -- glue-adjT≃'  (suc (suc n)) (suc k) i (x , xs) =
-- -- -- -- -- -- -- -- -- -- --   glue (λ { (i = i0) → x , adjT×^ k xs ;
-- -- -- -- -- -- -- -- -- -- --     (i = i1) → x , xs })
-- -- -- -- -- -- -- -- -- -- --     (x , unglue (i ∨ ~ i) (glue-adjT≃'  (suc n) k i xs))


-- -- -- -- -- -- -- -- -- -- -- glue-adjT≃ : ∀ {ℓ} {A : Type ℓ} → ∀ n k
-- -- -- -- -- -- -- -- -- -- --        → (X : (A ×^ n) ≡ (A ×^ n)) →
-- -- -- -- -- -- -- -- -- -- --            PathP (λ i → X i ≃ (adjT×^≃ k ₑ∙ₚ X) i) (adjT×^≃ k)
-- -- -- -- -- -- -- -- -- -- --            (idEquiv (X i1))
-- -- -- -- -- -- -- -- -- -- -- glue-adjT≃  n k = glue-invol-ₑ∙p {B = A ×^ n} (adjT×^≃  {n} k)
-- -- -- -- -- -- -- -- -- -- --    (isInvo-adjT×^ {n = n} k) 

-- -- -- -- -- -- -- -- -- -- -- -- withAdjTlook : ∀ n → Σ ℕ (λ k₁ → suc k₁ < n) →  A ×^ n → Fin n → A
-- -- -- -- -- -- -- -- -- -- -- -- withAdjTlook n x x₁ x₂ = {!n!}

-- -- -- -- -- -- -- -- -- -- -- lawAdj : ∀ n k → (f : Fin n → A) → tabulate {n = n}
-- -- -- -- -- -- -- -- -- -- --       (f ∘ adjT n k)
-- -- -- -- -- -- -- -- -- -- --       ≡ adjT×^ (fst k) (tabulate f)
-- -- -- -- -- -- -- -- -- -- -- lawAdj (suc (suc n)) (zero , snd₁) f = refl
-- -- -- -- -- -- -- -- -- -- -- lawAdj (suc (suc n)) (suc k , k<) f =
-- -- -- -- -- -- -- -- -- -- --   cong ((f (zero , _)) ,_) (lawAdj (suc n) (k , k<) (f ∘ sucF) )

-- -- -- -- -- -- -- -- -- -- -- lawAdj' : ∀ n k → (v : A ×^ n) →
-- -- -- -- -- -- -- -- -- -- --                 lookup v ∘ (adjT n k)
-- -- -- -- -- -- -- -- -- -- --             ≡  lookup (adjT×^ {n = n} (fst k) v)
-- -- -- -- -- -- -- -- -- -- -- lawAdj' (suc (suc n)) (zero , k<) v =
-- -- -- -- -- -- -- -- -- -- --   funExt (uncurry (cases (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --     (cases (λ _ → refl) λ _ _ → refl)))
-- -- -- -- -- -- -- -- -- -- -- lawAdj' (suc (suc (suc n))) (suc k , k<) v =
-- -- -- -- -- -- -- -- -- -- --   funExt (uncurry (cases (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --      λ kk y → funExt⁻ (lawAdj' (suc (suc n)) (k , k<) (snd v)) (kk , y)) )


-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq'' : ∀ n k → PathP (λ i →
-- -- -- -- -- -- -- -- -- -- --       ua (isoToEquiv (invIso (Iso-×^-F→  n))) i →
-- -- -- -- -- -- -- -- -- -- --       ua (isoToEquiv (invIso (Iso-×^-F→  n))) i)
-- -- -- -- -- -- -- -- -- -- --         (_∘' adjT n k)
-- -- -- -- -- -- -- -- -- -- --         (adjT×^ {n = n} (fst k))
-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq''  (suc (suc n)) (zero , k<) i x =
-- -- -- -- -- -- -- -- -- -- --  let e = (isoToEquiv (invIso (Iso-×^-F→  (suc (suc n)))))
-- -- -- -- -- -- -- -- -- -- --  in ua-glue e i (λ { (i = i0) → x ∘' adjT (suc (suc n)) (zero , k<)  })
-- -- -- -- -- -- -- -- -- -- --        (inS (adjT×^ zero (ua-unglue e i x)))
-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq''  (suc (suc (suc n))) (suc k , k<) i x =
-- -- -- -- -- -- -- -- -- -- --  let e = (isoToEquiv (invIso (Iso-×^-F→  (suc (suc (suc n))))))
-- -- -- -- -- -- -- -- -- -- --      e' = (isoToEquiv (invIso (Iso-×^-F→  (suc (suc n)))))
-- -- -- -- -- -- -- -- -- -- --      v = ((ua-unglue e i x))
-- -- -- -- -- -- -- -- -- -- --  in ua-glue e i (λ { (i = i0) → x ∘' adjT (suc (suc (suc n))) (suc k , k<)  })
-- -- -- -- -- -- -- -- -- -- --        (inS (fst v ,
-- -- -- -- -- -- -- -- -- -- --           ua-unglue e' i (adjT-×-sq''  (suc (suc n)) (k , k<) i
-- -- -- -- -- -- -- -- -- -- --            (ua-glue e' i
-- -- -- -- -- -- -- -- -- -- --              (λ { (i = i0) → x ∘' sucF}) (inS (snd v))))))

-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq : ∀ n k → PathP (λ i →
-- -- -- -- -- -- -- -- -- -- --       ua (isoToEquiv (invIso (Iso-×^-F→  n))) i ≃
-- -- -- -- -- -- -- -- -- -- --       ua (isoToEquiv (invIso (Iso-×^-F→  n))) i)
-- -- -- -- -- -- -- -- -- -- --         (preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k) )
-- -- -- -- -- -- -- -- -- -- --         (adjT×^≃ {n = n} (fst k))
-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq n k = ΣPathPProp (isPropIsEquiv) (adjT-×-sq'' n k)

-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq-invo : ∀ n k →
-- -- -- -- -- -- -- -- -- -- --  PathP (λ j → isInvolution (fst (adjT-×-sq  n k j)))
-- -- -- -- -- -- -- -- -- -- --    (λ f → funExt (cong f ∘ isInvolution-adjT n k))
-- -- -- -- -- -- -- -- -- -- --    (isInvo-adjT×^ {n = n} (fst k) )
-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq-invo  (suc (suc n)) (zero , k<) =
-- -- -- -- -- -- -- -- -- -- --  let e = (isoToEquiv (invIso (Iso-×^-F→  (suc (suc n)))))     
-- -- -- -- -- -- -- -- -- -- --  in λ i x j →
-- -- -- -- -- -- -- -- -- -- --       ua-glue e i 
-- -- -- -- -- -- -- -- -- -- --         (λ { ( i = i0) →
-- -- -- -- -- -- -- -- -- -- --              x ∘ (funExt (isInvolution-adjT (suc (suc n)) (zero , k<)) j) })
-- -- -- -- -- -- -- -- -- -- --              (inS (ua-unglue e i x))
-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq-invo  (suc (suc (suc n))) ((suc k) , k<) =
-- -- -- -- -- -- -- -- -- -- --  let e = (isoToEquiv (invIso (Iso-×^-F→  (suc (suc (suc n))))))
-- -- -- -- -- -- -- -- -- -- --      e' = (isoToEquiv (invIso (Iso-×^-F→  (suc (suc n)))))
     
-- -- -- -- -- -- -- -- -- -- --  in λ i x j →
-- -- -- -- -- -- -- -- -- -- --       let v = ((ua-unglue e i x))
-- -- -- -- -- -- -- -- -- -- --       in ua-glue e i 
-- -- -- -- -- -- -- -- -- -- --         (λ { ( i = i0) →
-- -- -- -- -- -- -- -- -- -- --              x ∘ (funExt (isInvolution-adjT (suc (suc (suc n))) (suc k , k<)) j) })
-- -- -- -- -- -- -- -- -- -- --              (inS (fst v ,
-- -- -- -- -- -- -- -- -- -- --                 ua-unglue e' i
-- -- -- -- -- -- -- -- -- -- --                  ( adjT-×-sq-invo  (suc (suc n)) (k , k<)
-- -- -- -- -- -- -- -- -- -- --                     i (ua-glue e' i (λ { (i = i0) → x ∘' sucF }) (inS (snd v))) j)
-- -- -- -- -- -- -- -- -- -- --                   ))

-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq-braid : ∀ n k k< →
-- -- -- -- -- -- -- -- -- -- --  PathP (λ j → (x : ua (isoToEquiv (invIso (Iso-×^-F→  n))) j) →
-- -- -- -- -- -- -- -- -- -- --          (adjT-×-sq'' n (k , <-weaken {n = n} k<) j
-- -- -- -- -- -- -- -- -- -- --       ∘' adjT-×-sq'' n (suc k , k<) j
-- -- -- -- -- -- -- -- -- -- --       ∘' adjT-×-sq'' n (k , <-weaken {n = n} k<) j) x ≡
-- -- -- -- -- -- -- -- -- -- --       (adjT-×-sq'' n (suc k , k<) j
-- -- -- -- -- -- -- -- -- -- --       ∘' adjT-×-sq'' n (k , <-weaken {n = n} k<) j
-- -- -- -- -- -- -- -- -- -- --       ∘' adjT-×-sq'' n (suc k , k<) j) x)
-- -- -- -- -- -- -- -- -- -- --    (λ x → cong (x ∘'_) 
-- -- -- -- -- -- -- -- -- -- --           (cong (Iso.fun ∘ permuteIso n) (braid k k< ε)))
-- -- -- -- -- -- -- -- -- -- --    (braid-adjT×^  {n = n} k k<)
-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq-braid  (suc (suc (suc n))) zero  k< =
-- -- -- -- -- -- -- -- -- -- --  let e = (isoToEquiv (invIso (Iso-×^-F→  (suc (suc (suc n))))))     
-- -- -- -- -- -- -- -- -- -- --  in λ i x j →
-- -- -- -- -- -- -- -- -- -- --       ua-glue e i 
-- -- -- -- -- -- -- -- -- -- --         (λ { ( i = i0) → x ∘ adjT-braid (suc (suc (suc n))) zero k< j })
-- -- -- -- -- -- -- -- -- -- --              (inS (braid-adjT×^  {n = (suc (suc (suc n)))}
-- -- -- -- -- -- -- -- -- -- --               zero k< (ua-unglue e i x) j))
-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq-braid  (suc (suc (suc (suc n)))) (suc k)  k< =
-- -- -- -- -- -- -- -- -- -- --  let e = (isoToEquiv (invIso (Iso-×^-F→  (suc (suc (suc (suc n)))))))
-- -- -- -- -- -- -- -- -- -- --      e' = (isoToEquiv (invIso (Iso-×^-F→  (suc (suc (suc n))))))
     
-- -- -- -- -- -- -- -- -- -- --  in λ i x j →
-- -- -- -- -- -- -- -- -- -- --       let v = ((ua-unglue e i x))
-- -- -- -- -- -- -- -- -- -- --       in ua-glue e i 
-- -- -- -- -- -- -- -- -- -- --         (λ { ( i = i0) → x ∘ adjT-braid (suc (suc (suc (suc n)))) (suc k) k< j})
-- -- -- -- -- -- -- -- -- -- --              (inS (fst v ,
-- -- -- -- -- -- -- -- -- -- --                 ua-unglue e' i
-- -- -- -- -- -- -- -- -- -- --                  ( adjT-×-sq-braid  (suc (suc (suc n))) k  k<
-- -- -- -- -- -- -- -- -- -- --                     i (ua-glue e' i (λ { (i = i0) → x ∘' sucF }) (inS (snd v))) j)
-- -- -- -- -- -- -- -- -- -- --                   ))

-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq-commTy : {A : Type ℓ} → ℕ → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq-commTy  n = ∀ k l → (z : A.commT (fst k) (fst l)) →
-- -- -- -- -- -- -- -- -- -- --  PathP (λ j → (x : ua (isoToEquiv (invIso (Iso-×^-F→  n))) j) →
-- -- -- -- -- -- -- -- -- -- --          (adjT-×-sq'' n l j ∘' adjT-×-sq'' n k j) x ≡
-- -- -- -- -- -- -- -- -- -- --       (adjT-×-sq'' n k j ∘' adjT-×-sq'' n l j) x)
-- -- -- -- -- -- -- -- -- -- --    (λ x → cong (x ∘'_) 
-- -- -- -- -- -- -- -- -- -- --           (cong (Iso.fun ∘ permuteIso n) (sym (comm k l z ε))))
-- -- -- -- -- -- -- -- -- -- --    (comm-adjT×^  (fst k) (fst l) (snd k) (snd l) z)

-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq-comm : ∀ n → adjT-×-sq-commTy  n
-- -- -- -- -- -- -- -- -- -- -- adjT-×-sq-comm  =
-- -- -- -- -- -- -- -- -- -- --   ℕ.elim (uncurry (λ _ ()))
-- -- -- -- -- -- -- -- -- -- --    s
-- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- --  s : (n : ℕ) → adjT-×-sq-commTy n → adjT-×-sq-commTy (suc n)
-- -- -- -- -- -- -- -- -- -- --  s (suc (suc (suc n))) _ (zero , k<) (suc (suc l) , l<) z =
-- -- -- -- -- -- -- -- -- -- --   let e = (isoToEquiv (invIso (Iso-×^-F→  (suc (suc (suc (suc n)))))))
-- -- -- -- -- -- -- -- -- -- --       e' = (isoToEquiv (invIso (Iso-×^-F→  (suc (suc n)))))
-- -- -- -- -- -- -- -- -- -- --   in λ i x j →
-- -- -- -- -- -- -- -- -- -- --       let (v0 , v1 , v) = ua-unglue e i x
-- -- -- -- -- -- -- -- -- -- --       in glue
-- -- -- -- -- -- -- -- -- -- --            (λ { (i = i0) → 
-- -- -- -- -- -- -- -- -- -- --                   x ∘ funExt (adjT-comm (suc (suc (suc (suc n))))
-- -- -- -- -- -- -- -- -- -- --                                    (zero , k<) (suc (suc l) , l<) z) ( ~ j)
-- -- -- -- -- -- -- -- -- -- --               ; (i = i1) → _
-- -- -- -- -- -- -- -- -- -- --               }) (v1 , v0 ,
-- -- -- -- -- -- -- -- -- -- --                    ua-unglue e' i (adjT-×-sq'' (suc (suc n)) ((l , l<))
-- -- -- -- -- -- -- -- -- -- --                             i ( ua-glue e' i
-- -- -- -- -- -- -- -- -- -- --                                  (λ { (i = i0) → x ∘ sucF ∘ sucF})
-- -- -- -- -- -- -- -- -- -- --                                   (inS ((snd (snd (ua-unglue e i x))))))))

-- -- -- -- -- -- -- -- -- -- --  s (suc (suc (suc n))) S (suc k , k<) (suc (suc (suc l)) , l<) z =
-- -- -- -- -- -- -- -- -- -- --    λ i x j →
-- -- -- -- -- -- -- -- -- -- --       let v = ((unglue (i ∨ ~ i) x))
-- -- -- -- -- -- -- -- -- -- --       in glue 
-- -- -- -- -- -- -- -- -- -- --         (λ { ( i = i0) → x ∘ funExt (adjT-comm (suc (suc (suc (suc n))))
-- -- -- -- -- -- -- -- -- -- --                       (suc k , k<) (suc (suc (suc l)) , l<) z) (~ j)
-- -- -- -- -- -- -- -- -- -- --              ;(i = i1) → _
-- -- -- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- -- -- --              ((fst v ,
-- -- -- -- -- -- -- -- -- -- --                 unglue (i ∨ ~ i)
-- -- -- -- -- -- -- -- -- -- --                 (S (k , k<) (suc (suc l) , l<) z i
-- -- -- -- -- -- -- -- -- -- --                      (glue (λ { (i = i0) → x ∘' sucF
-- -- -- -- -- -- -- -- -- -- --                                ; (i = i1) → _}) ((snd v))) j)))
   
 


-- -- -- -- -- -- -- -- -- -- -- 𝕍Si : (isGrpA : isGroupoid A) → ∀ n →  (em : ℙrm' n) →
-- -- -- -- -- -- -- -- -- -- --              singl (perm𝔽 isGrpA n em) 
-- -- -- -- -- -- -- -- -- -- -- 𝕍Si  isGrpA n = {!!} --EMelim.f w
-- -- -- -- -- -- -- -- -- -- --  where

-- -- -- -- -- -- -- -- -- -- --  𝕍≡ : ∀ n → (g : Perm n) →
-- -- -- -- -- -- -- -- -- -- --               singlP (λ i →
-- -- -- -- -- -- -- -- -- -- --                 ua (isoToEquiv (invIso (Iso-×^-F→  n))) i
-- -- -- -- -- -- -- -- -- -- --               ≡ ua (isoToEquiv (invIso (Iso-×^-F→  n))) i)
-- -- -- -- -- -- -- -- -- -- --               --{A = (A ×^ n) ≡ (A ×^ n) }
-- -- -- -- -- -- -- -- -- -- --               (fst (perm𝔽≡ n g)) 
-- -- -- -- -- -- -- -- -- -- --  𝕍≡ n = Relim.f (w)
-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --   open Relim

-- -- -- -- -- -- -- -- -- -- --   w : Relim _
-- -- -- -- -- -- -- -- -- -- --   isSetA w _ = isOfHLevelPlus 2 (isContrSinglP _ _)
-- -- -- -- -- -- -- -- -- -- --   εA w = refl , λ i → refl
-- -- -- -- -- -- -- -- -- -- --   fst (∷A w k (X , _)) = adjT×^≃ (fst k) ₑ∙ₚ X
-- -- -- -- -- -- -- -- -- -- --   snd (∷A w k {xs} (_ , P)) i =  adjT-×-sq n k i ₑ∙ₚ P i
      
-- -- -- -- -- -- -- -- -- -- --   fst (invoA w k (X , _) i) =
-- -- -- -- -- -- -- -- -- -- --     invol-ₑ∙p (adjT×^≃ (fst k))
-- -- -- -- -- -- -- -- -- -- --      (isInvo-adjT×^ {n = n} (fst k)) X i
-- -- -- -- -- -- -- -- -- -- --   snd (invoA w k (_ , P) i) j =
-- -- -- -- -- -- -- -- -- -- --      invol-ₑ∙p (adjT-×-sq n k j)
-- -- -- -- -- -- -- -- -- -- --       (adjT-×-sq-invo n k j)
-- -- -- -- -- -- -- -- -- -- --       (P j) i 
-- -- -- -- -- -- -- -- -- -- --   fst (braidA w k k< (X , _) i) =
-- -- -- -- -- -- -- -- -- -- --     ₑ∙ₚ-comp³eq (adjT×^≃ k) (adjT×^≃ (suc k)) X
-- -- -- -- -- -- -- -- -- -- --       (equivEq (funExt (braid-adjT×^ k k<))) i
-- -- -- -- -- -- -- -- -- -- --   snd (braidA w k k< (_ , P) i) j =
-- -- -- -- -- -- -- -- -- -- --     ₑ∙ₚ-comp³eq (adjT-×-sq n (k , <-weaken {n = n} k<) j)
-- -- -- -- -- -- -- -- -- -- --                   (adjT-×-sq n (suc k , k<) j) (P j)
-- -- -- -- -- -- -- -- -- -- --       (equivEq (funExt (adjT-×-sq-braid n k k< j)) ) i
-- -- -- -- -- -- -- -- -- -- --   fst (commA w k l z (X , _) i) =
-- -- -- -- -- -- -- -- -- -- --       ₑ∙ₚ-comp²eq (adjT×^≃ (fst l)) (adjT×^≃ (fst k)) X
-- -- -- -- -- -- -- -- -- -- --         (equivEq (funExt (comm-adjT×^ _ _ (snd k) (snd l) z))) i
-- -- -- -- -- -- -- -- -- -- --   snd (commA w k l z (_ , P) i) j =
-- -- -- -- -- -- -- -- -- -- --       ₑ∙ₚ-comp²eq (adjT-×-sq n l j) (adjT-×-sq n k j) (P j)
-- -- -- -- -- -- -- -- -- -- --         (equivEq (funExt (adjT-×-sq-comm n k l z j))) i


-- -- -- -- -- -- -- -- -- -- -- --  isGpdA×^ : isGroupoid (A ×^ n)
-- -- -- -- -- -- -- -- -- -- -- --  isGpdA×^ = isOfHLevel×^ n 3 isGrpA

-- -- -- -- -- -- -- -- -- -- -- --  wSqFst : (h : Perm n) → Relim
-- -- -- -- -- -- -- -- -- -- -- --    λ g → Square
-- -- -- -- -- -- -- -- -- -- -- --      (fst (𝕍≡ n g))
-- -- -- -- -- -- -- -- -- -- -- --      (fst (𝕍≡ n (g · h)))
-- -- -- -- -- -- -- -- -- -- -- --      refl
-- -- -- -- -- -- -- -- -- -- -- --      (fst (𝕍≡ n h))
-- -- -- -- -- -- -- -- -- -- -- --  Relim.isSetA (wSqFst h) g = isOfHLevelRetractFromIso 2
-- -- -- -- -- -- -- -- -- -- -- --      (invIso PathP→comm-Iso)
-- -- -- -- -- -- -- -- -- -- -- --      (isOfHLevel≡ 3 isGpdA×^ isGpdA×^ _ _)
-- -- -- -- -- -- -- -- -- -- -- --  Relim.εA (wSqFst h) i j = fst (𝕍≡ n h) (j ∧ i)
-- -- -- -- -- -- -- -- -- -- -- --  Relim.∷A (wSqFst h) k {xs} X j i = (adjT×^≃ (fst k) ₑ∙ₚ X j) i 
-- -- -- -- -- -- -- -- -- -- -- --  Relim.invoA (wSqFst h) k X l j i = 
-- -- -- -- -- -- -- -- -- -- -- --     invol-ₑ∙p (adjT×^≃ (fst k))
-- -- -- -- -- -- -- -- -- -- -- --                 (isInvo-adjT×^ {n = n} (fst k))
-- -- -- -- -- -- -- -- -- -- -- --                 (X j) l i
-- -- -- -- -- -- -- -- -- -- -- --  Relim.braidA (wSqFst h) k k< X l j i =
-- -- -- -- -- -- -- -- -- -- -- --    ₑ∙ₚ-comp³eq (adjT×^≃ k) (adjT×^≃ (suc k)) (X j)
-- -- -- -- -- -- -- -- -- -- -- --      (equivEq (funExt (braid-adjT×^ k k<))) l i
-- -- -- -- -- -- -- -- -- -- -- --  Relim.commA (wSqFst h) k l z X l' j i =
-- -- -- -- -- -- -- -- -- -- -- --    ₑ∙ₚ-comp²eq (adjT×^≃ (fst l)) (adjT×^≃ (fst k)) (X j)
-- -- -- -- -- -- -- -- -- -- -- --         (equivEq (funExt (comm-adjT×^ _ _ (snd k) (snd l) z))) l' i

-- -- -- -- -- -- -- -- -- -- -- --  wSqSnd : (h : Perm n) → RelimProp
-- -- -- -- -- -- -- -- -- -- -- --    λ g → SquareP (λ i j → perm𝔽 isGrpA n (emcomp g h i j) ≡ Relim.f (wSqFst h) g i j)
-- -- -- -- -- -- -- -- -- -- -- --      (flipSquare (snd (𝕍≡ n g)))
-- -- -- -- -- -- -- -- -- -- -- --      (flipSquare (snd (𝕍≡ n (g · h))))
-- -- -- -- -- -- -- -- -- -- -- --      refl
-- -- -- -- -- -- -- -- -- -- -- --      (flipSquare (snd (𝕍≡ n h)))

-- -- -- -- -- -- -- -- -- -- -- --  RelimProp.isPropA (wSqSnd h) g =
-- -- -- -- -- -- -- -- -- -- -- --       isOfHLevelRespectEquiv 1
-- -- -- -- -- -- -- -- -- -- -- --     (invEquiv (PathP≃Path _ _ _))
-- -- -- -- -- -- -- -- -- -- -- --       (isOfHLevelRespectEquiv 2
-- -- -- -- -- -- -- -- -- -- -- --         (invEquiv (PathP≃Path _ _ _))
-- -- -- -- -- -- -- -- -- -- -- --          ((isOfHLevelRespectEquiv 3
-- -- -- -- -- -- -- -- -- -- -- --         (invEquiv (PathP≃Path _ _ _))
-- -- -- -- -- -- -- -- -- -- -- --          (isOfHLevel≡ 3 (isGroupoidΠ λ _ → isGrpA) isGpdA×^ ) _ _)) _ _)
-- -- -- -- -- -- -- -- -- -- -- --  RelimProp.εA (wSqSnd h) j i = flipSquare (snd (𝕍≡ n h)) (j ∧ i)
-- -- -- -- -- -- -- -- -- -- -- --  RelimProp.∷A (wSqSnd h) k {xs} X j i l =
-- -- -- -- -- -- -- -- -- -- -- --    (adjT-×-sq n k l ₑ∙ₚ λ i → X j i l) i
 
-- -- -- -- -- -- -- -- -- -- -- --  w : EMelim (PermG n) (λ z → singl (perm𝔽 isGrpA n z))
-- -- -- -- -- -- -- -- -- -- -- --  EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
-- -- -- -- -- -- -- -- -- -- -- --  EMelim.b w = A ×^ n , ua (isoToEquiv (invIso (Iso-×^-F→  n)))
-- -- -- -- -- -- -- -- -- -- -- --  EMelim.bPathP w g =
-- -- -- -- -- -- -- -- -- -- -- --    let z = 𝕍≡ n g
-- -- -- -- -- -- -- -- -- -- -- --    in ΣPathP (fst z , flipSquare (snd z))
-- -- -- -- -- -- -- -- -- -- -- --  fst (EMelim.bSqP w g h i j) = Relim.f (wSqFst h) g i j
-- -- -- -- -- -- -- -- -- -- -- --  snd (EMelim.bSqP w g h i j) = RelimProp.f (wSqSnd h) g i j

-- -- -- -- -- -- -- -- -- -- -- -- module 𝕍 {A : Type ℓ} (isGrpA : isGroupoid A) where

-- -- -- -- -- -- -- -- -- -- -- --   𝕍 : ∀ {n} →  (em : ℙrm' n) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- --   𝕍 {n} = fst ∘ 𝕍Si isGrpA n             

-- -- -- -- -- -- -- -- -- -- -- --   isGrp𝕍 : ∀ {n} →  (em : ℙrm' n) → isGroupoid (𝕍 em)
-- -- -- -- -- -- -- -- -- -- -- --   isGrp𝕍 {n} em = subst isGroupoid (snd (perm𝔽Si isGrpA n em) ∙ snd (𝕍Si isGrpA n em))
-- -- -- -- -- -- -- -- -- -- -- --        (isGroupoidΠ λ _ → isGrpA)             



-- -- -- -- -- -- -- -- -- -- -- -- -- from𝕍 : {A : Type ℓ} → (isGrpA : isGroupoid A) → ∀ n →  (em : ℙrm' n) →
-- -- -- -- -- -- -- -- -- -- -- -- --               𝕍 isGrpA n em → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- from𝕍  isGrpA n' = EMelim.f (w {n'})
-- -- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- -- --  open EMelim

-- -- -- -- -- -- -- -- -- -- -- -- --  open Relim

-- -- -- -- -- -- -- -- -- -- -- -- --  wB : ∀ {n} → A ×^ n → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- --  wB {zero} _ = []
-- -- -- -- -- -- -- -- -- -- -- -- --  wB {suc n} (x , xs) = x ∷2 (wB xs)


-- -- -- -- -- -- -- -- -- -- -- -- --  w≡ : ∀ {n} → Relim
-- -- -- -- -- -- -- -- -- -- -- -- --       (λ z →
-- -- -- -- -- -- -- -- -- -- -- -- --          PathP (λ i → 𝕍 isGrpA n (emloop z i) → FMSet2 A) (wB) (wB))
-- -- -- -- -- -- -- -- -- -- -- -- --  isSetA w≡ _ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --  εA w≡ = refl
-- -- -- -- -- -- -- -- -- -- -- -- --  ∷A (w≡ {suc (suc n)}) (k , k<) {xs} X i x =
-- -- -- -- -- -- -- -- -- -- -- -- --    let v = funExt (λ y → {!!}) ◁ congP (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- --              _∘' fst (unglue-ₑ∙p (adjT×^≃ k)
-- -- -- -- -- -- -- -- -- -- -- -- --              (cong (𝕍 isGrpA (suc (suc n))) (emloop xs)) i)) X
-- -- -- -- -- -- -- -- -- -- -- -- --    in v i x
-- -- -- -- -- -- -- -- -- -- -- -- --  -- ∷A (w≡ {suc (suc n)}) (zero , k<) {xs} X i x =
     
-- -- -- -- -- -- -- -- -- -- -- -- --  --   let v = funExt (λ _ → comm _ _ _) ◁ congP (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- --  --             _∘' fst (unglue-ₑ∙p (adjT×^≃ zero)
-- -- -- -- -- -- -- -- -- -- -- -- --  --             (cong (𝕍 isGrpA (suc (suc n))) (emloop xs)) i)) X
-- -- -- -- -- -- -- -- -- -- -- -- --  --   in v i x
-- -- -- -- -- -- -- -- -- -- -- -- --  -- ∷A (w≡ {suc (suc (suc n))}) (suc k , k<) {xs} X i x =
-- -- -- -- -- -- -- -- -- -- -- -- --  --   let v = {!!} ◁ congP (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- --  --             _∘' fst (unglue-ₑ∙p (adjT×^≃ (suc k))
-- -- -- -- -- -- -- -- -- -- -- -- --  --             (cong (𝕍 isGrpA (suc (suc (suc n)))) (emloop xs)) i)) X
-- -- -- -- -- -- -- -- -- -- -- -- --  --   in v i x
-- -- -- -- -- -- -- -- -- -- -- -- --  invoA w≡ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --  braidA w≡ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --  commA w≡ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --  w : ∀ {n} → EMelim (PermG n) (λ z → 𝕍 isGrpA n z → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- --  isGrpB w x = isGroupoidΠ λ _ → trunc
-- -- -- -- -- -- -- -- -- -- -- -- --  b w = wB
-- -- -- -- -- -- -- -- -- -- -- -- --  bPathP (w {n}) = Relim.f (w≡ {n})
-- -- -- -- -- -- -- -- -- -- -- -- --  bSqP w = {!!}
