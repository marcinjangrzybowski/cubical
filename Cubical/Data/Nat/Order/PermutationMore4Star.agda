{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.PermutationMore4Star where

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
open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Nat.Order.RecursiveMoreEquiv

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
-- open import Cubical.Data.Nat.Order.PermutationMore


-- open import Cubical.Data.FinData.GTrun

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)

open import Cubical.HITs.ListedFiniteSet.Base3
import Cubical.HITs.ListedFiniteSet.Base22Star2 as S
import Cubical.HITs.ListedFiniteSet.Base22Star3 as S'

open import Cubical.Relation.Binary

import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint

private
  variable
    ℓ : Level
    A : Type ℓ


-- ΣhSetPred : ∀ {ℓ} {ℓ'}
--         {a₀₀ a₀₁ : Type ℓ} {a₀₋ : a₀₀ ≡ a₀₁}
--   {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
--   (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
   
--    {a₀₀ : A i0 i0 → hProp ℓ'}
--    {a₀₁ : A i0 i1  → hProp ℓ'}
--    (a₀₋ : PathP (λ j → A i0 j → hProp ℓ') a₀₀ a₀₁)
--    {a₁₀ : A i1 i0  → hProp ℓ'} {a₁₁ : A i1 i1  → hProp ℓ'}
--    (a₁₋ : PathP (λ j → A i1 j  → hProp ℓ') a₁₀ a₁₁)
--    (a₋₀ : PathP (λ i → A i i0  → hProp ℓ') a₀₀ a₁₀)
--    (a₋₁ : PathP (λ i → A i i1  → hProp ℓ') a₀₁ a₁₁)

--           → Square {A = Type (ℓ-max ℓ ℓ')}              
--               (λ j → Σ (A i0 j) (fst ∘ a₀₋ j)) 
--               (λ j → Σ (A i1 j) (fst ∘ a₁₋ j)) 
--               (λ i → Σ (A i i0) (fst ∘ a₋₀ i)) 
--               (λ i → Σ (A i i1) (fst ∘ a₋₁ i)) 
-- ΣhSetPred a₀₋ a₁₋ a₋₀ a₋₁ = {!!}


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

unglueFlooopPathExt : ∀ n (k l : Σ ℕ  λ k → (suc k < n)) →
  PathP (λ i → Flooop n k l i → Fin n)
    (adjT n k) (adjT n l)
unglueFlooopPathExt n k l i x = unglue (i ∨ ~ i) x

glueFlooopPathExt : ∀ n (k l : Σ ℕ  λ k → (suc k < n)) →
  PathP (λ i → Fin n → Flooop n k l i )
    (adjT n k) (adjT n l)
glueFlooopPathExt n k l i x =
  glue
    (λ {(i = i0) → adjT n k x
      ;(i = i1) → adjT n l x
       })
      (isInvolution-adjT n k
      (isInvolution-adjT n l x (~ i)) i)


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


gluePathAdjT' : ∀ n → ∀ k
       →  PathP (λ i → Fin n → (ua (adjT'≃ {n = n} k) i))
           (adjT n k) (idfun _)
gluePathAdjT' n k i x =
   ua-gluePath (adjT'≃ {n = n} k) (isInvolution-adjT n k x) i


ungluePathAdjT' : ∀ n → ∀ k
       →  PathP (λ i →  ((ua (adjT'≃ {n = n} k) i)) → Fin n)
           (idfun _) (adjT n k)
ungluePathAdjT' n k = (sym (funExt (isInvolution-adjT n k)) ◁
      congP (λ _ → (adjT n k) ∘_) (ua-ungluePathExt (adjT'≃ {n = n} k)))


glueSq-Flooop-comp : ∀ n (k l : Σ ℕ  λ k → (suc k < n))
   → SquareP (λ i j → Fin n → Flooop-comp n k l i j)
         (gluePathAdjT' n k)
         (gluePathAdjT' n l)
         (glueFlooopPathExt n k l)
         λ _ → idfun _
glueSq-Flooop-comp n k l i j x =
  glue (λ {
       (j = i0)(i = i0) → adjT n k x
      ;(j = i0)(i = i1) → adjT n l x
      ;(j = i1) → x
       }) (isInvolution-adjT n k
          (isInvolution-adjT n l
             x (~ i ∨ j)) (i ∨ j))


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

-- 𝕡comp' : ∀ {n} → (k l : Σ ℕ  λ k → (suc k < n)) →
--    Square {A = ℙrm n}
--      (𝕡loop k)
--      (𝕡loop l)
--      refl
--      (𝕡looop k l)
-- 𝕡comp' k l =
--    (𝕡invol k) ◁
--    (λ i j → (𝕡comp k l i (~ j)))
--    ▷ sym (𝕡invol l)

-- 𝕡looop-invol : ∀ n → (k l : Σ ℕ  λ k → (suc k < n)) →
--     𝕡looop {n = n} k l ≡ sym (𝕡looop l k)
-- 𝕡looop-invol n k l i j =
--    hcomp
--       (λ l' → λ {
--         (i = i0) → 𝕡comp k l j (~ l')
--        ;(i = i1) → 𝕡comp l k (~ j) (~ l')
--        ;(j = i0) → 𝕡loop k (~ l')
--        ;(j = i1) → 𝕡loop l (~ l')
--        }) 𝕡base

-- record R𝕡rec {n} (A : Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--    abase : A
--    aloop : (Σ ℕ  λ k → (suc k < n)) → abase ≡ abase
--    alooop : (k l : Σ ℕ  λ k → (suc k < n)) → abase ≡ abase
--    acomp : (k l : Σ ℕ  λ k → (suc k < n)) →
--       Square
--         (aloop k)
--         (aloop l)
--         (alooop k l)
--         refl

--    ainvol : ∀ k → aloop k ≡ sym (aloop k)
--    acomm : (k l : Σ ℕ  λ k → (suc k < n)) →
--       commT (fst k) (fst l) →
--         Square
--           refl
--           refl
--         (alooop k l)
--         (alooop l k)

--    abraid : ∀ k k<  →        
--           Square
--           (aloop (suc k , k<))
--           (aloop (k , <-weaken {n = n} k<))
--           (alooop (k , <-weaken {n = n} k<) (suc k , k<))
--           (alooop (k , <-weaken {n = n} k<) (suc k , k<))
--    asquash : isGroupoid A


--  f : ℙrm n → A
--  f 𝕡base = abase
--  f (𝕡loop x i) = aloop x i
--  f (𝕡looop k l i) = alooop k l i
--  f (𝕡comp k l i i₁) = acomp k l i i₁
--  -- f (𝕡comp' k l i i₁) = acomp' k l i i₁
--  f (𝕡invol k i i₁) = ainvol k i i₁
--  f (𝕡comm k l x i i₁) = acomm k l x i i₁
--  f (𝕡braid k k< i i₁) = abraid k k< i i₁
--  f (𝕡squash _ _ _ _ r s i₀ i₁ i₂) =
--    asquash _ _ _ _
--      (λ i j → (f (r i j)))
--      (λ i j → (f (s i j)))
--      i₀ i₁ i₂

-- record R𝕡elim {n} (A : ℙrm n → Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--    isGroupoidA : ∀ x → isGroupoid (A x)
--    abase : A 𝕡base
--    aloop : (k : Σ ℕ  λ k → (suc k < n)) →
--      PathP (λ i → A (𝕡loop k i)) abase abase
--    alooop : (k l : Σ ℕ  λ k → (suc k < n)) →
--      PathP (λ i → A (𝕡looop k l i)) abase abase
--    acomp : ∀ k l →
--      SquareP (λ j i → A (𝕡comp k l j i))
--        (aloop k)
--        (aloop l)
--        (alooop k l)
--        refl
--    ainvol : ∀ k →
--      SquareP (λ i j → A (𝕡invol k i j))
--        (aloop k)
--        (symP (aloop k))
--        refl refl
--    acomm : (k l : Σ ℕ  λ k → (suc k < n)) → ∀ x →     
--        SquareP (λ i j → A (𝕡comm k l x i j))
--          refl
--          refl
--        (alooop k l)
--        (alooop l k)
--    abraid : ∀ k k<  →        
--          SquareP (λ i j → A (𝕡braid k k< i j))
--          (aloop (suc k , k<))
--          (aloop (k , <-weaken {n = n} k<))
--          (alooop (k , <-weaken {n = n} k<) (suc k , k<))
--          (alooop (k , <-weaken {n = n} k<) (suc k , k<))
  


--  f : ∀ x → A x
--  f 𝕡base = abase
--  f (𝕡loop x i) = aloop x i
--  f (𝕡looop k l i) = alooop k l i
--  f (𝕡comp k l j i) = acomp k l j i
   
--  f (𝕡invol k i j) = ainvol k i j
 
--  f (𝕡comm k l x i j) = acomm k l x i j
    
 
--  f (𝕡braid k k< i j) = abraid k k< i j
--  f (𝕡squash x y p q r s i j k) =
--    isOfHLevel→isOfHLevelDep 3 isGroupoidA
--      _ _ _ _
--      (λ j k → f (r j k)) (λ j k → f (s j k))
--      (𝕡squash x y p q r s) i j k


-- record R𝕡elimSet {n} (A : ℙrm n → Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--    isSetA : ∀ x → isSet (A x)
--    abase : A 𝕡base
--    aloop : (k : Σ ℕ  λ k → (suc k < n)) →
--      PathP (λ i → A (𝕡loop k i)) abase abase
--    alooop : (k l : Σ ℕ  λ k → (suc k < n)) →
--      PathP (λ i → A (𝕡looop k l i)) abase abase
--    -- (k l : Σ ℕ  λ k → (suc k < n)) → abase ≡ abase

--  fR : R𝕡elim (λ z → A z)
--  R𝕡elim.isGroupoidA fR = isSet→isGroupoid ∘ isSetA
--  R𝕡elim.abase fR = abase
--  R𝕡elim.aloop fR = aloop
--  R𝕡elim.alooop fR = alooop
--  R𝕡elim.acomp fR k l = 
--    isSet→SquareP (λ j i → isSetA (𝕡comp k l j i)) _ _ _ _
--  R𝕡elim.ainvol fR k =
--   isSet→SquareP (λ j i → isSetA (𝕡invol k j i)) _ _ _ _
--  R𝕡elim.acomm fR k l x =
--   isSet→SquareP (λ j i → isSetA (𝕡comm k l x j i)) _ _ _ _
--  R𝕡elim.abraid fR k k< =
--   isSet→SquareP (λ j i → isSetA (𝕡braid k k< j i)) _ _ _ _

--  f : ∀ x → A x
--  f = R𝕡elim.f fR

-- record R𝕡elimSet' {n} (A : ℙrm n → Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--    isSetA : ∀ x → isSet (A x)
--    abase : A 𝕡base
--    aloop : (k : Σ ℕ  λ k → (suc k < n)) →
--      PathP (λ i → A (𝕡loop k i)) abase abase

--  fR : R𝕡elimSet (λ z → A z)
--  R𝕡elimSet.isSetA fR = isSetA
--  R𝕡elimSet.abase fR = abase
--  R𝕡elimSet.aloop fR = aloop
--  R𝕡elimSet.alooop fR k l i =
--    comp (λ j → A (𝕡comp k l i (~ j)))
--      (λ j → λ { (i = i0) → aloop k (~ j) ; (i = i1) → aloop l (~ j) })
--      abase

--  f : ∀ x → A x
--  f = R𝕡elimSet.f fR



-- record R𝕡elimProp {n} (A : ℙrm n → Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--    isPropA : ∀ x → isProp (A x)
--    abase : A 𝕡base

--  fR : R𝕡elimSet (λ z → A z)
--  R𝕡elimSet.isSetA fR = isProp→isSet ∘ isPropA
--  R𝕡elimSet.abase fR = abase
--  R𝕡elimSet.aloop fR k = isProp→PathP (λ _ → isPropA _) _ _
--  R𝕡elimSet.alooop fR k l = isProp→PathP (λ _ → isPropA _) _ _

--  f : ∀ x → A x
--  f = R𝕡elimSet.f fR



-- toℙrmR≡ : ∀ n → Rrec {n = n} (Path (ℙrm n) 𝕡base 𝕡base)
-- Rrec.isSetA (toℙrmR≡ n) = 𝕡squash _ _
-- Rrec.εA (toℙrmR≡ n) = refl
-- Rrec.∷A (toℙrmR≡ n) k = 𝕡loop k ∙_ 
-- Rrec.invoA (toℙrmR≡ n) k x i j = 
--   hcomp (λ l →
--        λ { (i = i1) → x (j ∧ l)
--          ; (j = i0) → 𝕡base
--          ; (j = i1) → (hcomp (λ l' →
--                  λ { (i = i1) → x (l' ∧ l)
--                    ; (l = i0) → 𝕡invol k l' i
--                    ; (l = i1) → x l'
--                    }) (𝕡loop k (l ∨ i)))
--          }) (𝕡loop k (~ i ∧ j))

-- Rrec.braidA (toℙrmR≡ n) k k< x i =
--     𝕡comp' (k , <-weaken {n = n} k<) (suc k , k<) i
--   ∙ 𝕡braid k k< i
--   ∙ 𝕡comp (k , <-weaken {n = n} k<) (suc k , k<) i ∙ x

-- Rrec.commA (toℙrmR≡ n) k l z x i =
--     𝕡comp' k l i
--     ∙ (𝕡comm k l z i ∙∙ 𝕡comp l k i ∙∙ x)
  

-- toℙrmRsq : ∀ n → (h : Perm n) → RelimProp
--       (λ z →
         
--          Square (Rrec.f (toℙrmR≡ n) z)
--          (Rrec.f (toℙrmR≡ n) ((snd (PermG n) GroupStr.· z) h)) refl
--          (Rrec.f (toℙrmR≡ n) h))
-- RelimProp.isPropA (toℙrmRsq n h) _ =
--   isOfHLevelRetractFromIso
--     1 (invIso PathP→comm-Iso) (𝕡squash _ _ _ _)
-- RelimProp.εA (toℙrmRsq n h) i j = (Rrec.f (toℙrmR≡ n) h) (i ∧ j)
-- RelimProp.∷A (toℙrmRsq n h) k x i = 𝕡loop k ∙ x i

-- toℙrmR : ∀ n → EMrec (PermG n) {B = ℙrm n} 𝕡squash
-- EMrec.b (toℙrmR n) = 𝕡base
-- EMrec.bloop (toℙrmR n) = Rrec.f (toℙrmR≡ n)
-- EMrec.bComp (toℙrmR n) g h = RelimProp.f (toℙrmRsq n h) g 


-- toℙrm : ∀ n → ℙrm' n → ℙrm n
-- toℙrm n = EMrec.f (toℙrmR n)


-- commSq : ∀ n → ∀ k xs → Square {A = ℙrm' n}
--            (emloop (η k))
--            (emloop xs)
--            refl
--            (emloop (η k · xs))
-- commSq n k xs i j =
--   hcomp (λ l' → λ {
--        (i = i0) → emloop (η k) j
--       ;(i = i1) → emloop (invo k xs l') j
--       ;(j = i0) → embase
--       ;(j = i1) → emloop (k ∷ xs) i
--       }) (emcomp (η k) (η k · xs) i j)

-- -- commSq' : ∀ n → ∀ k l → Square {A = ℙrm' n}
-- --            (emloop (η l))
-- --            (emloop (η k))
-- --            refl
-- --            (emloop (η l · η k))
           
-- -- commSq' n k l i j = {!!}
-- --   -- hcomp (λ l' → λ {
-- --   --      (i = i0) → emloop (η k) j
-- --   --     ;(i = i1) → emloop (invo k (η l) l') j
-- --   --     ;(j = i0) → embase
-- --   --     ;(j = i1) → emloop (k ∷ η l) i
-- --   --     }) (emcomp (η k) (η k · η l) i j)

-- involSq : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
--       emloop (η {n = n} k) ≡ sym (emloop (η k))
-- involSq n k i j =
--   hcomp (λ l → λ {
--        (i = i0) → emcomp (η k) (η k) j l
--       ;(i = i1) → emcomp ε (η k) (~ j) l
--       ;(j = i0) → emloop (k ∷ ε) l
--       ;(j = i1) → emloop {Group = PermG n} ((invo {n = n} k ε) i) l
--       }) embase


-- braidSq : ∀ n k l →
--    Square {A = ℙrm' n}
--      (emloop (η k))
--      (emloop (η k))
--      (emloop (η l))
--      (emloop (k  ∷ l ∷ k ∷ ε))
-- braidSq n k l =
--     (involSq n k) ◁
--       emloop-doubleCompFill (PermG n) (η k) (η l) (η k)
-- braidSq' : ∀ n k l →
--    Square {A = ℙrm' n}
--      (sym (emloop (η l)))
--      (sym (emloop (η l)))
--      (emloop (l ∷ k ∷ l ∷ ε))
--      (emloop (η k))
-- braidSq' n k l =
--   (sym (involSq n l)) ◁
--      λ i j → emloop-doubleCompFill (PermG n) (η l) (η k) (η l) i (~ j)


-- braidSqC : ∀ n k k< →
--    Square {A = ℙrm' n}
--      refl
--      refl
--      (emloop ((k , <-weaken {n = n} k<)
--          ∷ (suc k , k<) ∷ (k , <-weaken  {n = n} k<) ∷ ε))
--      (emloop ((suc k , k<) ∷ (k , <-weaken  {n = n} k<) ∷ (suc k , k<) ∷ ε))
      
-- braidSqC n k k< i j = emloop (braid k k< ε j ) i
--   -- (braidSqC0 n k k< j
--   --   ∙∙ (λ i → emloop (braid k k< ε i ) j)
--   --   ∙∙
--   --   braidSqC1 n k k< j) i

-- Rfromℙrm : ∀ n → R𝕡rec {n = n} (ℙrm' n)
-- R𝕡rec.abase (Rfromℙrm n) = embase
-- R𝕡rec.aloop (Rfromℙrm n) = emloop ∘ η
-- R𝕡rec.alooop (Rfromℙrm n) k l i =
--   hcomp (λ z → λ {(i = i0) → emloop (η k) (~ z)
--                 ; (i = i1) → emloop (η l) (~ z)} ) embase

-- R𝕡rec.acomp (Rfromℙrm n) k l i j =
--   doubleCompPath-filler (emloop (η k)) refl (sym (emloop (η l))) (~ j) i
-- R𝕡rec.ainvol (Rfromℙrm n) = involSq n
    
-- R𝕡rec.acomm (Rfromℙrm n) k l x i j =
--   (commSq n k (η l) j ∙∙
--     (λ i → emloop (comm k l x ε i ) j)
--    ∙∙ sym (commSq n l (η k) j)) i
-- R𝕡rec.abraid (Rfromℙrm n) k k< i j =
--   (braidSq n (k , (<-weaken {n = n} k<) ) (suc k , k<) j ∙∙
--    (braidSqC n k k< j)
--    ∙∙ braidSq' n (k , (<-weaken {n = n} k<) ) (suc k , k<) j) i

-- R𝕡rec.asquash (Rfromℙrm n) = emsquash

-- fromℙrm : ∀ n → ℙrm n → ℙrm' n
-- fromℙrm n = R𝕡rec.f (Rfromℙrm n)

-- emloop-ε : ∀ n → refl ≡ emloop {Group = PermG n} ε 
-- emloop-ε n i j =
--   hcomp (λ l →
--     primPOr i (~ i ∨ j ∨ ~ j)
--       (λ _ → emcomp ε ε j l)
--        λ _ → emloop ε l)
--     embase 

-- RelimProp≡ : ∀ n → RelimProp
--       λ z →
--         Square
--          (λ j → fromℙrm n (Rrec.f (toℙrmR≡ n) z j))
--          (emloop z)
--         refl
--         refl
-- RelimProp.isPropA (RelimProp≡ n) x = emsquash _ _ _ _
-- RelimProp.εA (RelimProp≡ n) = emloop-ε n
-- RelimProp.∷A (RelimProp≡ n) k {xs} X =
--   (cong-∙ (fromℙrm n) (𝕡loop k) (cong (toℙrm n) (emloop xs))
--     ∙ cong (emloop (η k) ∙_) X) ∙ sym (emloop-comp _ (η k) xs)
   
-- RfromToℙrm : ∀ n → EMelimSet (PermG n) (λ z → fromℙrm n (toℙrm n z) ≡ z)
-- EMelimSet.isSetB (RfromToℙrm n) x = emsquash _ _
-- EMelimSet.b (RfromToℙrm n) = refl
-- EMelimSet.bPathP (RfromToℙrm n) = flipSquare ∘ RelimProp.f (RelimProp≡ n)

-- fromToℙrm : ∀ n → section (fromℙrm n) (toℙrm n)
-- fromToℙrm n = EMelimSet.f (RfromToℙrm n)


-- RtoFromℙrm : ∀ n → 
--      R𝕡elimSet {n = n} (λ z → toℙrm n (fromℙrm n z) ≡ z)
-- R𝕡elimSet.isSetA (RtoFromℙrm n) _ = 𝕡squash _ _
-- R𝕡elimSet.abase (RtoFromℙrm n) = refl
-- R𝕡elimSet.aloop (RtoFromℙrm n) k i j =
--    (compPath-filler (𝕡loop k) refl) (~ j) i
-- R𝕡elimSet.alooop (RtoFromℙrm n) k l i j = 
  
--    hcomp (λ l' → λ {
--        (i = i0) → compPath-filler (𝕡loop k) refl (~ j) (~ l')
--       ;(i = i1) → compPath-filler (𝕡loop l) refl (~ j) (~ l')
--       ;(j = i0) → toℙrm n
--          (doubleCompPath-filler
--             (emloop (η k)) refl
--              (sym (emloop (η l))) l' i)
--       ;(j = i1) → 𝕡comp k l i (~ l')
--       }) 𝕡base

-- toFromℙrm : ∀ n → retract (fromℙrm n) (toℙrm n)
-- toFromℙrm n = R𝕡elimSet.f (RtoFromℙrm n)

-- IsoEmℙrm : ∀ n →  Iso (ℙrm n) (ℙrm' n)
-- Iso.fun (IsoEmℙrm n) = fromℙrm n
-- Iso.inv (IsoEmℙrm n) = toℙrm n
-- Iso.rightInv (IsoEmℙrm n) = fromToℙrm n
-- Iso.leftInv (IsoEmℙrm n) = toFromℙrm n



-- IsoEmℙrmΩ : ∀ n → Iso (Path (ℙrm n) 𝕡base 𝕡base) (Perm n)
-- IsoEmℙrmΩ n = compIso
--  (congIso (IsoEmℙrm n))
--  (EMP.ΩEM₁Iso (PermG n))


-- 𝕡baseΩ-elimProp : ∀ {ℓ} n → (A : Path (ℙrm n) 𝕡base 𝕡base → Type ℓ)
--                   → (∀ x → isProp (A x))
--                   → (A refl)
--                   → (∀ p k → A p → A (𝕡loop k ∙ p))
--                   → ∀ x → A x 
-- 𝕡baseΩ-elimProp n A truncA a a∙ x =
--   subst A (Iso.leftInv (IsoEmℙrmΩ n) x) (w (Iso.fun (IsoEmℙrmΩ n) x))

--  where
--  wR : RelimProp (λ z → A (Iso.inv (IsoEmℙrmΩ n) z))
--  RelimProp.isPropA wR x = truncA _
--  RelimProp.εA wR = subst A compPathRefl a
--  RelimProp.∷A wR k {xs} x =
--    subst A (λ i → (compPath-filler (𝕡loop k) (Rrec.f (toℙrmR≡ n) xs) i
--             ∙ compPath-filler' (Rrec.f (toℙrmR≡ n) xs) refl (~ i))) (a∙ _ k x)
   

--  w : (∀ x → A (Iso.inv (IsoEmℙrmΩ n) x))
--  w = RelimProp.f wR


module comm-× {ℓ} (A : Type ℓ) where 

 record Comm-×-def : Type (ℓ-suc ℓ) where
  constructor comm-×-def
  field
   Vec𝟚 : Type
   isSetVec𝟚 : isSet Vec𝟚
   Fin×sndProp : Vec𝟚 → hProp ℓ-zero
   VecTy : Type ℓ
  FinTy : Type
  FinTy = Σ Vec𝟚 (fst ∘ Fin×sndProp)
  field
   FinVec-tab : (FinTy → A) → VecTy
   isEquivFinVec-tab : isEquiv FinVec-tab

 open Comm-×-def


 -- c-base : ℕ → Comm-×-def
 -- c-base 

 isGroupoidComm-×-def : isGroupoid Comm-×-def 
 isGroupoidComm-×-def = {!!}

 -- open R𝕡rec

 open Tab×≃ {A = A}

 𝑹 : ∀ n → ℙrm n → Comm-×-def
 Vec𝟚 (𝑹 n 𝕡base) = Bool ×^ n
 isSetVec𝟚 (𝑹 n 𝕡base) = isOfHLevel×^ n 2 isSetBool
 Fin×sndProp (𝑹 n 𝕡base) = Fin×Snd n
 VecTy (𝑹 n 𝕡base) = A ×^ n
 FinVec-tab (𝑹 n 𝕡base) = tab× n
 isEquivFinVec-tab (𝑹 n 𝕡base) = snd (tab×≃ n)

 𝑹 (suc n) (𝕡loop (suc k , k<) i) = w
  where

  w : Comm-×-def
  Vec𝟚 w = {!!}
  isSetVec𝟚 w = {!!}
  Fin×sndProp w = {!!}
  VecTy w = {!!}
  FinVec-tab w = {!!}
  isEquivFinVec-tab w = {!!}
  
 𝑹 (suc (suc n)) (𝕡loop (zero , k<) i) = {!!}
 
  -- where
  -- w : ℕ → (Σ ℕ  λ k → (suc k < n)) → Comm-×-def
  -- w n (k , k<) = {!n!}
 
 -- 𝑹 n (𝕡looop k l i) = {!!}
 -- 𝑹 n (𝕡comp k l i i₁) = {!!}
 -- 𝑹 n (𝕡invol k i i₁) = {!!}
 -- 𝑹 n (𝕡comm k l x i i₁) = {!!}
 -- 𝑹 n (𝕡braid k k< i i₁) = {!!}
 -- 𝑹 n (𝕡squash x x₁ x₂ y x₃ y₁ i i₁ x₄) = {!!}



 -- 𝑹 : ∀ n → R𝕡rec {n = n} Comm-×-def
 -- abase (𝑹 n) = {!!}
 -- aloop (𝑹 (suc n)) (suc k , k<) = {!!}
 -- aloop (𝑹 (suc (suc n))) (zero , k<) = {!!} 
 -- alooop (𝑹 n) = {!!}
 -- acomp (𝑹 n) = {!!}
 -- ainvol (𝑹 n) = {!!}
 -- acomm (𝑹 n) = {!!}
 -- abraid (𝑹 n) = {!!}
 -- asquash (𝑹 n) = {!!}
 
-- R×^₂ : ∀ {ℓ} → hSet ℓ → ∀ n → R𝕡rec {n = n} (hSet ℓ)
-- R×^₂ (A , isSetA) n = w
--  where
--   open R𝕡rec
--   w : R𝕡rec (hSet _)
--   abase w = A ×^ n , isOfHLevel×^ n 2 isSetA
--   aloop w k =
--     Σ≡Prop (λ _ → isPropIsOfHLevel 2) (adjT×^≡ {n = n} (fst k))
--   alooop w k l =
--     Σ≡Prop (λ _ → isPropIsOfHLevel 2) (biAdjT×^≡ {n = n} k l)
--   acomp w k l =
--     ΣSquareSet (λ _ → isProp→isSet  (isPropIsOfHLevel 2))
--      (biAdjT×^≡-comp k l)
--   ainvol w k =
--     ΣSquareSet (λ _ → isProp→isSet  (isPropIsOfHLevel 2))
--      (adjT×^≡-invol n (fst k))
--   acomm w k l x =
--     ΣSquareSet (λ _ → isProp→isSet  (isPropIsOfHLevel 2))
--      (biAdjT×^≡-comm k l x)
--   abraid w = {!!}
--   asquash w = isGroupoidHSet

-- ×^₂ : ∀ {ℓ} → hSet ℓ → ∀ n → ℙrm n → (hSet ℓ)
-- ×^₂ A n = R𝕡rec.f (R×^₂ A n)

-- R𝔽inSnd : ∀ n 
--    → R𝕡elimSet {n = n} λ p → ⟨ ×^₂ (𝟚.Bool , 𝟚.isSetBool) n p ⟩  → hProp ℓ-zero
-- R𝕡elimSet.isSetA (R𝔽inSnd n) _ = isSet→ isSetHProp
-- R𝕡elimSet.abase (R𝔽inSnd n) = Fin×Snd n
-- R𝕡elimSet.aloop (R𝔽inSnd n) = F×adjSnd {n = n} ∘ fst
-- R𝕡elimSet.alooop (R𝔽inSnd n) k l = cong snd (F×biAdjT≡' {n} k l)

-- h𝔽in× : ∀ n → ℙrm n → hSet ℓ-zero
-- h𝔽in× n p =
--  (Σ ⟨ ×^₂ (𝟚.Bool , 𝟚.isSetBool) n p ⟩
--    (fst ∘ R𝕡elimSet.f (R𝔽inSnd n) p) )  ,
--     isSetΣ (snd (×^₂ (𝟚.Bool , 𝟚.isSetBool) n p))
--        (isProp→isSet ∘ snd ∘ R𝕡elimSet.f (R𝔽inSnd n) p) 

-- 𝔽in× : ∀ {n} → ℙrm n → Type₀
-- 𝔽in× {n} = fst ∘ h𝔽in× n

-- module _ (A : hGroupoid ℓ) where
 
--  open Tab×

--  R×^ : ∀ n →
--     R𝕡elim {n = n} λ p → singl (𝔽in× p → ⟨ A ⟩)
--  R×^ n = w
--   where
--    open R𝕡elim
--    w : R𝕡elim λ p → singl (𝔽in× p → ⟨ A ⟩) 
--    isGroupoidA w p = isOfHLevelPlus {zero} 3 (isContrSingl (𝔽in× p → ⟨ A ⟩))
--    abase w = ⟨ A ⟩ ×^ n , tab×≡ {A = ⟨ A ⟩} n
--    aloop w k = ΣPathP (adjT×^≡ {A = ⟨ A ⟩ } {n = n} (fst k)
--        , tab×adjT× {A = fst A} n k)
--    alooop w k l = ΣPathP 
--      (biAdjT×^≡ {A = ⟨ A ⟩} {n = n} k l ,
--       tab×biAdjT× {A = fst A} n k l)
--    acomp w k l i j =
--      biAdjT×^≡-comp {A = ⟨ A ⟩} {n = n}  k l i j ,
--        {!tab×BiadjT×!}
--      -- Σ (λ i j X →
--      --     {!isOfHLevelPath' 4 !}) _
--      --   _ _ _ (biAdjT×^≡-comp {A = ⟨ A ⟩} {n = n}  k l)
--      -- biAdjT×^≡-comp {A = ⟨ A ⟩} {n = n}  k l i j
--      --  , {!!}
--    ainvol w k i j = 
--      adjT×^≡-invol {A = ⟨ A ⟩} n (fst k) i j ,
--      tab×adjT×-invol n k
--        (λ n k i j →
--          R𝕡elimSet.f (R𝔽inSnd n) (𝕡invol {n} k i j)) i j 
--    acomm w k l x i j = {!!}
--     -- biAdjT×^≡-comm {A = ⟨ A ⟩} {n = n}  k l x i j ,
--     --  {!!}
--    abraid w =
--     {!!}


-- -- -- R𝔽in× : ∀ n → R𝕡rec {n = n} (hSet ℓ-zero)
-- -- -- R𝕡rec.abase (R𝔽in× n) = (Fin× n) , isSetFin× n
-- -- -- R𝕡rec.aloop (R𝔽in× n) (k , _) = 
-- -- --   Σ≡Prop (λ _ → isPropIsOfHLevel 2) (F×adjT≡ {n = n} k)
-- -- -- R𝕡rec.alooop (R𝔽in× n) k l =
-- -- --   Σ≡Prop (λ _ → isPropIsOfHLevel 2) (F×biAdjT≡ k l)
-- -- -- R𝕡rec.acomp (R𝔽in× n) k l =
-- -- --   ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- --     (congSq {ℓ = ℓ-suc ℓ-zero} {ℓ' = ℓ-suc ℓ-zero} {A = Σ Type λ X → X → hProp ℓ-zero}
-- -- --             {B = Type}
-- -- --             {a₀₀ = _ , Fin×Snd n} {_ , Fin×Snd n}
-- -- --             {a₀₋ = λ i → (adjT×^≡ {A = 𝟚.Bool} {n = n} (fst k) i)
-- -- --                    , F×adjSnd {n} (fst k) i}
-- -- --             {a₁₋ =  
-- -- --               λ i → (adjT×^≡ {A = 𝟚.Bool} {n = n} (fst l) i)
-- -- --                    , λ x → (F×adjTP {n} (fst l) i) x ,
-- -- --                        isProp→PathP {ℓ = ℓ-zero} {B = λ i →
-- -- --                          ∀ x → isProp (F×adjTP {n} (fst l) i x)}
-- -- --                        (λ i → isPropΠ λ _ → isPropIsProp)
-- -- --                         (snd ∘ (Fin×Snd n)) (snd ∘ (Fin×Snd n)) i x
-- -- --                     -- λ x → (F×adjTP {n} (fst k) i) x ,
-- -- --                     --   isProp→PathP
-- -- --                     --     (λ i → isPropIsProp {A = (F×adjTP (fst k) i x)})
-- -- --                     --     (snd (Fin×Snd n {!!})) {!!} i
-- -- --                         }
-- -- --             (λ A → Σ (fst A) (fst ∘ snd A))
-- -- --      (ΣSquareSet (λ _ → isSet→ isSetHProp)
-- -- --       (biAdjT×^≡-comp {A = 𝟚.Bool} {n = n} k l)))
    
-- -- -- R𝕡rec.ainvol (R𝔽in× n) = {!!}
-- -- -- R𝕡rec.acomm (R𝔽in× n) = {!!}
-- -- -- R𝕡rec.abraid (R𝔽in× n) = {!!}
-- -- -- R𝕡rec.asquash (R𝔽in× n) = {!!}


-- -- R𝔽in : ∀ n → R𝕡rec {n = n} (hSet ℓ-zero)
-- -- R𝕡rec.abase (R𝔽in n) = Fin n , isSetFin {n = n}
-- -- R𝕡rec.aloop (R𝔽in n) k =
-- --   Σ≡Prop (λ _ → isPropIsOfHLevel 2) (ua (adjT'≃ {n = n} k))
-- -- R𝕡rec.alooop (R𝔽in n) k l =
-- --   Σ≡Prop (λ _ → isPropIsOfHLevel 2) (Flooop n k l)
-- -- R𝕡rec.acomp (R𝔽in n) k l =
-- --       ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- --         (Flooop-comp n k l)

-- -- R𝕡rec.ainvol (R𝔽in n) k =
-- --     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- --         (involPathSym _)

-- -- R𝕡rec.acomm (R𝔽in n) k l x =
-- --       ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- --        (flipSquare (Flooop-comm n k l x))
-- -- R𝕡rec.abraid (R𝔽in n) k k< =
-- --   ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- --     (comm→PathP (isInjectiveTransport
-- --       (funExt λ x → ≡Fin {n = n}
-- --         (funExt⁻ (A.adjTranspositionBraid k ) (fst x) ))))
-- -- R𝕡rec.asquash (R𝔽in n) = isGroupoidHSet

-- -- 𝔽inH : ∀ n → ℙrm n → hSet ℓ-zero
-- -- 𝔽inH n = R𝕡rec.f {n = n} (R𝔽in n)

-- -- 𝔽in : ∀ {n} → ℙrm n → Type
-- -- 𝔽in {n} = fst ∘' 𝔽inH n



-- -- module _ (A : Type ℓ) where

-- --  𝔽in→ : ℕ → Type ℓ
-- --  𝔽in→ n = Σ (ℙrm n) λ p → 𝔽in p → A

-- --  ↔kP : ∀ n → (a : Fin n → A) → ∀ k
-- --         → PathP (λ i → 𝔽in {n = n} (𝕡loop k i) → A)
-- --              (a ∘ fst (adjT'≃  {n = n} k)) a
-- --  ↔kP n a k i = a ∘' ua-ungluePathExt (adjT'≃ {n = n} k) i

 
-- --  ↔k'P : ∀ n → (a : Fin n → A) → ∀ k
-- --         → PathP (λ i → 𝔽in {n = n} (𝕡loop k i) → A)
-- --              a (a ∘ fst (adjT'≃ {n = n} k))
-- --  ↔k'P n a k =
-- --    congP (λ _ → a ∘_) (ungluePathAdjT' n k)

-- --  -- ↔k-fill : SquareP
-- --  --             {!λ i j → ↔kP A n p k!}
-- --  --             {!!} {!!} {!!} {!!}
-- --  -- ↔k-fill = {!!}

-- --  pop↔ : ∀ n → (a b : Fin n → A) → ∀ (p : 𝕡base ≡ 𝕡base) k
-- --         → PathP (λ i → 𝔽in {n = n} ((𝕡loop k ∙ p) i) → A) a b
-- --         → PathP (λ i → 𝔽in (p i) → A) (a ∘ fst (adjT'≃ {n} k)) b
-- --  pop↔ n a  b p k P i =
-- --    comp  (λ z → 𝔽in (compPath-filler' (𝕡loop k) p (~ z) i) → A )
-- --       (λ z →
-- --        λ {(i = i0) → ↔k'P n a k z
-- --          ;(i = i1) → b
-- --          }) (P i)


-- --  -- pop↔sq : ∀ n → (a b : Fin n → A) → ∀ (p : 𝕡base ≡ 𝕡base) k
-- --  --        → (P : PathP (λ i → 𝔽in {n = n} ((𝕡loop k ∙ p) i) → A) a b)
-- --  --        → P ≡
-- --  --          compPathP' {B = λ x → 𝔽in x → A} {p = 𝕡loop k} {q = p}
-- --  --            (↔k' n a k) (pop↔ n a b p k P) 
-- --  -- pop↔sq = {!!}

-- -- [_]_↔_ : ∀ n → (Fin n → A) → (Fin n → A) → Type _
-- -- [_]_↔_ {A = A} n x y = Σ (Path (ℙrm n) 𝕡base 𝕡base)
-- --   λ p → PathP (λ i → 𝔽in (p i) → A) x y



-- -- isTrans-[]↔ : ∀ n → BinaryRelation.isTrans ([_]_↔_ {A = A}  n)
-- -- fst (isTrans-[]↔ n a b c (p , _) (q , _)) = p ∙ q
-- -- snd (isTrans-[]↔ {A = A} n a b c (p , P) (q , Q)) =
-- --    compPathP' {B = λ x → 𝔽in x → A} {p = p} {q = q} P Q

-- -- ↔k : ∀ n k → (a : Fin n → A) → [ n ] a ↔ (a ∘ fst (adjT'≃ {n} k))
-- -- ↔k n k a = (𝕡loop k) , (↔k'P _ n a k)


-- -- -- pop↔trans-fill : ∀ n (p : 𝕡base {n = n} ≡ 𝕡base) k →
     
-- -- --         (𝕡loop k ∙ p) ≡ (𝕡loop k ∙ p)
        
-- -- -- pop↔trans-fill = {!!}

-- -- pop↔trans : ∀ n → (a b : Fin n → A) → ∀ (p : 𝕡base ≡ 𝕡base) k
-- --         → (P : PathP (λ i → 𝔽in {n = n} ((𝕡loop k ∙ p) i) → A) a b)
-- --         → Path ([ n ] a ↔ b) (𝕡loop k ∙ p , P)
-- --               (isTrans-[]↔ n a (a ∘ fst (adjT'≃ {n} k)) b
-- --                  (↔k n k a) (p , (pop↔ _ n a b p k P)))
-- -- pop↔trans {A = A} n a b p k P =
-- --  ΣPathP (refl ,
-- --     ppp)

-- --  where
-- --   ppp : PathP (λ i → PathP (λ i₁ → 𝔽in ((𝕡loop k ∙ p) i₁) → A) a b)
-- --           P
-- --           (snd
-- --            (isTrans-[]↔ n a (a ∘ fst (adjT'≃ {n = n} k)) b
-- --             (↔k n k a)
-- --             (p , pop↔ A n a b p k P)))
-- --   ppp i j = --𝔽in ((𝕡loop k ∙ p) j) → A
-- --     comp
-- --        (λ z → 𝔽in (filler'≡filler (𝕡loop k) p (~ i) z j) → A)
-- --         (λ z →
-- --          λ { (i = i0) → 
-- --              fill (λ z → 𝔽in (compPath-filler' (𝕡loop k) p (~ z) j) → A)
-- --                 (λ z → λ {(j = i0) → ↔k'P A n a k z
-- --                          ;(j = i1) → b
-- --                         }) (inS (P j)) (~ z)
-- --            ; (i = i1) → (snd
-- --            (isTrans-[]↔ n a (a ∘ fst (adjT'≃ {n = n} k)) b
-- --             (↔k n k a)
-- --             (p , pop↔ A n a b p k P))) (~ z ∨ j)
-- --            ; (j = i0) →
-- --                 fill (λ i → 𝔽in (compPath-filler (𝕡loop k) p i (~ z)) → A)
-- --                 (λ i → λ {(z = i0) → pop↔ A n a b p k P i
-- --                          ;(z = i1) → ↔k'P A n a k (~ z)
-- --                         }) (inS (↔k'P A n a k (~ z))) (i)
             
-- --            ; (j = i1) → b
         
-- --            })
-- --        (pop↔ A n a b p k P (j ∨ i))

-- --   pop→fill : ∀ i → I → (i₁ : I) →
-- --     𝔽in (compPath-filler' (𝕡loop k) p (~ i₁) i) → A
-- --   pop→fill i j =
-- --     fill (λ z → 𝔽in (compPath-filler' (𝕡loop k) p (~ z) i) → A )
-- --       (λ z →
-- --        λ {(i = i0) → ↔k'P A n a k z
-- --          ;(i = i1) → b
-- --          }) (inS (P i))


-- -- uncurry-flip : ∀ {ℓ ℓ' ℓ'' ℓ'''} → {A : Type ℓ} {B : Type ℓ'}
-- --                {C : A → A → B → Type ℓ''} {D : ∀ a a' b → C a a' b → Type ℓ'''}
-- --                → (∀ b → ∀ a a' → (c : C a a' b) → D a a' b c )
-- --                → (∀ {a a'} → (bc : Σ B (C a a')) → D a a' (fst bc) (snd bc))
-- -- uncurry-flip x bc = x _ _ _ (snd bc)

-- -- module _ (A : Type ℓ) where

-- --  Fin→/↔ : ∀ n → Type ℓ
-- --  Fin→/↔ n = (Fin n → A) // isTrans-[]↔ n


-- --  sym-/↔ : ∀ n p {a b : Fin n → A} P →
-- --               Path (Path (Fin→/↔ n) [ a ]// [ b ]//)
-- --                 (eq// (sym p , P) )
-- --                 (sym (eq// (p , symP P)))
-- --  sym-/↔ n p P i j =
-- --    hcomp
-- --      (λ z → λ {
-- --        (i = i0) → comp// (sym p , P) (p , symP P) (~ z) j
-- --       ;(i = i1) → invSides-filler
-- --                     (sym (eq// (refl , refl)))
-- --                 (sym (eq// (p , symP P))) j (~ z)   
-- --       ;(j = i0) → refl≡Id (isTrans-[]↔ n) {P i0} (refl , refl)
-- --            (ΣPathP ((sym compPathRefl) ,
-- --               symP (compPathP'-filler {B = λ x → 𝔽in {n = n} x → A} {P i0}
-- --                 {p = λ _ → 𝕡base} {q = refl}
-- --                refl refl))) (~ i) z
-- --       ;(j = i1) → eq// (p , symP P) (~ z)
-- --       })
-- --      (eq// {a = P i0} {P i0}
-- --        (lCancel p i , λ j' →
-- --         comp (λ z → 𝔽in {n = n} (rCancel-filler (sym p) z i j') → A)
-- --             ((λ z → λ { (j' = i0) → P i0
-- --                 ; (j' = i1) → P (~ z ∧ ~ i)
-- --                 ; (i = i1) → P i0
-- --                 }))
-- --             (P (j' ∧ ~ i))) j)


-- -- module Iso-𝔽in→-Fin→/↔ {A : Type ℓ} (isGroupoidA : isGroupoid A) where

-- --  isGroupoidΣ𝔽in→ : ∀ n → isGroupoid (𝔽in→ A n)
-- --  isGroupoidΣ𝔽in→ _ = isGroupoidΣ 𝕡squash
-- --      λ _ → isGroupoidΠ λ _ → isGroupoidA


-- --  zz-aloop' : ∀ n k → 
-- --     SquareP (λ i₁ j → 𝔽in {n = n} (𝕡loop k i₁) →
-- --                       𝔽in {n = n} (𝕡loop k j))
-- --     {idfun (Fin n)}
-- --     {!!}
-- --     {{!!}} {idfun _}
-- --     {!!}
-- --     {!!}
-- --     {!!}
-- --  zz-aloop' n k = {!!}

-- --  to-loop' : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- --       PathP (λ i → (𝔽in {n} (𝕡loop k i) → A) → Fin→/↔ A n) [_]// [_]//
-- --  to-loop' n k i p = eq// 
-- --                 {a = p ∘ {!!}}
-- --                 {b = p ∘ {!!} }
-- --                 ((𝕡loop k) , λ j x → p (zz-aloop' n k j i x)) i


-- -- --  zz-aloop : ∀ n k → 
-- -- --     SquareP (λ i₁ j → 𝔽in {n = n} (𝕡loop k i₁) →
-- -- --                       𝔽in {n = n} (𝕡loop k j))
-- -- --     (ua-gluePathExt (adjT'≃ {n = n} k))
-- -- --     (λ i x → glue
-- -- --         (λ { (i = i0) → adjT n k x
-- -- --            ; (i = i1) → x
-- -- --            })
-- -- --         (isInvolution-adjT n k x i))
-- -- --     (funExt (λ kk → sym (isInvolution-adjT n k kk)) ◁
-- -- --       (λ i → fst (adjT'≃ {n = n} k)
-- -- --          ∘' ua-ungluePathExt (adjT'≃ {n = n} k) i))
-- -- --     (ua-ungluePathExt (adjT'≃ {n = n} k))
-- -- --  zz-aloop n k = isSet→SquareP (λ i₁ j → isSet→ (snd (𝔽inH n (𝕡loop k j))))
-- -- --            _ _ _ _

-- -- --  -- zz-aloop-invol : ∀ n k → PathP (λ i →
-- -- --  --                        SquareP (λ i₁ j →
-- -- --  --                      𝔽in {n = n} (𝕡invol k i i₁) →
-- -- --  --                      𝔽in {n = n} (𝕡invol k i  j))
-- -- --  --                          {idfun _} {adjT n k}
-- -- --  --                          {!!}
-- -- --  --                          {_} {idfun _}
-- -- --  --                          {!!}
-- -- --  --                          (λ i₁ → {!!})
-- -- --  --                          {!!})
-- -- --  --                   (zz-aloop n k)
-- -- --  --                    (congP (λ _ → symP-fromGoal)
-- -- --  --                     (symP-fromGoal (zz-aloop n k)))
-- -- --  -- zz-aloop-invol n k = {!!}
-- -- --  zz-aloop-invol : ∀ n k →
-- -- --     SquareP (λ j' j → PathP (λ i → 𝔽in {n = n} (𝕡invol k i j') →
-- -- --                       𝔽in {n = n} (𝕡invol k i  j))
-- -- --           (zz-aloop n k j' j) (zz-aloop n k (~ j') (~ j)))
-- -- --       {refl} {refl}
-- -- --       (isSet→SquareP (λ i₁ j → isSet→ (snd (𝔽inH n (𝕡invol k j i₁))))
-- -- --            _ _ _ _)
-- -- --       {refl} {refl}
-- -- --       (isSet→SquareP (λ i₁ j → isSet→ (snd (𝔽inH n (𝕡invol k j i₁))))
-- -- --            _ _ _ _)
-- -- --       (isSet→SquareP (λ i₁ j → isSet→ (isSetFin {n = n}))
-- -- --            _ _ _ _)
-- -- --       (isSet→SquareP (λ i₁ j → isSet→ (isSetFin {n = n}))
-- -- --            _ _ _ _)
                    
-- -- --  zz-aloop-invol n k =
-- -- --    isSet→SquareP (λ i₁ j → isOfHLevelPathP 2
-- -- --      (isSet→ (snd (𝔽inH n (𝕡invol k i1  j)))) _ _)
-- -- --            _ _ _ _


-- -- --  to-loop : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- --       PathP (λ i → (𝔽in {n} (𝕡loop k i) → A) → Fin→/↔ A n) [_]// [_]//
-- -- --  to-loop n k i p = eq// 
-- -- --                 {a = p ∘ ua-gluePathExt (adjT'≃ {n = n} k) i}
-- -- --                 {b = p ∘ λ x →
-- -- --                    ua-gluePath (adjT'≃ {n = n} k)
-- -- --                      (isInvolution-adjT n k x) i }
-- -- --                 ((𝕡loop k) , λ j x → p (zz-aloop n k j i x)) i

-- -- -- --  zz-alooop : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n))
-- -- -- --       → SquareP (λ i₁ j → (fst (𝔽inH n (𝕡looop k l i₁)))
-- -- -- --               → (fst (𝔽inH n (𝕡looop k l j))))
-- -- -- --                  (λ i x → glue (λ {(i = i0) → x ;(i = i1) → _ })
-- -- -- --                       (isInvolution-adjT n l (adjT n k x) (~ i)))
-- -- -- --                  (λ i x → glue (λ {(i = i0) → _ ;(i = i1) → x })
-- -- -- --                       (isInvolution-adjT n k (adjT n l x) i))
-- -- -- --                  ((λ i x → isInvolution-adjT n k x (~ i))
-- -- -- --                    ◁ (λ i → adjT n k ∘ unglue (i ∨ ~ i)))
-- -- -- --                  ((λ i → adjT n l ∘ unglue (i ∨ ~ i)) ▷
-- -- -- --                   funExt (isInvolution-adjT n l))
-- -- -- --  zz-alooop n k l = isSet→SquareP (λ i₁ j → isSet→ (snd (𝔽inH n (𝕡looop k l j))))
-- -- -- --              _ _ _ _
 
-- -- -- --  to-looop : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- --       PathP (λ i → (𝔽in {n} (𝕡looop k l i) → A) → Fin→/↔ A n) [_]// [_]//
-- -- -- --  to-looop n k l =
-- -- -- --     λ i p → eq//
-- -- -- --                  -- {a = p ∘ λ x → glue (λ {(i = i0) → x ;(i = i1) → _ })
-- -- -- --                  --      (isInvolution-adjT n l (adjT n k x) (~ i))}
-- -- -- --                  -- {b = p ∘ λ x → glue (λ {(i = i0) → _ ;(i = i1) → x })
-- -- -- --                  --      (isInvolution-adjT n k (adjT n l x) i)}
-- -- -- --                ((𝕡looop k l) ,
-- -- -- --     λ j x → p (zz-alooop n k l j i x)) i


-- -- -- --  to-invol' : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- --       SquareP (λ i j → (𝔽in {n = n} (𝕡invol k i j) → A) → Fin→/↔ A n)
-- -- -- --       (to-loop n k)
-- -- -- --       (λ j p → eq// (sym (𝕡loop k) , λ j' x → p (zz-aloop n k (~ j') (~ j) x)) j)
-- -- -- --       refl
-- -- -- --       refl
-- -- -- --  to-invol' n k i j p =
-- -- -- --     eq// (𝕡invol k i , λ j' → p ∘ zz-aloop-invol n k j' j i ) j 
  

-- -- -- --  to-invol : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- --       SquareP (λ i j → (𝔽in {n = n} (𝕡invol k i j) → A) → Fin→/↔ A n)
-- -- -- --       (to-loop n k) (symP (to-loop n k)) refl refl
-- -- -- --  to-invol n k  = to-invol' n k ▷
-- -- -- --      invEq (congEquiv (invEquiv funExtDepEquiv))      
-- -- -- --       λ i p j → sym-/↔ A n (𝕡loop k)
-- -- -- --          (λ j' → p j ∘ (zz-aloop n k (~ j') (~ j))) i j 




-- -- -- --  -- ss' : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) → SquareP (λ i j →
-- -- -- --  --              PathP (λ j' → 𝔽in {n = n} (𝕡looop k l j')
-- -- -- --  --                          → 𝔽in {n = n} (𝕡comp k l i j))
-- -- -- --  --                 {!!}
-- -- -- --  --                 {!!})
-- -- -- --  --           (λ j j' → {!!})
-- -- -- --  --           (λ j j' → {!zz-aloop n l j' j!})
-- -- -- --  --           (λ i j' → zz-alooop n k l j' i)
-- -- -- --  --           λ _ j' → unglueFlooopPathExt n k l j'
-- -- -- --  -- ss' = {!!}

-- -- -- --  p* : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- --        SquareP (λ i j → 𝔽in {n = n} 𝕡base → 𝔽in {n = n} (𝕡comp k l i j))
-- -- -- --           (λ j → gluePathAdjT' n k j ∘' adjT n l) --(gluePathAdjT' n k)
-- -- -- --           (ua-gluePathExt (adjT'≃ {n = n} l)) --(gluePathAdjT' n l)
-- -- -- --           (λ i x → glue (λ { (i = i0) → adjT n k (adjT n l x)
-- -- -- --                          ; (i = i1) → x
-- -- -- --                          }) (isInvolution-adjT n k (adjT n l x) i))
-- -- -- --           λ i → adjT n l 
-- -- -- --  p* n k l = isSet→SquareP (λ i j → isSet→ (snd (𝔽inH n (𝕡comp k l i j))))
-- -- -- --              _ _ _ _


-- -- -- --  ss* : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) → SquareP (λ i j' →
-- -- -- --            PathP (λ j → 𝔽in {n = n} (𝕡looop k l j')
-- -- -- --                        → 𝔽in {n = n} (𝕡comp k l i j))
-- -- -- --                  (zz-alooop n k l j' i)
-- -- -- --                  (unglueFlooopPathExt n k l j'))
-- -- -- --           {ua-gluePathExt (adjT'≃ {n = n} k)}
          
-- -- -- --           (isSet→SquareP (λ j' j → isSet→ (snd (𝔽inH n (𝕡comp k l i0 j))))
-- -- -- --              _ _ _ _)
-- -- -- --           {λ j → gluePathAdjT' n l j ∘' adjT n k} 
-- -- -- --           (isSet→SquareP (λ j' j → isSet→ (snd (𝔽inH n (𝕡comp k l i1 j))))
-- -- -- --              _ _ _ _)
-- -- -- --           (isSet→SquareP (λ i j → isSet→ (snd (𝔽inH n (𝕡comp k l i j))))
-- -- -- --              _ _ _ _)
-- -- -- --           (p* n k l)
-- -- -- --  ss* n k l = isSet→SquareP (λ i j' → isOfHLevelPathP 2
-- -- -- --      (isSet→ (snd (𝔽inH n (𝕡comp k l i i1)))) _ _)
-- -- -- --            _ _ _ _


-- -- -- --  ss** : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) → SquareP (λ i j' →
-- -- -- --            PathP (λ j → 𝔽in {n = n} (𝕡loop l j')
-- -- -- --                        → 𝔽in {n = n} (𝕡comp k l i j))
-- -- -- --                  ((isSet→SquareP
-- -- -- --                     (λ i j' → isSet→ {A = 𝔽in {n = n} (𝕡loop l j')}
-- -- -- --                         (snd (𝔽inH n (𝕡comp k l i i0))))
                    
                    
-- -- -- --                 (λ z → adjT n k ∘ ua-ungluePathExt (adjT'≃ {n = n} l) z)
-- -- -- --                  (ungluePathAdjT' n l)
-- -- -- --                 ((λ i x → glue (λ { (i = i0) → adjT n k (adjT n l x)
-- -- -- --                          ; (i = i1) → x
-- -- -- --                          }) (isInvolution-adjT n k (adjT n l x) i)))
-- -- -- --                          (glueFlooopPathExt n k l)) i j')
-- -- -- --                  (ua-ungluePathExt (adjT'≃ {n = n} l) j'))
-- -- -- --           {λ j → gluePathAdjT' n k j ∘ adjT n l} {gluePathAdjT' n k}
-- -- -- --           (isSet→SquareP (λ j' j → isSet→ (snd (𝔽inH n (𝕡comp k l i0 j))))
-- -- -- --             _ _ _ _)
-- -- -- --           (λ j' j → zz-aloop n l j' j)
-- -- -- --           (p* n k l)
-- -- -- --           (isSet→SquareP (λ i j → isSet→ (snd (𝔽inH n (𝕡comp k l i j))))
-- -- -- --             _ _ _ _)
-- -- -- --  ss** n k l = isSet→SquareP (λ i j' → isOfHLevelPathP 2
-- -- -- --      (isSet→ (snd (𝔽inH n (𝕡comp k l i i1)))) _ _)
-- -- -- --            _ _ _ _

-- -- -- --  zz-comp-eq : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- --                 SquareP (λ i j →
-- -- -- --                        PathP (λ j' → {!!} → Fin n)
-- -- -- --                           (adjT n k)
-- -- -- --                           (idfun _))
-- -- -- --                    {!!}
-- -- -- --                    {!!}
-- -- -- --                    {!!}
-- -- -- --                    {!!}
-- -- -- --  zz-comp-eq n k l = {!!}
 
-- -- -- --  to-comp-eq : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- --       Path (PathP (λ i → (𝔽in {n = n} (𝕡comp k l i i1) → A) → Fin→/↔ A n)
-- -- -- --                ([_]// ∘' (_∘' adjT n k)) [_]//)
-- -- -- --         (λ i f → eq// {a = f ∘' adjT n k} {f}
-- -- -- --           (isTrans-[]↔ n (f ∘' adjT n k) (f ∘' adjT n l)
-- -- -- --                   f
-- -- -- --              (𝕡looop k l , λ j' → f ∘' unglueFlooopPathExt n k l j')
-- -- -- --              (𝕡loop l , λ j' → f ∘' ua-ungluePathExt (adjT'≃ {n = n} l) j')) i)
-- -- -- --         (λ i f → to-loop n k i (f ∘' ua-ungluePathExt (adjT'≃ {n = n} k) i))
-- -- -- --  to-comp-eq n k l j i f =
-- -- -- --    eq// {a = f ∘' {!!}}
-- -- -- --         {b = f ∘' {!!}}
-- -- -- --         {!!}
-- -- -- --         i

-- -- -- -- -- --  to-comp' : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- --       SquareP (λ j i → (𝔽in {n = n} (𝕡comp k l i j) → A) → Fin→/↔ A n)
-- -- -- -- -- --         (to-looop n k l)
-- -- -- -- -- --         (λ i f → to-loop n k i (f ∘' ua-ungluePathExt (adjT'≃ {n = n} k) i))
-- -- -- -- -- --         -- λ i f → eq// {a = f ∘' adjT n k} {f}
-- -- -- -- -- --         --   (isTrans-[]↔ n (f ∘' adjT n k) (f ∘' adjT n l)
-- -- -- -- -- --         --           f
-- -- -- -- -- --         --      (𝕡looop k l , λ j' → f ∘' unglueFlooopPathExt n k l j')
-- -- -- -- -- --         --      (𝕡loop l , λ j' → f ∘' ua-ungluePathExt (adjT'≃ {n = n} l) j')) i
-- -- -- -- -- --         (λ j f → [ f ∘ ua-gluePathExt (adjT'≃ {n = n} k) j ]//)
-- -- -- -- -- --         (to-loop n l)
-- -- -- -- -- --  to-comp' n k l = 
-- -- -- -- -- --     (λ j i f → 
-- -- -- -- -- --    comp//
-- -- -- -- -- --     (𝕡looop k l , λ j' → f ∘' ss* n k l i j' j)
-- -- -- -- -- --     (𝕡loop l , λ j' → f ∘' ss** n k l i j' j) j i)
-- -- -- -- -- --     ▷ to-comp-eq n k l


-- -- -- -- -- -- --  ploop∧ : ∀ n k → SquareP (λ z j → (a : 𝔽in {n = n} (𝕡loop k (j ∧ z))) →
-- -- -- -- -- -- --                            𝔽in {n = n} (𝕡loop k j))
-- -- -- -- -- -- --                   (ua-gluePathExt (adjT'≃ {n = n} k))
-- -- -- -- -- -- --                   (λ _ → idfun _)
-- -- -- -- -- -- --                   refl
-- -- -- -- -- -- --                   (ua-ungluePathExt (adjT'≃ {n = n} k))
-- -- -- -- -- -- --  ploop∧ n k =
-- -- -- -- -- -- --     (isSet→SquareP (λ z j → isSet→ (snd (𝔽inH n (𝕡loop k j))))
-- -- -- -- -- -- --             _ _ _ _)

-- -- -- -- -- -- --  to-comp : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- --       SquareP (λ j i → (𝔽in {n = n} (𝕡comp k l j i) → A) → Fin→/↔ A n)
-- -- -- -- -- -- --       (to-loop n k)
-- -- -- -- -- -- --       (to-loop n l) (to-looop n k l) refl
-- -- -- -- -- -- --  to-comp n k l i j f =   
-- -- -- -- -- -- --    hcomp
-- -- -- -- -- -- --      (λ z →
-- -- -- -- -- -- --       λ { (i = i0) → to-loop n k (j ∧ z) (f ∘ ploop∧ n k z j)
-- -- -- -- -- -- --         ; (i = i1) → to-comp' n k l j i f 
-- -- -- -- -- -- --         ; (j = i0) → to-comp' n k l j i f
-- -- -- -- -- -- --         ; (j = i1) → {!!} --to-comp' n k l (i ∨ z) j f
-- -- -- -- -- -- --         })
-- -- -- -- -- -- --      (to-comp' n k l j i f)
 

-- -- -- -- -- -- -- --  zz-to-comm : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) (x' : A.commT (fst k) (fst l))
-- -- -- -- -- -- -- --                   → SquareP (λ i j' →
-- -- -- -- -- -- -- --                    PathP (λ j → 𝔽in {n} (𝕡comm k l x' j' j)
-- -- -- -- -- -- -- --                                → 𝔽in {n} (𝕡comm k l x' i j))
-- -- -- -- -- -- -- --                      (zz-alooop n k l j' i)
-- -- -- -- -- -- -- --                      (zz-alooop n l k j' i))
-- -- -- -- -- -- -- --                 {refl} {sym (funExt (adjT-comm n k l x'))}
-- -- -- -- -- -- -- --                 (isSet→SquareP (λ i j' → (isSet→ (isSetFin {n = n})))
-- -- -- -- -- -- -- --                       _ _ _ _)
-- -- -- -- -- -- -- --                 {funExt (adjT-comm n k l x')}
-- -- -- -- -- -- -- --                 {refl}
-- -- -- -- -- -- -- --                 (isSet→SquareP (λ i j' → (isSet→ (isSetFin {n = n})))
-- -- -- -- -- -- -- --                       _ _ _ _)
-- -- -- -- -- -- -- --                 (isSet→SquareP (λ i j →
-- -- -- -- -- -- -- --                    isSet→ (snd (𝔽inH n (𝕡comm k l x' i j))))
-- -- -- -- -- -- -- --                     _ _ _ _)
-- -- -- -- -- -- -- --                 (isSet→SquareP (λ i j →
-- -- -- -- -- -- -- --                    isSet→ (snd (𝔽inH n (𝕡comm k l x' i j))))
-- -- -- -- -- -- -- --                     _ _ _ _)
-- -- -- -- -- -- -- --  zz-to-comm n k l x' = 
-- -- -- -- -- -- -- --   isSet→SquareP (λ i j' → isOfHLevelPathP 2
-- -- -- -- -- -- -- --      (isSet→ (snd (𝔽inH n (𝕡comm k l x' i i1)))) _ _)
-- -- -- -- -- -- -- --            _ _ _ _

-- -- -- -- -- -- -- --  to-comm : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n))
-- -- -- -- -- -- -- --    (x : A.commT (fst k) (fst l)) →
-- -- -- -- -- -- -- --    SquareP (λ i j → (𝔽in {n} (𝕡comm k l x i j) → A) → Fin→/↔ A n) refl
-- -- -- -- -- -- -- --    refl (to-looop n k l) (to-looop n l k)
-- -- -- -- -- -- -- --  to-comm n k l x' i j f =
-- -- -- -- -- -- -- --    eq// ((λ i → 𝕡comm k l x' i j) ,
-- -- -- -- -- -- -- --      λ j' → f ∘ zz-to-comm n k l x' i j' j) i

-- -- -- -- -- -- -- --  to : ∀ n → R𝕡elim {n = n} (λ z → (y : 𝔽in z → A) → Fin→/↔ A n)
-- -- -- -- -- -- -- --  R𝕡elim.isGroupoidA (to n) _ = isGroupoidΠ λ _ → squash//
-- -- -- -- -- -- -- --  R𝕡elim.abase (to n) = [_]//
-- -- -- -- -- -- -- --  R𝕡elim.aloop (to n) = to-loop n  


-- -- -- -- -- -- -- --  R𝕡elim.alooop (to n) = to-looop n

-- -- -- -- -- -- -- --  R𝕡elim.acomp (to n) k l =
-- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- --    -- hcomp (λ z →
-- -- -- -- -- -- -- --    --    λ { (i = i0) → {!to-invol n k (~ z) i!}
-- -- -- -- -- -- -- --    --      ; (i = i1) → to-loop n l j p 
-- -- -- -- -- -- -- --    --      ; (j = i0) → to-looop n k l i p
-- -- -- -- -- -- -- --    --      ; (j = i1) → {!!}
-- -- -- -- -- -- -- --    --      })
-- -- -- -- -- -- -- --    --   (comp// {a = {!!}} {b = {!!}} {c = {!!}}
-- -- -- -- -- -- -- --    --       ((𝕡looop k l) ,
-- -- -- -- -- -- -- --    --         {!!}) {!!} j i)
-- -- -- -- -- -- -- --    -- -- {!comp// {a = ?} {?} {?} ? ? i  !}
-- -- -- -- -- -- -- --  R𝕡elim.ainvol (to n) = to-invol n
-- -- -- -- -- -- -- --  R𝕡elim.acomm (to n) = to-comm n
-- -- -- -- -- -- -- --  R𝕡elim.abraid (to n) = {!!}
 
-- -- -- -- -- -- -- -- --  from : ∀ n → Fin→/↔ A n → 𝔽in→ A n
-- -- -- -- -- -- -- -- --  from n = GQ.Rrec.f w
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   w : Rrec// (𝔽in→ A n)
-- -- -- -- -- -- -- -- --   Rrec//.Bgpd w = isGroupoidΣ𝔽in→ n
    
-- -- -- -- -- -- -- -- --   Rrec//.fb w = 𝕡base ,_
-- -- -- -- -- -- -- -- --   Rrec//.feq w = ΣPathP
-- -- -- -- -- -- -- -- --   Rrec//.fsq w (p , P) (q , Q) =
-- -- -- -- -- -- -- -- --     ΣSquareP ((compPath-filler _ _) ,
-- -- -- -- -- -- -- -- --       compPathP'-filler
-- -- -- -- -- -- -- -- --         {B = λ x → 𝔽in x → A} {p = p} {q = q} P Q)


-- -- -- -- -- -- -- -- --  ss''k :  ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- --    (a : Fin n → A) →
-- -- -- -- -- -- -- -- --         (λ i → to-loop n k i (↔k'P A n a k i))  ≡ eq// (↔k n k a)

-- -- -- -- -- -- -- -- --  ss''k n k a j i = 
-- -- -- -- -- -- -- -- --     eq// {a = a ∘ ungluePathAdjT' n k (~ j ∧ i)
-- -- -- -- -- -- -- -- --            ∘ ua-gluePathExt (adjT'≃ {n = n} k) (~ j ∧ i)}
-- -- -- -- -- -- -- -- --          {b = a ∘ ungluePathAdjT' n k (j ∨  i)
-- -- -- -- -- -- -- -- --                  ∘ λ x →
-- -- -- -- -- -- -- -- --                    ua-gluePath (adjT'≃ {n = n} k)
-- -- -- -- -- -- -- -- --                      (isInvolution-adjT n k x) (j ∨ i) }
-- -- -- -- -- -- -- -- --           (𝕡loop k , λ j' x → a (ccc i j j' x) ) i 
-- -- -- -- -- -- -- -- --    where

-- -- -- -- -- -- -- -- --      ccc : SquareP (λ i j → PathP
-- -- -- -- -- -- -- -- --                  (λ j' → 𝔽in {n = n} (𝕡loop k j') → Fin n)
-- -- -- -- -- -- -- -- --                  (ungluePathAdjT' n k (~ j ∧ i)
-- -- -- -- -- -- -- -- --                       ∘ ua-gluePathExt (adjT'≃ {n = n} k) (~ j ∧ i))
-- -- -- -- -- -- -- -- --                  (ungluePathAdjT' n k (j ∨  i)
-- -- -- -- -- -- -- -- --                  ∘ λ x →
-- -- -- -- -- -- -- -- --                    ua-gluePath (adjT'≃ {n = n} k)
-- -- -- -- -- -- -- -- --                      (isInvolution-adjT n k x) (j ∨ i) ))
-- -- -- -- -- -- -- -- --                   (isSet→SquareP (λ _ _ → isSet→ (isSetFin {n = n})) _ _ _ _)
-- -- -- -- -- -- -- -- --                   (isSet→SquareP (λ _ _ → isSet→ (isSetFin {n = n})) _ _ _ _)
-- -- -- -- -- -- -- -- --                   (λ i j' → ungluePathAdjT' n k i ∘ (zz-aloop n k j' i))
-- -- -- -- -- -- -- -- --                   λ _ → ungluePathAdjT' n k
-- -- -- -- -- -- -- -- --      ccc = isSet→SquareP (λ i j → isOfHLevelPathP 2 (isSet→ (isSetFin {n})) _ _)
-- -- -- -- -- -- -- -- --       _ _ _ _

-- -- -- -- -- -- -- -- --  from-to : ∀ n → section (uncurry (R𝕡elim.f (to n))) (from n)
-- -- -- -- -- -- -- -- --  from-to n = GQ.RelimSet.f w
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   w : RelimSet (λ z → uncurry (R𝕡elim.f (to n)) (from n z) ≡ z)
-- -- -- -- -- -- -- -- --   RelimSet.truncB w _ = squash// _ _
-- -- -- -- -- -- -- -- --   RelimSet.fb w _ = refl
-- -- -- -- -- -- -- -- --   RelimSet.fbEq w = 
-- -- -- -- -- -- -- -- --     uncurry-flip {A = Fin n → A}
-- -- -- -- -- -- -- -- --        {C = λ a a' p → PathP (λ i → 𝔽in (p i) → A) a a'}
-- -- -- -- -- -- -- -- --        {D = λ a a' p P →
-- -- -- -- -- -- -- -- --         let r : [ n ] a ↔ a'
-- -- -- -- -- -- -- -- --             r = (p , P)
-- -- -- -- -- -- -- -- --         in
-- -- -- -- -- -- -- -- --           PathP
-- -- -- -- -- -- -- -- --           (λ i → uncurry (R𝕡elim.f (to n)) (from n (eq// r i)) ≡ eq// r i)
-- -- -- -- -- -- -- -- --           (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a ]//))
-- -- -- -- -- -- -- -- --           (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a' ]//))} 
-- -- -- -- -- -- -- -- --     (𝕡baseΩ-elimProp n _ (λ _ → isPropΠ3 λ _ _ _ →
-- -- -- -- -- -- -- -- --           isOfHLevelPathP' 1 (squash// _ _) _ _)
-- -- -- -- -- -- -- -- --       ss' ss'')

-- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- --     ss' : (a b : Fin n → A) → (y : a ≡ b) →
-- -- -- -- -- -- -- -- --           Square {A = (Fin n → A) // isTrans-[]↔ n}
-- -- -- -- -- -- -- -- --             (λ j → [ a ]//)
-- -- -- -- -- -- -- -- --             (λ j → [ b ]//)
-- -- -- -- -- -- -- -- --             (λ i → [ y i ]//)
-- -- -- -- -- -- -- -- --             (λ i → eq// (refl , y) i)          

-- -- -- -- -- -- -- -- --     ss' a b y i j =
-- -- -- -- -- -- -- -- --               hcomp
-- -- -- -- -- -- -- -- --         (λ l →
-- -- -- -- -- -- -- -- --            λ { (i = i0) → [ a ]//
-- -- -- -- -- -- -- -- --              ; (i = i1) → eq// {a = y (l ∨ j)} {b = b}
-- -- -- -- -- -- -- -- --                         (refl , (λ j' → y (l ∨ j ∨ j'))) (~ l)
-- -- -- -- -- -- -- -- --              ; (j = i0) → eq// {a = y (i ∧ l)} {b = b}
-- -- -- -- -- -- -- -- --                                (refl , (λ j' → (y ((i ∧ l) ∨  j')))) (i ∧ ~ l) 
-- -- -- -- -- -- -- -- --              ; (j = i1) → comp// {a = a} {b = b} {c = b}
-- -- -- -- -- -- -- -- --                               (refl , y) (refl , refl) (~ l) i
-- -- -- -- -- -- -- -- --              }) (eq// {a = a} {b = b}
-- -- -- -- -- -- -- -- --                     (compPathRefl j ,  compPathP'-filler 
-- -- -- -- -- -- -- -- --                       {B = λ x → 𝔽in {n = n} x → A}
-- -- -- -- -- -- -- -- --                        {p = λ _ → 𝕡base {n = n}} {q = refl} y refl
-- -- -- -- -- -- -- -- --                     j) i)
-- -- -- -- -- -- -- -- --     ss'' : (p : Path (ℙrm n) 𝕡base 𝕡base)
-- -- -- -- -- -- -- -- --       (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- --       ((a a' : Fin n → A) (c : PathP (λ i → 𝔽in (p i) → A) a a') →
-- -- -- -- -- -- -- -- --        PathP
-- -- -- -- -- -- -- -- --        (λ i →
-- -- -- -- -- -- -- -- --           uncurry (R𝕡elim.f (to n)) (from n (eq// (p , c) i)) ≡
-- -- -- -- -- -- -- -- --           eq// (p , c) i)
-- -- -- -- -- -- -- -- --        (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a ]//))
-- -- -- -- -- -- -- -- --        (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a' ]//))) →
-- -- -- -- -- -- -- -- --       (a a' : Fin n → A)
-- -- -- -- -- -- -- -- --       (c : PathP (λ i → 𝔽in ((𝕡loop k ∙ p) i) → A) a a') →
-- -- -- -- -- -- -- -- --       PathP
-- -- -- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- -- -- --          uncurry (R𝕡elim.f (to n)) (from n (eq// (𝕡loop k ∙ p , c) i)) ≡
-- -- -- -- -- -- -- -- --          eq// (𝕡loop k ∙ p , c) i)
-- -- -- -- -- -- -- -- --       (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a ]//))
-- -- -- -- -- -- -- -- --       (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a' ]//))


-- -- -- -- -- -- -- -- --     ss'' p k y a b P i j = 
-- -- -- -- -- -- -- -- --        hcomp (λ z →
-- -- -- -- -- -- -- -- --         λ { (i = i0) → [ a ]//
-- -- -- -- -- -- -- -- --           ; (i = i1) → (y _ _ (pop↔ A n a b p k P)) z j
-- -- -- -- -- -- -- -- --           ; (j = i0) →
-- -- -- -- -- -- -- -- --             (_▷_ {A = λ z → [ a ]// ≡
-- -- -- -- -- -- -- -- --               uncurry (R𝕡elim.f (to n)) (from n
-- -- -- -- -- -- -- -- --                  (eq// (p , (pop↔ A n a b p k P)) z))}
-- -- -- -- -- -- -- -- --                (λ z i →
-- -- -- -- -- -- -- -- --                  uncurry (R𝕡elim.f (to n)) (from n
-- -- -- -- -- -- -- -- --                   (comp// (↔k n k a)
-- -- -- -- -- -- -- -- --                     (p , pop↔ A n a b p k P) z i)) )
-- -- -- -- -- -- -- -- --                (cong
-- -- -- -- -- -- -- -- --                 (cong′ ((uncurry (R𝕡elim.f (to n))) ∘ (from n)) ∘ eq//)
-- -- -- -- -- -- -- -- --                 (sym (pop↔trans n a b p k P))) ) z i
-- -- -- -- -- -- -- -- --           ; (j = i1) →
-- -- -- -- -- -- -- -- --             (comp// (↔k n k a)
-- -- -- -- -- -- -- -- --                     (p , pop↔ A n a b p k P)
-- -- -- -- -- -- -- -- --               ▷ cong eq// (sym (pop↔trans n a b p k P)) ) z i
-- -- -- -- -- -- -- -- --           }) (ss''k n k a j i)

-- -- -- -- -- -- -- -- --  to-from : ∀ n → retract (uncurry (R𝕡elim.f (to n))) (from n)
-- -- -- -- -- -- -- -- --  to-from n = uncurry (R𝕡elimSet.f w)
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   w : R𝕡elimSet
-- -- -- -- -- -- -- -- --         (λ z →
-- -- -- -- -- -- -- -- --            (y : 𝔽in z → A) →
-- -- -- -- -- -- -- -- --            from n (uncurry (R𝕡elim.f (to n)) (z , y)) ≡ (z , y))
-- -- -- -- -- -- -- -- --   R𝕡elimSet.isSetA w _ = isSetΠ λ _ → isGroupoidΣ𝔽in→ _ _ _
-- -- -- -- -- -- -- -- --   R𝕡elimSet.abase w _ = refl
-- -- -- -- -- -- -- -- --   R𝕡elimSet.aloop w k =
-- -- -- -- -- -- -- -- --     funExtDep λ p → ΣSquareP ((λ i j → 𝕡loop k i) ,
-- -- -- -- -- -- -- -- --          S.congSqP (λ i j → p i ∘'_)
-- -- -- -- -- -- -- -- --             (isSet→SquareP (λ i _ → isSet→ (snd (𝔽inH n (𝕡loop k i))))
-- -- -- -- -- -- -- -- --               _ _ _ _) )
  
-- -- -- -- -- -- -- -- --   R𝕡elimSet.alooop w k l =
-- -- -- -- -- -- -- -- --      funExtDep λ p → ΣSquareP ((λ i j → 𝕡looop k l i) ,
-- -- -- -- -- -- -- -- --          S.congSqP (λ i j → p i ∘'_)
-- -- -- -- -- -- -- -- --             (isSet→SquareP (λ i _ → isSet→ (snd (𝔽inH n (𝕡looop k l i))))
-- -- -- -- -- -- -- -- --               _ _ _ _))

-- -- -- -- -- -- -- -- --  Iso-𝔽in→-Fin→/↔ : ∀ n → Iso (𝔽in→ A n) (Fin→/↔ A n)
-- -- -- -- -- -- -- -- --  Iso.fun (Iso-𝔽in→-Fin→/↔ n) = uncurry (R𝕡elim.f (to n))
-- -- -- -- -- -- -- -- --  Iso.inv (Iso-𝔽in→-Fin→/↔ n) = from n
-- -- -- -- -- -- -- -- --  Iso.rightInv (Iso-𝔽in→-Fin→/↔ n) = from-to n
-- -- -- -- -- -- -- -- --  Iso.leftInv (Iso-𝔽in→-Fin→/↔ n) = to-from n

-- -- -- -- -- -- -- -- --  -- Iso-𝔽in→-Fin→/↔ : Iso (Σ _ (𝔽in→ A)) (Σ _ (Fin→/↔ A))
-- -- -- -- -- -- -- -- --  -- Iso.fun Iso-𝔽in→-Fin→/↔ = {!!}
-- -- -- -- -- -- -- -- --  -- Iso.inv Iso-𝔽in→-Fin→/↔ = {!!}
-- -- -- -- -- -- -- -- --  -- Iso.rightInv Iso-𝔽in→-Fin→/↔ = {!!}
-- -- -- -- -- -- -- -- --  -- Iso.leftInv Iso-𝔽in→-Fin→/↔ = {!!}




-- -- -- -- -- -- -- -- -- -- Rsucℙrm : ∀ n → R𝕡rec {n = n} (ℙrm (suc n))
-- -- -- -- -- -- -- -- -- -- R𝕡rec.abase (Rsucℙrm n) = 𝕡base
-- -- -- -- -- -- -- -- -- -- R𝕡rec.aloop (Rsucℙrm n) k = 𝕡loop (suc (fst k) , (snd k))
-- -- -- -- -- -- -- -- -- -- R𝕡rec.alooop (Rsucℙrm n) k l =
-- -- -- -- -- -- -- -- -- --   𝕡looop _ _
-- -- -- -- -- -- -- -- -- -- R𝕡rec.acomp (Rsucℙrm n) k l =
-- -- -- -- -- -- -- -- -- --   𝕡comp _ _
-- -- -- -- -- -- -- -- -- -- R𝕡rec.ainvol (Rsucℙrm n) k =
-- -- -- -- -- -- -- -- -- --   𝕡invol _
-- -- -- -- -- -- -- -- -- -- R𝕡rec.acomm (Rsucℙrm n) k l x =
-- -- -- -- -- -- -- -- -- --   𝕡comm _ _ (A.suc-commT (fst k) (fst l) x)
-- -- -- -- -- -- -- -- -- -- R𝕡rec.abraid (Rsucℙrm n) k k< =
-- -- -- -- -- -- -- -- -- --   𝕡braid _ _
-- -- -- -- -- -- -- -- -- -- R𝕡rec.asquash (Rsucℙrm n) = 𝕡squash

-- -- -- -- -- -- -- -- -- -- sucℙrm : ∀ n → ℙrm n → ℙrm (suc n)
-- -- -- -- -- -- -- -- -- -- sucℙrm n = R𝕡rec.f {n = n} (Rsucℙrm n)

-- -- -- -- -- -- -- -- -- -- fm2base : ℕ → FMSet2 Unit
-- -- -- -- -- -- -- -- -- -- fm2base zero = []
-- -- -- -- -- -- -- -- -- -- fm2base (suc x) = _ ∷2 (fm2base x)

-- -- -- -- -- -- -- -- -- -- fm2loop : ∀ n → ℕ → fm2base n ≡ fm2base n
-- -- -- -- -- -- -- -- -- -- fm2loop (suc n) (suc x) = cong (tt ∷2_) (fm2loop n x)
-- -- -- -- -- -- -- -- -- -- fm2loop zero x = refl
-- -- -- -- -- -- -- -- -- -- fm2loop (suc zero) zero = refl
-- -- -- -- -- -- -- -- -- -- fm2loop (suc (suc n)) zero = comm _ _ _

-- -- -- -- -- -- -- -- -- -- RtoFM2⊤ : ∀ n → R𝕡rec {n = n} (FMSet2 Unit)
-- -- -- -- -- -- -- -- -- -- R𝕡rec.abase (RtoFM2⊤ n) = fm2base n
-- -- -- -- -- -- -- -- -- -- R𝕡rec.aloop (RtoFM2⊤ n) (k , _) = fm2loop n k
-- -- -- -- -- -- -- -- -- -- --   cong (tt ∷2_) (R𝕡rec.aloop (RtoFM2⊤ n) (k , k<) )
-- -- -- -- -- -- -- -- -- -- -- R𝕡rec.aloop (RtoFM2⊤ (suc (suc n))) (zero , k<) = comm _ _ _

-- -- -- -- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ n) (zero , k<) (zero , l<) = refl
-- -- -- -- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ (suc n)) (suc k , k<) (suc l , l<) =
-- -- -- -- -- -- -- -- -- --     cong (tt ∷2_) (R𝕡rec.alooop (RtoFM2⊤ n) (k , k<) (l , l<))
-- -- -- -- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ (suc (suc n))) (zero , k<) (suc (suc l) , l<) i =
-- -- -- -- -- -- -- -- -- --   comm _ _ (R𝕡rec.aloop (RtoFM2⊤ n) (l , l<) (~ i)) (i)
-- -- -- -- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ (suc (suc n))) (suc (suc k) , k<) (zero , l<) i =
-- -- -- -- -- -- -- -- -- --   comm _ _ (R𝕡rec.aloop (RtoFM2⊤ n) (k , k<) i) (~ i)
  
-- -- -- -- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc zero , l<) =
-- -- -- -- -- -- -- -- -- --   sym (commmR _ _ _ _)  
-- -- -- -- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ (suc (suc (suc n)))) (suc zero , k<) (zero , l<) =
-- -- -- -- -- -- -- -- -- --   commmL _ _ _ _
  
-- -- -- -- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc n)) (zero , k<) (zero , l<) i j =
-- -- -- -- -- -- -- -- -- --   R𝕡rec.aloop (RtoFM2⊤ (suc n)) (0 , isProp≤ {m = 1} {n = n} k< l< i) j
 
-- -- -- -- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc zero , l<) =
-- -- -- -- -- -- -- -- -- --    symP (commpR tt tt tt (fm2base n))
-- -- -- -- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc (suc l) , l<) i j =
-- -- -- -- -- -- -- -- -- --   comm _ _ ((R𝕡rec.aloop (RtoFM2⊤ (suc n)) (l , l<) (~ i ∨ j))) (i ∨ j)
-- -- -- -- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (suc zero , k<) (zero , l<) =
-- -- -- -- -- -- -- -- -- --    (λ j i → tt ∷2 comm-inv tt tt (fm2base n) j i)
-- -- -- -- -- -- -- -- -- --     ◁ congP (λ _ → symP-fromGoal) (commpL tt tt tt (fm2base n)) ▷
-- -- -- -- -- -- -- -- -- --      λ j i → comm-inv tt tt (tt ∷2 fm2base n) (~ j) i
-- -- -- -- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (suc (suc k) , k<) (zero , l<) i j =
-- -- -- -- -- -- -- -- -- --     comm _ _ (R𝕡rec.aloop (RtoFM2⊤ (suc n)) (k , k<) (i ∨ j)) (~ i ∨  j)

-- -- -- -- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc n)) (suc k , k<) (suc l , l<) i j = 
-- -- -- -- -- -- -- -- -- --  tt ∷2 R𝕡rec.acomp (RtoFM2⊤ n) (k , k<) (l , l<) i j
 
-- -- -- -- -- -- -- -- -- -- R𝕡rec.ainvol (RtoFM2⊤ (suc (suc n))) (zero , k<) = comm-inv _ _ _
-- -- -- -- -- -- -- -- -- -- R𝕡rec.ainvol (RtoFM2⊤ (suc (suc (suc n)))) (suc k , k<) =
-- -- -- -- -- -- -- -- -- --   cong (cong (tt  ∷2_)) (R𝕡rec.ainvol (RtoFM2⊤ (suc (suc n))) (k , k<))
-- -- -- -- -- -- -- -- -- -- R𝕡rec.acomm (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc (suc l) , l<) x i j =
-- -- -- -- -- -- -- -- -- --   comm-inv tt tt
-- -- -- -- -- -- -- -- -- --     (R𝕡rec.ainvol (RtoFM2⊤ (suc n)) (l , l<) (~ j) i) (~ j) (~ i)
-- -- -- -- -- -- -- -- -- -- R𝕡rec.acomm (RtoFM2⊤ (suc n)) (suc k , k<) (suc l , l<) x i j = 
-- -- -- -- -- -- -- -- -- --   tt ∷2 R𝕡rec.acomm (RtoFM2⊤ (n)) (k , k<) (l , l<)
-- -- -- -- -- -- -- -- -- --     (A.pred-commT k l x) i j

-- -- -- -- -- -- -- -- -- -- R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc n)))) zero k< =
-- -- -- -- -- -- -- -- -- --   flipSquare
-- -- -- -- -- -- -- -- -- --     ( (λ i j → commmL≡R tt tt tt (fm2base n) (~ i)  (~ j))
-- -- -- -- -- -- -- -- -- --       ◁ ((flipSquare (symP-fromGoal (hex tt tt tt (fm2base n))))))

-- -- -- -- -- -- -- -- -- -- R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc (suc n))))) (suc k) k< i j =
-- -- -- -- -- -- -- -- -- --  tt ∷2 R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc n)))) k k< i j
-- -- -- -- -- -- -- -- -- -- R𝕡rec.asquash (RtoFM2⊤ n) = trunc


-- -- -- -- -- -- -- -- -- -- toFM2⊤ : Σ _ ℙrm → FMSet2 Unit
-- -- -- -- -- -- -- -- -- -- toFM2⊤ x = R𝕡rec.f {n = (fst x)} (RtoFM2⊤ (fst x)) (snd x)


-- -- -- -- -- -- -- -- -- -- comp0 : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- -- --      Square
-- -- -- -- -- -- -- -- -- --        (𝕡looop {n = suc (suc n)}(zero , tt) (suc (suc (fst k)) , snd k))
-- -- -- -- -- -- -- -- -- --        (𝕡loop (zero , tt))
-- -- -- -- -- -- -- -- -- --        (sym (𝕡loop (suc (suc (fst k)) , snd k)))
-- -- -- -- -- -- -- -- -- --        refl
-- -- -- -- -- -- -- -- -- -- comp0 n k i j =
-- -- -- -- -- -- -- -- -- --   hcomp
-- -- -- -- -- -- -- -- -- --     (λ l → λ {
-- -- -- -- -- -- -- -- -- --        (i = i0) → 𝕡comm (zero , tt) (suc (suc (fst k)) , snd k) _ j (~ l)
-- -- -- -- -- -- -- -- -- --      ; (i = i1) → 𝕡loop (zero , tt) (j ∧ l)
-- -- -- -- -- -- -- -- -- --      ; (j = i0) → 𝕡invol (suc (suc (fst k)) , snd k) l i
-- -- -- -- -- -- -- -- -- --      ; (j = i1) → 𝕡loop (0 , tt) (~ i ∨ l)
-- -- -- -- -- -- -- -- -- --      }) ((𝕡comp (suc (suc (fst k)) , snd k) (zero , tt) ▷ 𝕡invol (zero , tt)) j i)

-- -- -- -- -- -- -- -- -- -- comp1 : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- -- --      Square
-- -- -- -- -- -- -- -- -- --        (𝕡looop {n = n} k l)
-- -- -- -- -- -- -- -- -- --        (𝕡loop k)
-- -- -- -- -- -- -- -- -- --        refl
-- -- -- -- -- -- -- -- -- --        (𝕡loop l)
-- -- -- -- -- -- -- -- -- -- comp1 n k l i j =
-- -- -- -- -- -- -- -- -- --   hcomp
-- -- -- -- -- -- -- -- -- --     (λ l' → λ {
-- -- -- -- -- -- -- -- -- --        (i = i0) → (𝕡looop {n = n} k l) j
-- -- -- -- -- -- -- -- -- --      ; (i = i1) → (𝕡loop k) (j ∨ ~ l')
-- -- -- -- -- -- -- -- -- --      ; (j = i0) → 𝕡loop k (~ l' ∧ i)
-- -- -- -- -- -- -- -- -- --      ; (j = i1) → (𝕡loop l) i
-- -- -- -- -- -- -- -- -- --      }) ((𝕡comp {n = n} k l) j i)


-- -- -- -- -- -- -- -- -- -- aloopcommm : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- -- --       PathP
-- -- -- -- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- -- -- -- --          sucℙrm (suc n) (sucℙrm n (𝕡loop k i)) ≡
-- -- -- -- -- -- -- -- -- --          sucℙrm (suc n) (sucℙrm n (𝕡loop k i)))
-- -- -- -- -- -- -- -- -- --       (𝕡loop (zero , tt)) (𝕡loop (zero , tt)) 
-- -- -- -- -- -- -- -- -- -- aloopcommm n (k , k<) i j =
-- -- -- -- -- -- -- -- -- --      hcomp (λ l → λ {
-- -- -- -- -- -- -- -- -- --     (i = i0) → comp0 n (k , k<) l j
-- -- -- -- -- -- -- -- -- --    ;(i = i1) → comp1 (suc (suc n)) (zero , _) (suc (suc k) , k<) l j
-- -- -- -- -- -- -- -- -- --    ;(j = i0) → 𝕡loop (suc (suc k) , k<) (i ∨ ~ l)
-- -- -- -- -- -- -- -- -- --    ;(j = i1) → 𝕡loop (suc (suc k) , k<) (i ∧ l)
-- -- -- -- -- -- -- -- -- --    }) (𝕡looop (zero , _) (suc (suc k) , k<) j)

-- -- -- -- -- -- -- -- -- -- fromFM2comm-diag : ∀ n → ∀ l l< → Square {A = ℙrm (2 + n)}
-- -- -- -- -- -- -- -- -- --        (λ i →
-- -- -- -- -- -- -- -- -- --          aloopcommm n (l , l<) (~ i) i)
-- -- -- -- -- -- -- -- -- --       (𝕡looop (zero , _) (suc (suc l) , l<))
-- -- -- -- -- -- -- -- -- --       refl
-- -- -- -- -- -- -- -- -- --       refl
-- -- -- -- -- -- -- -- -- -- fromFM2comm-diag n l l< =
-- -- -- -- -- -- -- -- -- --   symP-fromGoal (compPath-filler (𝕡looop (zero , _) (suc (suc l) , l<)) refl)

-- -- -- -- -- -- -- -- -- -- fromFM2comm-diag' : ∀ n → ∀ l l< → Square {A = ℙrm (2 + n)}
-- -- -- -- -- -- -- -- -- --        (λ i →
-- -- -- -- -- -- -- -- -- --          aloopcommm n (l , l<) (i) (~ i))
-- -- -- -- -- -- -- -- -- --       (𝕡looop (suc (suc l) , l<) (zero , _))
-- -- -- -- -- -- -- -- -- --       refl
-- -- -- -- -- -- -- -- -- --       refl
-- -- -- -- -- -- -- -- -- -- fromFM2comm-diag' n k k< =
-- -- -- -- -- -- -- -- -- --   congP (λ _ → sym) (fromFM2comm-diag n k k<) ∙
-- -- -- -- -- -- -- -- -- --    sym (𝕡looop-invol _ _ _)





-- -- -- -- -- -- -- -- -- -- fromFM2comm : (n : ℕ) → R𝕡elimSet {n = n} (λ (y : ℙrm n) →
-- -- -- -- -- -- -- -- -- --       (sucℙrm (suc n) (sucℙrm n y)) ≡
-- -- -- -- -- -- -- -- -- --       (sucℙrm (suc n) (sucℙrm n y)))
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.isSetA (fromFM2comm n) _ = 𝕡squash _ _
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.abase (fromFM2comm n) = 𝕡loop (zero , _)
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.aloop (fromFM2comm n) = aloopcommm n
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.alooop (fromFM2comm n) k l i j =
-- -- -- -- -- -- -- -- -- --  hcomp
-- -- -- -- -- -- -- -- -- --    (λ l' → λ {
-- -- -- -- -- -- -- -- -- --      (i = i0) → aloopcommm n k (~ l') j
-- -- -- -- -- -- -- -- -- --     ;(i = i1) → aloopcommm n l (~ l') j
-- -- -- -- -- -- -- -- -- --     ;(j = i0) → sucℙrm (suc n) (sucℙrm n (𝕡comp k l i (~ l')))
-- -- -- -- -- -- -- -- -- --     ;(j = i1) → sucℙrm (suc n) (sucℙrm n (𝕡comp k l i (~ l')))
-- -- -- -- -- -- -- -- -- --      }) (𝕡loop (zero , tt) j)


-- -- -- -- -- -- -- -- -- -- fromFM2comm-inv : (n : ℕ) → R𝕡elimProp {n = n}
-- -- -- -- -- -- -- -- -- --   (λ (p : ℙrm n) →
-- -- -- -- -- -- -- -- -- --      R𝕡elimSet.f (fromFM2comm n) p
-- -- -- -- -- -- -- -- -- --   ≡ sym (R𝕡elimSet.f (fromFM2comm n) p))
-- -- -- -- -- -- -- -- -- -- R𝕡elimProp.isPropA (fromFM2comm-inv n) _ = 𝕡squash _ _ _ _
-- -- -- -- -- -- -- -- -- -- R𝕡elimProp.abase (fromFM2comm-inv n) = 𝕡invol _

-- -- -- -- -- -- -- -- -- -- -- fromFM2commmL : (n : ℕ) → R𝕡elimSet {n = n} (λ (y : ℙrm n) →
-- -- -- -- -- -- -- -- -- -- --       (sucℙrm (suc (suc n)) (sucℙrm (suc n) (sucℙrm n y))) ≡
-- -- -- -- -- -- -- -- -- -- --       (sucℙrm (suc (suc n)) (sucℙrm (suc n) (sucℙrm n y))))
-- -- -- -- -- -- -- -- -- -- -- R𝕡elimSet.isSetA (fromFM2commmL n) _ = 𝕡squash _ _
-- -- -- -- -- -- -- -- -- -- -- R𝕡elimSet.abase (fromFM2commmL n) = sym (𝕡looop (suc zero , _) (zero , _))
-- -- -- -- -- -- -- -- -- -- -- R𝕡elimSet.aloop (fromFM2commmL n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- R𝕡elimSet.alooop (fromFM2commmL n) = {!!}

-- -- -- -- -- -- -- -- -- -- RfromFM2⊤' : RElim {A = Unit} λ xs → ℙrm (len2 xs)
-- -- -- -- -- -- -- -- -- -- RElim.[]* RfromFM2⊤' = 𝕡base
-- -- -- -- -- -- -- -- -- -- RElim._∷*_ RfromFM2⊤' _ = sucℙrm _
-- -- -- -- -- -- -- -- -- -- RElim.comm* RfromFM2⊤' _ _ = (R𝕡elimSet.f (fromFM2comm _))
-- -- -- -- -- -- -- -- -- -- RElim.comm-inv* RfromFM2⊤' _ _ = R𝕡elimProp.f (fromFM2comm-inv _)
-- -- -- -- -- -- -- -- -- -- RElim.commmL* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- -- -- -- --     (sym (cong′ (sucℙrm _) ((R𝕡elimSet.f (fromFM2comm _)) p)))
-- -- -- -- -- -- -- -- -- --     ∙∙ refl ∙∙
-- -- -- -- -- -- -- -- -- --     (((R𝕡elimSet.f (fromFM2comm _)) (sucℙrm _ p)))

-- -- -- -- -- -- -- -- -- -- RElim.commmR* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- -- -- -- --      cong′ (sucℙrm _) ((R𝕡elimSet.f (fromFM2comm _)) p)
-- -- -- -- -- -- -- -- -- --     ∙∙ refl ∙∙
-- -- -- -- -- -- -- -- -- --      (sym ((R𝕡elimSet.f (fromFM2comm _)) (sucℙrm _ p)))
    
-- -- -- -- -- -- -- -- -- -- RElim.commpL* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- -- -- -- --   flipSquare (doubleCompPath-filler
-- -- -- -- -- -- -- -- -- --     (sym (cong′ (sucℙrm _) ((R𝕡elimSet.f (fromFM2comm _)) p))) _ _)
-- -- -- -- -- -- -- -- -- -- RElim.commpR* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- -- -- -- --   flipSquare (symP-fromGoal (doubleCompPath-filler
-- -- -- -- -- -- -- -- -- --     (cong′ (sucℙrm _) ((R𝕡elimSet.f (fromFM2comm _)) p)) _ _))
-- -- -- -- -- -- -- -- -- -- RElim.hex* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- -- -- -- --   {!𝕡braid!}
  
-- -- -- -- -- -- -- -- -- -- -- RElim.hexDiag* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- -- -- -- -- --       (cong′ (sucℙrm _) (((R𝕡elimSet.f (fromFM2comm _)) p))
-- -- -- -- -- -- -- -- -- -- --       ∙∙ ((R𝕡elimSet.f (fromFM2comm _)) (sucℙrm _ p))
-- -- -- -- -- -- -- -- -- -- --       ∙∙ cong′ (sucℙrm _) (sym ((R𝕡elimSet.f (fromFM2comm _)) p)) )
-- -- -- -- -- -- -- -- -- -- -- RElim.hexU* RfromFM2⊤' _ _ _ =
-- -- -- -- -- -- -- -- -- -- --   R𝕡elimProp.f (record { isPropA =
-- -- -- -- -- -- -- -- -- -- --     λ _ → isOfHLevelRetractFromIso 1 (invIso PathP→comm-Iso)
-- -- -- -- -- -- -- -- -- -- --       (𝕡squash _ _ _ _) ;
-- -- -- -- -- -- -- -- -- -- --     abase = λ i j →
-- -- -- -- -- -- -- -- -- -- --       hcomp (λ l →
-- -- -- -- -- -- -- -- -- -- --         primPOr (~ i) (j ∨ ~ j) (λ _ → 𝕡loop (1 , tt) j)
-- -- -- -- -- -- -- -- -- -- --           λ _ → hcomp
-- -- -- -- -- -- -- -- -- -- --               (λ l' → λ {
-- -- -- -- -- -- -- -- -- -- --                   (i = i0) → 𝕡loop (zero , tt) (~ l' ∧ l)
-- -- -- -- -- -- -- -- -- -- --                  ;(i = i1) → 𝕡invol (1 , tt) l' l
-- -- -- -- -- -- -- -- -- -- --                  ;(l = i0) → 𝕡looop (zero , tt) (1 , tt) i
-- -- -- -- -- -- -- -- -- -- --                  ;(l = i1) → 𝕡loop (zero , tt) (i ∨ (~ l'))
-- -- -- -- -- -- -- -- -- -- --                  }) (𝕡comp (zero , tt) (1 , tt) i l))
-- -- -- -- -- -- -- -- -- -- --        (𝕡braid zero tt i j) })
  
-- -- -- -- -- -- -- -- -- -- -- RElim.hexL* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- -- -- -- -- --   symP-fromGoal (doubleCompPath-filler _ _ _)
-- -- -- -- -- -- -- -- -- -- RElim.trunc* RfromFM2⊤' _ = 𝕡squash

-- -- -- -- -- -- -- -- -- -- fromFM2⊤ : FMSet2 Unit → Σ ℕ ℙrm
-- -- -- -- -- -- -- -- -- -- fromFM2⊤ xs = (len2 xs) , (RElim.f RfromFM2⊤' xs )


-- -- -- -- -- -- -- -- -- -- Rsucℙrm-lem : ∀ n → R𝕡elimSet {n = n}
-- -- -- -- -- -- -- -- -- --   λ p → toFM2⊤ (suc n , sucℙrm n p) ≡ tt ∷2 toFM2⊤ (n , p)
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.isSetA (Rsucℙrm-lem n) _ = trunc _ _
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.abase (Rsucℙrm-lem n) = refl
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.aloop (Rsucℙrm-lem n) k _ = refl
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.alooop (Rsucℙrm-lem n) k l _ = refl

-- -- -- -- -- -- -- -- -- -- sucℙrm-lem : ∀ n p → toFM2⊤ (suc n , sucℙrm n p) ≡ tt ∷2 toFM2⊤ (n , p)
-- -- -- -- -- -- -- -- -- -- sucℙrm-lem n = R𝕡elimSet.f (Rsucℙrm-lem n)

-- -- -- -- -- -- -- -- -- -- comm*-lem : ∀ n → R𝕡elimProp {n = n}
-- -- -- -- -- -- -- -- -- --                (λ p → Square {A = FMSet2 Unit}
-- -- -- -- -- -- -- -- -- --         (sucℙrm-lem (suc n) (sucℙrm n p) ∙ cong′ (tt ∷2_) (sucℙrm-lem n p))
-- -- -- -- -- -- -- -- -- --         (sucℙrm-lem (suc n) (sucℙrm n p) ∙ cong′ (tt ∷2_) (sucℙrm-lem n p))
-- -- -- -- -- -- -- -- -- --         (λ i → toFM2⊤ (suc (suc n) , (R𝕡elimSet.f {n = n} (fromFM2comm n)) p i))
-- -- -- -- -- -- -- -- -- --         (comm tt tt (toFM2⊤ (n , p))))
-- -- -- -- -- -- -- -- -- -- R𝕡elimProp.isPropA (comm*-lem n) _ =
-- -- -- -- -- -- -- -- -- --    isOfHLevelRetractFromIso 1 (invIso PathP→comm-Iso) (trunc _ _ _ _)
-- -- -- -- -- -- -- -- -- -- R𝕡elimProp.abase (comm*-lem n) i = refl ∙∙ refl ∙∙ refl

-- -- -- -- -- -- -- -- -- -- RfromToFM2⊤ : RElimSet' (λ z → toFM2⊤ (fromFM2⊤ z) ≡ z) 
-- -- -- -- -- -- -- -- -- -- RElimSet'.[]* RfromToFM2⊤ = refl
-- -- -- -- -- -- -- -- -- -- (RfromToFM2⊤ RElimSet'.∷* tt) {xs} X =
-- -- -- -- -- -- -- -- -- --   uncurry sucℙrm-lem (fromFM2⊤ xs) ∙ cong (tt ∷2_) X
  
-- -- -- -- -- -- -- -- -- -- RElimSet'.comm* RfromToFM2⊤ tt tt {xs} X i j =
-- -- -- -- -- -- -- -- -- --  hcomp
-- -- -- -- -- -- -- -- -- --    (λ l → primPOr (j ∨ ~ j) ((i ∨ ~ i))
-- -- -- -- -- -- -- -- -- --       (primPOr j (~ j) (λ _ → comm tt tt (X l) i)
-- -- -- -- -- -- -- -- -- --         λ _ → toFM2⊤ (fromFM2⊤ (comm tt tt xs i)))
-- -- -- -- -- -- -- -- -- --       λ _ → (uncurry sucℙrm-lem (fromFM2⊤ (tt ∷2 xs)) ∙
-- -- -- -- -- -- -- -- -- --          cong′ (tt ∷2_) (compPath-filler (uncurry sucℙrm-lem (fromFM2⊤ xs))
-- -- -- -- -- -- -- -- -- --                     (cong′ (tt ∷2_) X) l)) j)

-- -- -- -- -- -- -- -- -- --   (R𝕡elimProp.f {n = (fst (fromFM2⊤ xs))}
-- -- -- -- -- -- -- -- -- --     (comm*-lem (fst (fromFM2⊤ xs))) (snd (fromFM2⊤ xs)) i j)

-- -- -- -- -- -- -- -- -- -- -- RElimSet.hexDiag* RfromToFM2⊤ _ _ _ b i j = 
-- -- -- -- -- -- -- -- -- -- --   hcomp
-- -- -- -- -- -- -- -- -- -- --     (λ l → λ {
-- -- -- -- -- -- -- -- -- -- --       (i = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- --      ;(i = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- --      ;(j = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- --      ;(j = i1) → hexDiag _ _ _ (b l) i
-- -- -- -- -- -- -- -- -- -- --        })
-- -- -- -- -- -- -- -- -- -- --     {!!}

-- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ (uncurry sucℙrm-lem (fromFM2⊤ (y ∷2 z ∷2 xs)) ∙
-- -- -- -- -- -- -- -- -- -- --           (λ i₁ →
-- -- -- -- -- -- -- -- -- -- --              tt ∷2
-- -- -- -- -- -- -- -- -- -- --              (uncurry sucℙrm-lem (fromFM2⊤ (z ∷2 xs)) ∙
-- -- -- -- -- -- -- -- -- -- --               (λ i₂ →
-- -- -- -- -- -- -- -- -- -- --                  tt ∷2 (uncurry sucℙrm-lem (fromFM2⊤ xs) ∙ (λ i₃ → tt ∷2 b i₃)) i₂))
-- -- -- -- -- -- -- -- -- -- --              i₁))
-- -- -- -- -- -- -- -- -- -- --          j
-- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ (uncurry sucℙrm-lem (fromFM2⊤ (y ∷2 x ∷2 xs)) ∙
-- -- -- -- -- -- -- -- -- -- --           (λ i₁ →
-- -- -- -- -- -- -- -- -- -- --              tt ∷2
-- -- -- -- -- -- -- -- -- -- --              (uncurry sucℙrm-lem (fromFM2⊤ (x ∷2 xs)) ∙
-- -- -- -- -- -- -- -- -- -- --               (λ i₂ →
-- -- -- -- -- -- -- -- -- -- --                  tt ∷2 (uncurry sucℙrm-lem (fromFM2⊤ xs) ∙ (λ i₃ → tt ∷2 b i₃)) i₂))
-- -- -- -- -- -- -- -- -- -- --              i₁))
-- -- -- -- -- -- -- -- -- -- --          j
-- -- -- -- -- -- -- -- -- -- -- j = i0 ⊢ toFM2⊤ (fromFM2⊤ (hexDiag x y z xs i))
-- -- -- -- -- -- -- -- -- -- -- j = i1 ⊢ hexDiag x y z xs i
-- -- -- -- -- -- -- -- -- -- -- b  : toFM2⊤ (fromFM2⊤ xs) ≡ xs

-- -- -- -- -- -- -- -- -- -- RElimSet'.trunc* RfromToFM2⊤ _ = trunc _ _

-- -- -- -- -- -- -- -- -- -- fromToFM2⊤ : retract fromFM2⊤ toFM2⊤
-- -- -- -- -- -- -- -- -- -- fromToFM2⊤ = RElimSet'.f RfromToFM2⊤

-- -- -- -- -- -- -- -- -- -- dccf-lem : ∀ {a a' : A} → (p : a ≡ a') →
-- -- -- -- -- -- -- -- -- --              Square p p (refl ∙∙ refl ∙∙ refl) refl
-- -- -- -- -- -- -- -- -- -- dccf-lem {a = a} {a'} p i j = 
-- -- -- -- -- -- -- -- -- --    hcomp
-- -- -- -- -- -- -- -- -- --      (λ l → λ {
-- -- -- -- -- -- -- -- -- --        (i = i0) → p j
-- -- -- -- -- -- -- -- -- --       ;(i = i1) → p j
-- -- -- -- -- -- -- -- -- --       ;(j = i1) → a'
-- -- -- -- -- -- -- -- -- --        })
-- -- -- -- -- -- -- -- -- --      (p j)



-- -- -- -- -- -- -- -- -- -- RtoFromFM2⊤-fst : ∀ n → R𝕡elimSet {n = n} (λ z → len2 (toFM2⊤ (n , z)) ≡ n)
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.isSetA (RtoFromFM2⊤-fst n) _ = isProp→isSet (isSetℕ _ _)
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.abase (RtoFromFM2⊤-fst zero) = refl
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.abase (RtoFromFM2⊤-fst (suc n)) =
-- -- -- -- -- -- -- -- -- --   cong suc (R𝕡elimSet.abase (RtoFromFM2⊤-fst n))
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc n)) (suc k , k<) i j =
-- -- -- -- -- -- -- -- -- --   suc (R𝕡elimSet.aloop (RtoFromFM2⊤-fst (n)) (k , k<) i j)
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc (suc n))) (zero , k<) = refl

-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc n)) (suc k , k<) (suc l , l<) i j =
-- -- -- -- -- -- -- -- -- --   suc (R𝕡elimSet.alooop (RtoFromFM2⊤-fst n) (k , k<) (l , l<) i j)
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc n)) (zero , k<) (zero , l<) = refl
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc n)))) (zero , k<) (suc zero , l<) = refl
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc (suc n))))) (zero , k<) (suc (suc l) , l<) i j = suc (suc (R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc (suc n))) (l , l<) (~ i) j))
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc n)))) (suc zero , k<) (zero , l<) = refl
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc (suc n))))) (suc (suc k) , k<) (zero , l<) i j = suc (suc ((R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc (suc n))) (k , k<) i j)))


-- -- -- -- -- -- -- -- -- -- -- -- ∷2-lem-fst : ∀ xs → (fromFM2⊤ (tt ∷2 xs)) ≡
-- -- -- -- -- -- -- -- -- -- -- --    (suc (fst (fromFM2⊤ xs)) , uncurry sucℙrm (fromFM2⊤ xs))

-- -- -- -- -- -- -- -- -- -- base≡ : ∀ n → PathP (λ i → ℙrm (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) i))
-- -- -- -- -- -- -- -- -- --       (RElim.f RfromFM2⊤' (fm2base n)) 𝕡base
-- -- -- -- -- -- -- -- -- -- base≡ zero _ = 𝕡base
-- -- -- -- -- -- -- -- -- -- base≡ (suc n) = congP (λ _ → sucℙrm _) (base≡ n)



-- -- -- -- -- -- -- -- -- -- loop≡ : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- -- --       PathP
-- -- -- -- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- -- -- -- --          PathP (λ i₁ → ℙrm (R𝕡elimSet.f (RtoFromFM2⊤-fst n) (𝕡loop k i) i₁))
-- -- -- -- -- -- -- -- -- --          (snd (fromFM2⊤ (toFM2⊤ (n , 𝕡loop k i)))) (𝕡loop k i))
-- -- -- -- -- -- -- -- -- --       (base≡ n) (base≡ n)
-- -- -- -- -- -- -- -- -- -- loop≡ (suc n) (suc k , k<) i j = sucℙrm _ (loop≡ n (k , k<) i j) 
-- -- -- -- -- -- -- -- -- -- loop≡ (suc (suc n)) (zero , k<) i j =
-- -- -- -- -- -- -- -- -- --         (R𝕡elim.f
-- -- -- -- -- -- -- -- -- --           (R𝕡elimSet.fR (fromFM2comm (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j)))
-- -- -- -- -- -- -- -- -- --          ((base≡ n) j ) i)

-- -- -- -- -- -- -- -- -- -- looop≡ : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- -- --       PathP
-- -- -- -- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- -- -- -- --          PathP
-- -- -- -- -- -- -- -- -- --          (λ i₁ → ℙrm (R𝕡elimSet.f (RtoFromFM2⊤-fst n) (𝕡looop k l i) i₁))
-- -- -- -- -- -- -- -- -- --                            (snd (fromFM2⊤ (toFM2⊤ (n , 𝕡looop k l i))))
-- -- -- -- -- -- -- -- -- --          (𝕡looop k l i))
-- -- -- -- -- -- -- -- -- --       (base≡ n) (base≡ n)
-- -- -- -- -- -- -- -- -- -- looop≡ (suc n) (suc k , k<) (suc l , l<) i j =
-- -- -- -- -- -- -- -- -- --    sucℙrm _ (looop≡ n (k , k<) (l , l<) i j)      
-- -- -- -- -- -- -- -- -- -- looop≡ (suc (suc n)) (zero , k<) (zero , l<) i j =
-- -- -- -- -- -- -- -- -- --   hcomp (λ l' → primPOr j (i ∨ ~ i ∨ ~ j)
-- -- -- -- -- -- -- -- -- --              (λ _ → 𝕡comp (zero , _) (zero , _) i (~ l'))
-- -- -- -- -- -- -- -- -- --              λ _ → loop≡ (suc (suc n)) (zero , _) (~ l') j)
-- -- -- -- -- -- -- -- -- --         (sucℙrm _ (sucℙrm _ (base≡ n j)))
-- -- -- -- -- -- -- -- -- -- looop≡ (suc (suc (suc n))) (zero , k<) (suc zero , l<) = {!!}
-- -- -- -- -- -- -- -- -- --    -- hcomp (λ l' → {!!}
-- -- -- -- -- -- -- -- -- --    --          )
-- -- -- -- -- -- -- -- -- --    --      (sucℙrm _ (sucℙrm _ (sucℙrm _ (base≡ n j))))
-- -- -- -- -- -- -- -- -- --   -- comp (λ l' →  ℙrm (3 +
-- -- -- -- -- -- -- -- -- --   --          hfill
-- -- -- -- -- -- -- -- -- --   --         (λ { l (i = i0) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
-- -- -- -- -- -- -- -- -- --   --            ; l (i = i1) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
-- -- -- -- -- -- -- -- -- --   --            ; l (j = i1) → n
-- -- -- -- -- -- -- -- -- --   --            }) (inS (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j)) l'))
-- -- -- -- -- -- -- -- -- --   --    (λ l' → λ {
-- -- -- -- -- -- -- -- -- --   --        (i = i0) → loop≡ (suc (suc (suc n))) (zero , _) (~ l') j
-- -- -- -- -- -- -- -- -- --   --       ;(i = i1) → loop≡ (suc (suc (suc n))) (1 , _) (~ l') j
-- -- -- -- -- -- -- -- -- --   --       ;(j = i1) → 𝕡comp (zero , _) (1 , _) i (~ l')
-- -- -- -- -- -- -- -- -- --   --       })
-- -- -- -- -- -- -- -- -- --   --       ((sucℙrm _ (sucℙrm _ (sucℙrm _ (base≡ n j)))))

-- -- -- -- -- -- -- -- -- -- looop≡ (suc (suc (suc (suc n)))) kk@(zero , k<) ll@(suc (suc l) , l<) =
-- -- -- -- -- -- -- -- -- --   flipSquareP ((λ j i →
-- -- -- -- -- -- -- -- -- --       (((R𝕡elim.f
-- -- -- -- -- -- -- -- -- --             (R𝕡elimSet.fR (fromFM2comm _))
-- -- -- -- -- -- -- -- -- --             (loop≡ (suc (suc n)) (l , l<) (~ i) j) i))) ) ▷
-- -- -- -- -- -- -- -- -- --              fromFM2comm-diag (suc (suc n)) l l<)
   
-- -- -- -- -- -- -- -- -- -- looop≡ (suc (suc (suc n))) (suc zero , k<) (zero , l<) i j =
-- -- -- -- -- -- -- -- -- --   {!!}
-- -- -- -- -- -- -- -- -- --      -- comp (λ l' →  ℙrm (3 +
-- -- -- -- -- -- -- -- -- --      --       hfill
-- -- -- -- -- -- -- -- -- --      --      (λ { l (i = i1) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
-- -- -- -- -- -- -- -- -- --      --         ; l (i = i0) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
-- -- -- -- -- -- -- -- -- --      --         ; l (j = i1) → n
-- -- -- -- -- -- -- -- -- --      --         }) (inS (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j)) l'))
-- -- -- -- -- -- -- -- -- --      -- (λ l' → λ {
-- -- -- -- -- -- -- -- -- --      --     (i = i1) → loop≡ (suc (suc (suc n))) (zero , _) (~ l') j
-- -- -- -- -- -- -- -- -- --      --    ;(i = i0) → loop≡ (suc (suc (suc n))) (1 , _) (~ l') j
-- -- -- -- -- -- -- -- -- --      --    ;(j = i1) → 𝕡comp (1 , _) (zero , _) i (~ l')
-- -- -- -- -- -- -- -- -- --      --    })
-- -- -- -- -- -- -- -- -- --      --    ((sucℙrm _ (sucℙrm _ (sucℙrm _ (base≡ n j)))))

-- -- -- -- -- -- -- -- -- -- looop≡ (suc (suc (suc (suc n)))) (suc (suc k) , k<) (zero , l<) =
-- -- -- -- -- -- -- -- -- --     flipSquareP ((λ j i →
-- -- -- -- -- -- -- -- -- --       (((R𝕡elim.f
-- -- -- -- -- -- -- -- -- --             (R𝕡elimSet.fR (fromFM2comm _))
-- -- -- -- -- -- -- -- -- --             (loop≡ (suc (suc n)) (k , k<) (i) j) (~ i)))) ) ▷
-- -- -- -- -- -- -- -- -- --              fromFM2comm-diag' (suc (suc n)) k k<)


-- -- -- -- -- -- -- -- -- -- RtoFromFM2⊤ : ∀ n → R𝕡elimSet {n = n} (λ z →
-- -- -- -- -- -- -- -- -- --        PathP (λ i → ℙrm ((R𝕡elimSet.f (RtoFromFM2⊤-fst n) z i)))
-- -- -- -- -- -- -- -- -- --            (snd (fromFM2⊤ (toFM2⊤ (n , z)))) z)
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.isSetA (RtoFromFM2⊤ n) _ =
-- -- -- -- -- -- -- -- -- --  isOfHLevelRetractFromIso 2 (PathPIsoPath _ _ _) (𝕡squash _ _)
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.abase (RtoFromFM2⊤ n) = base≡ n
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.aloop (RtoFromFM2⊤ n) = loop≡ n
-- -- -- -- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤ n) = looop≡ n

-- -- -- -- -- -- -- -- -- -- toFromFM2⊤ : section fromFM2⊤ toFM2⊤
-- -- -- -- -- -- -- -- -- -- toFromFM2⊤ (n , p) = ΣPathP (_  , R𝕡elimSet.f {n = n} (RtoFromFM2⊤ n) p)

-- -- -- -- -- -- -- -- -- -- Iso-FM2⊤-Σℙrm : Iso (FMSet2 Unit) (Σ _ ℙrm)
-- -- -- -- -- -- -- -- -- -- Iso.fun Iso-FM2⊤-Σℙrm = fromFM2⊤
-- -- -- -- -- -- -- -- -- -- Iso.inv Iso-FM2⊤-Σℙrm = toFM2⊤
-- -- -- -- -- -- -- -- -- -- Iso.rightInv Iso-FM2⊤-Σℙrm = toFromFM2⊤
-- -- -- -- -- -- -- -- -- -- Iso.leftInv Iso-FM2⊤-Σℙrm = fromToFM2⊤

-- -- -- -- -- -- -- -- -- -- Iso-FM2⊤-EMP : Iso (FMSet2 Unit) (Σ _ ℙrm')
-- -- -- -- -- -- -- -- -- -- Iso-FM2⊤-EMP = compIso Iso-FM2⊤-Σℙrm (Σ-cong-iso-snd IsoEmℙrm)

-- -- -- -- -- -- -- -- -- -- fmbase⊤ : ℕ → FMSet2 Unit
-- -- -- -- -- -- -- -- -- -- fmbase⊤ zero = []
-- -- -- -- -- -- -- -- -- -- fmbase⊤ (suc n) = tt ∷2 fmbase⊤ n

-- -- -- -- -- -- -- -- -- -- Iso-𝔽in-S𝔽in : ∀ n → Iso (𝔽in (𝕡base {n})) (S.𝔽in (fmbase⊤ n))
-- -- -- -- -- -- -- -- -- -- Iso-𝔽in-S𝔽in zero = w
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --    open Iso

-- -- -- -- -- -- -- -- -- --    w : Iso _ _
-- -- -- -- -- -- -- -- -- --    fun w = snd
-- -- -- -- -- -- -- -- -- --    Iso.inv w ()
-- -- -- -- -- -- -- -- -- --    rightInv w ()
-- -- -- -- -- -- -- -- -- --    leftInv w (_ , ())
-- -- -- -- -- -- -- -- -- -- Iso.fun (Iso-𝔽in-S𝔽in (suc n)) (zero , snd₁) = nothing
-- -- -- -- -- -- -- -- -- -- Iso.fun (Iso-𝔽in-S𝔽in (suc n)) (suc fst₁ , snd₁) =
-- -- -- -- -- -- -- -- -- --   just (Iso.fun (Iso-𝔽in-S𝔽in n) (fst₁ , snd₁))
-- -- -- -- -- -- -- -- -- -- Iso.inv (Iso-𝔽in-S𝔽in (suc n)) nothing = zero , _
-- -- -- -- -- -- -- -- -- -- Iso.inv (Iso-𝔽in-S𝔽in (suc n)) (just x) =
-- -- -- -- -- -- -- -- -- --  sucF (Iso.inv (Iso-𝔽in-S𝔽in n) x)
-- -- -- -- -- -- -- -- -- -- Iso.rightInv (Iso-𝔽in-S𝔽in (suc n)) nothing = refl
-- -- -- -- -- -- -- -- -- -- Iso.rightInv (Iso-𝔽in-S𝔽in (suc n)) (just x) =
-- -- -- -- -- -- -- -- -- --   cong just (Iso.rightInv (Iso-𝔽in-S𝔽in n) x)
-- -- -- -- -- -- -- -- -- -- Iso.leftInv (Iso-𝔽in-S𝔽in (suc n)) (zero , snd₁) = refl
-- -- -- -- -- -- -- -- -- -- Iso.leftInv (Iso-𝔽in-S𝔽in (suc n)) (suc k , snd₁) =
-- -- -- -- -- -- -- -- -- --   ≡Fin {n = suc n} (cong (suc ∘ fst)
-- -- -- -- -- -- -- -- -- --    (Iso.leftInv (Iso-𝔽in-S𝔽in (n)) (k , snd₁)))


      


-- -- -- -- -- -- -- -- -- -- -- -- module _ {A : Type ℓ} where


-- -- -- -- -- -- -- -- -- -- -- -- --  -- pci = preCompInvol.e' {f = f} (B j i) fInvol
-- -- -- -- -- -- -- -- -- -- -- --  →adjT : ∀ n (k : Σ ℕ (λ k₁ → suc k₁ < n))  → (Fin n → A) ≃ (Fin n → A)
-- -- -- -- -- -- -- -- -- -- -- --  →adjT n k = preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k)
 
-- -- -- -- -- -- -- -- -- -- -- --  𝔽→looop : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n))  → (Fin n → A) ≡ (Fin n → A)
-- -- -- -- -- -- -- -- -- -- -- --  𝔽→looop n k l i =
-- -- -- -- -- -- -- -- -- -- -- --    Glue (Fin n → A)
-- -- -- -- -- -- -- -- -- -- -- --      λ { (i = i0) → (Fin n → A) , →adjT n k
-- -- -- -- -- -- -- -- -- -- -- --        ; (i = i1) → (Fin n → A) , →adjT n l } 

-- -- -- -- -- -- -- -- -- -- -- --  𝔽→looop-comp-si : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- -- -- -- --       Square
-- -- -- -- -- -- -- -- -- -- -- --          (λ i → Flooop n k l i → A)
-- -- -- -- -- -- -- -- -- -- -- --          (𝔽→looop n k l)
-- -- -- -- -- -- -- -- -- -- -- --          refl
-- -- -- -- -- -- -- -- -- -- -- --          refl
-- -- -- -- -- -- -- -- -- -- -- --  𝔽→looop-comp-si n k l j i =
-- -- -- -- -- -- -- -- -- -- -- --    Glue (Flooop n k l (i ∨ j) → A)
-- -- -- -- -- -- -- -- -- -- -- --      λ { (i = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- --        ; (i = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- --        ; (j = i0) → _ , idEquiv _
-- -- -- -- -- -- -- -- -- -- -- --        }

-- -- -- -- -- -- -- -- -- -- -- --  𝔽→looop-comp : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- -- -- -- --      Square
-- -- -- -- -- -- -- -- -- -- -- --        (ua (→adjT n k))
-- -- -- -- -- -- -- -- -- -- -- --        (ua (→adjT n l))
-- -- -- -- -- -- -- -- -- -- -- --        (𝔽→looop n k l)
-- -- -- -- -- -- -- -- -- -- -- --        refl
-- -- -- -- -- -- -- -- -- -- -- --  𝔽→looop-comp = {!!}

-- -- -- -- -- -- -- -- -- -- -- --  R𝔽→ : ∀ n → R𝕡elim {n = n} λ p → singl (𝔽in p → A)
-- -- -- -- -- -- -- -- -- -- -- --  R𝕡elim.isGroupoidA (R𝔽→ n) _ = isOfHLevelPlus 3 (isContrSingl _)
-- -- -- -- -- -- -- -- -- -- -- --  R𝕡elim.abase (R𝔽→ n) = _ , refl
-- -- -- -- -- -- -- -- -- -- -- --  R𝕡elim.aloop (R𝔽→ n) k i = _ ,
-- -- -- -- -- -- -- -- -- -- -- --    λ j → preCompInvol.eq {f = adjT n k} A (isInvolution-adjT n  k) j i   
-- -- -- -- -- -- -- -- -- -- -- --  fst (R𝕡elim.alooop (R𝔽→ n) k l i) = 𝔽→looop n k l i
-- -- -- -- -- -- -- -- -- -- -- --  snd (R𝕡elim.alooop (R𝔽→ n) k l i) j = 𝔽→looop-comp-si n k l j i
-- -- -- -- -- -- -- -- -- -- -- --  R𝕡elim.acomp (R𝔽→ n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  R𝕡elim.ainvol (R𝔽→ n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  R𝕡elim.acomm (R𝔽→ n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  R𝕡elim.abraid (R𝔽→ n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- R𝕡elim.isGroupoidA (R𝕍 n) p =
-- -- -- -- -- -- -- -- -- -- -- --  --    isOfHLevelPlus 3 (isContrSingl _)
-- -- -- -- -- -- -- -- -- -- -- --  -- R𝕡elim.abase (R𝔽→ n) = (𝔽in p → A) , ua (tabEquiv n)
-- -- -- -- -- -- -- -- -- -- -- --  -- R𝕡elim.aloop (R𝕍 n) k = ΣPathP (ua (adjT×^≃ (fst k)) , ua-adj-law n k)
-- -- -- -- -- -- -- -- -- -- -- --  -- R𝕡elim.alooop (R𝕍 n) k l = ΣPathP (𝕍looop n (fst k) (fst l) , 𝕍loopSi n k l )
-- -- -- -- -- -- -- -- -- -- -- --  -- fst (R𝕡elim.acomp (R𝕍 n) (k , _) (l , _) i j) = 𝕍comp n k l i j

-- -- -- -- -- -- -- -- -- -- -- --  -- snd (R𝕡elim.acomp (R𝕍 n) k l i j) m = 𝕍compSi n k l m i j
-- -- -- -- -- -- -- -- -- -- -- --  -- fst (R𝕡elim.ainvol (R𝕍 n) k i j) = 𝕍invol n (fst k) i j
-- -- -- -- -- -- -- -- -- -- -- --  -- snd (R𝕡elim.ainvol (R𝕍 n) k i j) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- R𝕡elim.acomm (R𝕍 n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- R𝕡elim.abraid (R𝕍 n) = {!!}


-- -- -- -- -- -- -- -- -- -- -- sucF'-fst : ∀ n k k< → PathP (λ i → ua (adjT'≃ {n = n} (k , k<)) i → ℕ)
-- -- -- -- -- -- -- -- -- -- --                   (fst ∘ fst (adjT'≃ {suc n} (suc k , k<)) ∘ sucF)
-- -- -- -- -- -- -- -- -- -- --                   (suc ∘ fst)
-- -- -- -- -- -- -- -- -- -- -- sucF'-fst n k k< i x = suc (fst (unglue (i ∨ ~ i) x))

-- -- -- -- -- -- -- -- -- -- -- sucF'-snd : ∀ n k k< → PathP (λ i → (x : ua (adjT'≃ {n = n} (k , k<)) i) →
-- -- -- -- -- -- -- -- -- -- --                                 (sucF'-fst n k k< i x) ≤ n)
-- -- -- -- -- -- -- -- -- -- --                  (λ x → adjT< (suc n) (suc k) (fst (sucF {n = n} x))
-- -- -- -- -- -- -- -- -- -- --                          k< (snd (sucF {n = n} x)))
-- -- -- -- -- -- -- -- -- -- --                  λ x → snd x
-- -- -- -- -- -- -- -- -- -- -- sucF'-snd n k k< =
-- -- -- -- -- -- -- -- -- -- --   isProp→PathP (λ i → isPropΠ λ x → isProp≤ {m = sucF'-fst n k k< i x} {n = n})
-- -- -- -- -- -- -- -- -- -- --     (λ x → adjT< (suc n) (suc k) (suc (fst x)) k< (snd x)) snd

-- -- -- -- -- -- -- -- -- -- -- sucF' : ∀ n k k< → PathP (λ i → ua (adjT'≃ {n = n} (k , k<)) i → Fin (suc n))
-- -- -- -- -- -- -- -- -- -- --                   (fst (adjT'≃ {suc n} (suc k , k<)) ∘ sucF)
-- -- -- -- -- -- -- -- -- -- --                   sucF
-- -- -- -- -- -- -- -- -- -- -- sucF' n k k< i x =
-- -- -- -- -- -- -- -- -- -- --   sucF'-fst n k k< i x ,
-- -- -- -- -- -- -- -- -- -- --    sucF'-snd n k k< i x


-- -- -- -- -- -- -- -- -- -- -- module _ {A : Type ℓ} where

 
-- -- -- -- -- -- -- -- -- -- --  swap-01-× : ∀ {n} → (A ×^ n) → (A ×^ n)
-- -- -- -- -- -- -- -- -- -- --  swap-01-× {zero} = idfun _
-- -- -- -- -- -- -- -- -- -- --  swap-01-× {suc zero} = idfun _
-- -- -- -- -- -- -- -- -- -- --  swap-01-× {suc (suc n)} = swap-01

-- -- -- -- -- -- -- -- -- -- --  invo-swap-01-× : ∀ n → isInvolution (swap-01-× {n})
-- -- -- -- -- -- -- -- -- -- --  invo-swap-01-× zero x = refl
-- -- -- -- -- -- -- -- -- -- --  invo-swap-01-× (suc zero) x = refl
-- -- -- -- -- -- -- -- -- -- --  invo-swap-01-× (suc (suc n)) x = refl

-- -- -- -- -- -- -- -- -- -- --  adjT×^ : ∀ {n} → ℕ →
-- -- -- -- -- -- -- -- -- -- --               (A ×^ n) → (A ×^ n)
-- -- -- -- -- -- -- -- -- -- --  adjT×^ zero = swap-01-×
-- -- -- -- -- -- -- -- -- -- --  adjT×^ {suc n} (suc k) (x , xs) = x , (adjT×^ k xs)
-- -- -- -- -- -- -- -- -- -- --  adjT×^ {zero} (suc k) = idfun _
 
-- -- -- -- -- -- -- -- -- -- --  isEquiv-adjT×^ : ∀ n k → isEquiv (adjT×^ {n} k)
-- -- -- -- -- -- -- -- -- -- --  isEquiv-adjT×^ (suc n) (suc k) =
-- -- -- -- -- -- -- -- -- -- --    snd (≃-× (_ , idIsEquiv _) (_ , isEquiv-adjT×^ n k))
-- -- -- -- -- -- -- -- -- -- --  isEquiv-adjT×^ zero zero = idIsEquiv _
-- -- -- -- -- -- -- -- -- -- --  isEquiv-adjT×^ (suc zero) zero = idIsEquiv _
-- -- -- -- -- -- -- -- -- -- --  isEquiv-adjT×^ (suc (suc n)) zero = snd Σ-swap-01-≃
-- -- -- -- -- -- -- -- -- -- --  isEquiv-adjT×^ zero (suc k) = idIsEquiv _

-- -- -- -- -- -- -- -- -- -- --  adjT×^≃ : ∀ {n} → ℕ → (A ×^ n) ≃ (A ×^ n)
-- -- -- -- -- -- -- -- -- -- --  adjT×^≃ k = adjT×^ k , isEquiv-adjT×^ _ k

-- -- -- -- -- -- -- -- -- -- --  isInvo-adjT×^ : ∀ {n} → ∀ k → isInvolution (adjT×^ {n} k)
-- -- -- -- -- -- -- -- -- -- --  isInvo-adjT×^ zero = invo-swap-01-× _
-- -- -- -- -- -- -- -- -- -- --  isInvo-adjT×^ {zero} (suc k) _ = refl
-- -- -- -- -- -- -- -- -- -- --  isInvo-adjT×^ {suc n} (suc k) (x , xs) =
-- -- -- -- -- -- -- -- -- -- --    cong′ (x ,_) (isInvo-adjT×^ {n} k xs)

-- -- -- -- -- -- -- -- -- -- --  braid-adjT×^ : ∀ {n} → ∀ k →  suc (suc k) < n → ∀ v → 
-- -- -- -- -- -- -- -- -- -- --    (adjT×^  {n} k ∘ adjT×^  {n} (suc k) ∘ adjT×^  {n} (k)) v
-- -- -- -- -- -- -- -- -- -- --    ≡ (adjT×^  {n} (suc k) ∘ adjT×^  {n} (k) ∘ adjT×^  {n} (suc k)) v
-- -- -- -- -- -- -- -- -- -- --  braid-adjT×^ {suc n} (suc k) x (v , vs) = cong′ (v ,_) (braid-adjT×^ {n} k x vs)
-- -- -- -- -- -- -- -- -- -- --  braid-adjT×^ {suc (suc (suc n))} zero x v = refl
 

-- -- -- -- -- -- -- -- -- -- --  comm-adjT×^ : ∀ {n} → ∀ k l → (k< : (suc k) < n) (l< : (suc l) < n) → 
-- -- -- -- -- -- -- -- -- -- --    A.commT k l → ∀ v →  
-- -- -- -- -- -- -- -- -- -- --    (adjT×^  {n} l
-- -- -- -- -- -- -- -- -- -- --      ∘ adjT×^  {n} k ) v
-- -- -- -- -- -- -- -- -- -- --    ≡ (adjT×^  {n} k
-- -- -- -- -- -- -- -- -- -- --      ∘ adjT×^  {n} l ) v
-- -- -- -- -- -- -- -- -- -- --  comm-adjT×^ {n = suc n} (suc k) (suc l) k< l< x (v , vs) =
-- -- -- -- -- -- -- -- -- -- --     cong (v ,_) (comm-adjT×^ {n = n} k l k< l< (A.pred-commT k l x) vs)
-- -- -- -- -- -- -- -- -- -- --  comm-adjT×^ {n = suc (suc n)} zero (suc (suc l)) k< l< x v = refl



-- -- -- -- -- -- -- -- -- -- --  tabEquiv : ∀ n → (Fin n → A) ≃ (A ×^ n)
-- -- -- -- -- -- -- -- -- -- --  tabEquiv n = isoToEquiv (invIso (Iso-×^-F→ n))

    
-- -- -- -- -- -- -- -- -- -- --  zz : ∀ n k → PathP (λ i → (ua (adjT'≃ {n} k) i → A) → (A ×^ n))
-- -- -- -- -- -- -- -- -- -- --         (adjT×^ (fst k) ∘ tabulate)
-- -- -- -- -- -- -- -- -- -- --         (tabulate)           

-- -- -- -- -- -- -- -- -- -- --  zz (suc n) (suc k , k<) i x =
-- -- -- -- -- -- -- -- -- -- --    x (glue (λ { (i = i0) → zero , tt ; (i = i1) → zero , tt }) (0 , tt)) ,
-- -- -- -- -- -- -- -- -- -- --    zz n (k , k<) i
-- -- -- -- -- -- -- -- -- -- --        (x ∘ (λ y → glue (λ { (i = i0) → sucF y ; (i = i1) → sucF y })
-- -- -- -- -- -- -- -- -- -- --          (sucF' n k k< i y)))   
-- -- -- -- -- -- -- -- -- -- --  zz (suc (suc n)) (zero , k<) i x =
-- -- -- -- -- -- -- -- -- -- --    (x (glue (λ { (i = i0) → suc zero , tt ; (i = i1) → zero , tt }) (0 , tt)) ,
-- -- -- -- -- -- -- -- -- -- --     x (glue (λ { (i = i0) → zero , tt ; (i = i1) → suc zero , tt }) (1 , tt)) ,
-- -- -- -- -- -- -- -- -- -- --    tabulate λ y → x (glue (λ { (i = i0) → sucF (sucF y)
-- -- -- -- -- -- -- -- -- -- --                              ; (i = i1) → sucF (sucF y) })
-- -- -- -- -- -- -- -- -- -- --                (sucF (sucF y))))

-- -- -- -- -- -- -- -- -- -- --  ua-adj-lawP : ∀ n k →
-- -- -- -- -- -- -- -- -- -- --        PathP (λ i → (ua (adjT'≃ {n = n} k) i → A) ≃ ua (adjT×^≃ {n = n} (fst k)) i)
-- -- -- -- -- -- -- -- -- -- --                  (tabEquiv n)
-- -- -- -- -- -- -- -- -- -- --                  (tabEquiv n)
-- -- -- -- -- -- -- -- -- -- --  ua-adj-lawP n k = ΣPathPProp isPropIsEquiv
-- -- -- -- -- -- -- -- -- -- --    λ i x → glue (λ { (i = i0) → tabulate x
-- -- -- -- -- -- -- -- -- -- --                    ; (i = i1) → tabulate x }) (zz n k i x) 

-- -- -- -- -- -- -- -- -- -- --  ua-adj-law : ∀ n k →
-- -- -- -- -- -- -- -- -- -- --    Square
-- -- -- -- -- -- -- -- -- -- --        (ua (tabEquiv n))
-- -- -- -- -- -- -- -- -- -- --        (ua (tabEquiv n))
-- -- -- -- -- -- -- -- -- -- --        (λ i → ua (adjT'≃ {n = n} k) i → A)
-- -- -- -- -- -- -- -- -- -- --        (ua (adjT×^≃ {n = n} (fst k)))
       
-- -- -- -- -- -- -- -- -- -- --  ua-adj-law n k i j =
-- -- -- -- -- -- -- -- -- -- --    Glue (ua (adjT×^≃ {n = n} (fst k)) i)
-- -- -- -- -- -- -- -- -- -- --         λ {  (j = i0) → (ua (adjT'≃ {n = n} k) i → A) , ua-adj-lawP n k i
-- -- -- -- -- -- -- -- -- -- --            ; (j = i1) → ua (adjT×^≃ {n = n} (fst k)) i , idEquiv _
-- -- -- -- -- -- -- -- -- -- --            }
