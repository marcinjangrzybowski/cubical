{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.BaseFinGen where

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
-- open import Cubical.Data.Nat.Order.RecursiveMoreEquiv

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

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)


open import Cubical.Relation.Binary

-- import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint

private
  variable
    ℓ : Level
    A : Type ℓ


-- List-adjTransposition : ℕ → Li.List A → Li.List A
-- List-adjTransposition k [] = []
-- List-adjTransposition (suc k) (x ∷ l) = x ∷ List-adjTransposition k l
-- List-adjTransposition zero (x ∷ []) = x ∷ []
-- List-adjTransposition zero (x ∷ x' ∷ l) = x' ∷ x ∷ l


data ℙrm {trunc : Bool} : Type₀ where 
  𝕡base : ℙrm
  𝕡loop : ℕ → 𝕡base ≡ 𝕡base  
  𝕡looop : ℕ → ℕ → 𝕡base ≡ 𝕡base
  
  𝕡comp : ∀ k l →
     Square
       (𝕡loop k)
       (𝕡loop l)
       (𝕡looop k l)
       refl
         
  𝕡invol : ∀ k → 𝕡loop k ≡ sym (𝕡loop k)
  𝕡comm : ∀ k l  →
     commT k l →
       Square
         refl
         refl
       (𝕡looop k l)
       (𝕡looop l k)

  𝕡braid : ∀ k →        
         Square
         (𝕡loop (suc k))
         (𝕡loop k)
         (𝕡looop k (suc k))
         (𝕡looop k (suc k))


  𝕡squash : Bool→Type trunc → isGroupoid ℙrm




toTruncℙ : ∀ {b} → ℙrm {b} → ℙrm {true}
toTruncℙ 𝕡base = 𝕡base
toTruncℙ (𝕡loop x i) = 𝕡loop x i
toTruncℙ (𝕡looop k l i) = 𝕡looop k l i
toTruncℙ (𝕡comp k l i i₁) = 𝕡comp k l i i₁
toTruncℙ (𝕡invol k i i₁) = 𝕡invol k i i₁
toTruncℙ (𝕡comm k l x i i₁) = 𝕡comm k l x i i₁
toTruncℙ (𝕡braid k i i₁) = 𝕡braid k i i₁
toTruncℙ (𝕡squash _ x y p q r s i i₁ x₅) =
 𝕡squash _ _ _ _ _
  (λ i j → toTruncℙ (r i j)) (λ i j → toTruncℙ (s i j))
  i i₁ x₅

𝕡comp' : ∀ {b} → (k l : ℕ) →
   Square {A = ℙrm {b}}
     (𝕡loop k)
     (𝕡loop l)
     refl
     (𝕡looop k l)
𝕡comp' k l =
   (𝕡invol k) ◁
   (λ i j → (𝕡comp k l i (~ j)))
   ▷ sym (𝕡invol l)

𝕡looop-invol : ∀ {b} k l →
    𝕡looop {b} k l ≡ sym (𝕡looop l k)
𝕡looop-invol k l i j =
   hcomp
      (λ l' → λ {
        (i = i0) → 𝕡comp k l j (~ l')
       ;(i = i1) → 𝕡comp l k (~ j) (~ l')
       ;(j = i0) → 𝕡loop k (~ l')
       ;(j = i1) → 𝕡loop l (~ l')
       }) 𝕡base

record R𝕡rec (A : Type ℓ) : Type ℓ where
 no-eta-equality
 field
   abase : A
   aloop : ℕ → abase ≡ abase
   alooop : ℕ → ℕ → abase ≡ abase
   acomp : ∀ k l →
      Square
        (aloop k)
        (aloop l)
        (alooop k l)
        refl

   ainvol : ∀ k → aloop k ≡ sym (aloop k)
   acomm : ∀ k l →
      commT k l →
        Square
          refl
          refl
        (alooop k l)
        (alooop l k)

   abraid : ∀ k  →        
          Square
          (aloop (suc k))
          (aloop k)
          (alooop k (suc k))
          (alooop k (suc k))


 f : ∀ {trunc} → {squashA : if trunc then (isGroupoid A) else Unit*} →
       ℙrm {trunc} → A
 f 𝕡base = abase
 f (𝕡loop x i) = aloop x i
 f (𝕡looop k l i) = alooop k l i
 f (𝕡comp k l i i₁) = acomp k l i i₁
 f (𝕡invol k i i₁) = ainvol k i i₁
 f (𝕡comm k l x i i₁) = acomm k l x i i₁
 f (𝕡braid k i i₁) = abraid k i i₁
 f {true} {t} (𝕡squash _ _ _ _ _ r s i₀ i₁ i₂) =   
   t _ _ _ _
     (λ i j → (f {true} {t} (r i j)))
     (λ i j → (f {true} {t} (s i j)))
     i₀ i₁ i₂



record R𝕡elim {trunc} (A : ℙrm {trunc} → Type ℓ) : Type ℓ where
 no-eta-equality
 field
   isGroupoidA : Bool→Type trunc → ∀ x → isGroupoid (A x)
   abase : A 𝕡base
   aloop : ∀ k →
     PathP (λ i → A (𝕡loop k i)) abase abase
   alooop : ∀ k l →
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
   acomm : ∀ k l → ∀ x →     
       SquareP (λ i j → A (𝕡comm k l x i j))
         refl
         refl
       (alooop k l)
       (alooop l k)
   abraid : ∀ k →        
         SquareP (λ i j → A (𝕡braid k i j))
         (aloop (suc k))
         (aloop k)
         (alooop k (suc k))
         (alooop k (suc k))
  


 f : ∀ x → A x
 f 𝕡base = abase
 f (𝕡loop x i) = aloop x i
 f (𝕡looop k l i) = alooop k l i
 f (𝕡comp k l j i) = acomp k l j i
   
 f (𝕡invol k i j) = ainvol k i j
 
 f (𝕡comm k l x i j) = acomm k l x i j
    
 
 f (𝕡braid k i j) = abraid k i j
 f (𝕡squash X x y p q r s i j k) =
   isOfHLevel→isOfHLevelDep 3 (isGroupoidA X)
     _ _ _ _
     (λ j k → f (r j k)) (λ j k → f (s j k))
     (𝕡squash X x y p q r s) i j k





-- record R𝕡elimSet {n} {trunc} (A : ℙrm {trunc} n → Type ℓ) : Type ℓ where
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
--  R𝕡elim.isGroupoidA fR X = isSet→isGroupoid ∘ isSetA
--  R𝕡elim.abase fR = abase
--  R𝕡elim.aloop fR = aloop
--  R𝕡elim.alooop fR = alooop
--  R𝕡elim.acomp fR = w
--    where
--    abstract
--     w : (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
--       SquareP (λ j i → A (𝕡comp k l j i)) (aloop k) (aloop l)
--       (alooop k l) refl
--     w k l = isSet→SquareP (λ j i → isSetA (𝕡comp k l j i)) _ _ _ _
--  R𝕡elim.ainvol fR = w
--   where
--   abstract
--    w : (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
--       SquareP (λ i j → A (𝕡invol k i j)) (aloop k) (symP (aloop k)) refl
--       refl
--    w k = isSet→SquareP (λ j i → isSetA (𝕡invol k j i)) _ _ _ _
--  R𝕡elim.acomm fR = w
--   where
--   abstract
--    w : (k l : Σ ℕ (λ k₁ → suc k₁ < n)) (x : commT (fst k) (fst l)) →
--     SquareP (λ i j → A (𝕡comm k l x i j)) refl refl
--     (R𝕡elim.alooop fR k l) (R𝕡elim.alooop fR l k)
--    w k l x = isSet→SquareP (λ j i → isSetA (𝕡comm k l x j i)) _ _ _ _ 
--  R𝕡elim.abraid fR = w
--   where
--   abstract
--    w : (k : ℕ)
--     (k< : suc (suc (suc k)) Cubical.Data.Nat.Order.Recursive.≤ n) →
--     SquareP (λ i j → A (𝕡braid k k< i j))
--     (R𝕡elim.aloop fR (suc k , k<)) (R𝕡elim.aloop fR (k , <-weaken {n = n} k<))
--     (R𝕡elim.alooop fR (k , <-weaken {n = n} k<) (suc k , k<))
--     (R𝕡elim.alooop fR (k , <-weaken {n = n} k<) (suc k , k<))
--    w k k< = isSet→SquareP (λ j i → isSetA (𝕡braid k k< j i)) _ _ _ _


--  f : ∀ x → A x
--  f = R𝕡elim.f fR



-- record R𝕡elimSet' {n} {trunc} (A : ℙrm {trunc} n → Type ℓ) : Type ℓ where
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
--  R𝕡elimSet.alooop fR  = w
--   where
--    abstract
--     w : (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
--      PathP (λ i → A (𝕡looop k l i)) (R𝕡elimSet.abase fR)
--      (R𝕡elimSet.abase fR)
--     w = λ k l i → comp (λ j → A (𝕡comp k l i (~ j)))
--       (λ j → λ { (i = i0) → aloop k (~ j) ; (i = i1) → aloop l (~ j) })
--       abase

--  f : ∀ x → A x
--  f = R𝕡elimSet.f fR



-- record R𝕡elimProp {n} {trunc} (A : ℙrm {trunc} n → Type ℓ) : Type ℓ where
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


-- truncℙ : ∀ {ℓ} {A : Type ℓ} → (isGroupoid A)
--            → (∀ n → ℙrm {false} n → A)
--            → ∀ n → ℙrm {true} n → A
-- truncℙ isGrpA f n = w
--  where
--  f' = f n

--  w : ℙrm n → _
--  w 𝕡base = f' 𝕡base
--  w (𝕡loop x i) =  f' (𝕡loop x i)
--  w (𝕡looop k l i) = f' (𝕡looop k l i)
--  w (𝕡comp k l i i₁) = f' (𝕡comp k l i i₁)
--  w (𝕡invol k i i₁) = f' (𝕡invol k i i₁)
--  w (𝕡comm k l x i i₁) = f' (𝕡comm k l x i i₁)
--  w (𝕡braid k k< i i₁) = f' (𝕡braid k k< i i₁)
--  w (𝕡squash _ _ _ _ _ r s i₀ i₁ i₂) =   
--    isGrpA _ _ _ _
--      (λ i j → (w (r i j)))
--      (λ i j → (w (s i j)))
--      i₀ i₁ i₂

-- -- Truncℙ₂ : ∀ {ℓ} 
-- --            → (A : ∀ n → ℙrm {false} n → Type ℓ)
-- --            → (∀ n → ∀ 𝕡 → isSet (A n 𝕡))
-- --            → ∀ n → ℙrm {true} n → hSet ℓ
-- -- Truncℙ₂ A isSetA = truncℙ isGroupoidHSet λ n 𝕡 → A n 𝕡 , isSetA n 𝕡

-- -- truncℙ₂ : ∀ {ℓ} 
-- --            → (A : ∀ n → ℙrm {false} n → Type ℓ)
-- --            → (isSetA : ∀ n → ∀ 𝕡 → isSet (A n 𝕡))
-- --            → (∀ n 𝕡 → A n 𝕡)
-- --            → ∀ n → ∀ 𝕡 → ⟨ Truncℙ₂ A isSetA n 𝕡 ⟩
-- -- truncℙ₂ A isSetA f n = w
-- --  where
-- --  f' = f n

-- --  w : ∀ 𝕡 → _
-- --  w 𝕡base = f' 𝕡base
-- --  w (𝕡loop x i) =  f' (𝕡loop x i)
-- --  w (𝕡looop k l i) = f' (𝕡looop k l i)
-- --  w (𝕡comp k l i i₁) = f' (𝕡comp k l i i₁)
-- --  w (𝕡invol k i i₁) = f' (𝕡invol k i i₁)
-- --  w (𝕡comm k l x i i₁) = f' (𝕡comm k l x i i₁)
-- --  w (𝕡braid k k< i i₁) = f' (𝕡braid k k< i i₁)
-- --  w (𝕡squash _ x y p q r s i₀ i₁ i₂) = 
-- --    isOfHLevel→isOfHLevelDep 3
-- --       (isSet→isGroupoid ∘ snd ∘ Truncℙ₂ A isSetA n)
-- --      (w x) (w y) _ _
-- --      (λ j k → w (r j k)) (λ j k → w (s j k))
-- --      (𝕡squash _ x y p q r s) i₀ i₁ i₂

-- truncℙ₂ : ∀ {ℓ} 
--            → (A : ∀ n → ℙrm {true} n → Type ℓ)
--            → (isGroupoidA : ∀ n → ∀ 𝕡 → isGroupoid (A n 𝕡))
--            → (∀ n 𝕡 → A n (toTruncℙ {_} {false} 𝕡))
--            → ∀ n → ∀ 𝕡 → A n 𝕡
-- truncℙ₂ A isSetA f n = w
--  where
--  f' = f n

--  w : ∀ 𝕡 → A n 𝕡
--  w 𝕡base = f' 𝕡base
--  w (𝕡loop x i) =  f' (𝕡loop x i)
--  w (𝕡looop k l i) = f' (𝕡looop k l i)
--  w (𝕡comp k l i i₁) = f' (𝕡comp k l i i₁)
--  w (𝕡invol k i i₁) = f' (𝕡invol k i i₁)
--  w (𝕡comm k l x i i₁) = f' (𝕡comm k l x i i₁)
--  w (𝕡braid k k< i i₁) = f' (𝕡braid k k< i i₁)
--  w (𝕡squash _ x y p q r s i₀ i₁ i₂) = 
--    isOfHLevel→isOfHLevelDep 3
--       (isSetA n)
--      (w x) (w y) _ _
--      (λ j k → w (r j k)) (λ j k → w (s j k))
--      (𝕡squash _ x y p q r s) i₀ i₁ i₂



-- ℕ↔ : ℙrm {true} → Type
-- ℕ↔ = R𝕡rec.f w {squashA = {!!}}
--  where
--  w : R𝕡rec Type
--  R𝕡rec.abase w = ℕ
--  R𝕡rec.aloop w = isoToPath ∘ A.adjTransposition≃
--  R𝕡rec.alooop w k l =
--    isoToPath
--      (compIso (A.adjTransposition≃ k)
--               (A.adjTransposition≃ l))
--  R𝕡rec.acomp w = {!!}
--  R𝕡rec.ainvol w = {!!}
--  R𝕡rec.acomm w = {!!}
--  R𝕡rec.abraid w = {!!}
-- -- module _ {ℓ} (A : Type ℓ) where 


--  𝕍r : R𝕡rec (Type ℓ)
--  R𝕡rec.abase 𝕍r = {!ℕ!}
--  R𝕡rec.aloop 𝕍r = {!!}
--  R𝕡rec.alooop 𝕍r = {!!}
--  R𝕡rec.acomp 𝕍r = {!!}
--  R𝕡rec.ainvol 𝕍r = {!!}
--  R𝕡rec.acomm 𝕍r = {!!}
--  R𝕡rec.abraid 𝕍r = {!!}
 -- R𝕡rec.abase (𝕍r n) = A ×^ n
 -- R𝕡rec.aloop (𝕍r n) k = adjT×^≡ {n = n} (fst k)
 -- R𝕡rec.alooop (𝕍r n) = biAdjT×^≡ {n = n}
 -- R𝕡rec.acomp (𝕍r n) = biAdjT×^≡-comp
 -- R𝕡rec.ainvol (𝕍r n) k = adjT×^≡-invol n (fst k)
 -- R𝕡rec.acomm (𝕍r n) = biAdjT×^≡-comm
 -- R𝕡rec.abraid (𝕍r n) = adjT×^≡-braid

 -- 𝕍 : ∀ n → ℙrm {false} n → Type ℓ
 -- 𝕍 n = R𝕡rec.f (𝕍r n) 

 -- isOfHLevel𝕍r : ∀ n m → isOfHLevel m A →
 --                   R𝕡elimProp {n = n} {false}
 --                         (λ 𝕡 → isOfHLevel m (𝕍 n 𝕡))
 -- R𝕡elimProp.isPropA (isOfHLevel𝕍r n m x) _ = isPropIsOfHLevel m
 -- R𝕡elimProp.abase (isOfHLevel𝕍r n m x) = isOfHLevel×^ n m x

 -- module _ (isSetA : isSet A) where

 --  𝕍₂ : ∀ n → ℙrm {true} n → hSet ℓ
 --  𝕍₂ = truncℙ isGroupoidHSet
 --        λ n 𝕡 → 𝕍 n 𝕡 , R𝕡elimProp.f (isOfHLevel𝕍r n 2 isSetA) 𝕡



--   -- concat𝕧₂ : ∀ n m → {!𝕍₂ n → 𝕍₂ n → ? !}
--   -- concat𝕧₂ = {!!}


-- 𝔽inSnd : ∀ n 𝕡 → ⟨ 𝕍₂ Bool isSetBool n 𝕡 ⟩ → hProp ℓ-zero
-- 𝔽inSnd n = R𝕡elimSet'.f {n = n} w
--  where
--  w : R𝕡elimSet' (λ z → ⟨ 𝕍₂ Bool isSetBool n z ⟩ → hProp ℓ-zero)
--  R𝕡elimSet'.isSetA w _ = isSetΠ λ _ → isSetHProp
--  R𝕡elimSet'.abase w = Fin×Snd n
--  fst (R𝕡elimSet'.aloop w (k , k<) i v) = F×adjTP {n = n} k i v
--  snd (R𝕡elimSet'.aloop w (k , k<) i v) =
--    isProp→PathP 
--      (λ i → isPropΠ λ v → isPropIsProp {A = (F×adjTP {n = n} k i v)} )
--       (snd ∘ Fin×Snd n) (snd ∘ Fin×Snd n) i v

-- -- 𝔽inSnd : ∀ n 𝕡 → ⟨ 𝕍₂ Bool isSetBool n 𝕡 ⟩ → hProp ℓ-zero
-- -- 𝔽inSnd n 𝕡base = Fin×Snd n
-- -- 𝔽inSnd n = {!𝔽inSnd* n!}

-- h𝔽in : ∀ n 𝕡 → hSet ℓ-zero
-- h𝔽in n 𝕡 = _ , isSetΣ (snd (𝕍₂ Bool isSetBool n 𝕡))
--                        (isProp→isSet ∘ snd ∘ 𝔽inSnd n 𝕡)

-- 𝔽in : ∀ n 𝕡 → Type
-- 𝔽in n = fst ∘ h𝔽in n

-- Rsucℙrm : ∀ n {b} → R𝕡rec {n = n} (ℙrm {b} (suc n))
-- R𝕡rec.abase (Rsucℙrm n) = 𝕡base
-- R𝕡rec.aloop (Rsucℙrm n) k = 𝕡loop (suc (fst k) , (snd k))
-- R𝕡rec.alooop (Rsucℙrm n) k l =
--   𝕡looop _ _
-- R𝕡rec.acomp (Rsucℙrm n) k l =
--   𝕡comp _ _
-- R𝕡rec.ainvol (Rsucℙrm n) k =
--   𝕡invol _
-- R𝕡rec.acomm (Rsucℙrm n) k l x =
--   𝕡comm _ _ (suc-commT (fst k) (fst l) x)
-- R𝕡rec.abraid (Rsucℙrm n) k k< =
--   𝕡braid _ _

-- sucℙrm : ∀ {b} n → ℙrm {b} n → ℙrm {b} (suc n)
-- sucℙrm {b} n = R𝕡rec.f {n = n} (Rsucℙrm n) {squashA = w b}
--  where
--   w : ∀ b → if b then isGroupoid (ℙrm {b} (suc n)) else Unit*
--   w false = tt*
--   w true = 𝕡squash _


-- ℙrm+ : ∀ {b} n m → ℙrm {b} m → ℙrm {b} (n + m)
-- ℙrm+ zero m x = x
-- ℙrm+ (suc n) m x = sucℙrm (n + m) (ℙrm+ n m x)

-- Rsucℙrm' : ∀ n {b} → R𝕡rec {n = n} (ℙrm {b} (suc n))
-- R𝕡rec.abase (Rsucℙrm' n) = 𝕡base
-- R𝕡rec.aloop (Rsucℙrm' n) k = 𝕡loop ((fst k) , (<-weaken {n = n} (snd k)))
-- R𝕡rec.alooop (Rsucℙrm' n) k l =
--   𝕡looop _ _
-- R𝕡rec.acomp (Rsucℙrm' n) k l =
--   𝕡comp _ _
-- R𝕡rec.ainvol (Rsucℙrm' n) k =
--   𝕡invol _
-- R𝕡rec.acomm (Rsucℙrm' n) k l =
--   𝕡comm _ _
-- R𝕡rec.abraid (Rsucℙrm' n) k k< =
--   𝕡braid _ _

-- sucℙrm' : ∀ {b} n → ℙrm {b} n → ℙrm {b} (suc n)
-- sucℙrm' {b} n = R𝕡rec.f {n = n} (Rsucℙrm' n) {squashA = w b}
--  where
--   w : ∀ b → if b then isGroupoid (ℙrm {b} (suc n)) else Unit*
--   w false = tt*
--   w true = 𝕡squash _



-- ℙrm+* : ∀ {b} n m → ℙrm {b} m → ℙrm {b} (n + m)
-- ℙrm+* zero m x = x
-- ℙrm+* (suc n) m x = sucℙrm' (n + m) (ℙrm+* n m x)


-- ℙrm+' : ∀ {b} n m → ℙrm {b} n → ℙrm {b} (n + m)
-- ℙrm+' n zero = subst ℙrm (sym (+-zero n))
-- ℙrm+' n (suc m) x = subst ℙrm (sym (+-suc _ _)) (ℙrm+' (suc n) m (sucℙrm' n x))


-- ⊕ : ∀ {n m} → (ℙrm {true} n ⊎  ℙrm {true} m) → ℙrm {true} (n + m)
-- ⊕ (inl x) = ℙrm+' _ _ x
-- ⊕ (inr x) = ℙrm+ _ _ x


-- -- record R𝕡elimCons {n} {trunc} (A : ℙrm {trunc} (suc n) → Type ℓ) : Type ℓ where
-- --  no-eta-equality
-- --  field
-- --    isGroupoidA : Bool→Type trunc → ∀ x → isGroupoid (A x)
-- --    abase : A 𝕡base
-- --    acons : ∀ n → {!A !}
-- --    -- aloop : (k : Σ ℕ  λ k → (suc k < n)) →
-- --    --   PathP (λ i → A (𝕡loop k i)) abase abase
-- --    -- alooop : (k l : Σ ℕ  λ k → (suc k < n)) →
-- --    --   PathP (λ i → A (𝕡looop k l i)) abase abase
-- --    -- acomp : ∀ k l →
-- --    --   SquareP (λ j i → A (𝕡comp k l j i))
-- --    --     (aloop k)
-- --    --     (aloop l)
-- --    --     (alooop k l)
-- --    --     refl
-- --    -- ainvol : ∀ k →
-- --    --   SquareP (λ i j → A (𝕡invol k i j))
-- --    --     (aloop k)
-- --    --     (symP (aloop k))
-- --    --     refl refl
-- --    -- acomm : (k l : Σ ℕ  λ k → (suc k < n)) → ∀ x →     
-- --    --     SquareP (λ i j → A (𝕡comm k l x i j))
-- --    --       refl
-- --    --       refl
-- --    --     (alooop k l)
-- --    --     (alooop l k)
-- --    -- abraid : ∀ k k<  →        
-- --    --       SquareP (λ i j → A (𝕡braid k k< i j))
-- --    --       (aloop (suc k , k<))
-- --    --       (aloop (k , <-weaken {n = n} k<))
-- --    --       (alooop (k , <-weaken {n = n} k<) (suc k , k<))
-- --    --       (alooop (k , <-weaken {n = n} k<) (suc k , k<))



-- 𝕗0 : ∀ n (𝕡 : ℙrm n) → 𝔽in (suc n) (sucℙrm n 𝕡)
-- 𝕗0 n = R𝕡elimSet'.f (w n)
--  where
--  open R𝕡elimSet'
--  w : ∀ n → R𝕡elimSet' (𝔽in (suc n) ∘ sucℙrm n)
--  isSetA (w n) 𝕡 = snd (h𝔽in (suc n) (sucℙrm n 𝕡)) 
--  abase (w n) = Fin×0
--  aloop (w n) (k , k<) = 
--   ΣPathPProp (snd ∘ (Fin×Snd (1 + n)))
--     λ i → true , glue-repeat-false n k i

-- 𝕗suc : ∀ n (𝕡 : ℙrm n) → 𝔽in n 𝕡 → 𝔽in (suc n) (sucℙrm n 𝕡)
-- 𝕗suc n = R𝕡elimSet'.f (w n)
--  where
--  open R𝕡elimSet'
--  w : ∀ n → R𝕡elimSet' (λ 𝕡 → 𝔽in n 𝕡 → 𝔽in (suc n) (sucℙrm n 𝕡))
--  isSetA (w n) 𝕡 = isSet→ (snd (h𝔽in (suc n) (sucℙrm n 𝕡)))
--  abase (w n) = sucFin×
--  aloop (w n) k i (x , y) = (false , x) , y


-- 𝕗glue01 : ∀ n →
--        PathP (λ i → (Fin× (suc (suc n))) →
--       𝔽in (suc (suc n)) (𝕡loop (zero , _) i))
--         (idfun _)
--         (F×adjT {n = 2 + n} zero )
-- 𝕗glue01 n i = fst (glue-F×adjT≃ (suc (suc n)) zero i)

-- 𝕗glue210 : ∀ n →
--        PathP (λ i → (Fin× (suc (suc (suc n)))) →
--       𝔽in (suc (suc (suc n))) (𝕡looop (suc zero , _) (zero , _) i))
--         (F×adjT {n = 3 + n} (suc zero))
--         (F×adjT {n = 3 + n} zero)
-- 𝕗glue210 n =
--    funExt λ (xs , ys) →
--     ΣPathPProp (snd ∘ Fin×Snd (3 + n))
--      (funExt⁻ (glueBiAdjT×< n) xs)

-- 𝕗glue210sym : ∀ n →
--        PathP (λ i → (Fin× (suc (suc (suc n)))) →
--       𝔽in (suc (suc (suc n))) (𝕡looop (zero , _) (suc zero , _)  i))
        
--         (F×adjT {n = 3 + n} zero)
--         (F×adjT {n = 3 + n} (suc zero))
-- 𝕗glue210sym n =
--    funExt λ (xs , ys) →
--     ΣPathPProp (snd ∘ Fin×Snd (3 + n))
--       (toPathP (ΣPathP (refl ,
--         ΣPathP (refl ,
--         ΣPathP (refl , transportRefl _)))))
--      -- (funExt⁻ (glueBiAdjT×< n) ?)
--      -- (funExt⁻ (glueBiAdjT×< n) xs)


-- 𝕗glueBi< : ∀ n k →
--        PathP (λ i → 
--          𝔽in (suc (suc n)) (𝕡loop (suc (suc (fst k)) , snd k) i)
--            →
--       𝔽in (suc (suc n)) (𝕡looop (suc (suc (fst k)) , snd k) (zero , _) i))
--         (idfun _)
--         (F×adjT {n = 2 + n} zero)
-- fst (𝕗glueBi< n k i (xs , ys)) = glueBiAdjT×<SS n k i xs
-- snd (𝕗glueBi< n k i (xs , ys)) =
--   isProp→PathP
--     (λ i → isPropΠ λ ((xs , ys) : 𝔽in (suc (suc n)) (𝕡loop (suc (suc (fst k)) , snd k) i)) → snd
--       (𝔽inSnd (suc (suc n))
--        (𝕡looop (suc (suc (fst k)) , snd k) (zero , tt) i)
--        (glueBiAdjT×<SS n k i xs)))
--      snd (snd ∘ F×adjT {n = 2 + n} zero) i (xs , ys)

-- 𝕗glueBi<sym : ∀ n k →
--        PathP (λ i → 
--          𝔽in (suc (suc n)) (𝕡loop (suc (suc (fst k)) , snd k) (~ i))
--            →
--       𝔽in (suc (suc n)) (𝕡looop  (zero , _) (suc (suc (fst k)) , snd k) i))

--         (F×adjT {n = 2 + n} zero)
--          (idfun _)
-- fst (𝕗glueBi<sym n k i (xs , ys)) = glueBiAdjT×<SS n k (~ i) xs
-- snd (𝕗glueBi<sym n k i (xs , ys)) = 
--   isProp→PathP
--     (λ i → isPropΠ λ ((xs , ys) : 𝔽in (suc (suc n)) (𝕡loop (suc (suc (fst k)) , snd k) (~ i))) → snd
--       (𝔽inSnd (suc (suc n))
--        (𝕡looop (zero , tt) (suc (suc (fst k)) , snd k) i)
--        (glueBiAdjT×<SS n k (~ i) xs)))
--       (snd ∘ F×adjT {n = 2 + n} zero) snd i (xs , ys)


-- 𝕗glue01-involSS : ∀ n →
--    SquareP (λ i j → Fin× (n)
--      → 𝔽in (suc (suc n)) (𝕡invol (zero , _) i j))
--      (λ i → 𝕗glue01 n i ∘' sucFin× ∘' sucFin×)
--      (λ i → 𝕗glue01 n (~ i) ∘' sucFin× ∘' sucFin×)
--      (λ _ → sucFin× ∘' sucFin×)
--      λ _ → sucFin× ∘' sucFin×
-- 𝕗glue01-involSS n =
--   isSet→SquareP'
--    (isSet→ (isSetFin× (2 + n)))
--    _ _ _ _

-- 𝕗glue01-invol01 : ∀ n →
--    SquareP (λ i j → 𝔽in (suc (suc n)) (𝕡invol (zero , _) i j))
--      (λ j → 𝕗glue01 n j Fin×0)
--      (λ j → (𝕗glue01 n (~ j) (sucFin× Fin×0)))
--      refl
--      refl
-- 𝕗glue01-invol01 n = isSet→SquareP' (isSetFin× (2 + n)) _ _ _ _


-- 𝕗glue01-invol10 : ∀ n →
--    SquareP (λ i j → 𝔽in (suc (suc n)) (𝕡invol (zero , _) i j))
--      (λ j → 𝕗glue01 n j (sucFin× Fin×0))
--      (λ j → (𝕗glue01 n (~ j) (Fin×0)))
--      refl
--      refl
-- 𝕗glue01-invol10 n = isSet→SquareP' (isSetFin× (2 + n)) _ _ _ _

-- 𝕗glue01invol : ∀ n → SquareP
--     (λ i j → (𝔽in (suc (suc n)) (𝕡invol (zero , _) i j)
--        × 𝔽in (suc (suc n)) (𝕡invol (zero , _) i j))
--        × (Fin× n → 𝔽in (suc (suc n)) (𝕡invol (zero , _) i j)))
--             (λ j → (𝕗glue01 n j (Fin×0) , 𝕗glue01 n j (sucFin× Fin×0)) ,
--              𝕗glue01 n j ∘' sucFin× ∘' sucFin×)
--             (λ j → (𝕗glue01 n (~ j) (sucFin× Fin×0) , 𝕗glue01 n (~ j) (Fin×0))
--                    , 𝕗glue01 n (~ j) ∘' sucFin× ∘' sucFin×)
--                       refl
--                       refl
                      
-- 𝕗glue01invol n = (congSqP₂ (λ _ _ → _,_)
--          (congSqP₂ (λ _ _ → _,_)
--            (𝕗glue01-invol01 n)
--            (𝕗glue01-invol10 n))
--             (𝕗glue01-involSS n))

-- 𝕗glue01comp< : ∀ n →
--  SquareP
--    (λ i j →
--      ((𝔽in (suc (suc (suc n))) ((𝕡comp (1 , _) (zero , _) i j))) ×^ 3)
--       × (Fin× (n) →
--     𝔽in (suc (suc (suc n))) ((𝕡comp (1 , _) (zero , _) i j))))
--    (λ j → (𝕗0 (suc (suc n)) (𝕡loop (zero , _) j)
--         , 𝕗suc (suc (suc n)) (𝕡loop (zero , _) j) (𝕗glue01 n j (sucFin× Fin×0))
--         , 𝕗suc (suc (suc n)) (𝕡loop (zero , _) j) (𝕗glue01 n j (Fin×0)) , _) ,
--      𝕗suc (suc (suc n)) (𝕡loop (zero , _) j)
--        ∘' 𝕗glue01 n j ∘' sucFin× ∘' sucFin×)
--    (λ j → (𝕗glue01 (suc n) j (sucFin× Fin×0) ,
--            𝕗glue01 (suc n) j (Fin×0) ,
--            𝕗glue01 (suc n) j (sucFin× (sucFin× Fin×0)) , _) ,
--      𝕗glue01 (suc n) j ∘' sucFin× ∘' sucFin× ∘'  sucFin×)
--    (λ i → (𝕗glue210 n i Fin×0 ,
--           𝕗glue210 n i (sucFin× Fin×0) ,
--           𝕗glue210 n i (sucFin× (sucFin× Fin×0)) , _) ,
--      𝕗glue210 n i ∘' sucFin× ∘' sucFin× ∘' sucFin×)
--    refl
-- 𝕗glue01comp< n =
--  isSet→SquareP'
--   (isSet× (isOfHLevel×^ 3 2 (isSetFin× (3 + n)))
--           (isSet→ (isSetFin× (3 + n)))) _ _ _ _


-- 𝕗glue01comp<sym : ∀ n →
--  SquareP
--    (λ i j →
--      ((𝔽in (suc (suc (suc n))) ((𝕡comp (zero , _) (1 , _) i j))) ×^ 3)
--       × (Fin× (n) →
--     𝔽in (suc (suc (suc n))) ((𝕡comp  (zero , _) (1 , _) i j))))
   
--    (λ j → (𝕗glue01 (suc n) j (sucFin× Fin×0) ,
--            𝕗glue01 (suc n) j (Fin×0) ,
--            𝕗glue01 (suc n) j (sucFin× (sucFin× Fin×0)) , _) ,
--      𝕗glue01 (suc n) (j) ∘' sucFin× ∘' sucFin× ∘'  sucFin×)
--    (λ j → (𝕗0 (suc (suc n)) (𝕡loop (zero , _) j)
--         , 𝕗suc (suc (suc n)) (𝕡loop (zero , _) j) (𝕗glue01 n j (sucFin× Fin×0))
--         , 𝕗suc (suc (suc n)) (𝕡loop (zero , _) j) (𝕗glue01 n j (Fin×0)) , _) ,
      
--      𝕗suc (suc (suc n)) (𝕡loop (zero , _) j)
--        ∘' 𝕗glue01 n j ∘' sucFin× ∘' sucFin×
--        )

--    (λ i → (𝕗glue210sym n i Fin×0 ,
--           𝕗glue210sym n i (sucFin× Fin×0) ,
--           𝕗glue210sym n i (sucFin× (sucFin× Fin×0)) , _) ,
--            𝕗glue210sym n i ∘' sucFin× ∘' sucFin× ∘' sucFin×)
--    refl
-- 𝕗glue01comp<sym n = 
--  isSet→SquareP'
--   (isSet× (isOfHLevel×^ 3 2 (isSetFin× (3 + n)))
--           (isSet→ (isSetFin× (3 + n)))) _ _ _ _




-- -- (a : 𝔽in (suc n) (𝕡invol (l , l<) j (~ i))) →
-- --       𝔽in (suc (suc (suc n)))
-- --       (𝕡comm (zero , k<) (suc (suc l) , l<) x i j)

-- 𝕗glue01commS : ∀ n l l<
--  → SquareP (λ i j →
--     let Z = 𝔽in (suc (suc (n)))
--                (𝕡comm (zero , tt) (suc (suc l) , l<) _ i j)
--     in (Z × Z) ×
--      (𝔽in (n) (𝕡invol (l , l<) j (~ i)) → Z))
--       refl
--       refl
--       (λ i → (𝕗glueBi<sym (n) (l , l<) i
--            (𝕗suc (suc (n)) (𝕡loop (suc l , l<) (~ i))
--               (𝕗0 (n) (𝕡loop (l , l<) (~ i))))
--         , 𝕗glueBi<sym (n) (l , l<) i
--            (𝕗0 (1 + n) (𝕡loop (suc l , l<) (~ i))))
--         ,
--          𝕗glueBi<sym (n) (l , l<) i
--          ∘' 𝕗suc (suc (n)) (𝕡loop (suc l , l<) (~ i))
--          ∘' 𝕗suc (n) (𝕡loop (l , l<) (~ i)))
--       λ i → (
--         (𝕗glueBi< (n) (l , l<) i (𝕗0 (1 + n) (𝕡loop (suc l , l<) i)))
--          ,
--          𝕗glueBi< (n) (l , l<) i
--            (𝕗suc (suc (n)) (𝕡loop (suc l , l<) (i))
--               (𝕗0 (n) (𝕡loop (l , l<) (i))))) , (𝕗glueBi< (n) (l , l<) i ∘'
--          𝕗suc (suc (n)) (𝕡loop (suc l , l<) i)
--          ∘' 𝕗suc (n) (𝕡loop (l , l<) i))
-- 𝕗glue01commS n l l< =
--     isSet→SquareP'
--   (isSet× (isSet× (isSetFin× (2 + n)) (isSetFin× (2 + n)) )
--           (isSet→ (isSetFin× (2 + n)))) _ _ _ _

-- 𝕗glueBraid : ∀ n → SquareP
--   (λ i j →
--      let Z = 𝔽in (suc (suc (suc n))) (𝕡braid zero tt i j)
--      in (Z × Z × Z) × (Fin× (n) → Z))
--     (λ j → (𝕗suc (suc (suc n)) (𝕡loop (zero , _) j) (𝕗glue01 n j Fin×0)
--          , (𝕗suc (suc (suc n)) (𝕡loop (zero , _) j) (𝕗glue01 n j (sucFin× Fin×0))
--           , 𝕗0 (2 + n) (𝕡loop (zero , _) j) ))
--       , 𝕗suc (suc (suc n)) (𝕡loop (zero , _) j) ∘' 𝕗glue01 n j ∘' sucFin× ∘' sucFin× )
--     (λ j → (𝕗glue01 (suc n) j Fin×0 
--         , 𝕗glue01 (suc n) j (sucFin× Fin×0)
--          , 𝕗glue01 (suc n) j  (sucFin× (sucFin× Fin×0)) )
--       , 𝕗glue01 (suc n) j ∘' sucFin× ∘' sucFin× ∘' sucFin× )
--     (λ j → ((𝕗glue210sym n j Fin×0 
--         , 𝕗glue210sym n j (sucFin× (sucFin× Fin×0))
--          , 𝕗glue210sym n j  (sucFin× Fin×0) ))
--            , 𝕗glue210sym n j ∘' sucFin× ∘' sucFin× ∘' sucFin×)
--     λ j → ((𝕗glue210sym n j ((sucFin× (sucFin× Fin×0)))
--         , 𝕗glue210sym n j Fin×0
--          , 𝕗glue210sym n j  (sucFin× Fin×0) )) ,
--            𝕗glue210sym n j ∘' sucFin× ∘' sucFin× ∘' sucFin×
-- 𝕗glueBraid n =
--   isSet→SquareP'
--   (isSet× (isSet× (isSetFin× (3 + n))
--       ((isSet× (isSetFin× (3 + n)) (isSetFin× (3 + n)) )) )
--           (isSet→ (isSetFin× (3 + n)))) _ _ _ _



-- -- abstract
-- Σ-swap-012-≡-comp-ua-glue* : ∀ {ℓ} {A : Type ℓ} → {B : Type ℓ}  →
--       SquareP (λ i j → A × A × A × B
--         → Σ-swap-012-≡-comp-ua {A = A} {B} (λ _ → A × A × A × B) i j)
--          (((λ i (a , x) →
--           a , glue
--             (λ { (i = i0) → _
--                ; (i = i1) → _
--                })
--                x)))
--          ((λ i x →
--           glue (λ { (i = i0) → _ ; (i = i1) → _ }) x))
--         (λ i x →
--           glue
--             (λ { (i = i0) → _
--                ; (i = i1) → _
--                })
--                x)
--         λ _ x → x

-- Σ-swap-012-≡-comp-ua-glue* i j x =
--   glue
--      (λ { (i = i1)(j = i0) → _
--         ; (i = i0) → fst x ,
--            glue (λ { (j = i0) → _
--                    ; (j = i1) → _
--                    }) (snd x)
--         ; (j = i1) → _ })
--      x

-- isContrΣ≃ : (A : (Type ℓ)) → isContr (Σ (Type ℓ) λ T → (A ≃ T))
-- isContrΣ≃ A = isOfHLevelRespectEquiv 0
--   (Σ-cong-equiv-snd λ _ → univalence)
--    (isContrSingl A)


-- module _ {ℓ} (A : Type ℓ) where 

--  -- look𝕍 : ∀ n → ∀ 𝕡 → (𝕍 Bool n 𝕡 → A) → 𝕍 A n 𝕡

--  -- open Tab×≃ {A = A}


--  tab×≃ : ∀ n → (Fin× n → A) ≃ (A ×^ n)
--  tab×≃ zero = isoToEquiv Tab×.IsoFin×0→AUnit*
--  tab×≃ (suc n) =
--    preCompEquiv (Maybe∘Fin×≃Fin×∘suc n) ∙ₑ
--        ≃MaybeFunProd ∙ₑ ≃-× (idEquiv _) (tab×≃ n)

--  tab× : ∀ n → (Fin× n → A) → (A ×^ n)
--  tab× = fst ∘ tab×≃


--  cons𝕍 : ∀ n → ∀ 𝕡 → A → 𝕍 A n 𝕡
--      → 𝕍 A (suc n) (sucℙrm n 𝕡)
--  cons𝕍 n 𝕡base = _,_
--  cons𝕍 n (𝕡loop x i) = _,_
--  cons𝕍 n (𝕡looop k l i) = _,_
--  cons𝕍 n (𝕡comp k l i i₁) = _,_
--  cons𝕍 n (𝕡invol k i i₁) = _,_
--  cons𝕍 n (𝕡comm (k , k<) (suc l , l<) x i i₁) = _,_
--  cons𝕍 n (𝕡braid k k< i i₁) = _,_
 
--  tab𝕍 : ∀ n → ∀ 𝕡 → (𝔽in n (toTruncℙ 𝕡) → A) → 𝕍 A n 𝕡
--  tab𝕍 n = R𝕡elim.f (w n) 
--   where
--   open R𝕡elim

--   w : ∀ n → R𝕡elim {n = n} λ 𝕡 → (𝔽in n (toTruncℙ 𝕡) → A) → 𝕍 A n 𝕡
--   isGroupoidA (w n) ()
--   abase (w n) = tab× n
  
--   aloop (w (suc n)) (suc k , k<) i f =
--     f (𝕗0 n (𝕡loop (k , k<) i))
--       , aloop (w n) (k , k<) i (f ∘ 𝕗suc n (𝕡loop (k , k<) i))
--   aloop (w (suc (suc n))) (zero , tt) i f =
--     glueAdjT× (2 + n) zero i
--      (tab× (2 + n) (f ∘ 𝕗glue01 n i))

--   alooop (w (suc n)) (suc k , k<) (suc l , l<) i f =
--     f (𝕗0 n (𝕡looop (k , k<) (l , l<) i))
--     , alooop (w n) (k , k<) (l , l<) i
--        (f ∘ 𝕗suc n (𝕡looop (k , k<) (l , l<) i))
--   alooop (w (suc (suc n))) (zero , tt) (zero , tt) = 
--     congP {B = λ i _ → _ →
--              𝕍 A (suc (suc n)) (𝕡looop (zero , tt) (zero , tt) i)}
--       (λ _ g f → tab× (2 + n) (f ∘' g))
--       {idfun _} {idfun _}
--       (funExt λ x → ΣPathPProp (snd ∘ Fin×Snd (suc (suc n))) refl)
--   alooop (w (suc (suc n))) (zero , tt) (suc (suc k) , k<) i f =
--     glueBiAdjT×<SS {A = A} n (k , k<) (~ i)
--      (aloop (w (suc (suc n))) (suc (suc k) , k<) (~ i)
--         (f ∘' 𝕗glueBi<sym n (k , k<) i))

--   alooop (w (suc (suc (suc n)))) (zero , tt) (suc zero , tt) i f =  
--     glueBiAdjT×< n (~ i) (tab× (3 + n) (f ∘ 𝕗glue210sym n i))
  
--   alooop (w (suc (suc n))) (suc (suc k) , k<) (zero , tt) i f =
--    glueBiAdjT×<SS {A = A} n (k , k<) i
--      (aloop (w (suc (suc n))) (suc (suc k) , k<) i
--         (f ∘' 𝕗glueBi< n (k , k<) i))
--   alooop (w (suc (suc (suc n)))) (suc zero , tt) (zero , tt) i f =
--     glueBiAdjT×< n i (tab× (3 + n) (f ∘ 𝕗glue210 n i))

--   acomp (w (suc n)) (suc k , k<) (suc l , l<) i j f =
--     f (𝕗0 n (𝕡comp (k , k<) (l , l<) i j))
--     , acomp (w n) (k , k<) (l , l<) i j
--        (f ∘ 𝕗suc n (𝕡comp (k , k<) (l , l<) i j))
--   acomp (w (suc (suc n))) (zero , tt) (zero , tt) i j f =
--    aloop (w (suc (suc n))) (zero , tt) j (f ∘'     
--      isSet→SquareP' {A = λ i j →
--        𝔽in (suc (suc n)) (𝕡loop (zero , tt) j) →
--       𝔽in (suc (suc n)) (𝕡comp (zero , tt) (zero , tt) i j)}
--    (isSet→ (isSetFin× (2 + n)))
--     (λ _ x → x) (λ _ x → x)
--     (funExt λ x → ΣPathPProp (snd ∘ Fin×Snd (suc (suc n))) refl)
--       refl i j)
  
  
--   acomp (w (suc (suc n))) (zero , tt) (suc (suc l) , l<) i j f =
--     glue-biAdjT×^≡-comp<SS {n = n} l l< tt (~ i) j
--        (f (isSet→SquareP'
--            {A =
--              (λ i j → 𝔽in (suc (suc n)) (𝕡comp (zero , tt) (suc (suc l) , l<) i j))}
--            (isSetFin× (2 + n))
--            (λ j → 𝕗glue01 n j (sucFin× Fin×0))
--            (λ j → 𝕗0 (suc n) (𝕡loop ((suc l) , l<) j))
--            (λ i → 𝕗glueBi<sym n (l , l<) i (𝕗0 (suc n) (𝕡loop ((suc l) , l<) (~ i))))
--            (λ _ → Fin×0) i j)
--          , f (isSet→SquareP'
--            {A =
--              (λ i j → 𝔽in (suc (suc n)) (𝕡comp (zero , tt) (suc (suc l) , l<) i j))}
--            (isSetFin× (2 + n))

--            (λ j → 𝕗glue01 n j (Fin×0))
--            (λ j → 𝕗suc (suc n) (𝕡loop (suc l , l<) (j))
--                   (𝕗0 (n) (𝕡loop ((l) , l<) (j))))
--            (λ i → 𝕗glueBi<sym n (l , l<) i
--                      (𝕗suc (suc n) (𝕡loop (suc l , l<) (~ i))
--                         (𝕗0 n (𝕡loop (l , l<) (~ i)))))
--            (λ _ → sucFin× Fin×0) i j)
--          , aloop (w n) (l , l<) ((~ i) ∨ j)
--         (f ∘'
--           isSet→SquareP'
--             {A = λ i j →
--               𝔽in n (𝕡loop (l , l<) ((~ i) ∨ j)) →
--       𝔽in (suc (suc n)) (𝕡comp (zero , tt) (suc (suc l) , l<) i j)}
--             (isSet→ (isSetFin× (2 + n)))
--             (λ j → 𝕗glue01 n j ∘' sucFin× ∘' sucFin×)
--             (λ j → 𝕗suc (suc n) (𝕡loop (suc l , l<) j)
--                 ∘' 𝕗suc n (𝕡loop (l , l<) j))
--             (λ i → 𝕗glueBi<sym n (l , l<) (i) ∘'
--                 𝕗suc (suc n) (𝕡loop (suc l , l<) (~ i))
--                 ∘' 𝕗suc n (𝕡loop (l , l<) (~ i)))
--             (λ _ → sucFin× ∘' sucFin×)

--             i j)
--             )

--   acomp (w (suc (suc (suc n)))) (zero , tt) (suc zero , l<) i j f =
--     let ((f0 , f1 , f2 , _) , fSSS) = 𝕗glue01comp<sym n i j
--     in Σ-swap-012-≡-comp-ua-glue* {A = A} {A ×^ n} (~ i) j 
--           (f f0 , f f1 , f f2 , tab× n (f ∘' fSSS))


--   acomp (w (suc (suc n))) (suc (suc k) , k<) (zero , tt) i j f =
--    glue-biAdjT×^≡-comp<SS {n = n} k k< tt i j
--       (f (isSet→SquareP'
--            {A =
--              (λ i j → 𝔽in (suc (suc n)) (𝕡comp (suc (suc k) , k<) (zero , tt) i j))}
--            (isSetFin× (2 + n))
--            (λ j → 𝕗0 (suc n) (𝕡loop ((suc k) , k<) j))
--            (λ j → 𝕗glue01 n j (sucFin× Fin×0))
--            (λ i → 𝕗glueBi< n (k , k<) i (𝕗0 (suc n) (𝕡loop ((suc k) , k<) i)))
--            (λ _ → Fin×0) i j) 
--      , f (isSet→SquareP'
--            {A =
--              (λ i j → 𝔽in (suc (suc n)) (𝕡comp (suc (suc k) , k<) (zero , tt) i j))}
--            (isSetFin× (2 + n))
--            (λ j → 𝕗suc (suc n) (𝕡loop (suc k , k<) j)
--                   (𝕗0 (n) (𝕡loop ((k) , k<) j)))
--            (λ j → 𝕗glue01 n j (Fin×0))
--            (λ i → 𝕗glueBi< n (k , k<) i
--                      (𝕗suc (suc n) (𝕡loop (suc k , k<) i)
--                         (𝕗0 n (𝕡loop (k , k<) i))))
--            (λ _ → sucFin× Fin×0) i j) 
--      , aloop (w n) (k , k<) (i ∨ j)
--         (f ∘'
--           isSet→SquareP'
--             {A = λ i j →
--               𝔽in n (𝕡loop (k , k<) (i ∨ j)) →
--       𝔽in (suc (suc n)) (𝕡comp (suc (suc k) , k<) (zero , tt) i j)}
--             (isSet→ (isSetFin× (2 + n)))
--             (λ j → 𝕗suc (suc n) (𝕡loop (suc k , k<) j)
--                 ∘' 𝕗suc n (𝕡loop (k , k<) j))
--             (λ j → 𝕗glue01 n j ∘' sucFin× ∘' sucFin×)
--             (λ i → 𝕗glueBi< n (k , k<) i ∘'
--                 𝕗suc (suc n) (𝕡loop (suc k , k<) i)
--                 ∘' 𝕗suc n (𝕡loop (k , k<) i))
--             (λ _ → sucFin× ∘' sucFin×) i j))

--   acomp (w (suc (suc (suc n)))) (suc zero , tt) (zero , tt) i j f =
--     let ((f0 , f1 , f2 , _) , fSSS) = 𝕗glue01comp< n i j
--     in Σ-swap-012-≡-comp-ua-glue* {A = A} {A ×^ n} i j
--           (f f0 , f f1 , f f2 , tab× n (f ∘' fSSS))
  
  
--   ainvol (w (suc n)) (suc k , k<) i j f =
--     f (𝕗0 n (𝕡invol (k , k<) i j))
--     , ainvol (w n) (k , k<) i j
--         (f ∘ 𝕗suc n (𝕡invol (k , k<) i j))
--   ainvol (w (suc (suc n))) (zero , tt) i j f =    
--    let ((f0 , f1) , fSS) = 𝕗glue01invol n i j
--    in Σ-swap-01-≡-invol-ua-glue {A = A} {B = A ×^ n} i j
--          (f f0 , f f1 , tab× n (f ∘' fSS))

--   acomm (w (suc n)) (suc k , k<) (suc (suc (suc l)) , l<) x i j f =    
--     f (𝕗0 n (𝕡comm (k , k<) (suc (suc l) , l<) x i j))
--     , acomm (w n) (k , k<) (suc (suc l) , l<) x i j
--        (f ∘ 𝕗suc n (𝕡comm (k , k<) (suc (suc l) , l<) x i j)) 
--   acomm (w (suc (suc n))) (zero , k<) (suc (suc l) , l<) x i j f =
--    let ((f0 , f1) , fSS) = 𝕗glue01commS n l l< i j
--    in glue-biAdjT×^≡-comm {n = n} (l , l<)
--       i j
--       (f f0 , f f1 , ainvol (w n) (l , l<) j (~ i) (f ∘ fSS))
   
--   abraid (w (suc n)) (suc k) k< i j f =
--       f (𝕗0 n (𝕡braid k k< i j))
--     , abraid (w n) k k< i j (f ∘  𝕗suc n (𝕡braid k  k< i j))
--   abraid (w (suc (suc (suc n)))) zero tt i j f =
--    let ((f0 , f1 , f2) , fSSS) = 𝕗glueBraid n i j
--    in glue-adjT×^≡-braid {n = n} i j
--          (ua-gluePath (adjT×^≃ 0 ∙ₑ compEquiv (adjT×^≃ 1) (adjT×^≃ 0))
--            (λ j → f f2 , f f0 , f f1 , tab× n (f ∘' fSSS)) j)
           

--  isEquivTab𝕍 : ∀ n → ∀ 𝕡 → (isEquiv (tab𝕍 n 𝕡))
--  isEquivTab𝕍 n = R𝕡elimProp.f w
--   where
--   w : R𝕡elimProp (isEquiv ∘ tab𝕍 n)
--   R𝕡elimProp.isPropA w _ = isPropIsEquiv _
--   R𝕡elimProp.abase w = snd (tab×≃ n)

--  s𝕍₃' : ∀ n → (𝕡 : ℙrm {false} n) →
--     Σ (Type ℓ) λ T → ((𝔽in n (toTruncℙ 𝕡) → A) ≃ T)
--  s𝕍₃' n 𝕡 = _ , (_ , isEquivTab𝕍 n 𝕡)


--  s𝕍₃ : ∀ n → (𝕡 : ℙrm {true} n) → Σ (Type ℓ) λ T → ((𝔽in n 𝕡 → A) ≃ T)
--  s𝕍₃ =  truncℙ₂ _ (λ _ _ → isOfHLevelPlus 3 (isContrΣ≃ _) )  s𝕍₃'


--  𝕍₃ : ∀ n → ℙrm {true} n → Type ℓ
--  𝕍₃ n = fst ∘ s𝕍₃ n

--  module _ (isGrpA : isGroupoid A) where

--   isGroupoid𝕍₃ : ∀ n → ∀ 𝕡 → isGroupoid (𝕍₃ n 𝕡)
--   isGroupoid𝕍₃ n = R𝕡elimProp.f w
--    where
--    w : R𝕡elimProp _
--    R𝕡elimProp.isPropA w _ = isPropIsOfHLevel 3
--    R𝕡elimProp.abase w = isOfHLevel×^ n 3 isGrpA 


--   cons𝕍₃ : ∀ n → ∀ 𝕡 → A → 𝕍₃ n 𝕡
--       → 𝕍₃ (suc n) (sucℙrm n 𝕡)
--   cons𝕍₃ n = R𝕡elim.f w
--    where
--    w : R𝕡elim (λ z → A → 𝕍₃ n z → 𝕍₃ (suc n) (sucℙrm n z))
--    R𝕡elim.isGroupoidA w _ 𝕡 =
--      isGroupoidΠ2 λ _ _ →  isGroupoid𝕍₃ (suc n) (sucℙrm n 𝕡)
--    R𝕡elim.abase w = _,_
--    R𝕡elim.aloop w _ _ = _,_
--    R𝕡elim.alooop w _ _ _ = _,_
--    R𝕡elim.acomp w _ _ _ _ = _,_
--    R𝕡elim.ainvol w _ _ _ = _,_
--    R𝕡elim.acomm w _ (suc l , l<) _ _ _ = _,_
--    R𝕡elim.abraid w _ _ _ _ = _,_
