{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.BaseLim where

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

open import Cubical.HITs.Permutation.Base

private
  variable
    ℓ : Level
    A : Type ℓ


data 𝕃rm {trunc : Bool} : Type₀ where 
  𝕝base : 𝕃rm
  𝕝loop : ∀ n → (Σ ℕ  λ k → (suc k < n)) → 𝕝base ≡ 𝕝base  
  𝕝looop : ∀ n → (k l : Σ ℕ  λ k → (suc k < n)) → 𝕝base ≡ 𝕝base
  
  𝕝comp : ∀ n → (k l : Σ ℕ  λ k → (suc k < n)) →
     Square
       (𝕝loop n k)
       (𝕝loop n l)
       (𝕝looop n k l)
       refl
         
  𝕝invol : ∀ n k → 𝕝loop n k ≡ sym (𝕝loop n k)
  𝕝comm : ∀ n (k l : Σ ℕ  λ k → (suc k < n)) →
     commT (fst k) (fst l) →
       Square
         refl
         refl
       (𝕝looop n k l)
       (𝕝looop n l k)

  𝕝braid : ∀ n k k<  →        
         Square
         (𝕝loop n (suc k , k<))
         (𝕝loop n (k , <-weaken {n = n} k<))
         (𝕝looop n (k , <-weaken {n = n} k<) (suc k , k<))
         (𝕝looop n (k , <-weaken {n = n} k<) (suc k , k<))

  𝕝squash : Bool→Type trunc → isGroupoid (𝕃rm)




toTrunc𝕃 : ∀ {b} → 𝕃rm {b} → 𝕃rm {true}
toTrunc𝕃 𝕝base = 𝕝base
toTrunc𝕃 (𝕝loop n x i) = 𝕝loop n x i
toTrunc𝕃 (𝕝looop n k l i) = 𝕝looop n k l i
toTrunc𝕃 (𝕝comp n k l i i₁) = 𝕝comp n k l i i₁
toTrunc𝕃 (𝕝invol n k i i₁) = 𝕝invol n k i i₁
toTrunc𝕃 (𝕝comm n k l x i i₁) = 𝕝comm n k l x i i₁
toTrunc𝕃 (𝕝braid n k k< i i₁) = 𝕝braid n k k< i i₁
toTrunc𝕃 (𝕝squash _ x y p q r s i i₁ x₅) =
 𝕝squash _ _ _ _ _
  (λ i j → toTrunc𝕃 (r i j)) (λ i j → toTrunc𝕃 (s i j))
  i i₁ x₅

-- 𝕝comp' : ∀ {n b} → (k l : Σ ℕ  λ k → (suc k < n)) →
--    Square {A = 𝕃rm {b} n}
--      (𝕝loop k)
--      (𝕝loop l)
--      refl
--      (𝕝looop k l)
-- 𝕝comp' k l =
--    (𝕝invol k) ◁
--    (λ i j → (𝕝comp k l i (~ j)))
--    ▷ sym (𝕝invol l)

𝕝looop-invol : ∀ {b} n → (k l : Σ ℕ  λ k → (suc k < n)) →
    𝕝looop {b} n k l ≡ sym (𝕝looop n l k)
𝕝looop-invol n k l i j =
   hcomp
      (λ l' → λ {
        (i = i0) → 𝕝comp n k l j (~ l')
       ;(i = i1) → 𝕝comp n l k (~ j) (~ l')
       ;(j = i0) → 𝕝loop n k (~ l')
       ;(j = i1) → 𝕝loop n l (~ l')
       }) 𝕝base

record R𝕝rec (A : Type ℓ) : Type ℓ where
 no-eta-equality
 field
   abase : A
   aloop : ∀ n → (Σ ℕ  λ k → (suc k < n)) → abase ≡ abase
   alooop : ∀ n → (k l : Σ ℕ  λ k → (suc k < n)) → abase ≡ abase
   acomp : ∀ n → (k l : Σ ℕ  λ k → (suc k < n)) →
      Square
        (aloop n k)
        (aloop n l)
        (alooop n k l)
        refl

   ainvol : ∀ n k → aloop n k ≡ sym (aloop n k)
   acomm : ∀ n → (k l : Σ ℕ  λ k → (suc k < n)) →
      commT (fst k) (fst l) →
        Square
          refl
          refl
        (alooop n k l)
        (alooop n l k)

   abraid : ∀ n k k<  →        
          Square
          (aloop n (suc k , k<))
          (aloop n (k , <-weaken {n = n} k<))
          (alooop n (k , <-weaken {n = n} k<) (suc k , k<))
          (alooop n (k , <-weaken {n = n} k<) (suc k , k<))


 f : ∀ {trunc} → {squashA : if trunc then (isGroupoid A) else Unit*} →
       𝕃rm {trunc} → A
 f 𝕝base = abase
 f (𝕝loop n x i) = aloop n x i
 f (𝕝looop n k l i) = alooop n k l i
 f (𝕝comp n k l i i₁) = acomp n k l i i₁
 f (𝕝invol n k i i₁) = ainvol n k i i₁
 f (𝕝comm n k l x i i₁) = acomm n k l x i i₁
 f (𝕝braid n k k< i i₁) = abraid n k k< i i₁
 f {true} {t} (𝕝squash _ _ _ _ _ r s i₀ i₁ i₂) =   
   t _ _ _ _
     (λ i j → (f {true} {t} (r i j)))
     (λ i j → (f {true} {t} (s i j)))
     i₀ i₁ i₂


 -- ℙrm→𝕃rm : ∀ {b} n → ℙrm {b} n → 𝕃rm {b}
 -- ℙrm→𝕃rm n 𝕡base = 𝕝base
 -- ℙrm→𝕃rm n (𝕡loop x i) = 𝕝loop n x i
 -- ℙrm→𝕃rm n (𝕡looop k l i) = 𝕝looop n k l i
 -- ℙrm→𝕃rm n (𝕡comp k l i i₁) = 𝕝comp n k l i i₁
 -- ℙrm→𝕃rm n (𝕡invol k i i₁) = 𝕝invol n k i i₁
 -- ℙrm→𝕃rm n (𝕡comm k l x i i₁) = 𝕝comm n k l x i i₁
 -- ℙrm→𝕃rm n (𝕡braid k k< i i₁) = 𝕝braid n k k< i i₁
 -- ℙrm→𝕃rm n (𝕡squash x _ _ _ _ r s i i₁ x₅) =
 --   𝕝squash x _ _ _ _
 --    (λ i j → ℙrm→𝕃rm n (r i j))
 --    (λ i j → ℙrm→𝕃rm n (s i j))
 --    i i₁ x₅
 
-- record R𝕝elim {n} {trunc} (A : 𝕃rm {trunc} n → Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--    isGroupoidA : Bool→Type trunc → ∀ x → isGroupoid (A x)
--    abase : A 𝕝base
--    aloop : (k : Σ ℕ  λ k → (suc k < n)) →
--      PathP (λ i → A (𝕝loop k i)) abase abase
--    alooop : (k l : Σ ℕ  λ k → (suc k < n)) →
--      PathP (λ i → A (𝕝looop k l i)) abase abase
--    acomp : ∀ k l →
--      SquareP (λ j i → A (𝕝comp k l j i))
--        (aloop k)
--        (aloop l)
--        (alooop k l)
--        refl
--    ainvol : ∀ k →
--      SquareP (λ i j → A (𝕝invol k i j))
--        (aloop k)
--        (symP (aloop k))
--        refl refl
--    acomm : (k l : Σ ℕ  λ k → (suc k < n)) → ∀ x →     
--        SquareP (λ i j → A (𝕝comm k l x i j))
--          refl
--          refl
--        (alooop k l)
--        (alooop l k)
--    abraid : ∀ k k<  →        
--          SquareP (λ i j → A (𝕝braid k k< i j))
--          (aloop (suc k , k<))
--          (aloop (k , <-weaken {n = n} k<))
--          (alooop (k , <-weaken {n = n} k<) (suc k , k<))
--          (alooop (k , <-weaken {n = n} k<) (suc k , k<))
  


--  f : ∀ x → A x
--  f 𝕝base = abase
--  f (𝕝loop x i) = aloop x i
--  f (𝕝looop k l i) = alooop k l i
--  f (𝕝comp k l j i) = acomp k l j i
   
--  f (𝕝invol k i j) = ainvol k i j
 
--  f (𝕝comm k l x i j) = acomm k l x i j
    
 
--  f (𝕝braid k k< i j) = abraid k k< i j
--  f (𝕝squash X x y p q r s i j k) =
--    isOfHLevel→isOfHLevelDep 3 (isGroupoidA X)
--      _ _ _ _
--      (λ j k → f (r j k)) (λ j k → f (s j k))
--      (𝕝squash X x y p q r s) i j k





-- record R𝕝elimSet {n} {trunc} (A : 𝕃rm {trunc} n → Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--    isSetA : ∀ x → isSet (A x)
--    abase : A 𝕝base
--    aloop : (k : Σ ℕ  λ k → (suc k < n)) →
--      PathP (λ i → A (𝕝loop k i)) abase abase
--    alooop : (k l : Σ ℕ  λ k → (suc k < n)) →
--      PathP (λ i → A (𝕝looop k l i)) abase abase
--    -- (k l : Σ ℕ  λ k → (suc k < n)) → abase ≡ abase

--  fR : R𝕝elim (λ z → A z)
--  R𝕝elim.isGroupoidA fR X = isSet→isGroupoid ∘ isSetA
--  R𝕝elim.abase fR = abase
--  R𝕝elim.aloop fR = aloop
--  R𝕝elim.alooop fR = alooop
--  R𝕝elim.acomp fR = w
--    where
--    abstract
--     w : (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
--       SquareP (λ j i → A (𝕝comp k l j i)) (aloop k) (aloop l)
--       (alooop k l) refl
--     w k l = isSet→SquareP (λ j i → isSetA (𝕝comp k l j i)) _ _ _ _
--  R𝕝elim.ainvol fR = w
--   where
--   abstract
--    w : (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
--       SquareP (λ i j → A (𝕝invol k i j)) (aloop k) (symP (aloop k)) refl
--       refl
--    w k = isSet→SquareP (λ j i → isSetA (𝕝invol k j i)) _ _ _ _
--  R𝕝elim.acomm fR = w
--   where
--   abstract
--    w : (k l : Σ ℕ (λ k₁ → suc k₁ < n)) (x : commT (fst k) (fst l)) →
--     SquareP (λ i j → A (𝕝comm k l x i j)) refl refl
--     (R𝕝elim.alooop fR k l) (R𝕝elim.alooop fR l k)
--    w k l x = isSet→SquareP (λ j i → isSetA (𝕝comm k l x j i)) _ _ _ _ 
--  R𝕝elim.abraid fR = w
--   where
--   abstract
--    w : (k : ℕ)
--     (k< : suc (suc (suc k)) Cubical.Data.Nat.Order.Recursive.≤ n) →
--     SquareP (λ i j → A (𝕝braid k k< i j))
--     (R𝕝elim.aloop fR (suc k , k<)) (R𝕝elim.aloop fR (k , <-weaken {n = n} k<))
--     (R𝕝elim.alooop fR (k , <-weaken {n = n} k<) (suc k , k<))
--     (R𝕝elim.alooop fR (k , <-weaken {n = n} k<) (suc k , k<))
--    w k k< = isSet→SquareP (λ j i → isSetA (𝕝braid k k< j i)) _ _ _ _


--  f : ∀ x → A x
--  f = R𝕝elim.f fR



-- record R𝕝elimSet' {n} {trunc} (A : 𝕃rm {trunc} n → Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--    isSetA : ∀ x → isSet (A x)
--    abase : A 𝕝base
--    aloop : (k : Σ ℕ  λ k → (suc k < n)) →
--      PathP (λ i → A (𝕝loop k i)) abase abase

--  fR : R𝕝elimSet (λ z → A z)
--  R𝕝elimSet.isSetA fR = isSetA
--  R𝕝elimSet.abase fR = abase
--  R𝕝elimSet.aloop fR = aloop
--  R𝕝elimSet.alooop fR  = w
--   where
--    abstract
--     w : (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
--      PathP (λ i → A (𝕝looop k l i)) (R𝕝elimSet.abase fR)
--      (R𝕝elimSet.abase fR)
--     w = λ k l i → comp (λ j → A (𝕝comp k l i (~ j)))
--       (λ j → λ { (i = i0) → aloop k (~ j) ; (i = i1) → aloop l (~ j) })
--       abase

--  f : ∀ x → A x
--  f = R𝕝elimSet.f fR



-- record R𝕝elimProp {n} {trunc} (A : 𝕃rm {trunc} n → Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--    isPropA : ∀ x → isProp (A x)
--    abase : A 𝕝base

--  fR : R𝕝elimSet (λ z → A z)
--  R𝕝elimSet.isSetA fR = isProp→isSet ∘ isPropA
--  R𝕝elimSet.abase fR = abase
--  R𝕝elimSet.aloop fR k = isProp→PathP (λ _ → isPropA _) _ _
--  R𝕝elimSet.alooop fR k l = isProp→PathP (λ _ → isPropA _) _ _

--  f : ∀ x → A x
--  f = R𝕝elimSet.f fR


-- trunc𝕃 : ∀ {ℓ} {A : Type ℓ} → (isGroupoid A)
--            → (∀ n → 𝕃rm {false} n → A)
--            → ∀ n → 𝕃rm {true} n → A
-- trunc𝕃 isGrpA f n = w
--  where
--  f' = f n

--  w : 𝕃rm n → _
--  w 𝕝base = f' 𝕝base
--  w (𝕝loop x i) =  f' (𝕝loop x i)
--  w (𝕝looop k l i) = f' (𝕝looop k l i)
--  w (𝕝comp k l i i₁) = f' (𝕝comp k l i i₁)
--  w (𝕝invol k i i₁) = f' (𝕝invol k i i₁)
--  w (𝕝comm k l x i i₁) = f' (𝕝comm k l x i i₁)
--  w (𝕝braid k k< i i₁) = f' (𝕝braid k k< i i₁)
--  w (𝕝squash _ _ _ _ _ r s i₀ i₁ i₂) =   
--    isGrpA _ _ _ _
--      (λ i j → (w (r i j)))
--      (λ i j → (w (s i j)))
--      i₀ i₁ i₂

-- -- Trunc𝕃₂ : ∀ {ℓ} 
-- --            → (A : ∀ n → 𝕃rm {false} n → Type ℓ)
-- --            → (∀ n → ∀ 𝕝 → isSet (A n 𝕝))
-- --            → ∀ n → 𝕃rm {true} n → hSet ℓ
-- -- Trunc𝕃₂ A isSetA = trunc𝕃 isGroupoidHSet λ n 𝕝 → A n 𝕝 , isSetA n 𝕝

-- -- trunc𝕃₂ : ∀ {ℓ} 
-- --            → (A : ∀ n → 𝕃rm {false} n → Type ℓ)
-- --            → (isSetA : ∀ n → ∀ 𝕝 → isSet (A n 𝕝))
-- --            → (∀ n 𝕝 → A n 𝕝)
-- --            → ∀ n → ∀ 𝕝 → ⟨ Trunc𝕃₂ A isSetA n 𝕝 ⟩
-- -- trunc𝕃₂ A isSetA f n = w
-- --  where
-- --  f' = f n

-- --  w : ∀ 𝕝 → _
-- --  w 𝕝base = f' 𝕝base
-- --  w (𝕝loop x i) =  f' (𝕝loop x i)
-- --  w (𝕝looop k l i) = f' (𝕝looop k l i)
-- --  w (𝕝comp k l i i₁) = f' (𝕝comp k l i i₁)
-- --  w (𝕝invol k i i₁) = f' (𝕝invol k i i₁)
-- --  w (𝕝comm k l x i i₁) = f' (𝕝comm k l x i i₁)
-- --  w (𝕝braid k k< i i₁) = f' (𝕝braid k k< i i₁)
-- --  w (𝕝squash _ x y p q r s i₀ i₁ i₂) = 
-- --    isOfHLevel→isOfHLevelDep 3
-- --       (isSet→isGroupoid ∘ snd ∘ Trunc𝕃₂ A isSetA n)
-- --      (w x) (w y) _ _
-- --      (λ j k → w (r j k)) (λ j k → w (s j k))
-- --      (𝕝squash _ x y p q r s) i₀ i₁ i₂

-- trunc𝕃₂ : ∀ {ℓ} 
--            → (A : ∀ n → 𝕃rm {true} n → Type ℓ)
--            → (isGroupoidA : ∀ n → ∀ 𝕝 → isGroupoid (A n 𝕝))
--            → (∀ n 𝕝 → A n (toTrunc𝕃 {_} {false} 𝕝))
--            → ∀ n → ∀ 𝕝 → A n 𝕝
-- trunc𝕃₂ A isSetA f n = w
--  where
--  f' = f n

--  w : ∀ 𝕝 → A n 𝕝
--  w 𝕝base = f' 𝕝base
--  w (𝕝loop x i) =  f' (𝕝loop x i)
--  w (𝕝looop k l i) = f' (𝕝looop k l i)
--  w (𝕝comp k l i i₁) = f' (𝕝comp k l i i₁)
--  w (𝕝invol k i i₁) = f' (𝕝invol k i i₁)
--  w (𝕝comm k l x i i₁) = f' (𝕝comm k l x i i₁)
--  w (𝕝braid k k< i i₁) = f' (𝕝braid k k< i i₁)
--  w (𝕝squash _ x y p q r s i₀ i₁ i₂) = 
--    isOfHLevel→isOfHLevelDep 3
--       (isSetA n)
--      (w x) (w y) _ _
--      (λ j k → w (r j k)) (λ j k → w (s j k))
--      (𝕝squash _ x y p q r s) i₀ i₁ i₂




module _ {ℓ} (A : Type ℓ) where 


 lswap01 : List A → List A
 lswap01 (x ∷ x' ∷ xs) = x' ∷ x ∷ xs
 lswap01 x = x

 invo-lswap01 : isInvolution lswap01
 invo-lswap01 [] = refl
 invo-lswap01 (x ∷ []) = refl
 invo-lswap01 (x ∷ x₁ ∷ x₂) = refl
 
 isEquivLswap01 : isEquiv lswap01 
 isEquivLswap01 = involIsEquiv invo-lswap01

 lswap01≃ : List A ≃ List A
 lswap01≃ = lswap01 , isEquivLswap01

 𝕃r : R𝕝rec (Type ℓ)
 R𝕝rec.abase 𝕃r = List A
 R𝕝rec.aloop 𝕃r = {!!}
 R𝕝rec.alooop 𝕃r = {!!}
 R𝕝rec.acomp 𝕃r = {!!}
 R𝕝rec.ainvol 𝕃r = {!!}
 R𝕝rec.acomm 𝕃r = {!!}
 R𝕝rec.abraid 𝕃r = {!!}
 -- R𝕝rec.abase (𝕃r n) = A ×^ n
 -- R𝕝rec.aloop (𝕃r n) k = adjT×^≡ {n = n} (fst k)
 -- R𝕝rec.alooop (𝕃r n) = biAdjT×^≡ {n = n}
 -- R𝕝rec.acomp (𝕃r n) = biAdjT×^≡-comp
 -- R𝕝rec.ainvol (𝕃r n) k = adjT×^≡-invol n (fst k)
 -- R𝕝rec.acomm (𝕃r n) = biAdjT×^≡-comm
 -- R𝕝rec.abraid (𝕃r n) = adjT×^≡-braid

 𝕃 : 𝕃rm {false} → Type ℓ
 𝕃 = R𝕝rec.f 𝕃r

--  isOfHLevel𝕍r : ∀ n m → isOfHLevel m A →
--                    R𝕝elimProp {n = n} {false}
--                          (λ 𝕝 → isOfHLevel m (𝕍 n 𝕝))
--  R𝕝elimProp.isPropA (isOfHLevel𝕍r n m x) _ = isPropIsOfHLevel m
--  R𝕝elimProp.abase (isOfHLevel𝕍r n m x) = isOfHLevel×^ n m x

--  module _ (isSetA : isSet A) where

--   𝕍₂ : ∀ n → 𝕃rm {true} n → hSet ℓ
--   𝕍₂ = trunc𝕃 isGroupoidHSet
--         λ n 𝕝 → 𝕍 n 𝕝 , R𝕝elimProp.f (isOfHLevel𝕍r n 2 isSetA) 𝕝

-- 𝔽inSnd : ∀ n 𝕝 → ⟨ 𝕍₂ Bool isSetBool n 𝕝 ⟩ → hProp ℓ-zero
-- 𝔽inSnd n = R𝕝elimSet'.f {n = n} w
--  where
--  w : R𝕝elimSet' (λ z → ⟨ 𝕍₂ Bool isSetBool n z ⟩ → hProp ℓ-zero)
--  R𝕝elimSet'.isSetA w _ = isSetΠ λ _ → isSetHProp
--  R𝕝elimSet'.abase w = Fin×Snd n
--  fst (R𝕝elimSet'.aloop w (k , k<) i v) = F×adjTP {n = n} k i v
--  snd (R𝕝elimSet'.aloop w (k , k<) i v) =
--    isProp→PathP 
--      (λ i → isPropΠ λ v → isPropIsProp {A = (F×adjTP {n = n} k i v)} )
--       (snd ∘ Fin×Snd n) (snd ∘ Fin×Snd n) i v

-- -- 𝔽inSnd : ∀ n 𝕝 → ⟨ 𝕍₂ Bool isSetBool n 𝕝 ⟩ → hProp ℓ-zero
-- -- 𝔽inSnd n 𝕝base = Fin×Snd n
-- -- 𝔽inSnd n = {!𝔽inSnd* n!}

-- h𝔽in : ∀ n 𝕝 → hSet ℓ-zero
-- h𝔽in n 𝕝 = _ , isSetΣ (snd (𝕍₂ Bool isSetBool n 𝕝))
--                        (isProp→isSet ∘ snd ∘ 𝔽inSnd n 𝕝)

-- 𝔽in : ∀ n 𝕝 → Type
-- 𝔽in n = fst ∘ h𝔽in n

-- Rsuc𝕃rm : ∀ n {b} → R𝕝rec {n = n} (𝕃rm {b} (suc n))
-- R𝕝rec.abase (Rsuc𝕃rm n) = 𝕝base
-- R𝕝rec.aloop (Rsuc𝕃rm n) k = 𝕝loop (suc (fst k) , (snd k))
-- R𝕝rec.alooop (Rsuc𝕃rm n) k l =
--   𝕝looop _ _
-- R𝕝rec.acomp (Rsuc𝕃rm n) k l =
--   𝕝comp _ _
-- R𝕝rec.ainvol (Rsuc𝕃rm n) k =
--   𝕝invol _
-- R𝕝rec.acomm (Rsuc𝕃rm n) k l x =
--   𝕝comm _ _ (suc-commT (fst k) (fst l) x)
-- R𝕝rec.abraid (Rsuc𝕃rm n) k k< =
--   𝕝braid _ _

-- suc𝕃rm : ∀ {b} n → 𝕃rm {b} n → 𝕃rm {b} (suc n)
-- suc𝕃rm {b} n = R𝕝rec.f {n = n} (Rsuc𝕃rm n) {squashA = w b}
--  where
--   w : ∀ b → if b then isGroupoid (𝕃rm {b} (suc n)) else Unit*
--   w false = tt*
--   w true = 𝕝squash _

-- Rsuc𝕃rm' : ∀ n {b} → R𝕝rec {n = n} (𝕃rm {b} (suc n))
-- R𝕝rec.abase (Rsuc𝕃rm' n) = 𝕝base
-- R𝕝rec.aloop (Rsuc𝕃rm' n) k = 𝕝loop ((fst k) , (<-weaken {n = n} (snd k)))
-- R𝕝rec.alooop (Rsuc𝕃rm' n) k l =
--   𝕝looop _ _
-- R𝕝rec.acomp (Rsuc𝕃rm' n) k l =
--   𝕝comp _ _
-- R𝕝rec.ainvol (Rsuc𝕃rm' n) k =
--   𝕝invol _
-- R𝕝rec.acomm (Rsuc𝕃rm' n) k l =
--   𝕝comm _ _
-- R𝕝rec.abraid (Rsuc𝕃rm' n) k k< =
--   𝕝braid _ _

-- suc𝕃rm' : ∀ {b} n → 𝕃rm {b} n → 𝕃rm {b} (suc n)
-- suc𝕃rm' {b} n = R𝕝rec.f {n = n} (Rsuc𝕃rm' n) {squashA = w b}
--  where
--   w : ∀ b → if b then isGroupoid (𝕃rm {b} (suc n)) else Unit*
--   w false = tt*
--   w true = 𝕝squash _


-- -- R𝕃rm+ : ∀ n m {b} → R𝕝rec {n = n} (𝕃rm {b} (n + m))
-- -- R𝕃rm+ = {!!}

-- -- 𝕃rm+ : ∀ {b} n m → 𝕃rm {b} n → 𝕃rm {b} (n + m)
-- -- 𝕃rm+ = {!!}

-- -- record R𝕝elimCons {n} {trunc} (A : 𝕃rm {trunc} (suc n) → Type ℓ) : Type ℓ where
-- --  no-eta-equality
-- --  field
-- --    isGroupoidA : Bool→Type trunc → ∀ x → isGroupoid (A x)
-- --    abase : A 𝕝base
-- --    acons : ∀ n → {!A !}
-- --    -- aloop : (k : Σ ℕ  λ k → (suc k < n)) →
-- --    --   PathP (λ i → A (𝕝loop k i)) abase abase
-- --    -- alooop : (k l : Σ ℕ  λ k → (suc k < n)) →
-- --    --   PathP (λ i → A (𝕝looop k l i)) abase abase
-- --    -- acomp : ∀ k l →
-- --    --   SquareP (λ j i → A (𝕝comp k l j i))
-- --    --     (aloop k)
-- --    --     (aloop l)
-- --    --     (alooop k l)
-- --    --     refl
-- --    -- ainvol : ∀ k →
-- --    --   SquareP (λ i j → A (𝕝invol k i j))
-- --    --     (aloop k)
-- --    --     (symP (aloop k))
-- --    --     refl refl
-- --    -- acomm : (k l : Σ ℕ  λ k → (suc k < n)) → ∀ x →     
-- --    --     SquareP (λ i j → A (𝕝comm k l x i j))
-- --    --       refl
-- --    --       refl
-- --    --     (alooop k l)
-- --    --     (alooop l k)
-- --    -- abraid : ∀ k k<  →        
-- --    --       SquareP (λ i j → A (𝕝braid k k< i j))
-- --    --       (aloop (suc k , k<))
-- --    --       (aloop (k , <-weaken {n = n} k<))
-- --    --       (alooop (k , <-weaken {n = n} k<) (suc k , k<))
-- --    --       (alooop (k , <-weaken {n = n} k<) (suc k , k<))



-- 𝕗0 : ∀ n (𝕝 : 𝕃rm n) → 𝔽in (suc n) (suc𝕃rm n 𝕝)
-- 𝕗0 n = R𝕝elimSet'.f (w n)
--  where
--  open R𝕝elimSet'
--  w : ∀ n → R𝕝elimSet' (𝔽in (suc n) ∘ suc𝕃rm n)
--  isSetA (w n) 𝕝 = snd (h𝔽in (suc n) (suc𝕃rm n 𝕝)) 
--  abase (w n) = Fin×0
--  aloop (w n) (k , k<) = 
--   ΣPathPProp (snd ∘ (Fin×Snd (1 + n)))
--     λ i → true , glue-repeat-false n k i

-- 𝕗suc : ∀ n (𝕝 : 𝕃rm n) → 𝔽in n 𝕝 → 𝔽in (suc n) (suc𝕃rm n 𝕝)
-- 𝕗suc n = R𝕝elimSet'.f (w n)
--  where
--  open R𝕝elimSet'
--  w : ∀ n → R𝕝elimSet' (λ 𝕝 → 𝔽in n 𝕝 → 𝔽in (suc n) (suc𝕃rm n 𝕝))
--  isSetA (w n) 𝕝 = isSet→ (snd (h𝔽in (suc n) (suc𝕃rm n 𝕝)))
--  abase (w n) = sucFin×
--  aloop (w n) k i (x , y) = (false , x) , y


-- 𝕗glue01 : ∀ n →
--        PathP (λ i → (Fin× (suc (suc n))) →
--       𝔽in (suc (suc n)) (𝕝loop (zero , _) i))
--         (idfun _)
--         (F×adjT {n = 2 + n} zero )
-- 𝕗glue01 n i = fst (glue-F×adjT≃ (suc (suc n)) zero i)

-- 𝕗glue210 : ∀ n →
--        PathP (λ i → (Fin× (suc (suc (suc n)))) →
--       𝔽in (suc (suc (suc n))) (𝕝looop (suc zero , _) (zero , _) i))
--         (F×adjT {n = 3 + n} (suc zero))
--         (F×adjT {n = 3 + n} zero)
-- 𝕗glue210 n =
--    funExt λ (xs , ys) →
--     ΣPathPProp (snd ∘ Fin×Snd (3 + n))
--      (funExt⁻ (glueBiAdjT×< n) xs)

-- 𝕗glue210sym : ∀ n →
--        PathP (λ i → (Fin× (suc (suc (suc n)))) →
--       𝔽in (suc (suc (suc n))) (𝕝looop (zero , _) (suc zero , _)  i))
        
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
--          𝔽in (suc (suc n)) (𝕝loop (suc (suc (fst k)) , snd k) i)
--            →
--       𝔽in (suc (suc n)) (𝕝looop (suc (suc (fst k)) , snd k) (zero , _) i))
--         (idfun _)
--         (F×adjT {n = 2 + n} zero)
-- fst (𝕗glueBi< n k i (xs , ys)) = glueBiAdjT×<SS n k i xs
-- snd (𝕗glueBi< n k i (xs , ys)) =
--   isProp→PathP
--     (λ i → isPropΠ λ ((xs , ys) : 𝔽in (suc (suc n)) (𝕝loop (suc (suc (fst k)) , snd k) i)) → snd
--       (𝔽inSnd (suc (suc n))
--        (𝕝looop (suc (suc (fst k)) , snd k) (zero , tt) i)
--        (glueBiAdjT×<SS n k i xs)))
--      snd (snd ∘ F×adjT {n = 2 + n} zero) i (xs , ys)

-- 𝕗glueBi<sym : ∀ n k →
--        PathP (λ i → 
--          𝔽in (suc (suc n)) (𝕝loop (suc (suc (fst k)) , snd k) (~ i))
--            →
--       𝔽in (suc (suc n)) (𝕝looop  (zero , _) (suc (suc (fst k)) , snd k) i))

--         (F×adjT {n = 2 + n} zero)
--          (idfun _)
-- fst (𝕗glueBi<sym n k i (xs , ys)) = glueBiAdjT×<SS n k (~ i) xs
-- snd (𝕗glueBi<sym n k i (xs , ys)) = 
--   isProp→PathP
--     (λ i → isPropΠ λ ((xs , ys) : 𝔽in (suc (suc n)) (𝕝loop (suc (suc (fst k)) , snd k) (~ i))) → snd
--       (𝔽inSnd (suc (suc n))
--        (𝕝looop (zero , tt) (suc (suc (fst k)) , snd k) i)
--        (glueBiAdjT×<SS n k (~ i) xs)))
--       (snd ∘ F×adjT {n = 2 + n} zero) snd i (xs , ys)


-- 𝕗glue01-involSS : ∀ n →
--    SquareP (λ i j → Fin× (n)
--      → 𝔽in (suc (suc n)) (𝕝invol (zero , _) i j))
--      (λ i → 𝕗glue01 n i ∘' sucFin× ∘' sucFin×)
--      (λ i → 𝕗glue01 n (~ i) ∘' sucFin× ∘' sucFin×)
--      (λ _ → sucFin× ∘' sucFin×)
--      λ _ → sucFin× ∘' sucFin×
-- 𝕗glue01-involSS n =
--   isSet→SquareP'
--    (isSet→ (isSetFin× (2 + n)))
--    _ _ _ _

-- 𝕗glue01-invol01 : ∀ n →
--    SquareP (λ i j → 𝔽in (suc (suc n)) (𝕝invol (zero , _) i j))
--      (λ j → 𝕗glue01 n j Fin×0)
--      (λ j → (𝕗glue01 n (~ j) (sucFin× Fin×0)))
--      refl
--      refl
-- 𝕗glue01-invol01 n = isSet→SquareP' (isSetFin× (2 + n)) _ _ _ _


-- 𝕗glue01-invol10 : ∀ n →
--    SquareP (λ i j → 𝔽in (suc (suc n)) (𝕝invol (zero , _) i j))
--      (λ j → 𝕗glue01 n j (sucFin× Fin×0))
--      (λ j → (𝕗glue01 n (~ j) (Fin×0)))
--      refl
--      refl
-- 𝕗glue01-invol10 n = isSet→SquareP' (isSetFin× (2 + n)) _ _ _ _

-- 𝕗glue01invol : ∀ n → SquareP
--     (λ i j → (𝔽in (suc (suc n)) (𝕝invol (zero , _) i j)
--        × 𝔽in (suc (suc n)) (𝕝invol (zero , _) i j))
--        × (Fin× n → 𝔽in (suc (suc n)) (𝕝invol (zero , _) i j)))
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
--      ((𝔽in (suc (suc (suc n))) ((𝕝comp (1 , _) (zero , _) i j))) ×^ 3)
--       × (Fin× (n) →
--     𝔽in (suc (suc (suc n))) ((𝕝comp (1 , _) (zero , _) i j))))
--    (λ j → (𝕗0 (suc (suc n)) (𝕝loop (zero , _) j)
--         , 𝕗suc (suc (suc n)) (𝕝loop (zero , _) j) (𝕗glue01 n j (sucFin× Fin×0))
--         , 𝕗suc (suc (suc n)) (𝕝loop (zero , _) j) (𝕗glue01 n j (Fin×0)) , _) ,
--      𝕗suc (suc (suc n)) (𝕝loop (zero , _) j)
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
--      ((𝔽in (suc (suc (suc n))) ((𝕝comp (zero , _) (1 , _) i j))) ×^ 3)
--       × (Fin× (n) →
--     𝔽in (suc (suc (suc n))) ((𝕝comp  (zero , _) (1 , _) i j))))
   
--    (λ j → (𝕗glue01 (suc n) j (sucFin× Fin×0) ,
--            𝕗glue01 (suc n) j (Fin×0) ,
--            𝕗glue01 (suc n) j (sucFin× (sucFin× Fin×0)) , _) ,
--      𝕗glue01 (suc n) (j) ∘' sucFin× ∘' sucFin× ∘'  sucFin×)
--    (λ j → (𝕗0 (suc (suc n)) (𝕝loop (zero , _) j)
--         , 𝕗suc (suc (suc n)) (𝕝loop (zero , _) j) (𝕗glue01 n j (sucFin× Fin×0))
--         , 𝕗suc (suc (suc n)) (𝕝loop (zero , _) j) (𝕗glue01 n j (Fin×0)) , _) ,
      
--      𝕗suc (suc (suc n)) (𝕝loop (zero , _) j)
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




-- -- (a : 𝔽in (suc n) (𝕝invol (l , l<) j (~ i))) →
-- --       𝔽in (suc (suc (suc n)))
-- --       (𝕝comm (zero , k<) (suc (suc l) , l<) x i j)

-- 𝕗glue01commS : ∀ n l l<
--  → SquareP (λ i j →
--     let Z = 𝔽in (suc (suc (n)))
--                (𝕝comm (zero , tt) (suc (suc l) , l<) _ i j)
--     in (Z × Z) ×
--      (𝔽in (n) (𝕝invol (l , l<) j (~ i)) → Z))
--       refl
--       refl
--       (λ i → (𝕗glueBi<sym (n) (l , l<) i
--            (𝕗suc (suc (n)) (𝕝loop (suc l , l<) (~ i))
--               (𝕗0 (n) (𝕝loop (l , l<) (~ i))))
--         , 𝕗glueBi<sym (n) (l , l<) i
--            (𝕗0 (1 + n) (𝕝loop (suc l , l<) (~ i))))
--         ,
--          𝕗glueBi<sym (n) (l , l<) i
--          ∘' 𝕗suc (suc (n)) (𝕝loop (suc l , l<) (~ i))
--          ∘' 𝕗suc (n) (𝕝loop (l , l<) (~ i)))
--       λ i → (
--         (𝕗glueBi< (n) (l , l<) i (𝕗0 (1 + n) (𝕝loop (suc l , l<) i)))
--          ,
--          𝕗glueBi< (n) (l , l<) i
--            (𝕗suc (suc (n)) (𝕝loop (suc l , l<) (i))
--               (𝕗0 (n) (𝕝loop (l , l<) (i))))) , (𝕗glueBi< (n) (l , l<) i ∘'
--          𝕗suc (suc (n)) (𝕝loop (suc l , l<) i)
--          ∘' 𝕗suc (n) (𝕝loop (l , l<) i))
-- 𝕗glue01commS n l l< =
--     isSet→SquareP'
--   (isSet× (isSet× (isSetFin× (2 + n)) (isSetFin× (2 + n)) )
--           (isSet→ (isSetFin× (2 + n)))) _ _ _ _

-- 𝕗glueBraid : ∀ n → SquareP
--   (λ i j →
--      let Z = 𝔽in (suc (suc (suc n))) (𝕝braid zero tt i j)
--      in (Z × Z × Z) × (Fin× (n) → Z))
--     (λ j → (𝕗suc (suc (suc n)) (𝕝loop (zero , _) j) (𝕗glue01 n j Fin×0)
--          , (𝕗suc (suc (suc n)) (𝕝loop (zero , _) j) (𝕗glue01 n j (sucFin× Fin×0))
--           , 𝕗0 (2 + n) (𝕝loop (zero , _) j) ))
--       , 𝕗suc (suc (suc n)) (𝕝loop (zero , _) j) ∘' 𝕗glue01 n j ∘' sucFin× ∘' sucFin× )
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

--  -- look𝕍 : ∀ n → ∀ 𝕝 → (𝕍 Bool n 𝕝 → A) → 𝕍 A n 𝕝

--  -- open Tab×≃ {A = A}


--  tab×≃ : ∀ n → (Fin× n → A) ≃ (A ×^ n)
--  tab×≃ zero = isoToEquiv Tab×.IsoFin×0→AUnit*
--  tab×≃ (suc n) =
--    preCompEquiv (Maybe∘Fin×≃Fin×∘suc n) ∙ₑ
--        ≃MaybeFunProd ∙ₑ ≃-× (idEquiv _) (tab×≃ n)

--  tab× : ∀ n → (Fin× n → A) → (A ×^ n)
--  tab× = fst ∘ tab×≃


--  cons𝕍 : ∀ n → ∀ 𝕝 → A → 𝕍 A n 𝕝
--      → 𝕍 A (suc n) (suc𝕃rm n 𝕝)
--  cons𝕍 n 𝕝base = _,_
--  cons𝕍 n (𝕝loop x i) = _,_
--  cons𝕍 n (𝕝looop k l i) = _,_
--  cons𝕍 n (𝕝comp k l i i₁) = _,_
--  cons𝕍 n (𝕝invol k i i₁) = _,_
--  cons𝕍 n (𝕝comm (k , k<) (suc l , l<) x i i₁) = _,_
--  cons𝕍 n (𝕝braid k k< i i₁) = _,_
 
--  tab𝕍 : ∀ n → ∀ 𝕝 → (𝔽in n (toTrunc𝕃 𝕝) → A) → 𝕍 A n 𝕝
--  tab𝕍 n = R𝕝elim.f (w n) 
--   where
--   open R𝕝elim

--   w : ∀ n → R𝕝elim {n = n} λ 𝕝 → (𝔽in n (toTrunc𝕃 𝕝) → A) → 𝕍 A n 𝕝
--   isGroupoidA (w n) ()
--   abase (w n) = tab× n
  
--   aloop (w (suc n)) (suc k , k<) i f =
--     f (𝕗0 n (𝕝loop (k , k<) i))
--       , aloop (w n) (k , k<) i (f ∘ 𝕗suc n (𝕝loop (k , k<) i))
--   aloop (w (suc (suc n))) (zero , tt) i f =
--     glueAdjT× (2 + n) zero i
--      (tab× (2 + n) (f ∘ 𝕗glue01 n i))

--   alooop (w (suc n)) (suc k , k<) (suc l , l<) i f =
--     f (𝕗0 n (𝕝looop (k , k<) (l , l<) i))
--     , alooop (w n) (k , k<) (l , l<) i
--        (f ∘ 𝕗suc n (𝕝looop (k , k<) (l , l<) i))
--   alooop (w (suc (suc n))) (zero , tt) (zero , tt) = 
--     congP {B = λ i _ → _ →
--              𝕍 A (suc (suc n)) (𝕝looop (zero , tt) (zero , tt) i)}
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
--     f (𝕗0 n (𝕝comp (k , k<) (l , l<) i j))
--     , acomp (w n) (k , k<) (l , l<) i j
--        (f ∘ 𝕗suc n (𝕝comp (k , k<) (l , l<) i j))
--   acomp (w (suc (suc n))) (zero , tt) (zero , tt) i j f =
--    aloop (w (suc (suc n))) (zero , tt) j (f ∘'     
--      isSet→SquareP' {A = λ i j →
--        𝔽in (suc (suc n)) (𝕝loop (zero , tt) j) →
--       𝔽in (suc (suc n)) (𝕝comp (zero , tt) (zero , tt) i j)}
--    (isSet→ (isSetFin× (2 + n)))
--     (λ _ x → x) (λ _ x → x)
--     (funExt λ x → ΣPathPProp (snd ∘ Fin×Snd (suc (suc n))) refl)
--       refl i j)
  
  
--   acomp (w (suc (suc n))) (zero , tt) (suc (suc l) , l<) i j f =
--     glue-biAdjT×^≡-comp<SS {n = n} l l< tt (~ i) j
--        (f (isSet→SquareP'
--            {A =
--              (λ i j → 𝔽in (suc (suc n)) (𝕝comp (zero , tt) (suc (suc l) , l<) i j))}
--            (isSetFin× (2 + n))
--            (λ j → 𝕗glue01 n j (sucFin× Fin×0))
--            (λ j → 𝕗0 (suc n) (𝕝loop ((suc l) , l<) j))
--            (λ i → 𝕗glueBi<sym n (l , l<) i (𝕗0 (suc n) (𝕝loop ((suc l) , l<) (~ i))))
--            (λ _ → Fin×0) i j)
--          , f (isSet→SquareP'
--            {A =
--              (λ i j → 𝔽in (suc (suc n)) (𝕝comp (zero , tt) (suc (suc l) , l<) i j))}
--            (isSetFin× (2 + n))

--            (λ j → 𝕗glue01 n j (Fin×0))
--            (λ j → 𝕗suc (suc n) (𝕝loop (suc l , l<) (j))
--                   (𝕗0 (n) (𝕝loop ((l) , l<) (j))))
--            (λ i → 𝕗glueBi<sym n (l , l<) i
--                      (𝕗suc (suc n) (𝕝loop (suc l , l<) (~ i))
--                         (𝕗0 n (𝕝loop (l , l<) (~ i)))))
--            (λ _ → sucFin× Fin×0) i j)
--          , aloop (w n) (l , l<) ((~ i) ∨ j)
--         (f ∘'
--           isSet→SquareP'
--             {A = λ i j →
--               𝔽in n (𝕝loop (l , l<) ((~ i) ∨ j)) →
--       𝔽in (suc (suc n)) (𝕝comp (zero , tt) (suc (suc l) , l<) i j)}
--             (isSet→ (isSetFin× (2 + n)))
--             (λ j → 𝕗glue01 n j ∘' sucFin× ∘' sucFin×)
--             (λ j → 𝕗suc (suc n) (𝕝loop (suc l , l<) j)
--                 ∘' 𝕗suc n (𝕝loop (l , l<) j))
--             (λ i → 𝕗glueBi<sym n (l , l<) (i) ∘'
--                 𝕗suc (suc n) (𝕝loop (suc l , l<) (~ i))
--                 ∘' 𝕗suc n (𝕝loop (l , l<) (~ i)))
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
--              (λ i j → 𝔽in (suc (suc n)) (𝕝comp (suc (suc k) , k<) (zero , tt) i j))}
--            (isSetFin× (2 + n))
--            (λ j → 𝕗0 (suc n) (𝕝loop ((suc k) , k<) j))
--            (λ j → 𝕗glue01 n j (sucFin× Fin×0))
--            (λ i → 𝕗glueBi< n (k , k<) i (𝕗0 (suc n) (𝕝loop ((suc k) , k<) i)))
--            (λ _ → Fin×0) i j) 
--      , f (isSet→SquareP'
--            {A =
--              (λ i j → 𝔽in (suc (suc n)) (𝕝comp (suc (suc k) , k<) (zero , tt) i j))}
--            (isSetFin× (2 + n))
--            (λ j → 𝕗suc (suc n) (𝕝loop (suc k , k<) j)
--                   (𝕗0 (n) (𝕝loop ((k) , k<) j)))
--            (λ j → 𝕗glue01 n j (Fin×0))
--            (λ i → 𝕗glueBi< n (k , k<) i
--                      (𝕗suc (suc n) (𝕝loop (suc k , k<) i)
--                         (𝕗0 n (𝕝loop (k , k<) i))))
--            (λ _ → sucFin× Fin×0) i j) 
--      , aloop (w n) (k , k<) (i ∨ j)
--         (f ∘'
--           isSet→SquareP'
--             {A = λ i j →
--               𝔽in n (𝕝loop (k , k<) (i ∨ j)) →
--       𝔽in (suc (suc n)) (𝕝comp (suc (suc k) , k<) (zero , tt) i j)}
--             (isSet→ (isSetFin× (2 + n)))
--             (λ j → 𝕗suc (suc n) (𝕝loop (suc k , k<) j)
--                 ∘' 𝕗suc n (𝕝loop (k , k<) j))
--             (λ j → 𝕗glue01 n j ∘' sucFin× ∘' sucFin×)
--             (λ i → 𝕗glueBi< n (k , k<) i ∘'
--                 𝕗suc (suc n) (𝕝loop (suc k , k<) i)
--                 ∘' 𝕗suc n (𝕝loop (k , k<) i))
--             (λ _ → sucFin× ∘' sucFin×) i j))

--   acomp (w (suc (suc (suc n)))) (suc zero , tt) (zero , tt) i j f =
--     let ((f0 , f1 , f2 , _) , fSSS) = 𝕗glue01comp< n i j
--     in Σ-swap-012-≡-comp-ua-glue* {A = A} {A ×^ n} i j
--           (f f0 , f f1 , f f2 , tab× n (f ∘' fSSS))
  
  
--   ainvol (w (suc n)) (suc k , k<) i j f =
--     f (𝕗0 n (𝕝invol (k , k<) i j))
--     , ainvol (w n) (k , k<) i j
--         (f ∘ 𝕗suc n (𝕝invol (k , k<) i j))
--   ainvol (w (suc (suc n))) (zero , tt) i j f =    
--    let ((f0 , f1) , fSS) = 𝕗glue01invol n i j
--    in Σ-swap-01-≡-invol-ua-glue {A = A} {B = A ×^ n} i j
--          (f f0 , f f1 , tab× n (f ∘' fSS))

--   acomm (w (suc n)) (suc k , k<) (suc (suc (suc l)) , l<) x i j f =    
--     f (𝕗0 n (𝕝comm (k , k<) (suc (suc l) , l<) x i j))
--     , acomm (w n) (k , k<) (suc (suc l) , l<) x i j
--        (f ∘ 𝕗suc n (𝕝comm (k , k<) (suc (suc l) , l<) x i j)) 
--   acomm (w (suc (suc n))) (zero , k<) (suc (suc l) , l<) x i j f =
--    let ((f0 , f1) , fSS) = 𝕗glue01commS n l l< i j
--    in glue-biAdjT×^≡-comm {n = n} (l , l<)
--       i j
--       (f f0 , f f1 , ainvol (w n) (l , l<) j (~ i) (f ∘ fSS))
   
--   abraid (w (suc n)) (suc k) k< i j f =
--       f (𝕗0 n (𝕝braid k k< i j))
--     , abraid (w n) k k< i j (f ∘  𝕗suc n (𝕝braid k  k< i j))
--   abraid (w (suc (suc (suc n)))) zero tt i j f =
--    let ((f0 , f1 , f2) , fSSS) = 𝕗glueBraid n i j
--    in glue-adjT×^≡-braid {n = n} i j
--          (ua-gluePath (adjT×^≃ 0 ∙ₑ compEquiv (adjT×^≃ 1) (adjT×^≃ 0))
--            (λ j → f f2 , f f0 , f f1 , tab× n (f ∘' fSSS)) j)
           

--  isEquivTab𝕍 : ∀ n → ∀ 𝕝 → (isEquiv (tab𝕍 n 𝕝))
--  isEquivTab𝕍 n = R𝕝elimProp.f w
--   where
--   w : R𝕝elimProp (isEquiv ∘ tab𝕍 n)
--   R𝕝elimProp.isPropA w _ = isPropIsEquiv _
--   R𝕝elimProp.abase w = snd (tab×≃ n)

--  s𝕍₃' : ∀ n → (𝕝 : 𝕃rm {false} n) →
--     Σ (Type ℓ) λ T → ((𝔽in n (toTrunc𝕃 𝕝) → A) ≃ T)
--  s𝕍₃' n 𝕝 = _ , (_ , isEquivTab𝕍 n 𝕝)


--  s𝕍₃ : ∀ n → (𝕝 : 𝕃rm {true} n) → Σ (Type ℓ) λ T → ((𝔽in n 𝕝 → A) ≃ T)
--  s𝕍₃ =  trunc𝕃₂ _ (λ _ _ → isOfHLevelPlus 3 (isContrΣ≃ _) )  s𝕍₃'


--  𝕍₃ : ∀ n → 𝕃rm {true} n → Type ℓ
--  𝕍₃ n = fst ∘ s𝕍₃ n

--  module _ (isGrpA : isGroupoid A) where

--   isGroupoid𝕍₃ : ∀ n → ∀ 𝕝 → isGroupoid (𝕍₃ n 𝕝)
--   isGroupoid𝕍₃ n = R𝕝elimProp.f w
--    where
--    w : R𝕝elimProp _
--    R𝕝elimProp.isPropA w _ = isPropIsOfHLevel 3
--    R𝕝elimProp.abase w = isOfHLevel×^ n 3 isGrpA 


--   cons𝕍₃ : ∀ n → ∀ 𝕝 → A → 𝕍₃ n 𝕝
--       → 𝕍₃ (suc n) (suc𝕃rm n 𝕝)
--   cons𝕍₃ n = R𝕝elim.f w
--    where
--    w : R𝕝elim (λ z → A → 𝕍₃ n z → 𝕍₃ (suc n) (suc𝕃rm n z))
--    R𝕝elim.isGroupoidA w _ 𝕝 =
--      isGroupoidΠ2 λ _ _ →  isGroupoid𝕍₃ (suc n) (suc𝕃rm n 𝕝)
--    R𝕝elim.abase w = _,_
--    R𝕝elim.aloop w _ _ = _,_
--    R𝕝elim.alooop w _ _ _ = _,_
--    R𝕝elim.acomp w _ _ _ _ = _,_
--    R𝕝elim.ainvol w _ _ _ = _,_
--    R𝕝elim.acomm w _ (suc l , l<) _ _ _ = _,_
--    R𝕝elim.abraid w _ _ _ _ = _,_
