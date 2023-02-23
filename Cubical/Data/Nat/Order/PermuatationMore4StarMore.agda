{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.PermuatationMore4StarMore where

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

open import Cubical.HITs.ListedFiniteSet.Base3
import Cubical.HITs.ListedFiniteSet.Base22Star2 as S
import Cubical.HITs.ListedFiniteSet.Base22Star3 as S'

open import Cubical.Relation.Binary

import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Data.Nat.Order.PermutationMore4Star

private
  variable
    ℓ : Level
    A : Type ℓ

module Iso-𝔽in→-Fin→/↔ {A : Type ℓ} (isGroupoidA : isGroupoid A) where

 isGroupoidΣ𝔽in→ : ∀ n → isGroupoid (𝔽in→ A n)
 isGroupoidΣ𝔽in→ _ = isGroupoidΣ 𝕡squash
     λ _ → isGroupoidΠ λ _ → isGroupoidA


 -- zz-aloop' : ∀ n k → 
 --    SquareP (λ i₁ j → 𝔽in {n = n} (𝕡loop k i₁) →
 --                      𝔽in {n = n} (𝕡loop k j))
 --    {idfun (Fin n)} {{!!}}
 --    (ua-gluePathExt (adjT'≃ {n = n} k))
 --    {{!!}} {idfun _}
 --    (gluePathAdjT' n k)
 --    {!!}
 --    {!!}
 -- zz-aloop' n k = {!!}

 -- to-loop' : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
 --      PathP (λ i → (𝔽in {n} (𝕡loop k i) → A) → Fin→/↔ A n) [_]// [_]//
 -- to-loop' n k i p = eq// 
 --                {a = p ∘ {!zz-aloop' n k i0 i!}}
 --                {b = p ∘ {!!} }
 --                ((𝕡loop k) , λ j x → p (zz-aloop' n k j i x)) i


 zz-aloop : ∀ n k → 
    SquareP (λ i₁ j → 𝔽in {n = n} (𝕡loop k i₁) →
                      𝔽in {n = n} (𝕡loop k j))
    (ua-gluePathExt (adjT'≃ {n = n} k))
    (λ i x → glue
        (λ { (i = i0) → adjT n k x
           ; (i = i1) → x
           })
        (isInvolution-adjT n k x i))
    (funExt (λ kk → sym (isInvolution-adjT n k kk)) ◁
      (λ i → fst (adjT'≃ {n = n} k)
         ∘' ua-ungluePathExt (adjT'≃ {n = n} k) i))
    (ua-ungluePathExt (adjT'≃ {n = n} k))
 zz-aloop n k = isSet→SquareP (λ i₁ j → isSet→ (snd (𝔽inH n (𝕡loop k j))))
           _ _ _ _

 -- zz-aloop-invol : ∀ n k → PathP (λ i →
 --                        SquareP (λ i₁ j →
 --                      𝔽in {n = n} (𝕡invol k i i₁) →
 --                      𝔽in {n = n} (𝕡invol k i  j))
 --                          {idfun _} {adjT n k}
 --                          {!!}
 --                          {_} {idfun _}
 --                          {!!}
 --                          (λ i₁ → {!!})
 --                          {!!})
 --                   (zz-aloop n k)
 --                    (congP (λ _ → symP-fromGoal)
 --                     (symP-fromGoal (zz-aloop n k)))
 -- zz-aloop-invol n k = {!!}
 zz-aloop-invol : ∀ n k →
    SquareP (λ j' j → PathP (λ i → 𝔽in {n = n} (𝕡invol k i j') →
                      𝔽in {n = n} (𝕡invol k i  j))
          (zz-aloop n k j' j) (zz-aloop n k (~ j') (~ j)))
      {refl} {refl}
      (isSet→SquareP (λ i₁ j → isSet→ (snd (𝔽inH n (𝕡invol k j i₁))))
           _ _ _ _)
      {refl} {refl}
      (isSet→SquareP (λ i₁ j → isSet→ (snd (𝔽inH n (𝕡invol k j i₁))))
           _ _ _ _)
      (isSet→SquareP (λ i₁ j → isSet→ (isSetFin {n = n}))
           _ _ _ _)
      (isSet→SquareP (λ i₁ j → isSet→ (isSetFin {n = n}))
           _ _ _ _)
                    
 zz-aloop-invol n k =
   isSet→SquareP (λ i₁ j → isOfHLevelPathP 2
     (isSet→ (snd (𝔽inH n (𝕡invol k i1  j)))) _ _)
           _ _ _ _



 to-loop : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
      PathP (λ i → (𝔽in {n} (𝕡loop k i) → A) → Fin→/↔ A n) [_]// [_]//
 to-loop n k i p = eq// 
                {a = p ∘ ua-gluePathExt (adjT'≃ {n = n} k) i}
                {b = p ∘ λ x →
                   ua-gluePath (adjT'≃ {n = n} k)
                     (isInvolution-adjT n k x) i }
                ((𝕡loop k) , λ j x → p (zz-aloop n k j i x)) i

 zz-alooop : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n))
      → SquareP (λ i₁ j → (fst (𝔽inH n (𝕡looop k l i₁)))
              → (fst (𝔽inH n (𝕡looop k l j))))
                 (λ i x → glue (λ {(i = i0) → x ;(i = i1) → _ })
                      (isInvolution-adjT n l (adjT n k x) (~ i)))
                 (λ i x → glue (λ {(i = i0) → _ ;(i = i1) → x })
                      (isInvolution-adjT n k (adjT n l x) i))
                 ((λ i x → isInvolution-adjT n k x (~ i))
                   ◁ (λ i → adjT n k ∘ unglue (i ∨ ~ i)))
                 ((λ i → adjT n l ∘ unglue (i ∨ ~ i)) ▷
                  funExt (isInvolution-adjT n l))
 zz-alooop n k l = isSet→SquareP (λ i₁ j → isSet→ (snd (𝔽inH n (𝕡looop k l j))))
             _ _ _ _
 
 to-looop : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
      PathP (λ i → (𝔽in {n} (𝕡looop k l i) → A) → Fin→/↔ A n) [_]// [_]//
 to-looop n k l =
    λ i p → eq//
                 -- {a = p ∘ λ x → glue (λ {(i = i0) → x ;(i = i1) → _ })
                 --      (isInvolution-adjT n l (adjT n k x) (~ i))}
                 -- {b = p ∘ λ x → glue (λ {(i = i0) → _ ;(i = i1) → x })
                 --      (isInvolution-adjT n k (adjT n l x) i)}
               ((𝕡looop k l) ,
    λ j x → p (zz-alooop n k l j i x)) i


 to-invol' : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
      SquareP (λ i j → (𝔽in {n = n} (𝕡invol k i j) → A) → Fin→/↔ A n)
      (to-loop n k)
      (λ j p → eq// (sym (𝕡loop k) , λ j' x → p (zz-aloop n k (~ j') (~ j) x)) j)
      refl
      refl
 to-invol' n k i j p =
    eq// (𝕡invol k i , λ j' → p ∘ zz-aloop-invol n k j' j i ) j 
  

 to-invol : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
      SquareP (λ i j → (𝔽in {n = n} (𝕡invol k i j) → A) → Fin→/↔ A n)
      (to-loop n k) (symP (to-loop n k)) refl refl
 to-invol n k  = to-invol' n k ▷
     invEq (congEquiv (invEquiv funExtDepEquiv))      
      λ i p j → sym-/↔ A n (𝕡loop k)
         (λ j' → p j ∘ (zz-aloop n k (~ j') (~ j))) i j 




 -- ss' : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) → SquareP (λ i j →
 --              PathP (λ j' → 𝔽in {n = n} (𝕡looop k l j')
 --                          → 𝔽in {n = n} (𝕡comp k l i j))
 --                 {!!}
 --                 {!!})
 --           (λ j j' → {!!})
 --           (λ j j' → {!zz-aloop n l j' j!})
 --           (λ i j' → zz-alooop n k l j' i)
 --           λ _ j' → unglueFlooopPathExt n k l j'
 -- ss' = {!!}

 p* : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
       SquareP (λ i j → 𝔽in {n = n} 𝕡base → 𝔽in {n = n} (𝕡comp k l i j))
          (λ j → gluePathAdjT' n k j ∘' adjT n l) --(gluePathAdjT' n k)
          (ua-gluePathExt (adjT'≃ {n = n} l)) --(gluePathAdjT' n l)
          (λ i x → glue (λ { (i = i0) → adjT n k (adjT n l x)
                         ; (i = i1) → x
                         }) (isInvolution-adjT n k (adjT n l x) i))
          λ i → adjT n l 
 p* n k l = isSet→SquareP (λ i j → isSet→ (snd (𝔽inH n (𝕡comp k l i j))))
             _ _ _ _


 ss* : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) → SquareP (λ i j' →
           PathP (λ j → 𝔽in {n = n} (𝕡looop k l j')
                       → 𝔽in {n = n} (𝕡comp k l i j))
                 (zz-alooop n k l j' i)
                 (unglueFlooopPathExt n k l j'))
          {ua-gluePathExt (adjT'≃ {n = n} k)}
          
          (isSet→SquareP (λ j' j → isSet→ (snd (𝔽inH n (𝕡comp k l i0 j))))
             _ _ _ _)
          {λ j → gluePathAdjT' n l j ∘' adjT n k} 
          (isSet→SquareP (λ j' j → isSet→ (snd (𝔽inH n (𝕡comp k l i1 j))))
             _ _ _ _)
          (isSet→SquareP (λ i j → isSet→ (snd (𝔽inH n (𝕡comp k l i j))))
             _ _ _ _)
          (p* n k l)
 ss* n k l = isSet→SquareP (λ i j' → isOfHLevelPathP 2
     (isSet→ (snd (𝔽inH n (𝕡comp k l i i1)))) _ _)
           _ _ _ _


 ss** : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) → SquareP (λ i j' →
           PathP (λ j → 𝔽in {n = n} (𝕡loop l j')
                       → 𝔽in {n = n} (𝕡comp k l i j))
                 ((isSet→SquareP
                    (λ i j' → isSet→ {A = 𝔽in {n = n} (𝕡loop l j')}
                        (snd (𝔽inH n (𝕡comp k l i i0))))
                    
                    
                (λ z → adjT n k ∘ ua-ungluePathExt (adjT'≃ {n = n} l) z)
                 (ungluePathAdjT' n l)
                ((λ i x → glue (λ { (i = i0) → adjT n k (adjT n l x)
                         ; (i = i1) → x
                         }) (isInvolution-adjT n k (adjT n l x) i)))
                         (glueFlooopPathExt n k l)) i j')
                 (ua-ungluePathExt (adjT'≃ {n = n} l) j'))
          {λ j → gluePathAdjT' n k j ∘ adjT n l} {gluePathAdjT' n k}
          (isSet→SquareP (λ j' j → isSet→ (snd (𝔽inH n (𝕡comp k l i0 j))))
            _ _ _ _)
          (λ j' j → zz-aloop n l j' j)
          (p* n k l)
          (isSet→SquareP (λ i j → isSet→ (snd (𝔽inH n (𝕡comp k l i j))))
            _ _ _ _)
 ss** n k l = isSet→SquareP (λ i j' → isOfHLevelPathP 2
     (isSet→ (snd (𝔽inH n (𝕡comp k l i i1)))) _ _)
           _ _ _ _

 zz-comp-eq-fst : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
    𝕡looop {n = n} k l ∙ 𝕡loop l ≡ 𝕡loop k
 zz-comp-eq-fst n k l i j =
    hcomp (λ z →
       λ { (i = i1) → 𝕡loop k (j ∨ ~ z)
         ; (j = i0) → 𝕡loop k (i ∧ ~ z)
         ; (j = i1) → 𝕡loop l (i ∨ z)
         }) (𝕡comp k l j i)

 zz-comp-eq-snd : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
             (f : Fin n → A)
              → SquareP (λ j i →
                   PathP (λ j' → 𝔽in (zz-comp-eq-fst n k l j j') → A)
                    (λ x → f (adjT n k x))
                    (λ x → f (isInvolution-adjT n k x (i ∨ ~ j))))
                   {!!}
                   {!!}
                   {!!}
                   {!!}
 zz-comp-eq-snd n k l = {!!}
 
 to-comp-eq : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
      Path (Path ((Fin n → A) → Fin→/↔ A n)
               ([_]// ∘' (_∘' adjT n k)) [_]//)
        (λ i f → eq// {a = f ∘' adjT n k} {f}
          (isTrans-[]↔ n (f ∘' adjT n k) (f ∘' adjT n l)
                  f
             (𝕡looop k l , λ j' → f ∘' unglueFlooopPathExt n k l j')
             (𝕡loop l , λ j' → f ∘' ua-ungluePathExt (adjT'≃ {n = n} l) j')) i)
        (λ i f → to-loop n k i (f ∘' ua-ungluePathExt (adjT'≃ {n = n} k) i))
 to-comp-eq n k l j i f =
   -- cong (funExt) (funExt
 --    λ f i j → eq//
 --       {a = f ∘' adjT n k}
 --       {b = f ∘' λ x → isInvolution-adjT n k x (i ∨ ~ j)}
 --       ((zz-comp-eq-fst n k l i) , {!!}) j 
 --    )
   eq// {a = f ∘' adjT n k}
        {b = f ∘' λ x → isInvolution-adjT n k x (i ∨ ~ j)}        
        (zz-comp-eq-fst n k l j , {!f!}) i

-- -- --  to-comp' : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- --       SquareP (λ j i → (𝔽in {n = n} (𝕡comp k l i j) → A) → Fin→/↔ A n)
-- -- --         (to-looop n k l)
-- -- --         (λ i f → to-loop n k i (f ∘' ua-ungluePathExt (adjT'≃ {n = n} k) i))
-- -- --         -- λ i f → eq// {a = f ∘' adjT n k} {f}
-- -- --         --   (isTrans-[]↔ n (f ∘' adjT n k) (f ∘' adjT n l)
-- -- --         --           f
-- -- --         --      (𝕡looop k l , λ j' → f ∘' unglueFlooopPathExt n k l j')
-- -- --         --      (𝕡loop l , λ j' → f ∘' ua-ungluePathExt (adjT'≃ {n = n} l) j')) i
-- -- --         (λ j f → [ f ∘ ua-gluePathExt (adjT'≃ {n = n} k) j ]//)
-- -- --         (to-loop n l)
-- -- --  to-comp' n k l = 
-- -- --     (λ j i f → 
-- -- --    comp//
-- -- --     (𝕡looop k l , λ j' → f ∘' ss* n k l i j' j)
-- -- --     (𝕡loop l , λ j' → f ∘' ss** n k l i j' j) j i)
-- -- --     ▷ to-comp-eq n k l


-- -- -- --  ploop∧ : ∀ n k → SquareP (λ z j → (a : 𝔽in {n = n} (𝕡loop k (j ∧ z))) →
-- -- -- --                            𝔽in {n = n} (𝕡loop k j))
-- -- -- --                   (ua-gluePathExt (adjT'≃ {n = n} k))
-- -- -- --                   (λ _ → idfun _)
-- -- -- --                   refl
-- -- -- --                   (ua-ungluePathExt (adjT'≃ {n = n} k))
-- -- -- --  ploop∧ n k =
-- -- -- --     (isSet→SquareP (λ z j → isSet→ (snd (𝔽inH n (𝕡loop k j))))
-- -- -- --             _ _ _ _)

-- -- -- --  to-comp : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- --       SquareP (λ j i → (𝔽in {n = n} (𝕡comp k l j i) → A) → Fin→/↔ A n)
-- -- -- --       (to-loop n k)
-- -- -- --       (to-loop n l) (to-looop n k l) refl
-- -- -- --  to-comp n k l i j f =   
-- -- -- --    hcomp
-- -- -- --      (λ z →
-- -- -- --       λ { (i = i0) → to-loop n k (j ∧ z) (f ∘ ploop∧ n k z j)
-- -- -- --         ; (i = i1) → to-comp' n k l j i f 
-- -- -- --         ; (j = i0) → to-comp' n k l j i f
-- -- -- --         ; (j = i1) → {!!} --to-comp' n k l (i ∨ z) j f
-- -- -- --         })
-- -- -- --      (to-comp' n k l j i f)
 

-- -- -- -- --  zz-to-comm : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) (x' : A.commT (fst k) (fst l))
-- -- -- -- --                   → SquareP (λ i j' →
-- -- -- -- --                    PathP (λ j → 𝔽in {n} (𝕡comm k l x' j' j)
-- -- -- -- --                                → 𝔽in {n} (𝕡comm k l x' i j))
-- -- -- -- --                      (zz-alooop n k l j' i)
-- -- -- -- --                      (zz-alooop n l k j' i))
-- -- -- -- --                 {refl} {sym (funExt (adjT-comm n k l x'))}
-- -- -- -- --                 (isSet→SquareP (λ i j' → (isSet→ (isSetFin {n = n})))
-- -- -- -- --                       _ _ _ _)
-- -- -- -- --                 {funExt (adjT-comm n k l x')}
-- -- -- -- --                 {refl}
-- -- -- -- --                 (isSet→SquareP (λ i j' → (isSet→ (isSetFin {n = n})))
-- -- -- -- --                       _ _ _ _)
-- -- -- -- --                 (isSet→SquareP (λ i j →
-- -- -- -- --                    isSet→ (snd (𝔽inH n (𝕡comm k l x' i j))))
-- -- -- -- --                     _ _ _ _)
-- -- -- -- --                 (isSet→SquareP (λ i j →
-- -- -- -- --                    isSet→ (snd (𝔽inH n (𝕡comm k l x' i j))))
-- -- -- -- --                     _ _ _ _)
-- -- -- -- --  zz-to-comm n k l x' = 
-- -- -- -- --   isSet→SquareP (λ i j' → isOfHLevelPathP 2
-- -- -- -- --      (isSet→ (snd (𝔽inH n (𝕡comm k l x' i i1)))) _ _)
-- -- -- -- --            _ _ _ _

-- -- -- -- --  to-comm : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n))
-- -- -- -- --    (x : A.commT (fst k) (fst l)) →
-- -- -- -- --    SquareP (λ i j → (𝔽in {n} (𝕡comm k l x i j) → A) → Fin→/↔ A n) refl
-- -- -- -- --    refl (to-looop n k l) (to-looop n l k)
-- -- -- -- --  to-comm n k l x' i j f =
-- -- -- -- --    eq// ((λ i → 𝕡comm k l x' i j) ,
-- -- -- -- --      λ j' → f ∘ zz-to-comm n k l x' i j' j) i

-- -- -- -- --  to : ∀ n → R𝕡elim {n = n} (λ z → (y : 𝔽in z → A) → Fin→/↔ A n)
-- -- -- -- --  R𝕡elim.isGroupoidA (to n) _ = isGroupoidΠ λ _ → squash//
-- -- -- -- --  R𝕡elim.abase (to n) = [_]//
-- -- -- -- --  R𝕡elim.aloop (to n) = to-loop n  


-- -- -- -- --  R𝕡elim.alooop (to n) = to-looop n

-- -- -- -- --  R𝕡elim.acomp (to n) k l =
-- -- -- -- --    {!!}
-- -- -- -- --    -- hcomp (λ z →
-- -- -- -- --    --    λ { (i = i0) → {!to-invol n k (~ z) i!}
-- -- -- -- --    --      ; (i = i1) → to-loop n l j p 
-- -- -- -- --    --      ; (j = i0) → to-looop n k l i p
-- -- -- -- --    --      ; (j = i1) → {!!}
-- -- -- -- --    --      })
-- -- -- -- --    --   (comp// {a = {!!}} {b = {!!}} {c = {!!}}
-- -- -- -- --    --       ((𝕡looop k l) ,
-- -- -- -- --    --         {!!}) {!!} j i)
-- -- -- -- --    -- -- {!comp// {a = ?} {?} {?} ? ? i  !}
-- -- -- -- --  R𝕡elim.ainvol (to n) = to-invol n
-- -- -- -- --  R𝕡elim.acomm (to n) = to-comm n
-- -- -- -- --  R𝕡elim.abraid (to n) = {!!}
 
-- -- -- -- -- --  from : ∀ n → Fin→/↔ A n → 𝔽in→ A n
-- -- -- -- -- --  from n = GQ.Rrec.f w
-- -- -- -- -- --   where
-- -- -- -- -- --   w : Rrec// (𝔽in→ A n)
-- -- -- -- -- --   Rrec//.Bgpd w = isGroupoidΣ𝔽in→ n
    
-- -- -- -- -- --   Rrec//.fb w = 𝕡base ,_
-- -- -- -- -- --   Rrec//.feq w = ΣPathP
-- -- -- -- -- --   Rrec//.fsq w (p , P) (q , Q) =
-- -- -- -- -- --     ΣSquareP ((compPath-filler _ _) ,
-- -- -- -- -- --       compPathP'-filler
-- -- -- -- -- --         {B = λ x → 𝔽in x → A} {p = p} {q = q} P Q)


-- -- -- -- -- --  ss''k :  ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- --    (a : Fin n → A) →
-- -- -- -- -- --         (λ i → to-loop n k i (↔k'P A n a k i))  ≡ eq// (↔k n k a)

-- -- -- -- -- --  ss''k n k a j i = 
-- -- -- -- -- --     eq// {a = a ∘ ungluePathAdjT' n k (~ j ∧ i)
-- -- -- -- -- --            ∘ ua-gluePathExt (adjT'≃ {n = n} k) (~ j ∧ i)}
-- -- -- -- -- --          {b = a ∘ ungluePathAdjT' n k (j ∨  i)
-- -- -- -- -- --                  ∘ λ x →
-- -- -- -- -- --                    ua-gluePath (adjT'≃ {n = n} k)
-- -- -- -- -- --                      (isInvolution-adjT n k x) (j ∨ i) }
-- -- -- -- -- --           (𝕡loop k , λ j' x → a (ccc i j j' x) ) i 
-- -- -- -- -- --    where

-- -- -- -- -- --      ccc : SquareP (λ i j → PathP
-- -- -- -- -- --                  (λ j' → 𝔽in {n = n} (𝕡loop k j') → Fin n)
-- -- -- -- -- --                  (ungluePathAdjT' n k (~ j ∧ i)
-- -- -- -- -- --                       ∘ ua-gluePathExt (adjT'≃ {n = n} k) (~ j ∧ i))
-- -- -- -- -- --                  (ungluePathAdjT' n k (j ∨  i)
-- -- -- -- -- --                  ∘ λ x →
-- -- -- -- -- --                    ua-gluePath (adjT'≃ {n = n} k)
-- -- -- -- -- --                      (isInvolution-adjT n k x) (j ∨ i) ))
-- -- -- -- -- --                   (isSet→SquareP (λ _ _ → isSet→ (isSetFin {n = n})) _ _ _ _)
-- -- -- -- -- --                   (isSet→SquareP (λ _ _ → isSet→ (isSetFin {n = n})) _ _ _ _)
-- -- -- -- -- --                   (λ i j' → ungluePathAdjT' n k i ∘ (zz-aloop n k j' i))
-- -- -- -- -- --                   λ _ → ungluePathAdjT' n k
-- -- -- -- -- --      ccc = isSet→SquareP (λ i j → isOfHLevelPathP 2 (isSet→ (isSetFin {n})) _ _)
-- -- -- -- -- --       _ _ _ _

-- -- -- -- -- --  from-to : ∀ n → section (uncurry (R𝕡elim.f (to n))) (from n)
-- -- -- -- -- --  from-to n = GQ.RelimSet.f w
-- -- -- -- -- --   where
-- -- -- -- -- --   w : RelimSet (λ z → uncurry (R𝕡elim.f (to n)) (from n z) ≡ z)
-- -- -- -- -- --   RelimSet.truncB w _ = squash// _ _
-- -- -- -- -- --   RelimSet.fb w _ = refl
-- -- -- -- -- --   RelimSet.fbEq w = 
-- -- -- -- -- --     uncurry-flip {A = Fin n → A}
-- -- -- -- -- --        {C = λ a a' p → PathP (λ i → 𝔽in (p i) → A) a a'}
-- -- -- -- -- --        {D = λ a a' p P →
-- -- -- -- -- --         let r : [ n ] a ↔ a'
-- -- -- -- -- --             r = (p , P)
-- -- -- -- -- --         in
-- -- -- -- -- --           PathP
-- -- -- -- -- --           (λ i → uncurry (R𝕡elim.f (to n)) (from n (eq// r i)) ≡ eq// r i)
-- -- -- -- -- --           (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a ]//))
-- -- -- -- -- --           (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a' ]//))} 
-- -- -- -- -- --     (𝕡baseΩ-elimProp n _ (λ _ → isPropΠ3 λ _ _ _ →
-- -- -- -- -- --           isOfHLevelPathP' 1 (squash// _ _) _ _)
-- -- -- -- -- --       ss' ss'')

-- -- -- -- -- --    where
-- -- -- -- -- --     ss' : (a b : Fin n → A) → (y : a ≡ b) →
-- -- -- -- -- --           Square {A = (Fin n → A) // isTrans-[]↔ n}
-- -- -- -- -- --             (λ j → [ a ]//)
-- -- -- -- -- --             (λ j → [ b ]//)
-- -- -- -- -- --             (λ i → [ y i ]//)
-- -- -- -- -- --             (λ i → eq// (refl , y) i)          

-- -- -- -- -- --     ss' a b y i j =
-- -- -- -- -- --               hcomp
-- -- -- -- -- --         (λ l →
-- -- -- -- -- --            λ { (i = i0) → [ a ]//
-- -- -- -- -- --              ; (i = i1) → eq// {a = y (l ∨ j)} {b = b}
-- -- -- -- -- --                         (refl , (λ j' → y (l ∨ j ∨ j'))) (~ l)
-- -- -- -- -- --              ; (j = i0) → eq// {a = y (i ∧ l)} {b = b}
-- -- -- -- -- --                                (refl , (λ j' → (y ((i ∧ l) ∨  j')))) (i ∧ ~ l) 
-- -- -- -- -- --              ; (j = i1) → comp// {a = a} {b = b} {c = b}
-- -- -- -- -- --                               (refl , y) (refl , refl) (~ l) i
-- -- -- -- -- --              }) (eq// {a = a} {b = b}
-- -- -- -- -- --                     (compPathRefl j ,  compPathP'-filler 
-- -- -- -- -- --                       {B = λ x → 𝔽in {n = n} x → A}
-- -- -- -- -- --                        {p = λ _ → 𝕡base {n = n}} {q = refl} y refl
-- -- -- -- -- --                     j) i)
-- -- -- -- -- --     ss'' : (p : Path (ℙrm n) 𝕡base 𝕡base)
-- -- -- -- -- --       (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- --       ((a a' : Fin n → A) (c : PathP (λ i → 𝔽in (p i) → A) a a') →
-- -- -- -- -- --        PathP
-- -- -- -- -- --        (λ i →
-- -- -- -- -- --           uncurry (R𝕡elim.f (to n)) (from n (eq// (p , c) i)) ≡
-- -- -- -- -- --           eq// (p , c) i)
-- -- -- -- -- --        (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a ]//))
-- -- -- -- -- --        (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a' ]//))) →
-- -- -- -- -- --       (a a' : Fin n → A)
-- -- -- -- -- --       (c : PathP (λ i → 𝔽in ((𝕡loop k ∙ p) i) → A) a a') →
-- -- -- -- -- --       PathP
-- -- -- -- -- --       (λ i →
-- -- -- -- -- --          uncurry (R𝕡elim.f (to n)) (from n (eq// (𝕡loop k ∙ p , c) i)) ≡
-- -- -- -- -- --          eq// (𝕡loop k ∙ p , c) i)
-- -- -- -- -- --       (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a ]//))
-- -- -- -- -- --       (λ _ → uncurry (R𝕡elim.f (to n)) (from n [ a' ]//))


-- -- -- -- -- --     ss'' p k y a b P i j = 
-- -- -- -- -- --        hcomp (λ z →
-- -- -- -- -- --         λ { (i = i0) → [ a ]//
-- -- -- -- -- --           ; (i = i1) → (y _ _ (pop↔ A n a b p k P)) z j
-- -- -- -- -- --           ; (j = i0) →
-- -- -- -- -- --             (_▷_ {A = λ z → [ a ]// ≡
-- -- -- -- -- --               uncurry (R𝕡elim.f (to n)) (from n
-- -- -- -- -- --                  (eq// (p , (pop↔ A n a b p k P)) z))}
-- -- -- -- -- --                (λ z i →
-- -- -- -- -- --                  uncurry (R𝕡elim.f (to n)) (from n
-- -- -- -- -- --                   (comp// (↔k n k a)
-- -- -- -- -- --                     (p , pop↔ A n a b p k P) z i)) )
-- -- -- -- -- --                (cong
-- -- -- -- -- --                 (cong′ ((uncurry (R𝕡elim.f (to n))) ∘ (from n)) ∘ eq//)
-- -- -- -- -- --                 (sym (pop↔trans n a b p k P))) ) z i
-- -- -- -- -- --           ; (j = i1) →
-- -- -- -- -- --             (comp// (↔k n k a)
-- -- -- -- -- --                     (p , pop↔ A n a b p k P)
-- -- -- -- -- --               ▷ cong eq// (sym (pop↔trans n a b p k P)) ) z i
-- -- -- -- -- --           }) (ss''k n k a j i)

-- -- -- -- -- --  to-from : ∀ n → retract (uncurry (R𝕡elim.f (to n))) (from n)
-- -- -- -- -- --  to-from n = uncurry (R𝕡elimSet.f w)
-- -- -- -- -- --   where
-- -- -- -- -- --   w : R𝕡elimSet
-- -- -- -- -- --         (λ z →
-- -- -- -- -- --            (y : 𝔽in z → A) →
-- -- -- -- -- --            from n (uncurry (R𝕡elim.f (to n)) (z , y)) ≡ (z , y))
-- -- -- -- -- --   R𝕡elimSet.isSetA w _ = isSetΠ λ _ → isGroupoidΣ𝔽in→ _ _ _
-- -- -- -- -- --   R𝕡elimSet.abase w _ = refl
-- -- -- -- -- --   R𝕡elimSet.aloop w k =
-- -- -- -- -- --     funExtDep λ p → ΣSquareP ((λ i j → 𝕡loop k i) ,
-- -- -- -- -- --          S.congSqP (λ i j → p i ∘'_)
-- -- -- -- -- --             (isSet→SquareP (λ i _ → isSet→ (snd (𝔽inH n (𝕡loop k i))))
-- -- -- -- -- --               _ _ _ _) )
  
-- -- -- -- -- --   R𝕡elimSet.alooop w k l =
-- -- -- -- -- --      funExtDep λ p → ΣSquareP ((λ i j → 𝕡looop k l i) ,
-- -- -- -- -- --          S.congSqP (λ i j → p i ∘'_)
-- -- -- -- -- --             (isSet→SquareP (λ i _ → isSet→ (snd (𝔽inH n (𝕡looop k l i))))
-- -- -- -- -- --               _ _ _ _))

-- -- -- -- -- --  Iso-𝔽in→-Fin→/↔ : ∀ n → Iso (𝔽in→ A n) (Fin→/↔ A n)
-- -- -- -- -- --  Iso.fun (Iso-𝔽in→-Fin→/↔ n) = uncurry (R𝕡elim.f (to n))
-- -- -- -- -- --  Iso.inv (Iso-𝔽in→-Fin→/↔ n) = from n
-- -- -- -- -- --  Iso.rightInv (Iso-𝔽in→-Fin→/↔ n) = from-to n
-- -- -- -- -- --  Iso.leftInv (Iso-𝔽in→-Fin→/↔ n) = to-from n

-- -- -- -- -- --  -- Iso-𝔽in→-Fin→/↔ : Iso (Σ _ (𝔽in→ A)) (Σ _ (Fin→/↔ A))
-- -- -- -- -- --  -- Iso.fun Iso-𝔽in→-Fin→/↔ = {!!}
-- -- -- -- -- --  -- Iso.inv Iso-𝔽in→-Fin→/↔ = {!!}
-- -- -- -- -- --  -- Iso.rightInv Iso-𝔽in→-Fin→/↔ = {!!}
-- -- -- -- -- --  -- Iso.leftInv Iso-𝔽in→-Fin→/↔ = {!!}




-- -- -- -- -- -- -- Rsucℙrm : ∀ n → R𝕡rec {n = n} (ℙrm (suc n))
-- -- -- -- -- -- -- R𝕡rec.abase (Rsucℙrm n) = 𝕡base
-- -- -- -- -- -- -- R𝕡rec.aloop (Rsucℙrm n) k = 𝕡loop (suc (fst k) , (snd k))
-- -- -- -- -- -- -- R𝕡rec.alooop (Rsucℙrm n) k l =
-- -- -- -- -- -- --   𝕡looop _ _
-- -- -- -- -- -- -- R𝕡rec.acomp (Rsucℙrm n) k l =
-- -- -- -- -- -- --   𝕡comp _ _
-- -- -- -- -- -- -- R𝕡rec.ainvol (Rsucℙrm n) k =
-- -- -- -- -- -- --   𝕡invol _
-- -- -- -- -- -- -- R𝕡rec.acomm (Rsucℙrm n) k l x =
-- -- -- -- -- -- --   𝕡comm _ _ (A.suc-commT (fst k) (fst l) x)
-- -- -- -- -- -- -- R𝕡rec.abraid (Rsucℙrm n) k k< =
-- -- -- -- -- -- --   𝕡braid _ _
-- -- -- -- -- -- -- R𝕡rec.asquash (Rsucℙrm n) = 𝕡squash

-- -- -- -- -- -- -- sucℙrm : ∀ n → ℙrm n → ℙrm (suc n)
-- -- -- -- -- -- -- sucℙrm n = R𝕡rec.f {n = n} (Rsucℙrm n)

-- -- -- -- -- -- -- fm2base : ℕ → FMSet2 Unit
-- -- -- -- -- -- -- fm2base zero = []
-- -- -- -- -- -- -- fm2base (suc x) = _ ∷2 (fm2base x)

-- -- -- -- -- -- -- fm2loop : ∀ n → ℕ → fm2base n ≡ fm2base n
-- -- -- -- -- -- -- fm2loop (suc n) (suc x) = cong (tt ∷2_) (fm2loop n x)
-- -- -- -- -- -- -- fm2loop zero x = refl
-- -- -- -- -- -- -- fm2loop (suc zero) zero = refl
-- -- -- -- -- -- -- fm2loop (suc (suc n)) zero = comm _ _ _

-- -- -- -- -- -- -- RtoFM2⊤ : ∀ n → R𝕡rec {n = n} (FMSet2 Unit)
-- -- -- -- -- -- -- R𝕡rec.abase (RtoFM2⊤ n) = fm2base n
-- -- -- -- -- -- -- R𝕡rec.aloop (RtoFM2⊤ n) (k , _) = fm2loop n k
-- -- -- -- -- -- -- --   cong (tt ∷2_) (R𝕡rec.aloop (RtoFM2⊤ n) (k , k<) )
-- -- -- -- -- -- -- -- R𝕡rec.aloop (RtoFM2⊤ (suc (suc n))) (zero , k<) = comm _ _ _

-- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ n) (zero , k<) (zero , l<) = refl
-- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ (suc n)) (suc k , k<) (suc l , l<) =
-- -- -- -- -- -- --     cong (tt ∷2_) (R𝕡rec.alooop (RtoFM2⊤ n) (k , k<) (l , l<))
-- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ (suc (suc n))) (zero , k<) (suc (suc l) , l<) i =
-- -- -- -- -- -- --   comm _ _ (R𝕡rec.aloop (RtoFM2⊤ n) (l , l<) (~ i)) (i)
-- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ (suc (suc n))) (suc (suc k) , k<) (zero , l<) i =
-- -- -- -- -- -- --   comm _ _ (R𝕡rec.aloop (RtoFM2⊤ n) (k , k<) i) (~ i)
  
-- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc zero , l<) =
-- -- -- -- -- -- --   sym (commmR _ _ _ _)  
-- -- -- -- -- -- -- R𝕡rec.alooop (RtoFM2⊤ (suc (suc (suc n)))) (suc zero , k<) (zero , l<) =
-- -- -- -- -- -- --   commmL _ _ _ _
  
-- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc n)) (zero , k<) (zero , l<) i j =
-- -- -- -- -- -- --   R𝕡rec.aloop (RtoFM2⊤ (suc n)) (0 , isProp≤ {m = 1} {n = n} k< l< i) j
 
-- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc zero , l<) =
-- -- -- -- -- -- --    symP (commpR tt tt tt (fm2base n))
-- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc (suc l) , l<) i j =
-- -- -- -- -- -- --   comm _ _ ((R𝕡rec.aloop (RtoFM2⊤ (suc n)) (l , l<) (~ i ∨ j))) (i ∨ j)
-- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (suc zero , k<) (zero , l<) =
-- -- -- -- -- -- --    (λ j i → tt ∷2 comm-inv tt tt (fm2base n) j i)
-- -- -- -- -- -- --     ◁ congP (λ _ → symP-fromGoal) (commpL tt tt tt (fm2base n)) ▷
-- -- -- -- -- -- --      λ j i → comm-inv tt tt (tt ∷2 fm2base n) (~ j) i
-- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (suc (suc k) , k<) (zero , l<) i j =
-- -- -- -- -- -- --     comm _ _ (R𝕡rec.aloop (RtoFM2⊤ (suc n)) (k , k<) (i ∨ j)) (~ i ∨  j)

-- -- -- -- -- -- -- R𝕡rec.acomp (RtoFM2⊤ (suc n)) (suc k , k<) (suc l , l<) i j = 
-- -- -- -- -- -- --  tt ∷2 R𝕡rec.acomp (RtoFM2⊤ n) (k , k<) (l , l<) i j
 
-- -- -- -- -- -- -- R𝕡rec.ainvol (RtoFM2⊤ (suc (suc n))) (zero , k<) = comm-inv _ _ _
-- -- -- -- -- -- -- R𝕡rec.ainvol (RtoFM2⊤ (suc (suc (suc n)))) (suc k , k<) =
-- -- -- -- -- -- --   cong (cong (tt  ∷2_)) (R𝕡rec.ainvol (RtoFM2⊤ (suc (suc n))) (k , k<))
-- -- -- -- -- -- -- R𝕡rec.acomm (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc (suc l) , l<) x i j =
-- -- -- -- -- -- --   comm-inv tt tt
-- -- -- -- -- -- --     (R𝕡rec.ainvol (RtoFM2⊤ (suc n)) (l , l<) (~ j) i) (~ j) (~ i)
-- -- -- -- -- -- -- R𝕡rec.acomm (RtoFM2⊤ (suc n)) (suc k , k<) (suc l , l<) x i j = 
-- -- -- -- -- -- --   tt ∷2 R𝕡rec.acomm (RtoFM2⊤ (n)) (k , k<) (l , l<)
-- -- -- -- -- -- --     (A.pred-commT k l x) i j

-- -- -- -- -- -- -- R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc n)))) zero k< =
-- -- -- -- -- -- --   flipSquare
-- -- -- -- -- -- --     ( (λ i j → commmL≡R tt tt tt (fm2base n) (~ i)  (~ j))
-- -- -- -- -- -- --       ◁ ((flipSquare (symP-fromGoal (hex tt tt tt (fm2base n))))))

-- -- -- -- -- -- -- R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc (suc n))))) (suc k) k< i j =
-- -- -- -- -- -- --  tt ∷2 R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc n)))) k k< i j
-- -- -- -- -- -- -- R𝕡rec.asquash (RtoFM2⊤ n) = trunc


-- -- -- -- -- -- -- toFM2⊤ : Σ _ ℙrm → FMSet2 Unit
-- -- -- -- -- -- -- toFM2⊤ x = R𝕡rec.f {n = (fst x)} (RtoFM2⊤ (fst x)) (snd x)


-- -- -- -- -- -- -- comp0 : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- --      Square
-- -- -- -- -- -- --        (𝕡looop {n = suc (suc n)}(zero , tt) (suc (suc (fst k)) , snd k))
-- -- -- -- -- -- --        (𝕡loop (zero , tt))
-- -- -- -- -- -- --        (sym (𝕡loop (suc (suc (fst k)) , snd k)))
-- -- -- -- -- -- --        refl
-- -- -- -- -- -- -- comp0 n k i j =
-- -- -- -- -- -- --   hcomp
-- -- -- -- -- -- --     (λ l → λ {
-- -- -- -- -- -- --        (i = i0) → 𝕡comm (zero , tt) (suc (suc (fst k)) , snd k) _ j (~ l)
-- -- -- -- -- -- --      ; (i = i1) → 𝕡loop (zero , tt) (j ∧ l)
-- -- -- -- -- -- --      ; (j = i0) → 𝕡invol (suc (suc (fst k)) , snd k) l i
-- -- -- -- -- -- --      ; (j = i1) → 𝕡loop (0 , tt) (~ i ∨ l)
-- -- -- -- -- -- --      }) ((𝕡comp (suc (suc (fst k)) , snd k) (zero , tt) ▷ 𝕡invol (zero , tt)) j i)

-- -- -- -- -- -- -- comp1 : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- --      Square
-- -- -- -- -- -- --        (𝕡looop {n = n} k l)
-- -- -- -- -- -- --        (𝕡loop k)
-- -- -- -- -- -- --        refl
-- -- -- -- -- -- --        (𝕡loop l)
-- -- -- -- -- -- -- comp1 n k l i j =
-- -- -- -- -- -- --   hcomp
-- -- -- -- -- -- --     (λ l' → λ {
-- -- -- -- -- -- --        (i = i0) → (𝕡looop {n = n} k l) j
-- -- -- -- -- -- --      ; (i = i1) → (𝕡loop k) (j ∨ ~ l')
-- -- -- -- -- -- --      ; (j = i0) → 𝕡loop k (~ l' ∧ i)
-- -- -- -- -- -- --      ; (j = i1) → (𝕡loop l) i
-- -- -- -- -- -- --      }) ((𝕡comp {n = n} k l) j i)


-- -- -- -- -- -- -- aloopcommm : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- --       PathP
-- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- --          sucℙrm (suc n) (sucℙrm n (𝕡loop k i)) ≡
-- -- -- -- -- -- --          sucℙrm (suc n) (sucℙrm n (𝕡loop k i)))
-- -- -- -- -- -- --       (𝕡loop (zero , tt)) (𝕡loop (zero , tt)) 
-- -- -- -- -- -- -- aloopcommm n (k , k<) i j =
-- -- -- -- -- -- --      hcomp (λ l → λ {
-- -- -- -- -- -- --     (i = i0) → comp0 n (k , k<) l j
-- -- -- -- -- -- --    ;(i = i1) → comp1 (suc (suc n)) (zero , _) (suc (suc k) , k<) l j
-- -- -- -- -- -- --    ;(j = i0) → 𝕡loop (suc (suc k) , k<) (i ∨ ~ l)
-- -- -- -- -- -- --    ;(j = i1) → 𝕡loop (suc (suc k) , k<) (i ∧ l)
-- -- -- -- -- -- --    }) (𝕡looop (zero , _) (suc (suc k) , k<) j)

-- -- -- -- -- -- -- fromFM2comm-diag : ∀ n → ∀ l l< → Square {A = ℙrm (2 + n)}
-- -- -- -- -- -- --        (λ i →
-- -- -- -- -- -- --          aloopcommm n (l , l<) (~ i) i)
-- -- -- -- -- -- --       (𝕡looop (zero , _) (suc (suc l) , l<))
-- -- -- -- -- -- --       refl
-- -- -- -- -- -- --       refl
-- -- -- -- -- -- -- fromFM2comm-diag n l l< =
-- -- -- -- -- -- --   symP-fromGoal (compPath-filler (𝕡looop (zero , _) (suc (suc l) , l<)) refl)

-- -- -- -- -- -- -- fromFM2comm-diag' : ∀ n → ∀ l l< → Square {A = ℙrm (2 + n)}
-- -- -- -- -- -- --        (λ i →
-- -- -- -- -- -- --          aloopcommm n (l , l<) (i) (~ i))
-- -- -- -- -- -- --       (𝕡looop (suc (suc l) , l<) (zero , _))
-- -- -- -- -- -- --       refl
-- -- -- -- -- -- --       refl
-- -- -- -- -- -- -- fromFM2comm-diag' n k k< =
-- -- -- -- -- -- --   congP (λ _ → sym) (fromFM2comm-diag n k k<) ∙
-- -- -- -- -- -- --    sym (𝕡looop-invol _ _ _)





-- -- -- -- -- -- -- fromFM2comm : (n : ℕ) → R𝕡elimSet {n = n} (λ (y : ℙrm n) →
-- -- -- -- -- -- --       (sucℙrm (suc n) (sucℙrm n y)) ≡
-- -- -- -- -- -- --       (sucℙrm (suc n) (sucℙrm n y)))
-- -- -- -- -- -- -- R𝕡elimSet.isSetA (fromFM2comm n) _ = 𝕡squash _ _
-- -- -- -- -- -- -- R𝕡elimSet.abase (fromFM2comm n) = 𝕡loop (zero , _)
-- -- -- -- -- -- -- R𝕡elimSet.aloop (fromFM2comm n) = aloopcommm n
-- -- -- -- -- -- -- R𝕡elimSet.alooop (fromFM2comm n) k l i j =
-- -- -- -- -- -- --  hcomp
-- -- -- -- -- -- --    (λ l' → λ {
-- -- -- -- -- -- --      (i = i0) → aloopcommm n k (~ l') j
-- -- -- -- -- -- --     ;(i = i1) → aloopcommm n l (~ l') j
-- -- -- -- -- -- --     ;(j = i0) → sucℙrm (suc n) (sucℙrm n (𝕡comp k l i (~ l')))
-- -- -- -- -- -- --     ;(j = i1) → sucℙrm (suc n) (sucℙrm n (𝕡comp k l i (~ l')))
-- -- -- -- -- -- --      }) (𝕡loop (zero , tt) j)


-- -- -- -- -- -- -- fromFM2comm-inv : (n : ℕ) → R𝕡elimProp {n = n}
-- -- -- -- -- -- --   (λ (p : ℙrm n) →
-- -- -- -- -- -- --      R𝕡elimSet.f (fromFM2comm n) p
-- -- -- -- -- -- --   ≡ sym (R𝕡elimSet.f (fromFM2comm n) p))
-- -- -- -- -- -- -- R𝕡elimProp.isPropA (fromFM2comm-inv n) _ = 𝕡squash _ _ _ _
-- -- -- -- -- -- -- R𝕡elimProp.abase (fromFM2comm-inv n) = 𝕡invol _

-- -- -- -- -- -- -- -- fromFM2commmL : (n : ℕ) → R𝕡elimSet {n = n} (λ (y : ℙrm n) →
-- -- -- -- -- -- -- --       (sucℙrm (suc (suc n)) (sucℙrm (suc n) (sucℙrm n y))) ≡
-- -- -- -- -- -- -- --       (sucℙrm (suc (suc n)) (sucℙrm (suc n) (sucℙrm n y))))
-- -- -- -- -- -- -- -- R𝕡elimSet.isSetA (fromFM2commmL n) _ = 𝕡squash _ _
-- -- -- -- -- -- -- -- R𝕡elimSet.abase (fromFM2commmL n) = sym (𝕡looop (suc zero , _) (zero , _))
-- -- -- -- -- -- -- -- R𝕡elimSet.aloop (fromFM2commmL n) = {!!}
-- -- -- -- -- -- -- -- R𝕡elimSet.alooop (fromFM2commmL n) = {!!}

-- -- -- -- -- -- -- RfromFM2⊤' : RElim {A = Unit} λ xs → ℙrm (len2 xs)
-- -- -- -- -- -- -- RElim.[]* RfromFM2⊤' = 𝕡base
-- -- -- -- -- -- -- RElim._∷*_ RfromFM2⊤' _ = sucℙrm _
-- -- -- -- -- -- -- RElim.comm* RfromFM2⊤' _ _ = (R𝕡elimSet.f (fromFM2comm _))
-- -- -- -- -- -- -- RElim.comm-inv* RfromFM2⊤' _ _ = R𝕡elimProp.f (fromFM2comm-inv _)
-- -- -- -- -- -- -- RElim.commmL* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- --     (sym (cong′ (sucℙrm _) ((R𝕡elimSet.f (fromFM2comm _)) p)))
-- -- -- -- -- -- --     ∙∙ refl ∙∙
-- -- -- -- -- -- --     (((R𝕡elimSet.f (fromFM2comm _)) (sucℙrm _ p)))

-- -- -- -- -- -- -- RElim.commmR* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- --      cong′ (sucℙrm _) ((R𝕡elimSet.f (fromFM2comm _)) p)
-- -- -- -- -- -- --     ∙∙ refl ∙∙
-- -- -- -- -- -- --      (sym ((R𝕡elimSet.f (fromFM2comm _)) (sucℙrm _ p)))
    
-- -- -- -- -- -- -- RElim.commpL* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- --   flipSquare (doubleCompPath-filler
-- -- -- -- -- -- --     (sym (cong′ (sucℙrm _) ((R𝕡elimSet.f (fromFM2comm _)) p))) _ _)
-- -- -- -- -- -- -- RElim.commpR* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- --   flipSquare (symP-fromGoal (doubleCompPath-filler
-- -- -- -- -- -- --     (cong′ (sucℙrm _) ((R𝕡elimSet.f (fromFM2comm _)) p)) _ _))
-- -- -- -- -- -- -- RElim.hex* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- --   {!𝕡braid!}
  
-- -- -- -- -- -- -- -- RElim.hexDiag* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- -- --       (cong′ (sucℙrm _) (((R𝕡elimSet.f (fromFM2comm _)) p))
-- -- -- -- -- -- -- --       ∙∙ ((R𝕡elimSet.f (fromFM2comm _)) (sucℙrm _ p))
-- -- -- -- -- -- -- --       ∙∙ cong′ (sucℙrm _) (sym ((R𝕡elimSet.f (fromFM2comm _)) p)) )
-- -- -- -- -- -- -- -- RElim.hexU* RfromFM2⊤' _ _ _ =
-- -- -- -- -- -- -- --   R𝕡elimProp.f (record { isPropA =
-- -- -- -- -- -- -- --     λ _ → isOfHLevelRetractFromIso 1 (invIso PathP→comm-Iso)
-- -- -- -- -- -- -- --       (𝕡squash _ _ _ _) ;
-- -- -- -- -- -- -- --     abase = λ i j →
-- -- -- -- -- -- -- --       hcomp (λ l →
-- -- -- -- -- -- -- --         primPOr (~ i) (j ∨ ~ j) (λ _ → 𝕡loop (1 , tt) j)
-- -- -- -- -- -- -- --           λ _ → hcomp
-- -- -- -- -- -- -- --               (λ l' → λ {
-- -- -- -- -- -- -- --                   (i = i0) → 𝕡loop (zero , tt) (~ l' ∧ l)
-- -- -- -- -- -- -- --                  ;(i = i1) → 𝕡invol (1 , tt) l' l
-- -- -- -- -- -- -- --                  ;(l = i0) → 𝕡looop (zero , tt) (1 , tt) i
-- -- -- -- -- -- -- --                  ;(l = i1) → 𝕡loop (zero , tt) (i ∨ (~ l'))
-- -- -- -- -- -- -- --                  }) (𝕡comp (zero , tt) (1 , tt) i l))
-- -- -- -- -- -- -- --        (𝕡braid zero tt i j) })
  
-- -- -- -- -- -- -- -- RElim.hexL* RfromFM2⊤' _ _ _ p =
-- -- -- -- -- -- -- --   symP-fromGoal (doubleCompPath-filler _ _ _)
-- -- -- -- -- -- -- RElim.trunc* RfromFM2⊤' _ = 𝕡squash

-- -- -- -- -- -- -- fromFM2⊤ : FMSet2 Unit → Σ ℕ ℙrm
-- -- -- -- -- -- -- fromFM2⊤ xs = (len2 xs) , (RElim.f RfromFM2⊤' xs )


-- -- -- -- -- -- -- Rsucℙrm-lem : ∀ n → R𝕡elimSet {n = n}
-- -- -- -- -- -- --   λ p → toFM2⊤ (suc n , sucℙrm n p) ≡ tt ∷2 toFM2⊤ (n , p)
-- -- -- -- -- -- -- R𝕡elimSet.isSetA (Rsucℙrm-lem n) _ = trunc _ _
-- -- -- -- -- -- -- R𝕡elimSet.abase (Rsucℙrm-lem n) = refl
-- -- -- -- -- -- -- R𝕡elimSet.aloop (Rsucℙrm-lem n) k _ = refl
-- -- -- -- -- -- -- R𝕡elimSet.alooop (Rsucℙrm-lem n) k l _ = refl

-- -- -- -- -- -- -- sucℙrm-lem : ∀ n p → toFM2⊤ (suc n , sucℙrm n p) ≡ tt ∷2 toFM2⊤ (n , p)
-- -- -- -- -- -- -- sucℙrm-lem n = R𝕡elimSet.f (Rsucℙrm-lem n)

-- -- -- -- -- -- -- comm*-lem : ∀ n → R𝕡elimProp {n = n}
-- -- -- -- -- -- --                (λ p → Square {A = FMSet2 Unit}
-- -- -- -- -- -- --         (sucℙrm-lem (suc n) (sucℙrm n p) ∙ cong′ (tt ∷2_) (sucℙrm-lem n p))
-- -- -- -- -- -- --         (sucℙrm-lem (suc n) (sucℙrm n p) ∙ cong′ (tt ∷2_) (sucℙrm-lem n p))
-- -- -- -- -- -- --         (λ i → toFM2⊤ (suc (suc n) , (R𝕡elimSet.f {n = n} (fromFM2comm n)) p i))
-- -- -- -- -- -- --         (comm tt tt (toFM2⊤ (n , p))))
-- -- -- -- -- -- -- R𝕡elimProp.isPropA (comm*-lem n) _ =
-- -- -- -- -- -- --    isOfHLevelRetractFromIso 1 (invIso PathP→comm-Iso) (trunc _ _ _ _)
-- -- -- -- -- -- -- R𝕡elimProp.abase (comm*-lem n) i = refl ∙∙ refl ∙∙ refl

-- -- -- -- -- -- -- RfromToFM2⊤ : RElimSet' (λ z → toFM2⊤ (fromFM2⊤ z) ≡ z) 
-- -- -- -- -- -- -- RElimSet'.[]* RfromToFM2⊤ = refl
-- -- -- -- -- -- -- (RfromToFM2⊤ RElimSet'.∷* tt) {xs} X =
-- -- -- -- -- -- --   uncurry sucℙrm-lem (fromFM2⊤ xs) ∙ cong (tt ∷2_) X
  
-- -- -- -- -- -- -- RElimSet'.comm* RfromToFM2⊤ tt tt {xs} X i j =
-- -- -- -- -- -- --  hcomp
-- -- -- -- -- -- --    (λ l → primPOr (j ∨ ~ j) ((i ∨ ~ i))
-- -- -- -- -- -- --       (primPOr j (~ j) (λ _ → comm tt tt (X l) i)
-- -- -- -- -- -- --         λ _ → toFM2⊤ (fromFM2⊤ (comm tt tt xs i)))
-- -- -- -- -- -- --       λ _ → (uncurry sucℙrm-lem (fromFM2⊤ (tt ∷2 xs)) ∙
-- -- -- -- -- -- --          cong′ (tt ∷2_) (compPath-filler (uncurry sucℙrm-lem (fromFM2⊤ xs))
-- -- -- -- -- -- --                     (cong′ (tt ∷2_) X) l)) j)

-- -- -- -- -- -- --   (R𝕡elimProp.f {n = (fst (fromFM2⊤ xs))}
-- -- -- -- -- -- --     (comm*-lem (fst (fromFM2⊤ xs))) (snd (fromFM2⊤ xs)) i j)

-- -- -- -- -- -- -- -- RElimSet.hexDiag* RfromToFM2⊤ _ _ _ b i j = 
-- -- -- -- -- -- -- --   hcomp
-- -- -- -- -- -- -- --     (λ l → λ {
-- -- -- -- -- -- -- --       (i = i0) → {!!}
-- -- -- -- -- -- -- --      ;(i = i1) → {!!}
-- -- -- -- -- -- -- --      ;(j = i0) → {!!}
-- -- -- -- -- -- -- --      ;(j = i1) → hexDiag _ _ _ (b l) i
-- -- -- -- -- -- -- --        })
-- -- -- -- -- -- -- --     {!!}

-- -- -- -- -- -- -- -- i = i0 ⊢ (uncurry sucℙrm-lem (fromFM2⊤ (y ∷2 z ∷2 xs)) ∙
-- -- -- -- -- -- -- --           (λ i₁ →
-- -- -- -- -- -- -- --              tt ∷2
-- -- -- -- -- -- -- --              (uncurry sucℙrm-lem (fromFM2⊤ (z ∷2 xs)) ∙
-- -- -- -- -- -- -- --               (λ i₂ →
-- -- -- -- -- -- -- --                  tt ∷2 (uncurry sucℙrm-lem (fromFM2⊤ xs) ∙ (λ i₃ → tt ∷2 b i₃)) i₂))
-- -- -- -- -- -- -- --              i₁))
-- -- -- -- -- -- -- --          j
-- -- -- -- -- -- -- -- i = i1 ⊢ (uncurry sucℙrm-lem (fromFM2⊤ (y ∷2 x ∷2 xs)) ∙
-- -- -- -- -- -- -- --           (λ i₁ →
-- -- -- -- -- -- -- --              tt ∷2
-- -- -- -- -- -- -- --              (uncurry sucℙrm-lem (fromFM2⊤ (x ∷2 xs)) ∙
-- -- -- -- -- -- -- --               (λ i₂ →
-- -- -- -- -- -- -- --                  tt ∷2 (uncurry sucℙrm-lem (fromFM2⊤ xs) ∙ (λ i₃ → tt ∷2 b i₃)) i₂))
-- -- -- -- -- -- -- --              i₁))
-- -- -- -- -- -- -- --          j
-- -- -- -- -- -- -- -- j = i0 ⊢ toFM2⊤ (fromFM2⊤ (hexDiag x y z xs i))
-- -- -- -- -- -- -- -- j = i1 ⊢ hexDiag x y z xs i
-- -- -- -- -- -- -- -- b  : toFM2⊤ (fromFM2⊤ xs) ≡ xs

-- -- -- -- -- -- -- RElimSet'.trunc* RfromToFM2⊤ _ = trunc _ _

-- -- -- -- -- -- -- fromToFM2⊤ : retract fromFM2⊤ toFM2⊤
-- -- -- -- -- -- -- fromToFM2⊤ = RElimSet'.f RfromToFM2⊤

-- -- -- -- -- -- -- dccf-lem : ∀ {a a' : A} → (p : a ≡ a') →
-- -- -- -- -- -- --              Square p p (refl ∙∙ refl ∙∙ refl) refl
-- -- -- -- -- -- -- dccf-lem {a = a} {a'} p i j = 
-- -- -- -- -- -- --    hcomp
-- -- -- -- -- -- --      (λ l → λ {
-- -- -- -- -- -- --        (i = i0) → p j
-- -- -- -- -- -- --       ;(i = i1) → p j
-- -- -- -- -- -- --       ;(j = i1) → a'
-- -- -- -- -- -- --        })
-- -- -- -- -- -- --      (p j)



-- -- -- -- -- -- -- RtoFromFM2⊤-fst : ∀ n → R𝕡elimSet {n = n} (λ z → len2 (toFM2⊤ (n , z)) ≡ n)
-- -- -- -- -- -- -- R𝕡elimSet.isSetA (RtoFromFM2⊤-fst n) _ = isProp→isSet (isSetℕ _ _)
-- -- -- -- -- -- -- R𝕡elimSet.abase (RtoFromFM2⊤-fst zero) = refl
-- -- -- -- -- -- -- R𝕡elimSet.abase (RtoFromFM2⊤-fst (suc n)) =
-- -- -- -- -- -- --   cong suc (R𝕡elimSet.abase (RtoFromFM2⊤-fst n))
-- -- -- -- -- -- -- R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc n)) (suc k , k<) i j =
-- -- -- -- -- -- --   suc (R𝕡elimSet.aloop (RtoFromFM2⊤-fst (n)) (k , k<) i j)
-- -- -- -- -- -- -- R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc (suc n))) (zero , k<) = refl

-- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc n)) (suc k , k<) (suc l , l<) i j =
-- -- -- -- -- -- --   suc (R𝕡elimSet.alooop (RtoFromFM2⊤-fst n) (k , k<) (l , l<) i j)
-- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc n)) (zero , k<) (zero , l<) = refl
-- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc n)))) (zero , k<) (suc zero , l<) = refl
-- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc (suc n))))) (zero , k<) (suc (suc l) , l<) i j = suc (suc (R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc (suc n))) (l , l<) (~ i) j))
-- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc n)))) (suc zero , k<) (zero , l<) = refl
-- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc (suc n))))) (suc (suc k) , k<) (zero , l<) i j = suc (suc ((R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc (suc n))) (k , k<) i j)))


-- -- -- -- -- -- -- -- -- ∷2-lem-fst : ∀ xs → (fromFM2⊤ (tt ∷2 xs)) ≡
-- -- -- -- -- -- -- -- --    (suc (fst (fromFM2⊤ xs)) , uncurry sucℙrm (fromFM2⊤ xs))

-- -- -- -- -- -- -- base≡ : ∀ n → PathP (λ i → ℙrm (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) i))
-- -- -- -- -- -- --       (RElim.f RfromFM2⊤' (fm2base n)) 𝕡base
-- -- -- -- -- -- -- base≡ zero _ = 𝕡base
-- -- -- -- -- -- -- base≡ (suc n) = congP (λ _ → sucℙrm _) (base≡ n)



-- -- -- -- -- -- -- loop≡ : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- --       PathP
-- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- --          PathP (λ i₁ → ℙrm (R𝕡elimSet.f (RtoFromFM2⊤-fst n) (𝕡loop k i) i₁))
-- -- -- -- -- -- --          (snd (fromFM2⊤ (toFM2⊤ (n , 𝕡loop k i)))) (𝕡loop k i))
-- -- -- -- -- -- --       (base≡ n) (base≡ n)
-- -- -- -- -- -- -- loop≡ (suc n) (suc k , k<) i j = sucℙrm _ (loop≡ n (k , k<) i j) 
-- -- -- -- -- -- -- loop≡ (suc (suc n)) (zero , k<) i j =
-- -- -- -- -- -- --         (R𝕡elim.f
-- -- -- -- -- -- --           (R𝕡elimSet.fR (fromFM2comm (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j)))
-- -- -- -- -- -- --          ((base≡ n) j ) i)

-- -- -- -- -- -- -- looop≡ : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- --       PathP
-- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- --          PathP
-- -- -- -- -- -- --          (λ i₁ → ℙrm (R𝕡elimSet.f (RtoFromFM2⊤-fst n) (𝕡looop k l i) i₁))
-- -- -- -- -- -- --                            (snd (fromFM2⊤ (toFM2⊤ (n , 𝕡looop k l i))))
-- -- -- -- -- -- --          (𝕡looop k l i))
-- -- -- -- -- -- --       (base≡ n) (base≡ n)
-- -- -- -- -- -- -- looop≡ (suc n) (suc k , k<) (suc l , l<) i j =
-- -- -- -- -- -- --    sucℙrm _ (looop≡ n (k , k<) (l , l<) i j)      
-- -- -- -- -- -- -- looop≡ (suc (suc n)) (zero , k<) (zero , l<) i j =
-- -- -- -- -- -- --   hcomp (λ l' → primPOr j (i ∨ ~ i ∨ ~ j)
-- -- -- -- -- -- --              (λ _ → 𝕡comp (zero , _) (zero , _) i (~ l'))
-- -- -- -- -- -- --              λ _ → loop≡ (suc (suc n)) (zero , _) (~ l') j)
-- -- -- -- -- -- --         (sucℙrm _ (sucℙrm _ (base≡ n j)))
-- -- -- -- -- -- -- looop≡ (suc (suc (suc n))) (zero , k<) (suc zero , l<) = {!!}
-- -- -- -- -- -- --    -- hcomp (λ l' → {!!}
-- -- -- -- -- -- --    --          )
-- -- -- -- -- -- --    --      (sucℙrm _ (sucℙrm _ (sucℙrm _ (base≡ n j))))
-- -- -- -- -- -- --   -- comp (λ l' →  ℙrm (3 +
-- -- -- -- -- -- --   --          hfill
-- -- -- -- -- -- --   --         (λ { l (i = i0) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
-- -- -- -- -- -- --   --            ; l (i = i1) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
-- -- -- -- -- -- --   --            ; l (j = i1) → n
-- -- -- -- -- -- --   --            }) (inS (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j)) l'))
-- -- -- -- -- -- --   --    (λ l' → λ {
-- -- -- -- -- -- --   --        (i = i0) → loop≡ (suc (suc (suc n))) (zero , _) (~ l') j
-- -- -- -- -- -- --   --       ;(i = i1) → loop≡ (suc (suc (suc n))) (1 , _) (~ l') j
-- -- -- -- -- -- --   --       ;(j = i1) → 𝕡comp (zero , _) (1 , _) i (~ l')
-- -- -- -- -- -- --   --       })
-- -- -- -- -- -- --   --       ((sucℙrm _ (sucℙrm _ (sucℙrm _ (base≡ n j)))))

-- -- -- -- -- -- -- looop≡ (suc (suc (suc (suc n)))) kk@(zero , k<) ll@(suc (suc l) , l<) =
-- -- -- -- -- -- --   flipSquareP ((λ j i →
-- -- -- -- -- -- --       (((R𝕡elim.f
-- -- -- -- -- -- --             (R𝕡elimSet.fR (fromFM2comm _))
-- -- -- -- -- -- --             (loop≡ (suc (suc n)) (l , l<) (~ i) j) i))) ) ▷
-- -- -- -- -- -- --              fromFM2comm-diag (suc (suc n)) l l<)
   
-- -- -- -- -- -- -- looop≡ (suc (suc (suc n))) (suc zero , k<) (zero , l<) i j =
-- -- -- -- -- -- --   {!!}
-- -- -- -- -- -- --      -- comp (λ l' →  ℙrm (3 +
-- -- -- -- -- -- --      --       hfill
-- -- -- -- -- -- --      --      (λ { l (i = i1) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
-- -- -- -- -- -- --      --         ; l (i = i0) → R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j
-- -- -- -- -- -- --      --         ; l (j = i1) → n
-- -- -- -- -- -- --      --         }) (inS (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j)) l'))
-- -- -- -- -- -- --      -- (λ l' → λ {
-- -- -- -- -- -- --      --     (i = i1) → loop≡ (suc (suc (suc n))) (zero , _) (~ l') j
-- -- -- -- -- -- --      --    ;(i = i0) → loop≡ (suc (suc (suc n))) (1 , _) (~ l') j
-- -- -- -- -- -- --      --    ;(j = i1) → 𝕡comp (1 , _) (zero , _) i (~ l')
-- -- -- -- -- -- --      --    })
-- -- -- -- -- -- --      --    ((sucℙrm _ (sucℙrm _ (sucℙrm _ (base≡ n j)))))

-- -- -- -- -- -- -- looop≡ (suc (suc (suc (suc n)))) (suc (suc k) , k<) (zero , l<) =
-- -- -- -- -- -- --     flipSquareP ((λ j i →
-- -- -- -- -- -- --       (((R𝕡elim.f
-- -- -- -- -- -- --             (R𝕡elimSet.fR (fromFM2comm _))
-- -- -- -- -- -- --             (loop≡ (suc (suc n)) (k , k<) (i) j) (~ i)))) ) ▷
-- -- -- -- -- -- --              fromFM2comm-diag' (suc (suc n)) k k<)


-- -- -- -- -- -- -- RtoFromFM2⊤ : ∀ n → R𝕡elimSet {n = n} (λ z →
-- -- -- -- -- -- --        PathP (λ i → ℙrm ((R𝕡elimSet.f (RtoFromFM2⊤-fst n) z i)))
-- -- -- -- -- -- --            (snd (fromFM2⊤ (toFM2⊤ (n , z)))) z)
-- -- -- -- -- -- -- R𝕡elimSet.isSetA (RtoFromFM2⊤ n) _ =
-- -- -- -- -- -- --  isOfHLevelRetractFromIso 2 (PathPIsoPath _ _ _) (𝕡squash _ _)
-- -- -- -- -- -- -- R𝕡elimSet.abase (RtoFromFM2⊤ n) = base≡ n
-- -- -- -- -- -- -- R𝕡elimSet.aloop (RtoFromFM2⊤ n) = loop≡ n
-- -- -- -- -- -- -- R𝕡elimSet.alooop (RtoFromFM2⊤ n) = looop≡ n

-- -- -- -- -- -- -- toFromFM2⊤ : section fromFM2⊤ toFM2⊤
-- -- -- -- -- -- -- toFromFM2⊤ (n , p) = ΣPathP (_  , R𝕡elimSet.f {n = n} (RtoFromFM2⊤ n) p)

-- -- -- -- -- -- -- Iso-FM2⊤-Σℙrm : Iso (FMSet2 Unit) (Σ _ ℙrm)
-- -- -- -- -- -- -- Iso.fun Iso-FM2⊤-Σℙrm = fromFM2⊤
-- -- -- -- -- -- -- Iso.inv Iso-FM2⊤-Σℙrm = toFM2⊤
-- -- -- -- -- -- -- Iso.rightInv Iso-FM2⊤-Σℙrm = toFromFM2⊤
-- -- -- -- -- -- -- Iso.leftInv Iso-FM2⊤-Σℙrm = fromToFM2⊤

-- -- -- -- -- -- -- Iso-FM2⊤-EMP : Iso (FMSet2 Unit) (Σ _ ℙrm')
-- -- -- -- -- -- -- Iso-FM2⊤-EMP = compIso Iso-FM2⊤-Σℙrm (Σ-cong-iso-snd IsoEmℙrm)

-- -- -- -- -- -- -- fmbase⊤ : ℕ → FMSet2 Unit
-- -- -- -- -- -- -- fmbase⊤ zero = []
-- -- -- -- -- -- -- fmbase⊤ (suc n) = tt ∷2 fmbase⊤ n

-- -- -- -- -- -- -- Iso-𝔽in-S𝔽in : ∀ n → Iso (𝔽in (𝕡base {n})) (S.𝔽in (fmbase⊤ n))
-- -- -- -- -- -- -- Iso-𝔽in-S𝔽in zero = w
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --    open Iso

-- -- -- -- -- -- --    w : Iso _ _
-- -- -- -- -- -- --    fun w = snd
-- -- -- -- -- -- --    Iso.inv w ()
-- -- -- -- -- -- --    rightInv w ()
-- -- -- -- -- -- --    leftInv w (_ , ())
-- -- -- -- -- -- -- Iso.fun (Iso-𝔽in-S𝔽in (suc n)) (zero , snd₁) = nothing
-- -- -- -- -- -- -- Iso.fun (Iso-𝔽in-S𝔽in (suc n)) (suc fst₁ , snd₁) =
-- -- -- -- -- -- --   just (Iso.fun (Iso-𝔽in-S𝔽in n) (fst₁ , snd₁))
-- -- -- -- -- -- -- Iso.inv (Iso-𝔽in-S𝔽in (suc n)) nothing = zero , _
-- -- -- -- -- -- -- Iso.inv (Iso-𝔽in-S𝔽in (suc n)) (just x) =
-- -- -- -- -- -- --  sucF (Iso.inv (Iso-𝔽in-S𝔽in n) x)
-- -- -- -- -- -- -- Iso.rightInv (Iso-𝔽in-S𝔽in (suc n)) nothing = refl
-- -- -- -- -- -- -- Iso.rightInv (Iso-𝔽in-S𝔽in (suc n)) (just x) =
-- -- -- -- -- -- --   cong just (Iso.rightInv (Iso-𝔽in-S𝔽in n) x)
-- -- -- -- -- -- -- Iso.leftInv (Iso-𝔽in-S𝔽in (suc n)) (zero , snd₁) = refl
-- -- -- -- -- -- -- Iso.leftInv (Iso-𝔽in-S𝔽in (suc n)) (suc k , snd₁) =
-- -- -- -- -- -- --   ≡Fin {n = suc n} (cong (suc ∘ fst)
-- -- -- -- -- -- --    (Iso.leftInv (Iso-𝔽in-S𝔽in (n)) (k , snd₁)))


      


-- -- -- -- -- -- -- -- -- module _ {A : Type ℓ} where


-- -- -- -- -- -- -- -- -- --  -- pci = preCompInvol.e' {f = f} (B j i) fInvol
-- -- -- -- -- -- -- -- --  →adjT : ∀ n (k : Σ ℕ (λ k₁ → suc k₁ < n))  → (Fin n → A) ≃ (Fin n → A)
-- -- -- -- -- -- -- -- --  →adjT n k = preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k)
 
-- -- -- -- -- -- -- -- --  𝔽→looop : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n))  → (Fin n → A) ≡ (Fin n → A)
-- -- -- -- -- -- -- -- --  𝔽→looop n k l i =
-- -- -- -- -- -- -- -- --    Glue (Fin n → A)
-- -- -- -- -- -- -- -- --      λ { (i = i0) → (Fin n → A) , →adjT n k
-- -- -- -- -- -- -- -- --        ; (i = i1) → (Fin n → A) , →adjT n l } 

-- -- -- -- -- -- -- -- --  𝔽→looop-comp-si : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- --       Square
-- -- -- -- -- -- -- -- --          (λ i → Flooop n k l i → A)
-- -- -- -- -- -- -- -- --          (𝔽→looop n k l)
-- -- -- -- -- -- -- -- --          refl
-- -- -- -- -- -- -- -- --          refl
-- -- -- -- -- -- -- -- --  𝔽→looop-comp-si n k l j i =
-- -- -- -- -- -- -- -- --    Glue (Flooop n k l (i ∨ j) → A)
-- -- -- -- -- -- -- -- --      λ { (i = i0) → {!!}
-- -- -- -- -- -- -- -- --        ; (i = i1) → {!!}
-- -- -- -- -- -- -- -- --        ; (j = i0) → _ , idEquiv _
-- -- -- -- -- -- -- -- --        }

-- -- -- -- -- -- -- -- --  𝔽→looop-comp : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- --      Square
-- -- -- -- -- -- -- -- --        (ua (→adjT n k))
-- -- -- -- -- -- -- -- --        (ua (→adjT n l))
-- -- -- -- -- -- -- -- --        (𝔽→looop n k l)
-- -- -- -- -- -- -- -- --        refl
-- -- -- -- -- -- -- -- --  𝔽→looop-comp = {!!}

-- -- -- -- -- -- -- -- --  R𝔽→ : ∀ n → R𝕡elim {n = n} λ p → singl (𝔽in p → A)
-- -- -- -- -- -- -- -- --  R𝕡elim.isGroupoidA (R𝔽→ n) _ = isOfHLevelPlus 3 (isContrSingl _)
-- -- -- -- -- -- -- -- --  R𝕡elim.abase (R𝔽→ n) = _ , refl
-- -- -- -- -- -- -- -- --  R𝕡elim.aloop (R𝔽→ n) k i = _ ,
-- -- -- -- -- -- -- -- --    λ j → preCompInvol.eq {f = adjT n k} A (isInvolution-adjT n  k) j i   
-- -- -- -- -- -- -- -- --  fst (R𝕡elim.alooop (R𝔽→ n) k l i) = 𝔽→looop n k l i
-- -- -- -- -- -- -- -- --  snd (R𝕡elim.alooop (R𝔽→ n) k l i) j = 𝔽→looop-comp-si n k l j i
-- -- -- -- -- -- -- -- --  R𝕡elim.acomp (R𝔽→ n) = {!!}
-- -- -- -- -- -- -- -- --  R𝕡elim.ainvol (R𝔽→ n) = {!!}
-- -- -- -- -- -- -- -- --  R𝕡elim.acomm (R𝔽→ n) = {!!}
-- -- -- -- -- -- -- -- --  R𝕡elim.abraid (R𝔽→ n) = {!!}
-- -- -- -- -- -- -- -- --  -- R𝕡elim.isGroupoidA (R𝕍 n) p =
-- -- -- -- -- -- -- -- --  --    isOfHLevelPlus 3 (isContrSingl _)
-- -- -- -- -- -- -- -- --  -- R𝕡elim.abase (R𝔽→ n) = (𝔽in p → A) , ua (tabEquiv n)
-- -- -- -- -- -- -- -- --  -- R𝕡elim.aloop (R𝕍 n) k = ΣPathP (ua (adjT×^≃ (fst k)) , ua-adj-law n k)
-- -- -- -- -- -- -- -- --  -- R𝕡elim.alooop (R𝕍 n) k l = ΣPathP (𝕍looop n (fst k) (fst l) , 𝕍loopSi n k l )
-- -- -- -- -- -- -- -- --  -- fst (R𝕡elim.acomp (R𝕍 n) (k , _) (l , _) i j) = 𝕍comp n k l i j

-- -- -- -- -- -- -- -- --  -- snd (R𝕡elim.acomp (R𝕍 n) k l i j) m = 𝕍compSi n k l m i j
-- -- -- -- -- -- -- -- --  -- fst (R𝕡elim.ainvol (R𝕍 n) k i j) = 𝕍invol n (fst k) i j
-- -- -- -- -- -- -- -- --  -- snd (R𝕡elim.ainvol (R𝕍 n) k i j) = {!!}
-- -- -- -- -- -- -- -- --  -- R𝕡elim.acomm (R𝕍 n) = {!!}
-- -- -- -- -- -- -- -- --  -- R𝕡elim.abraid (R𝕍 n) = {!!}


-- -- -- -- -- -- -- -- sucF'-fst : ∀ n k k< → PathP (λ i → ua (adjT'≃ {n = n} (k , k<)) i → ℕ)
-- -- -- -- -- -- -- --                   (fst ∘ fst (adjT'≃ {suc n} (suc k , k<)) ∘ sucF)
-- -- -- -- -- -- -- --                   (suc ∘ fst)
-- -- -- -- -- -- -- -- sucF'-fst n k k< i x = suc (fst (unglue (i ∨ ~ i) x))

-- -- -- -- -- -- -- -- sucF'-snd : ∀ n k k< → PathP (λ i → (x : ua (adjT'≃ {n = n} (k , k<)) i) →
-- -- -- -- -- -- -- --                                 (sucF'-fst n k k< i x) ≤ n)
-- -- -- -- -- -- -- --                  (λ x → adjT< (suc n) (suc k) (fst (sucF {n = n} x))
-- -- -- -- -- -- -- --                          k< (snd (sucF {n = n} x)))
-- -- -- -- -- -- -- --                  λ x → snd x
-- -- -- -- -- -- -- -- sucF'-snd n k k< =
-- -- -- -- -- -- -- --   isProp→PathP (λ i → isPropΠ λ x → isProp≤ {m = sucF'-fst n k k< i x} {n = n})
-- -- -- -- -- -- -- --     (λ x → adjT< (suc n) (suc k) (suc (fst x)) k< (snd x)) snd

-- -- -- -- -- -- -- -- sucF' : ∀ n k k< → PathP (λ i → ua (adjT'≃ {n = n} (k , k<)) i → Fin (suc n))
-- -- -- -- -- -- -- --                   (fst (adjT'≃ {suc n} (suc k , k<)) ∘ sucF)
-- -- -- -- -- -- -- --                   sucF
-- -- -- -- -- -- -- -- sucF' n k k< i x =
-- -- -- -- -- -- -- --   sucF'-fst n k k< i x ,
-- -- -- -- -- -- -- --    sucF'-snd n k k< i x


-- -- -- -- -- -- -- -- module _ {A : Type ℓ} where

 
-- -- -- -- -- -- -- --  swap-01-× : ∀ {n} → (A ×^ n) → (A ×^ n)
-- -- -- -- -- -- -- --  swap-01-× {zero} = idfun _
-- -- -- -- -- -- -- --  swap-01-× {suc zero} = idfun _
-- -- -- -- -- -- -- --  swap-01-× {suc (suc n)} = swap-01

-- -- -- -- -- -- -- --  invo-swap-01-× : ∀ n → isInvolution (swap-01-× {n})
-- -- -- -- -- -- -- --  invo-swap-01-× zero x = refl
-- -- -- -- -- -- -- --  invo-swap-01-× (suc zero) x = refl
-- -- -- -- -- -- -- --  invo-swap-01-× (suc (suc n)) x = refl

-- -- -- -- -- -- -- --  adjT×^ : ∀ {n} → ℕ →
-- -- -- -- -- -- -- --               (A ×^ n) → (A ×^ n)
-- -- -- -- -- -- -- --  adjT×^ zero = swap-01-×
-- -- -- -- -- -- -- --  adjT×^ {suc n} (suc k) (x , xs) = x , (adjT×^ k xs)
-- -- -- -- -- -- -- --  adjT×^ {zero} (suc k) = idfun _
 
-- -- -- -- -- -- -- --  isEquiv-adjT×^ : ∀ n k → isEquiv (adjT×^ {n} k)
-- -- -- -- -- -- -- --  isEquiv-adjT×^ (suc n) (suc k) =
-- -- -- -- -- -- -- --    snd (≃-× (_ , idIsEquiv _) (_ , isEquiv-adjT×^ n k))
-- -- -- -- -- -- -- --  isEquiv-adjT×^ zero zero = idIsEquiv _
-- -- -- -- -- -- -- --  isEquiv-adjT×^ (suc zero) zero = idIsEquiv _
-- -- -- -- -- -- -- --  isEquiv-adjT×^ (suc (suc n)) zero = snd Σ-swap-01-≃
-- -- -- -- -- -- -- --  isEquiv-adjT×^ zero (suc k) = idIsEquiv _

-- -- -- -- -- -- -- --  adjT×^≃ : ∀ {n} → ℕ → (A ×^ n) ≃ (A ×^ n)
-- -- -- -- -- -- -- --  adjT×^≃ k = adjT×^ k , isEquiv-adjT×^ _ k

-- -- -- -- -- -- -- --  isInvo-adjT×^ : ∀ {n} → ∀ k → isInvolution (adjT×^ {n} k)
-- -- -- -- -- -- -- --  isInvo-adjT×^ zero = invo-swap-01-× _
-- -- -- -- -- -- -- --  isInvo-adjT×^ {zero} (suc k) _ = refl
-- -- -- -- -- -- -- --  isInvo-adjT×^ {suc n} (suc k) (x , xs) =
-- -- -- -- -- -- -- --    cong′ (x ,_) (isInvo-adjT×^ {n} k xs)

-- -- -- -- -- -- -- --  braid-adjT×^ : ∀ {n} → ∀ k →  suc (suc k) < n → ∀ v → 
-- -- -- -- -- -- -- --    (adjT×^  {n} k ∘ adjT×^  {n} (suc k) ∘ adjT×^  {n} (k)) v
-- -- -- -- -- -- -- --    ≡ (adjT×^  {n} (suc k) ∘ adjT×^  {n} (k) ∘ adjT×^  {n} (suc k)) v
-- -- -- -- -- -- -- --  braid-adjT×^ {suc n} (suc k) x (v , vs) = cong′ (v ,_) (braid-adjT×^ {n} k x vs)
-- -- -- -- -- -- -- --  braid-adjT×^ {suc (suc (suc n))} zero x v = refl
 

-- -- -- -- -- -- -- --  comm-adjT×^ : ∀ {n} → ∀ k l → (k< : (suc k) < n) (l< : (suc l) < n) → 
-- -- -- -- -- -- -- --    A.commT k l → ∀ v →  
-- -- -- -- -- -- -- --    (adjT×^  {n} l
-- -- -- -- -- -- -- --      ∘ adjT×^  {n} k ) v
-- -- -- -- -- -- -- --    ≡ (adjT×^  {n} k
-- -- -- -- -- -- -- --      ∘ adjT×^  {n} l ) v
-- -- -- -- -- -- -- --  comm-adjT×^ {n = suc n} (suc k) (suc l) k< l< x (v , vs) =
-- -- -- -- -- -- -- --     cong (v ,_) (comm-adjT×^ {n = n} k l k< l< (A.pred-commT k l x) vs)
-- -- -- -- -- -- -- --  comm-adjT×^ {n = suc (suc n)} zero (suc (suc l)) k< l< x v = refl



-- -- -- -- -- -- -- --  tabEquiv : ∀ n → (Fin n → A) ≃ (A ×^ n)
-- -- -- -- -- -- -- --  tabEquiv n = isoToEquiv (invIso (Iso-×^-F→ n))

    
-- -- -- -- -- -- -- --  zz : ∀ n k → PathP (λ i → (ua (adjT'≃ {n} k) i → A) → (A ×^ n))
-- -- -- -- -- -- -- --         (adjT×^ (fst k) ∘ tabulate)
-- -- -- -- -- -- -- --         (tabulate)           

-- -- -- -- -- -- -- --  zz (suc n) (suc k , k<) i x =
-- -- -- -- -- -- -- --    x (glue (λ { (i = i0) → zero , tt ; (i = i1) → zero , tt }) (0 , tt)) ,
-- -- -- -- -- -- -- --    zz n (k , k<) i
-- -- -- -- -- -- -- --        (x ∘ (λ y → glue (λ { (i = i0) → sucF y ; (i = i1) → sucF y })
-- -- -- -- -- -- -- --          (sucF' n k k< i y)))   
-- -- -- -- -- -- -- --  zz (suc (suc n)) (zero , k<) i x =
-- -- -- -- -- -- -- --    (x (glue (λ { (i = i0) → suc zero , tt ; (i = i1) → zero , tt }) (0 , tt)) ,
-- -- -- -- -- -- -- --     x (glue (λ { (i = i0) → zero , tt ; (i = i1) → suc zero , tt }) (1 , tt)) ,
-- -- -- -- -- -- -- --    tabulate λ y → x (glue (λ { (i = i0) → sucF (sucF y)
-- -- -- -- -- -- -- --                              ; (i = i1) → sucF (sucF y) })
-- -- -- -- -- -- -- --                (sucF (sucF y))))

-- -- -- -- -- -- -- --  ua-adj-lawP : ∀ n k →
-- -- -- -- -- -- -- --        PathP (λ i → (ua (adjT'≃ {n = n} k) i → A) ≃ ua (adjT×^≃ {n = n} (fst k)) i)
-- -- -- -- -- -- -- --                  (tabEquiv n)
-- -- -- -- -- -- -- --                  (tabEquiv n)
-- -- -- -- -- -- -- --  ua-adj-lawP n k = ΣPathPProp isPropIsEquiv
-- -- -- -- -- -- -- --    λ i x → glue (λ { (i = i0) → tabulate x
-- -- -- -- -- -- -- --                    ; (i = i1) → tabulate x }) (zz n k i x) 

-- -- -- -- -- -- -- --  ua-adj-law : ∀ n k →
-- -- -- -- -- -- -- --    Square
-- -- -- -- -- -- -- --        (ua (tabEquiv n))
-- -- -- -- -- -- -- --        (ua (tabEquiv n))
-- -- -- -- -- -- -- --        (λ i → ua (adjT'≃ {n = n} k) i → A)
-- -- -- -- -- -- -- --        (ua (adjT×^≃ {n = n} (fst k)))
       
-- -- -- -- -- -- -- --  ua-adj-law n k i j =
-- -- -- -- -- -- -- --    Glue (ua (adjT×^≃ {n = n} (fst k)) i)
-- -- -- -- -- -- -- --         λ {  (j = i0) → (ua (adjT'≃ {n = n} k) i → A) , ua-adj-lawP n k i
-- -- -- -- -- -- -- --            ; (j = i1) → ua (adjT×^≃ {n = n} (fst k)) i , idEquiv _
-- -- -- -- -- -- -- --            }
