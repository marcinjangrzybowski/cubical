{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.PermutationMore3More where

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

open import Cubical.Data.Nat.Order.PermutationMore3

private
  variable
    ℓ : Level
    A : Type ℓ


Σ≃sq : ∀ {B : Type ℓ} → (p : A ≡ A) → (q : B ≡ B) → {a a' : A} {b b' : B}
            (P : PathP (λ i → p i) a a')
            → (Q : PathP (λ i → q i) b b')
            → SquareP (λ i j → p i × q j)
               (λ j → a , Q j)
               (λ j → a' , Q j)
               (λ i → P i , b)
               λ i → P i , b'
Σ≃sq p q P Q = λ i j → P i , Q j


-- Σ-swap-01-≃≡adjT×^'→0 : {A : Type ℓ} → ∀ n →
--                               Σ-swap-01-≃
--                                ≡ adjT×^≃ {A = A} {n = 2 + n} zero 
-- -- Σ-swap-01-≃≡adjT×^'→0 n = ΣPathP (refl , cong {!equiv-proof!} {!!})
-- fst (Σ-swap-01-≃≡adjT×^'→0 n i) x = fst (snd x) , fst x , snd (snd x)
-- fst (fst (equiv-proof (snd (Σ-swap-01-≃≡adjT×^'→0 n i)) y)) =
--   fst (snd y) , fst y , snd (snd y)
-- snd (fst (equiv-proof (snd (Σ-swap-01-≃≡adjT×^'→0 n i)) y)) =
--   λ _ → fst y , fst (snd y) , snd (snd y)
-- fst (snd (equiv-proof (snd (Σ-swap-01-≃≡adjT×^'→0 n i)) y) y₁ j) = {!!}
-- snd (snd (equiv-proof (snd (Σ-swap-01-≃≡adjT×^'→0 n i)) y) y₁ j) = {!!}

adjT≡ : ∀ n → (Σ ℕ  λ k → (suc k < n)) → (A ×^ n) ≡ (A ×^ n)
adjT≡ (suc (suc n)) (zero , k<) = ua Σ-swap-01-≃
adjT≡ {A = A} (suc (suc n)) (suc k , k<) i = A × adjT≡ {A = A} (suc n) (k , k<) i

adjT≡p : ∀ n k v → PathP (λ j → adjT≡ {A = A} n k j) v (adjT×^'→ (fst k) v)
adjT≡p (suc (suc n)) (zero , k<) v i =
  glue (λ { (i = i0) → _ ; (i =  i1) → _}) (fst (snd v) , fst v , snd (snd v))
adjT≡p (suc (suc n)) (suc k , k<) v i =
  fst v , adjT≡p (suc n) (k , k<) (snd v) i

-- glue-adjT≃-comp : ∀ {ℓ} {A : Type ℓ} → ∀ n k k' → 
--                           SquareP (λ i j → (A ×^ n) →
--                                (adjT×^≃ {A = A} {n = n} k ₑ∙ₚ
--                                    (λ j → ua (adjT×^≃ {A = A} {n = n} k') (j ∧ i))) j)
--                               (ua-gluePathExt (adjT×^≃ k))
--                              (glue-ₑ∙p-comp (adjT×^≃ k) (adjT×^≃ k'))
--                              refl
--                              λ i → (ua-gluePathExt (adjT×^≃ k')) i ∘ fst (adjT×^≃ k)
-- glue-adjT≃-comp n k k' i j = {!!}

-- -- (emcomp (η (suc (suc (fst k)) , snd k ))
-- --                (η (zero , _)) i j)


sucℙrm : ∀ {n} → ℙrm' n → ℙrm' (suc n) 
sucℙrm = gh→em₂→ _ (_ , sucPermGH _)

module _ (isGrpA : isGroupoid A) where
 open 𝕍 isGrpA


 -- glue-adjT≃-comp' : ∀ n k k' → 
 --                           SquareP (λ i j → (A ×^ n) →
 --                                𝕍 {n = n} (emcomp (η k) (η k') i j))
 --                                (ua-gluePathExt (adjT×^≃ (fst k)))
 --                                (glue-ₑ∙p-comp (adjT×^≃ (fst k)) (adjT×^≃ (fst k')))
 --                                refl
 --                                λ i → (ua-gluePathExt (adjT×^≃ (fst k'))) i
 --                                  ∘ fst (adjT×^≃ (fst k))
 -- glue-adjT≃-comp' n k k' i j = {!!}



 ∷𝕍≡ : ∀ n → ∀ a → Relim
      (λ (z : Perm n) →
         PathP (λ i → 𝕍 (emloop z i) → 𝕍 (sucℙrm (emloop z i))) (a ,_) (a ,_))
 Relim.isSetA (∷𝕍≡ n a) x =
   isOfHLevelRetractFromIso 2
     (PathPIsoPath _ _ _)
       (isGroupoidΠ (λ x → isGrp𝕍 embase) _ _  )
 Relim.εA (∷𝕍≡ n a) = refl
 Relim.∷A (∷𝕍≡ (suc n) a) k {xs} X i v =
   glue (λ {(i = i0) → a , v ; (i = i1) → _}) (X i (unglue (i ∨ ~ i) v))
 Relim.invoA (∷𝕍≡ (suc (suc n)) a) k X j i v =
   glue
         (λ {(i = i0) → a , v
                ; (i = i1) → a , v
                ; (j = i0) →
           glue
         (λ { (i = i0) → a , v ; (i = i1) → _ })
         (glue
          (λ { (i = i0) → a , _
             ; (i = i1) → a , _
             })
          (X i (unglue (i ∨ ~ i) (unglue (i ∨ ~ i) v))))
                ; (j = i1) → X i v })
         (X i (unglue (i ∨ ~ i ∨ j ∨ ~ j) v))

 Relim.braidA (∷𝕍≡ (suc (suc (suc n))) a) k k< X j i v = 
      glue
         (λ {(i = i0) → a , v
                ; (i = i1) → a , v
                ; (j = i0) →
                   glue (λ {(i = i0) → _ ; (i = i1) → _})
                     (glue (λ {(i = i0) → _ ; (i = i1) → _})
                        (glue (λ {(i = i0) → _ ; (i = i1) → _})
                        ((X i (unglue (i ∨ ~ i) (unglue (i ∨ ~ i) (unglue (i ∨ ~ i) v)))))))
                ; (j = i1) →
                    glue (λ {(i = i0) → _ ; (i = i1) → _})
                 (glue (λ {(i = i0) → _ ; (i = i1) → _})
                    (glue (λ {(i = i0) → _ ; (i = i1) → _})
                    ((X i (unglue (i ∨ ~ i) (unglue (i ∨ ~ i) (unglue (i ∨ ~ i) v)))))))})
         (X i (unglue (i ∨ ~ i ∨ j ∨ ~ j) v))

 Relim.commA (∷𝕍≡ (suc (suc n)) a) k (suc l , l<) z X j i v = 
         glue
         (λ {(i = i0) → a , v
                ; (i = i1) → a , v
                ; (j = i0) → glue
                  (λ { (i = i0) → _ ; (i = i1) → _ })
                  (glue
                   (λ { (i = i0) → _
                      ; (i = i1) → _
                      })
                   (X i (unglue (i ∨ ~ i) (unglue (i ∨ ~ i) v))))

                ; (j = i1) → glue
                  (λ { (i = i0) → _ ; (i = i1) → _ })
                  (glue
                   (λ { (i = i0) → _
                      ; (i = i1) → _
                      })
                   (X i (unglue (i ∨ ~ i) (unglue (i ∨ ~ i) v))))
           })
         (X i (unglue (i ∨ ~ i ∨ j ∨ ~ j) v))

 ∷𝕍'R : ∀ n → A → EMelim _ λ (em : ℙrm' n) → 𝕍 em → 𝕍 (sucℙrm em) 
 EMelim.isGrpB (∷𝕍'R n a) em = isGroupoidΠ λ _ → isGrp𝕍 (sucℙrm em) 
 EMelim.b (∷𝕍'R n a) = a ,_
 EMelim.bPathP (∷𝕍'R n a) = Relim.f (∷𝕍≡ n a)
 EMelim.bSqP (∷𝕍'R n a) g h = {!RelimProp.f (∷𝕍sq n a)!}
 
 ∷𝕍' : ∀ {n} → (em : ℙrm' n) → A → 𝕍 em → 𝕍 (sucℙrm em) 
 ∷𝕍' {n} em a = EMelim.f (∷𝕍'R n a) em


 _∷𝕍_ : ∀ {n} {em : ℙrm' n} → A → 𝕍 em → 𝕍 (sucℙrm em)
 _∷𝕍_ {n} {em} = ∷𝕍' em

 infixr 5 _∷𝕍_


-- (x y : A) {xs : FMSet2 A} (b : Σ (ℙrm' (len2 xs)) 𝕍) →
--       (sucℙrm (sucℙrm (fst b)) ,
--        ∷𝕍' (sucℙrm (fst b)) x (∷𝕍' (fst b) y (snd b)))
--       ≡
--       (sucℙrm (sucℙrm (fst b)) ,
--        ∷𝕍' (sucℙrm (fst b)) y (∷𝕍' (fst b) x (snd b)))


 -- sq-comm-fill :  ∀ n → (g : Perm n) → ∀ j i →
 --    I → Partial (i ∨ ~ i ∨ j ∨ ~ j) (ℙrm' (suc (suc n)))
 -- sq-comm-fill n g j i =
 --    (λ l → λ {
 --           (j = i0) → emcomp (η (zero , tt)) (sucPerm (sucPerm g)) (~ l) i
 --          ;(j = i1) → emcomp~ _ (sucPerm (sucPerm g)) (η (zero , tt)) (l) i
 --          ;(i = i0) → emloop (sucPerm (sucPerm g)) (l ∧ j)
 --          ;(i = i1) → emloop (sucPerm (sucPerm g)) (~ l ∨ j)
 --          })
 
 -- sq-comm : ∀ n → (g : Perm n)
 --    → Square {A = ℙrm' (suc (suc n))}
 --          (emloop (η (zero , tt)))
 --          (emloop (η (zero , tt)))
 --          (emloop (sucPerm (sucPerm g)))
 --          (emloop (sucPerm (sucPerm g)))
 -- sq-comm n g j i =
 --      hcomp
 --       (sq-comm-fill n g j i) (emloop (sucPermComm g j) i)

 -- zz : ∀ n → ∀ a a' → RelimProp
 --      (λ (g : Perm n) →
 --          SquareP (λ i j → 𝕍 (emloop g i) →
 --             𝕍 (emcomp (η (zero , tt)) (sucPerm (sucPerm g)) i j))
 --               (λ i y → glue (λ { (i = i0) → _ ; (i = i1) → _ }) (a' , a , y))
 --               (λ i y → {!!})
 --               (λ i y → {!!})
 --               (λ i y → ∷𝕍' (sucℙrm (emloop g i)) a' (∷𝕍' (emloop g i) a y))
 --               )
 -- zz = {!!}


 -- ∷𝕍≡-commR : ∀ n → ∀ a a' → RelimProp
 --      (λ (g : Perm n) →
 --          SquareP (λ i j → 𝕍 (emloop g i) → 𝕍 (sq-comm n g i j))
 --               (λ i y → glue (λ { (i = i0) → _ ; (i = i1) → _ }) (a' , a , y))
 --               (λ i y → glue (λ { (i = i0) → _ ; (i = i1) → _ }) (a' , a , y))
 --               (λ i y → ∷𝕍' (sucℙrm (emloop g i)) a (∷𝕍' (emloop g i) a' y))
 --               (λ i y → ∷𝕍' (sucℙrm (emloop g i)) a' (∷𝕍' (emloop g i) a y))
 --               )
 -- RelimProp.isPropA (∷𝕍≡-commR n a a') = {!!}
 -- RelimProp.εA (∷𝕍≡-commR n a a') j i v = 
 --    comp (λ l → 𝕍 (hfill (sq-comm-fill n ε j i)
 --        (inS (emloop (sucPermComm ε j) i)) l))
 --     ((λ l → λ {
 --           (j = i0) → glue (λ { (i = i0) → _ ; (i = i1) → _ }) (a' , a , v)
 --          ;(j = i1) → emcomp∼-fill _ 𝕍 ε ((η (zero , tt)))
 --             refl (λ i → glue (λ { (i = i0) → _ ; (i = i1) → _ }) (a' , a , v))
 --                   (λ i → glue (λ { (i = i0) → _ ; (i = i1) → _ }) (a' , a , v))
 --               (λ l i → glue (λ { (i = i0) → _ ; (i = i1)(l = i1) → _
 --                                 ; (l = i0) → _ }) (a' , a , v))
 --               l i
 --          ;(i = i0) → a , ∷𝕍' (emloop ε (l ∧ j)) a' v 
 --          ;(i = i1) → a' , ∷𝕍' (emloop ε (~ l ∨ j)) a v 
 --          }))
 --     (glue (λ { (i = i0) → _ ; (i = i1) → _ }) (a' , a , v))

 -- RelimProp.∷A (∷𝕍≡-commR (suc (suc n)) a a') k {xs} X j i v = 
 --       comp (λ l → 𝕍 (hfill (sq-comm-fill (suc (suc n)) (k ∷ xs) j i)
 --        (inS (emloop (sucPermComm (k ∷ xs) j) i)) l))
 --     ((λ l → λ {
 --           (j = i0) → {!!}
 --          ;(j = i1) → {!!}
 --            -- emcomp∼-fill _ 𝕍 (k ∷ xs) ((η (zero , tt)))
 --            --  ? ? ? ? 
 --            --    l i
 --          ;(i = i0) → {!!} 
 --          ;(i = i1) → {!!} 
 --          }))
 --     ({!(X j i (unglue (j ∨ ~ j) v))!})


 commΣ : ∀ n → ∀ a a' → (v : A ×^ n) → Path (Σ (ℙrm' (suc (suc n))) 𝕍)
                 (embase , a , a' , v) (embase , a' , a , v)
 commΣ n a a' v = ΣPathP
   (emloop (η (zero , _)) ,
    λ i → glue (λ { (i = i0) → _ ; (i = i1) → _ }) (a' , a , v))




 commAtk : ∀ n → (k : (Σ ℕ  λ k → (suc k < n))) →
         (v : A ×^ n) →
                 Path (Σ (ℙrm' n) 𝕍)
                 (embase , v)
                 (embase , adjT×^'→ (fst k) v)
 fst (commAtk n (k , k<) v i) = emloop (η (k , k<)) i
 snd (commAtk n (k , k<) v i) = ua-gluePathExt (adjT×^≃ k) i v


 ∷𝕍≡-commRem : ∀ n → ∀ a a' → EMelimSet _
           (λ (z : ℙrm' n) → (y : 𝕍 z) →
              Path (Σ (ℙrm' (suc (suc n))) 𝕍)
              ((sucℙrm (sucℙrm z) , ∷𝕍' (sucℙrm z) a (∷𝕍' z a' y)))
              ((sucℙrm (sucℙrm z) , ∷𝕍' (sucℙrm z) a' (∷𝕍' z a y))))
 ∷𝕍≡-commRem = {!!}

--  𝕍≡-≡-adjT≡' : ∀ n k → (k< : (suc k < n)) → 
--        cong′ 𝕍 (emloop (η (k , k<))) ≡ adjT≡ n (k , k<)
--  𝕍≡-≡-adjT≡' (suc (suc n)) zero k< = cong ua (equivEq refl)
--  𝕍≡-≡-adjT≡' (suc (suc (suc n))) (suc k) k< i j = 
--    Glue (A × 𝕍≡-≡-adjT≡' (suc (suc n)) k k< i j)
--              λ { (i = i1) → Σ A (λ _ → adjT≡ (suc (suc n)) (k , k<) j) , idEquiv _
--                ; (i = i0) → ua (adjT×^≃ (suc k)) j ,
--                    ua-unglueEquiv (adjT×^≃ (suc k)) j ∙ₑ
--                      ≃-× (idEquiv _)
--                        (invEquiv (ua-unglueEquiv (adjT×^≃ k) j))
--                ; (j = i0) → Σ A (λ _ → A ×^ suc (suc n)) ,
--                      (λ x → fst x ,
--                        isInvo-adjT×^'→ k (snd x) i) ,
--                         isProp→PathP (λ i → isPropIsEquiv
--                           (λ x → fst x ,
--                        isInvo-adjT×^'→ k (snd x) i))
--                           (snd (ua-unglueEquiv (adjT×^≃ (suc k)) j ∙ₑ
--                      ≃-× (idEquiv _)
--                        (invEquiv (ua-unglueEquiv (adjT×^≃ k) j))))
--                           (idIsEquiv _) i
--                ; (j = i1) → Σ A (λ _ → Σ A (λ _ → A ×^ (suc n))) ,
--                        idfun _ , isPropIsEquiv (idfun _)
--                          (snd (ua-unglueEquiv (adjT×^≃ (suc k)) j ∙ₑ
--                      ≃-× (idEquiv _)
--                        (invEquiv (ua-unglueEquiv (adjT×^≃ k) j))))
--                          (idIsEquiv _) i
--                }
--  𝕍≡-P-adjT≡' : ∀ n → (k : (Σ ℕ  λ k → (suc k < n))) →
--          (v : A ×^ n) →
--            SquareP (λ i j → 𝕍≡-≡-adjT≡' n (fst k) (snd k) i j)
--               (cong snd (commAtk n k v))
--               (adjT≡p n k v)
--               refl
--               refl
--  𝕍≡-P-adjT≡' (suc (suc n)) (zero , k<) v i j = 
--    glue (λ { (j = i0) → _ ; (j =  i1) → _}) (fst (snd v) , fst v , snd (snd v))
--  𝕍≡-P-adjT≡' (suc (suc (suc n))) (suc k , k<) v i j =
--      glue (λ { (i = i0) → ua-gluePathExt (adjT×^≃ (suc k)) j v
--              ; (i = i1) → fst v , adjT≡p (suc (suc  n)) (k , k<) (snd v) j
--              ; (j = i0) → fst v , (snd v)
--              ; (j = i1) → v
--              })
--           (fst v , {!!}) 
 
--  -- ℕ.cases (λ _ ()) (ℕ.cases (λ _ ())
   
-- -- --  𝕍≡-≡-adjT≡ : ∀ n → (k : (Σ ℕ  λ k → (suc k < n))) → 
-- -- --        cong′ 𝕍 (emloop (η k)) ≡ adjT≡ n k
-- -- --  𝕍≡-≡-adjT≡ = ℕ.cases (uncurry λ k ()) (ℕ.cases (uncurry λ k ())
-- -- --    λ n → uncurry (ℕ.cases {!!} {!!}))
-- -- --  -- 𝕍≡-≡-adjT≡ (suc (suc n)) (zero , k<) = cong ua (equivEq refl)
-- -- --  -- 𝕍≡-≡-adjT≡ (suc (suc )) (suc k , k<) i j =
-- -- --  --   Glue (A × 𝕍≡-≡-adjT≡ (suc (suc n)) (k , k<) i j)
-- -- --  --     λ { (i = i1) → {!!} , {!!}
-- -- --  --       ; (i = i0) → {!!} , {!!}
-- -- --  --       ; (j = i0) → (A ×^ (suc (suc (suc n)))) , {!!}
-- -- --  --       ; (j = i1) → (A ×^ (suc (suc (suc n)))) , idEquiv _
-- -- --  --       }
-- -- --    -- isInjectiveTransport (funExt λ x → (ΣPathP (refl ,
-- -- --    --   funExt⁻ (cong transport (𝕍≡-≡-adjT≡ (suc (suc n)) (k , k<))) (snd x) )))

-- -- -- --  𝕍≡-≡-adjT≡-sq : ∀ n → (k : (Σ ℕ  λ k → (suc k < n))) →
-- -- -- --          (v : A ×^ n) → SquareP
-- -- -- --            (λ i j → 𝕍≡-≡-adjT≡ n k i j)
-- -- -- --             (cong snd (commAtk n k v))
-- -- -- --             (adjT≡p n k v)
-- -- -- --             refl
-- -- -- --             refl
-- -- -- --  𝕍≡-≡-adjT≡-sq (suc (suc n)) (zero , k<) v i j =
-- -- -- --     glue
-- -- -- --          (λ { (j = i0) → fst v , fst (snd v) , snd (snd v)
-- -- -- --             ; (j = i1) → fst (snd v) , fst v , snd (snd v)
-- -- -- --             })
-- -- -- --          (fst (snd v) , fst v , snd (snd v))
-- -- -- --  𝕍≡-≡-adjT≡-sq (suc (suc (suc n))) (suc k , k<) v i j = 
-- -- -- --    hcomp
-- -- -- --     (λ l → λ {
-- -- -- --       (i = i0) → {!!}
-- -- -- --      ;(i = i1) → fst v , {!!}
-- -- -- --      ;(j = i0) → {!!}
-- -- -- --      ;(j = i1) → {!!}
-- -- -- --       })
-- -- -- --       {!!}
-- -- -- --     -- (glue {!!} (fst v , 𝕍≡-≡-adjT≡-sq (suc (suc n)) (k , k<) (snd v) i j))
 
-- -- -- -- --    i = i0 ⊢ cong snd (commAtk (suc (suc (suc n))) (suc k , k<) v) j
-- -- -- -- -- i = i1 ⊢ fst v , adjT≡p (suc (suc n)) (k , k<) (snd v) j
-- -- -- -- -- j = i0 ⊢ refl i
-- -- -- -- -- j = i1 ⊢ refl i

-- -- -- -- --  ε-sqΣ : ∀ n → (v : A ×^ n) →
-- -- -- -- --       Square {A = Σ (ℙrm' n) (𝕍 {n = n})}
-- -- -- -- --         (refl {x = embase , v})
-- -- -- -- --         (ΣPathP (emloop ε , refl))
-- -- -- -- --         (refl {x = embase , v})
-- -- -- -- --         (refl {x = embase , v})
-- -- -- -- --  ε-sqΣ n v i j =
-- -- -- -- --    hcomp
-- -- -- -- --      (λ l → primPOr i (~ i ∨ j ∨ ~ j)
-- -- -- -- --         (λ _ → emcomp ε ε j l , v)
-- -- -- -- --         λ _ → emloop ε l , v)
-- -- -- -- --      (embase , v)


-- -- -- -- --  sq-j0 : ∀ n a a' k k< → Square {A = 𝕍 {suc (suc n)} embase
-- -- -- -- --                    → Σ (ℙrm' (suc (suc (suc (suc n))))) 𝕍}
-- -- -- -- --               (λ j y → (commΣ (suc (suc n)) a a' (adjT×^'→ k y)) j)
-- -- -- -- --               (funExt (commΣ (suc (suc n)) a a'))              
-- -- -- -- --               (λ l y → commAtk (suc (suc (suc (suc n))))
-- -- -- -- --                         (suc (suc k) , k<) (a , a' , y) (~ l))
-- -- -- -- --               (λ l y → commAtk (suc (suc (suc (suc n))))
-- -- -- -- --                         (suc (suc k) , k<) (a' , a , y) (~ l))
-- -- -- -- --  sq-j0 n a a' k k< i j v =
-- -- -- -- --       hcomp
-- -- -- -- --     (λ l → λ {
-- -- -- -- --       (i = i0) → emloop (η (zero , tt)) j , {!!}
-- -- -- -- --      ;(i = i1) → emloop (η (zero , tt)) j , {!!}
-- -- -- -- --      ;(j = i0) → emloop (η (suc (suc k) , k<)) (~ i) , {!!}
-- -- -- -- --      ;(j = i1) → emloop (η (suc (suc k) , k<)) (~ i) , {!!}
-- -- -- -- --       })
-- -- -- -- --     {!!}
 
-- -- -- -- -- --  ∷𝕍≡-commR : ∀ n → ∀ a a' →
-- -- -- -- -- --     RelimProp
-- -- -- -- -- --       (λ z →
-- -- -- -- -- --          PathP
-- -- -- -- -- --          (λ i →
-- -- -- -- -- --             (y : 𝕍 (emloop z i)) →
-- -- -- -- -- --             Path (Σ (ℙrm' (suc (suc n))) 𝕍)
-- -- -- -- -- --             (sucℙrm (sucℙrm (emloop z i)) ,
-- -- -- -- -- --              ∷𝕍' (sucℙrm (emloop z i)) a (∷𝕍' (emloop z i) a' y))
-- -- -- -- -- --             (sucℙrm (sucℙrm (emloop z i)) ,
-- -- -- -- -- --              ∷𝕍' (sucℙrm (emloop z i)) a' (∷𝕍' (emloop z i) a y)))
-- -- -- -- -- --          (λ y → commΣ n a a' y) (λ y → commΣ n a a' y))
-- -- -- -- -- --  RelimProp.isPropA (∷𝕍≡-commR n a a') = {!!}
-- -- -- -- -- --  RelimProp.εA (∷𝕍≡-commR n a a') j y i = 
-- -- -- -- -- --    hcomp
-- -- -- -- -- --     (λ l → λ {
-- -- -- -- -- --       (j = i0) → commΣ n a a' y i
-- -- -- -- -- --      ;(j = i1) → commΣ n a a' y i
-- -- -- -- -- --      ;(i = i0) → ε-sqΣ _ (a , a' , y) l j
-- -- -- -- -- --      ;(i = i1) → ε-sqΣ _ (a' , a , y) l j
-- -- -- -- -- --       })
-- -- -- -- -- --     (commΣ n a a' y i)
-- -- -- -- -- --  RelimProp.∷A (∷𝕍≡-commR (suc (suc n')) a a') k {xs} X = {!!}
-- -- -- -- -- --  --   -- λ j y i →
-- -- -- -- -- --  --   -- hcomp
-- -- -- -- -- --  --   --  (λ l → λ {
-- -- -- -- -- --  --   --    (j = i0) → {!!}
-- -- -- -- -- --  --   --   ;(j = i1) → {!!}
-- -- -- -- -- --  --   --   ;(i = i0) → sucℙrm (sucℙrm  (emcomp (η k) xs l j)) ,
-- -- -- -- -- --  --   --       {!!}
-- -- -- -- -- --  --   --   ;(i = i1) → sucℙrm (sucℙrm  (emcomp (η k) xs l j)) ,
-- -- -- -- -- --  --   --       {!!}
-- -- -- -- -- --  --   --    })
-- -- -- -- -- --  --   --   {!!}
-- -- -- -- -- --  --  λ j y i →
-- -- -- -- -- --  --   hcomp
-- -- -- -- -- --  --    (λ l → λ {
-- -- -- -- -- --  --      (j = i0) → sq-j0 l i y
-- -- -- -- -- --  --     ;(j = i1) → commΣ n a a' y i 
-- -- -- -- -- --  --     ;(i = i0) → {!!}
-- -- -- -- -- --  --         --  sucℙrm (sucℙrm  (emcomp~ _ (η k) xs (~ l) j)) ,
-- -- -- -- -- --  --         -- {!!}
-- -- -- -- -- --  --     ;(i = i1) → {!!}
-- -- -- -- -- --  --         -- sucℙrm (sucℙrm  (emcomp~ _ (η k) xs (~ l) j)) ,
-- -- -- -- -- --  --         -- {!!}
-- -- -- -- -- --  --      })
-- -- -- -- -- --  --    (X j (unglue (j ∨ ~ j) y) i)
-- -- -- -- -- --   where
-- -- -- -- -- --   n = (suc (suc n'))
-- -- -- -- -- --   g' = emloop (η k)

-- -- -- -- -- --   sq-j0L : Path ((λ y → embase , a , a' , adjT×^'→ (fst k) y)
-- -- -- -- -- --                  ≡ λ x → embase , a' , a , x)
-- -- -- -- -- --               ((λ i y →
-- -- -- -- -- --          commAtk (suc (suc n)) (suc (suc (fst k)) , snd k) (a , a' , y)
-- -- -- -- -- --          (~ i))
-- -- -- -- -- --       ∙ funExt (commΣ n a a'))
-- -- -- -- -- --           (funExt λ x → ΣPathP ((emloop (η (suc (suc (fst k)) , snd k) · η (zero , _)))
-- -- -- -- -- --                 ,
-- -- -- -- -- --                  -- λ i → {!fst (glue-invol-ₑ∙p {B = A ×^ (suc (suc n))}
-- -- -- -- -- --                  --       (adjT×^≃ {A = A} {suc (suc n)} (suc (suc (fst k))) ∙ₑ ? )
-- -- -- -- -- --                  --             (?) refl i) (a' , a , x)!} 
-- -- -- -- -- --                 {!glue-ₑ∙p-comp ? ? !}
-- -- -- -- -- --             -- λ i → fst ( glue-adjT≃ {A = A} (2 + n) zero refl i
-- -- -- -- -- --             --              ∙ₑ glue-adjT≃ {A = A} (2 + n) (suc (suc (fst k)))
-- -- -- -- -- --             --                   (ua (adjT×^≃ zero)) i)
-- -- -- -- -- --             --                (a' , a , x)
-- -- -- -- -- --                            ))
-- -- -- -- -- --   sq-j0L = transport (PathP≡doubleCompPathˡ refl _ _ _)
-- -- -- -- -- --      λ i j y → emcomp (η (suc (suc (fst k)) , snd k))
-- -- -- -- -- --        (η (zero , _)) i j ,
-- -- -- -- -- --          {!!}

-- -- -- -- -- --   -- sq-j0 : Square {A = 𝕍 {n} embase → Σ (ℙrm' (suc (suc n))) 𝕍}
-- -- -- -- -- --   --             (λ j y → (commΣ n a a' (adjT×^'→ (fst k) y)) j)
-- -- -- -- -- --   --             (funExt (commΣ n a a'))              
-- -- -- -- -- --   --             (λ l y → commAtk (suc (suc n))
-- -- -- -- -- --   --                       (suc (suc (fst k)) , snd k) (a , a' , y) (~ l))
-- -- -- -- -- --   --             (λ l y → commAtk (suc (suc n))
-- -- -- -- -- --   --                       (suc (suc (fst k)) , snd k) (a' , a , y) (~ l))
-- -- -- -- -- --   -- sq-j0 = comm→PathP (
-- -- -- -- -- --   --          sq-j0L
-- -- -- -- -- --   --     -- (transport (PathP≡doubleCompPathˡ refl
           
-- -- -- -- -- --   --     --     ((λ l y → commAtk (suc (suc n))
-- -- -- -- -- --   --     --                   (suc (suc (fst k)) , snd k) (a , a' , y) (~ l)))
-- -- -- -- -- --   --     --      (funExt (λ v → ΣPathP ((emloop (
-- -- -- -- -- --   --     --            η ((suc (suc (fst k)) , snd k))
-- -- -- -- -- --   --     --           · η (zero , _))) ,
-- -- -- -- -- --   --     --               {!!}
-- -- -- -- -- --   --     --            -- λ i → fst ( glue-adjT≃ {A = A} (2 + n) zero refl i
-- -- -- -- -- --   --     --            --         ∙ₑ glue-adjT≃ {A = A} (2 + n) (suc (suc (fst k)))
-- -- -- -- -- --   --     --            --              (ua (adjT×^≃ zero)) i)
-- -- -- -- -- --   --     --            --           (a' , a , v)
-- -- -- -- -- --   --     --                      )))
-- -- -- -- -- --   --     --      (funExt (commΣ n a a'))
-- -- -- -- -- --   --     --      )
-- -- -- -- -- --   --     --      λ i j y → (emcomp (η (suc (suc (fst k)) , snd k ))
-- -- -- -- -- --   --     --          (η (zero , _)) i j) ,
-- -- -- -- -- --   --     --         glue-adjT≃-comp' _ _ _ i j (a , a' , y)  )
-- -- -- -- -- --   --          ◁ --glue-adjT≃ n zero ?
-- -- -- -- -- --   --       (λ i j x → (emloop
-- -- -- -- -- --   --          ((comm (suc (suc (fst k)) , snd k) (zero , _) _ ε i)) j ) ,
-- -- -- -- -- --   --            glue (λ {
-- -- -- -- -- --   --                  (i = i0) → {!!}
-- -- -- -- -- --   --                   -- fst ( glue-adjT≃ {A = A} (2 + n) zero refl j
-- -- -- -- -- --   --                   --      ∙ₑ glue-adjT≃ {A = A} (2 + n) (suc (suc (fst k)))
-- -- -- -- -- --   --                   --           (ua (adjT×^≃ zero)) j)
-- -- -- -- -- --   --                   --        (a' , a , x)
-- -- -- -- -- --   --                ; (i = i1) →
-- -- -- -- -- --   --                   fst ( glue-adjT≃ {A = A} (2 + n) (suc (suc (fst k))) refl j
-- -- -- -- -- --   --                        ∙ₑ glue-adjT≃ {A = A} (2 + n) zero
-- -- -- -- -- --   --                             (ua (adjT×^≃ (suc (suc (fst k))))) j)
-- -- -- -- -- --   --                          (a' , a , x)
-- -- -- -- -- --   --                ; (j = i0) → a , a' , adjT×^'→ (fst k) x
-- -- -- -- -- --   --                ; (j = i1) → a' , a , x
-- -- -- -- -- --   --                }) {!!} )
-- -- -- -- -- --   --       ▷ {!!}
-- -- -- -- -- --   --     -- comm→PathP (transport (PathP≡doubleCompPathˡ refl _ _ _)
-- -- -- -- -- --   --     --      (λ i j x → emcomp (η (zero , _))
-- -- -- -- -- --   --     --                         (η (suc (suc (fst k)) , snd k)) i j ,
-- -- -- -- -- --   --     --          {! (fst (glue-invol-ₑ∙p ? ? ? i))!})) ◁
-- -- -- -- -- --   --     -- {!!}
-- -- -- -- -- --   --     -- ▷ {!!}
-- -- -- -- -- --   --     )

-- -- -- -- -- -- -- comm→PathP (transport (PathP≡doubleCompPathˡ refl _ _ _)
-- -- -- -- -- -- --     (λ i j x → {!!} , {!!})
-- -- -- -- -- -- --      ◁ {!!} ▷
-- -- -- -- -- -- --      {!!})

-- -- -- -- -- -- -- j = i0 ⊢ commΣ (suc (suc n')) a a' y i
-- -- -- -- -- -- -- j = i1 ⊢ commΣ (suc (suc n')) a a' y i
-- -- -- -- -- -- -- i = i0 ⊢ sucℙrm (sucℙrm (emloop (k ∷ xs) j)) ,
-- -- -- -- -- -- --          ∷𝕍' (sucℙrm (emloop (k ∷ xs) j)) a (∷𝕍' (emloop (k ∷ xs) j) a' y)
-- -- -- -- -- -- -- i = i1 ⊢ sucℙrm (sucℙrm (emloop (k ∷ xs) j)) ,
-- -- -- -- -- -- --          ∷𝕍' (sucℙrm (emloop (k ∷ xs) j)) a' (∷𝕍' (emloop (k ∷ xs) j) a y)

-- -- -- -- -- --  ∷𝕍≡-commRem : ∀ n → ∀ a a' → EMelimSet _
-- -- -- -- -- --            (λ (z : ℙrm' n) → (y : 𝕍 z) →
-- -- -- -- -- --               Path (Σ (ℙrm' (suc (suc n))) 𝕍)
-- -- -- -- -- --               ((sucℙrm (sucℙrm z) , ∷𝕍' (sucℙrm z) a (∷𝕍' z a' y)))
-- -- -- -- -- --               ((sucℙrm (sucℙrm z) , ∷𝕍' (sucℙrm z) a' (∷𝕍' z a y))))
-- -- -- -- -- --  EMelimSet.isSetB (∷𝕍≡-commRem n a a') _ =
-- -- -- -- -- --    isSetΠ λ _ → isGroupoidΣ emsquash isGrp𝕍 _ _
-- -- -- -- -- --  EMelimSet.b (∷𝕍≡-commRem n a a') y = commΣ n a a' y  
-- -- -- -- -- --  EMelimSet.bPathP (∷𝕍≡-commRem n a a') =
-- -- -- -- -- --   RelimProp.f (∷𝕍≡-commR n a a')
-- -- -- -- -- --  -- fst (EMelimSet.bPathP (∷𝕍≡-commRem n a a') g i y j) = sq-comm n g i j
-- -- -- -- -- --  -- snd (EMelimSet.bPathP (∷𝕍≡-commRem n a a') g j v i) =
-- -- -- -- -- --  --   RelimProp.f (∷𝕍≡-commR n a a') g j i v





-- -- -- -- -- --  -- -- tab : ∀ {n} → A ×^ n → FMSet2 A
-- -- -- -- -- --  -- -- tab {zero} _ = []
-- -- -- -- -- --  -- -- tab {suc n} (x , xs) = x ∷2 (tab xs)

-- -- -- -- -- --  -- -- to𝕍R : RElim (λ z → Σ (ℙrm' (len2 z)) 𝕍)
-- -- -- -- -- --  -- -- RElim.[]* to𝕍R = embase , tt*
-- -- -- -- -- --  -- -- (to𝕍R RElim.∷* a) xs = sucℙrm (fst xs) , ∷𝕍' (fst xs) a (snd xs)
-- -- -- -- -- --  -- -- RElim.comm* to𝕍R = {!!}
-- -- -- -- -- --  -- -- RElim.comm-inv* to𝕍R = {!!}
-- -- -- -- -- --  -- -- RElim.hexDiag* to𝕍R = {!!}
-- -- -- -- -- --  -- -- RElim.hexU* to𝕍R = {!!}
-- -- -- -- -- --  -- -- RElim.hexL* to𝕍R = {!!}
-- -- -- -- -- --  -- -- RElim.trunc* to𝕍R = {!!}

-- -- -- -- -- --  -- -- -- to𝕍 : (fm : FMSet2 A) → Σ (ℙrm' (len2 fm)) 𝕍
-- -- -- -- -- --  -- -- -- to𝕍 = RElim.f to𝕍R

-- -- -- -- -- --  -- -- -- from𝕍 : ∀ {n} →  (em : ℙrm' n) →
-- -- -- -- -- --  -- -- --               𝕍 em → FMSet2 A
-- -- -- -- -- --  -- -- -- from𝕍 {n'} = EMelim.f (w {n'})
-- -- -- -- -- --  -- -- --  where
-- -- -- -- -- --  -- -- --  open EMelim

-- -- -- -- -- --  -- -- --  open Relim

-- -- -- -- -- --  -- -- --  adjT→comm : ∀ n (k : Σ ℕ  λ k → (suc k < n)) → (v : A ×^ n) → tab (adjT×^'→ (fst k) v) ≡
-- -- -- -- -- --  -- -- --                                       tab v
-- -- -- -- -- --  -- -- --  adjT→comm (suc (suc n)) (zero , k<) v = comm _ _ _
-- -- -- -- -- --  -- -- --  adjT→comm (suc (suc n)) (suc k , k<) v =
-- -- -- -- -- --  -- -- --    cong (fst v ∷2_) (adjT→comm (suc n) (k , k<) (snd v))

-- -- -- -- -- --  -- -- --  w≡ : ∀ {n} → Relim
-- -- -- -- -- --  -- -- --       (λ z →
-- -- -- -- -- --  -- -- --          PathP (λ i → 𝕍 (emloop z i) → FMSet2 A) (tab) (tab))
-- -- -- -- -- --  -- -- --  isSetA w≡ _ = {!!}
-- -- -- -- -- --  -- -- --  εA w≡ = refl
-- -- -- -- -- --  -- -- --  -- ∷A (w≡ {zero}) (k , ())
-- -- -- -- -- --  -- -- --  -- ∷A (w≡ {suc zero}) (k , ())
-- -- -- -- -- --  -- -- --  ∷A (w≡ {n}) k {xs} X i v =
-- -- -- -- -- --  -- -- --     hcomp (λ j → λ {
-- -- -- -- -- --  -- -- --            (i = i0) → adjT→comm n k v j
-- -- -- -- -- --  -- -- --          ; (i = i1) → tab v
-- -- -- -- -- --  -- -- --        }) (X i (unglue (i ∨ ~ i) v))
-- -- -- -- -- --  -- -- --  invoA w≡ = {!!}
-- -- -- -- -- --  -- -- --  braidA w≡ = {!!}
-- -- -- -- -- --  -- -- --  commA w≡ = {!!}


-- -- -- -- -- --  -- -- --  w : ∀ {n} → EMelim (PermG n) (λ z → 𝕍 z → FMSet2 A)
-- -- -- -- -- --  -- -- --  isGrpB w x = isGroupoidΠ λ _ → trunc
-- -- -- -- -- --  -- -- --  b w = tab
-- -- -- -- -- --  -- -- --  bPathP (w {n}) = Relim.f (w≡ {n})
-- -- -- -- -- --  -- -- --  bSqP w = {!!}


-- -- -- -- -- --  -- -- -- -- from𝕍 : {A : Type ℓ} → (isGrpA : isGroupoid A) → ∀ n →  (em : ℙrm' n) →
-- -- -- -- -- --  -- -- -- --               𝕍 isGrpA n em → FMSet2 A
-- -- -- -- -- --  -- -- -- -- from𝕍 {A = A} isGrpA n' = EMelim.f (w {n'})
-- -- -- -- -- --  -- -- -- --  where
-- -- -- -- -- --  -- -- -- --  open EMelim

-- -- -- -- -- --  -- -- -- --  open Relim


-- -- -- -- -- --  -- -- -- --  w : ∀ {n} → EMelim (PermG n) (λ z → 𝕍 isGrpA n z → FMSet2 A)
-- -- -- -- -- --  -- -- -- --  isGrpB w x = isGroupoidΠ λ _ → trunc
-- -- -- -- -- --  -- -- -- --  b w = wB
-- -- -- -- -- --  -- -- -- --  bPathP (w {n}) = Relim.f (w≡ {n})
-- -- -- -- -- --  -- -- -- --  bSqP w = {!!}
