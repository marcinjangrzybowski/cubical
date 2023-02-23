{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.PermutationMore3 where

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

infixr 30 _ₑ∙ₚ_

_ₑ∙ₚ_ : ∀ {ℓ} {A B C : Type ℓ} → A ≃ B → B ≡ C → A ≡ C 
(e ₑ∙ₚ p) i = Glue (p i) 
    λ { (i = i0) → _ , e
      ; (i = i1) → _ , idEquiv _
      }


ₑ∙ₚ-ua : ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) → (p : B ≡ C) →
          Square
             (ua e)
             (e ₑ∙ₚ p)             
             refl
             p
ₑ∙ₚ-ua {A = A} e p j i =
  Glue (p (j ∧ i) ) 
    λ { (i = i0) → A , e 
      ; (i = i1) → p j , idEquiv (p j)
      }

ₑ∙ₚ-fill : ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) → (p : B ≡ C) →
          Square
             (e ₑ∙ₚ p)
             p
             (ua e)
             refl
ₑ∙ₚ-fill {A = A} e p j i =
    Glue
       (p i)
       λ { (j = i0)(i = i0) → _ , e
          ; (i = i1) → _ , idEquiv (p i1)
          ; (j = i1) → _ , idEquiv (p i)
          }

ₑ∙ₚ≡∙ : ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) (p : A ≡ B)
               → (q q' : B ≡ C) → ua e ≡ p → q ≡ q'
               → e ₑ∙ₚ q ≡ p ∙ q'
ₑ∙ₚ≡∙ {A = A} e p q q' ep qq' i j =
  hcomp
    (λ k → λ { ( i = i0) → ₑ∙ₚ-ua e q k j
               ; (j = i0) → A
               ; (j = i1) → qq' i k
               }) (ep i j)


ₑ∙ₚ-compSq :  ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) → (f : B ≃ C)
            → PathP (λ j → A ≃ ua f j)
                   e
                  (e ∙ₑ f)
fst (ₑ∙ₚ-compSq e f j) = ua-gluePathExt f j ∘ fst e
snd (ₑ∙ₚ-compSq e f j) = isProp→PathP (λ j → isPropIsEquiv (ua-gluePathExt f j ∘ fst e))
    (snd e) (snd (e ∙ₑ f)) j

ₑ∙ₚ-comp :  ∀ {ℓ} {A B C D : Type ℓ} → (e : A ≃ B) → (f : B ≃ C) → (p : C ≡ D) →
                  e ₑ∙ₚ f ₑ∙ₚ p ≡ (e ∙ₑ f) ₑ∙ₚ p  
ₑ∙ₚ-comp {A = A} {B} {C} {D} e f p j i =
   Glue (ₑ∙ₚ-fill f p j i) 
    λ { (i = i0) → A , ₑ∙ₚ-compSq e f j
      ; (i = i1) → D , idEquiv D
      }


-- ₑ∙ₚ-comp³eq-fill :  ∀ {ℓ} {A B : Type ℓ}
--             → (e : A ≃ A) → (f : A ≃ A) → (p : A ≡ B)
--             → e ∙ₑ f ∙ₑ e ≡ f ∙ₑ e ∙ₑ f 
--             → Square (f ₑ∙ₚ e ₑ∙ₚ p)
--                       (e ₑ∙ₚ f ₑ∙ₚ p)
--                       {!ua!}
--                       {!!}
            
-- ₑ∙ₚ-comp³eq-fill = {!!}


unglue-ₑ∙p : ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) → (X : B ≡ C)
                → PathP (λ i → (e ₑ∙ₚ X) i ≃ X i) e (idEquiv _) 
unglue-ₑ∙p e X =
  ΣPathPProp (λ _ → isPropIsEquiv _)
   λ i x → unglue (i ∨ ~ i) x 

glue-ₑ∙p-comp : ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) (f : B ≃ C) 
                → PathP (λ i → A → (e ₑ∙ₚ (f ₑ∙ₚ refl)) i) (idfun _)
                    (fst  (e ∙ₑ f)) 
glue-ₑ∙p-comp e f i x =
  glue (λ { (i = i0) → x
           ; (i = i1) → fst (e ∙ₑ f) x }  )
              (glue (λ { (i = i0) → fst e x
                        ; (i = i1) → fst (e ∙ₑ f) x }  ) (fst (e ∙ₑ f) x))


ₑ∙ₚ-comp²eq-sides :
   ∀ {ℓ} {A B : Type ℓ}
            → (e : A ≃ A) → (f : A ≃ A) → (p : A ≡ B) 
            → f ∙ₑ e ≡ e ∙ₑ f → ∀ j i
            → Partial (j ∨ ~ j ∨ i ∨ ~ i) (Σ (Type ℓ) (λ T → T ≃ p i))
ₑ∙ₚ-comp²eq-sides {A = A} {B} e f p x j i =
      λ {
        (i = i0) → A , x j
      ; (i = i1) → B , (idEquiv B ∙ₑ idEquiv B)
      ; (j = i0) → (f ₑ∙ₚ e ₑ∙ₚ p) i ,
              unglue-ₑ∙p f (e ₑ∙ₚ p) i
            ∙ₑ unglue-ₑ∙p e p i
      ; (j = i1) → ( e ₑ∙ₚ f ₑ∙ₚ p) i ,
            unglue-ₑ∙p e (f ₑ∙ₚ p) i
            ∙ₑ unglue-ₑ∙p f p i
      }


ₑ∙ₚ-comp²eq :  ∀ {ℓ} {A B : Type ℓ}
            → (e : A ≃ A) → (f : A ≃ A) → (p : A ≡ B) 
            → f ∙ₑ e ≡ e ∙ₑ f 
            →  f ₑ∙ₚ e ₑ∙ₚ p ≡ e ₑ∙ₚ f ₑ∙ₚ p  
ₑ∙ₚ-comp²eq {A = A} {B} e f p x j i =
   Glue (p i) (ₑ∙ₚ-comp²eq-sides e f p x j i)


ₑ∙ₚ-comp³eq-sides :
   ∀ {ℓ} {A B : Type ℓ}
            → (e : A ≃ A) → (f : A ≃ A) → (p : A ≡ B) 
            → e ∙ₑ f ∙ₑ e ≡ f ∙ₑ e ∙ₑ f  → ∀ j i
            → Partial (j ∨ ~ j ∨ i ∨ ~ i) (Σ (Type ℓ) (λ T → T ≃ p i))
ₑ∙ₚ-comp³eq-sides {A = A} {B} e f p x j i =
      λ {
        (i = i0) → A , x j
      ; (i = i1) → B , compEquiv (idEquiv B) (idEquiv B ∙ₑ idEquiv B)
      ; (j = i0) → ( e ₑ∙ₚ f ₑ∙ₚ e ₑ∙ₚ p) i ,
              unglue-ₑ∙p e (f ₑ∙ₚ e ₑ∙ₚ p) i
            ∙ₑ unglue-ₑ∙p f (e ₑ∙ₚ p) i
            ∙ₑ unglue-ₑ∙p e p i
      ; (j = i1) → ( f ₑ∙ₚ e ₑ∙ₚ f ₑ∙ₚ p) i ,
            unglue-ₑ∙p f (e ₑ∙ₚ f ₑ∙ₚ p) i
            ∙ₑ unglue-ₑ∙p e (f ₑ∙ₚ p) i
            ∙ₑ unglue-ₑ∙p f p i
      }


ₑ∙ₚ-comp³eq :  ∀ {ℓ} {A B : Type ℓ}
            → (e : A ≃ A) → (f : A ≃ A) → (p : A ≡ B) 
            → e ∙ₑ f ∙ₑ e ≡ f ∙ₑ e ∙ₑ f 
            →  e ₑ∙ₚ f ₑ∙ₚ e ₑ∙ₚ p ≡ f ₑ∙ₚ e ₑ∙ₚ f ₑ∙ₚ p  
ₑ∙ₚ-comp³eq {A = A} {B} e f p x j i =
   Glue (p i)
     (ₑ∙ₚ-comp³eq-sides {A = A} {B} e f p x j i)




-- glue-invol-ₑ∙ₚ : ∀ {ℓ} {A B : Type ℓ} → (f : A → A) →
--     (fInvol : isInvolution f)  → (X : A ≡ B)
--         → PathP (λ i → X i ≃ (involEquiv {f = f} fInvol ₑ∙ₚ X) i)
           
--            (involEquiv {f = f} fInvol)
--            (idEquiv _)
-- glue-invol-ₑ∙ₚ f fInvol X =
--    ΣPathP ( ({!!} ◁
--               λ i → λ x → glue (λ {(i = i0) → f x ; (i = i1) → x })
--                 {!x!})
--     , {!!})
  -- e' i ,
  --        isProp→PathP (λ i → isPropIsEquiv (e' i))
  --          (snd e)
  --          (idIsEquiv _) i


glue-invol-ₑ∙p : ∀ {ℓ} {A B : Type ℓ} → (e : A ≃ A) →
    (fInvol : isInvolution (fst e))  → (X : A ≡ B)
        → PathP (λ i → X i ≃ (e ₑ∙ₚ X) i) e (idEquiv _)
glue-invol-ₑ∙p e eInvol X i =
  e' i ,
         isProp→PathP (λ i → isPropIsEquiv (e' i))
           (snd e)
           (idIsEquiv _) i

  where
    e' : ∀ i → X i → (e ₑ∙ₚ X) i
    e' i = (λ x → glue (λ { (i = i0) → _
          ; (i = i1) → _ })
       (hcomp (λ k → λ {(i = i0) → eInvol x (~ k)
                       ;(i = i1) → x
            }) x))




invol-ₑ∙pSides : ∀ {ℓ} {A B : Type ℓ} → (e : A ≃ A) →
    (fInvol : isInvolution (fst e))  → (X : A ≡ B)
                → ∀ j i → Partial (j ∨ ~ j ∨ i ∨ ~ i)
                 (Σ (Type ℓ) (λ T → T ≃ X i))
invol-ₑ∙pSides {A = A} {B = B} e eInvol X j i =
         (λ { (i = i0) → A ,
                equivEq {e = e ∙ₑ e} {f = idEquiv _} (funExt eInvol) j

          ; (i = i1) → B , equivEq
               {e = idEquiv _ ∙ₑ idEquiv _}
               {f = idEquiv _} refl j
          ; (j = i0) → _ ,
             (unglue-ₑ∙p e (e ₑ∙ₚ X) i) ∙ₑ (unglue-ₑ∙p e X i)

          ; (j = i1) → X i , idEquiv _
          })


invol-ₑ∙p : ∀ {ℓ} {A B : Type ℓ} → (e : A ≃ A) →
    (fInvol : isInvolution (fst e))  → (X : A ≡ B)
                → Square
                   (e ₑ∙ₚ e ₑ∙ₚ X )
                   X
                   (λ _ → A)
                   (λ _ → B)
invol-ₑ∙p {A = A} {B = B} e eInvol X j i =
 Glue (X i) (invol-ₑ∙pSides e eInvol X j i)


invol-ₑ∙pSq-reflTy : ∀ {ℓ} {A : Type ℓ} → (f : A → A) →
    (fInvol : isInvolution f)
     → Type (ℓ-suc ℓ)
invol-ₑ∙pSq-reflTy {A = A} f fInvol =
 let e = (involEquiv {f = f} fInvol)
 in Cube
     (invol-ₑ∙p e fInvol refl)
     (ua-CompFill∙ₑ e e)
     (symP-fromGoal (ₑ∙ₚ-ua e (e ₑ∙ₚ refl)))
     (λ i j → Glue A
       λ {  (j = i0) → A , equivEq {e = idEquiv _} {f = e ∙ₑ e} (sym (funExt fInvol)) i
          ; (j = i1) → A , idEquiv _
          ; (i = i0) → A , idEquiv _
          })
     (λ _ _ → A)
     λ j i → ua (involEquiv {f = f} fInvol) (i ∨ ~ j)

   


-- sqInv : (e : A ≃ A) → isInvolution (fst e) →
--            PathP (λ j → A ≃ ua e j) e (idEquiv A)
-- sqInv e eInvol j = {!!}

-- invol-ₑ∙p-refl : (e : A ≃ A) →
--     (fInvol : isInvolution (fst e))
--                 → Square
--                    (e ₑ∙ₚ e ₑ∙ₚ refl)
--                    refl
--                    (λ _ → A)
--                    (λ _ → A)
-- invol-ₑ∙p-refl {A = A} e fInvol j i =
--    Glue (ₑ∙ₚ-fill e refl j i)
--      λ {(i = i0) → A , ₑ∙ₚ-compSq e e j
--        ;(i = i1) → A , idEquiv A
--        ;(j = i1) → A , equivEq {e = (e ∙ₑ e)} {idEquiv A} (funExt fInvol) i
--         }

invol-ₑ∙pSq : ∀ {ℓ} {A B : Type ℓ} → (e : A ≃ A) →
    (eInvol : isInvolution (fst e))  → (X : A ≡ B)
                → PathP (λ l →
                     Square
                   (e ₑ∙ₚ e ₑ∙ₚ λ i → X (i ∧ l))
                   (λ i → X (i ∧ l))
                   (λ _ → A)
                   (λ _ → X l))
                     (invol-ₑ∙p e eInvol refl) (invol-ₑ∙p e eInvol X)
invol-ₑ∙pSq {A = A} {B = B} e eInvol X
  = λ l → invol-ₑ∙p e eInvol λ i → X (i ∧ l)



unglue-invol-ₑ∙p : ∀ {ℓ} {A B : Type ℓ} → (e : A ≃ A) →
    (fInvol : isInvolution (fst e))  → (X : A ≡ B)
                →  SquareP (λ j i → invol-ₑ∙p e fInvol X j i ≃ X i)
                     (λ i → unglue-ₑ∙p e (e ₑ∙ₚ X) i ∙ₑ unglue-ₑ∙p e X i)
                     (λ _ → idEquiv _)
                     (equivEq (funExt fInvol))
                     (equivEq refl)
                     
fst (unglue-invol-ₑ∙p e eInvol X j i) x =
 unglue (j ∨ ~ j ∨ i ∨ ~ i)
   {e = λ o → snd (invol-ₑ∙pSides e eInvol X j i o)} x
 
snd (unglue-invol-ₑ∙p e eInvol X j i) =
 let z = (λ j i → isPropIsEquiv
         (λ x → unglue (j ∨ ~ j ∨ i ∨ ~ i)
            {e = λ o → snd (invol-ₑ∙pSides e eInvol X j i o)} x))

 in isProp→SquareP z
    (isProp→PathP (λ j → z j i0) _ _)
    (isProp→PathP (λ j → z j i1) _ _)
    (λ i → snd (unglue-ₑ∙p e (e ₑ∙ₚ X) i ∙ₑ unglue-ₑ∙p e X i))
    (λ i → idIsEquiv _)
    j i



w∷ : ∀ n → Σ ℕ (λ k → suc k < n) → Fin n ≡ Fin n → Fin n ≡ Fin n
w∷ n k = (adjT'≃ {n = n} k) ₑ∙ₚ_

w∷≃ : ∀ n k → (X : Fin n ≡ Fin n) 
       → ∀ j → w∷ n k X j ≃ X j
w∷≃ n k X j = unglue-ₑ∙p (adjT'≃ {n = n} k) X j


w∷invo : ∀ n k X → w∷ n k (w∷ n k X) ≡ X  
w∷invo n k X i j = invol-ₑ∙p (adjT'≃ {n = n} k) (isInvolution-adjT n k) X i j 

w∷invo-unglue≃ : ∀ n k X → ∀ i j → w∷invo n k X i j ≃ X j
w∷invo-unglue≃ n k X i j =
   unglue-invol-ₑ∙p (adjT'≃ {n = n} k) (isInvolution-adjT n k) X i j 

permFin : ∀ n → Perm n → Fin n ≡ Fin n 
permFin n = Rrec.f (w)
 where


 w : Rrec {n = n} (Fin n ≡ Fin n)
 Rrec.isSetA (w) = isOfHLevel≡ 2 (isSetFin {n = n}) (isSetFin {n = n})
 Rrec.εA w = refl
 Rrec.∷A (w) = w∷ n
 Rrec.invoA (w) = w∷invo n      
 Rrec.braidA (w) k k< _ =
       ₑ∙ₚ-comp³eq _ _ _
    (equivEq (cong (Iso.fun ∘ permuteIso n) (braid k k< ε)))
 Rrec.commA w k l x X =
     ₑ∙ₚ-comp²eq _ _ _
       ((equivEq (cong (Iso.fun ∘ permuteIso n) (comm k l x ε))))

ℙrm : ℕ → Type
ℙrm n = EM₁ (Symmetric-Group (Fin n) (isSetFin {n}))

ℙrm' : ℕ → Type
ℙrm' n = EM₁ (PermG n)



h𝔽in' : ∀ n → ℙrm' n → hSet ℓ-zero
h𝔽in' n = EMrec.f w
 where
  w : EMrec _ isGroupoidHSet
  EMrec.b w = _ , isSetFin {n}
  EMrec.bloop w g = 
    TypeOfHLevel≡ 2 (permFin n g)
  EMrec.bComp w g h = 
    ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
      (RelimProp.f {n = n} w∷compR g)

   where
   w∷compR : RelimProp
      (λ z → Square (permFin n z) (permFin n (z · h)) refl (permFin n h))
   RelimProp.isPropA w∷compR _ =
      isOfHLevelRetractFromIso
         1
         (invIso PathP→comm-Iso)
           (isOfHLevel≡ 2 (isSetFin {n = n}) (isSetFin {n = n})
             _ _ )
   RelimProp.εA w∷compR i j = permFin n h (i ∧ j)
   RelimProp.∷A w∷compR k {xs} X j = (adjT'≃ {n = n} k) ₑ∙ₚ (X j)


𝔽in' : ∀ n → ℙrm' n → Type ℓ-zero
𝔽in'  n = fst ∘ h𝔽in' n 

-- dom-ₑ∙p : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : ∀ j i → Type ℓ'}
--               → (f : A → A) → (fInvol : isInvolution f)
--                 {X : (A → B i1 i0) ≡ (A' → B i1 i1)}
--                 {X' : A ≡ A'} 
                                
--               → (P : Square
--                       (λ i → X' i → B i0 i)
--                       X
--                       (λ j → A → B j i0)-
--                       (λ j → A' → B j i1))
--               → Square  
--                   (λ i →
--                     {!!} → B i0 i)
--                   (λ i → ((preCompInvol.e' {f = f} (B i1 i) fInvol) ₑ∙ₚ λ i' → {!X i'!}) i)
--                   {!!}
--                   {!!}
--               -- → (λ i →  ((involEquiv {f = f} fInvol) ₑ∙ₚ X') i → B )
--               --   ≡ ((preCompInvol.e' {f = f} B fInvol) ₑ∙ₚ X)
-- dom-ₑ∙p {A = A} {A'} {B = B} f fInvol {X} {X' = X'} P j i = {!!}



dom-ₑ∙p-sides : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : ∀ j i → Type ℓ'}
              → (f : A → A) → (fInvol : isInvolution f)
                {X : (A → B i1 i0) ≡ (A' → B i1 i1)}
                {X' : A ≡ A'} 
                                
              → (P : Square
                      (λ i → X' i → B i0 i)
                      X
                      (λ j → A → B j i0)
                      (λ j → A' → B j i1))
              → ∀ j i
              → Partial (~ j ∨ i ∨ ~ i)
                  (Σ (Type (ℓ-max ℓ ℓ')) (λ T → T ≃ P j i)) 
dom-ₑ∙p-sides {A = A} {A'} {B = B} f fInvol {X} {X' = X'} P j i = 
   let e = (involEquiv {f = f} fInvol)
  in λ {
      (i = i0) → (A → B j i0) , preCompInvol.e' {f = f} (B j i) fInvol
    ; (i = i1) → (A' → B j i1) , idEquiv _
    ; (j = i0) → ((e ₑ∙ₚ X') i → B i0 i) ,
            (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)) ,
            isProp→PathP
              (λ i → isPropIsEquiv {A = (e ₑ∙ₚ X') i → B j i} {B = X' i → B i0 i}
                (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)))
              (snd (preCompInvol.e' {f = f} (B j i0) fInvol))
              (idIsEquiv _) i
      }


-- dom-ₑ∙p-sides : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : Type ℓ'}
--               → (f : A → A) → (fInvol : isInvolution f) 
--                 {X : (A → B) ≡ (A' → B)}
--                 {X' : A ≡ A'}
--               → (P : (λ i → X' i → B) ≡ X)
--               → ∀ j i
--               → Partial (~ j ∨ i ∨ ~ i)
--                   (Σ (Type (ℓ-max ℓ ℓ')) (λ T → T ≃ P j i)) 
-- dom-ₑ∙p-sides {A = A} {A'} {B = B} f fInvol {X} {X' = X'} P j i =
--    let e = (involEquiv {f = f} fInvol)
--   in λ {
--       (i = i0) → (A → B) , preCompInvol.e' {f = f} B fInvol
--     ; (i = i1) → (A' → B) , idEquiv _
--     ; (j = i0) → ((e ₑ∙ₚ X') i → B) ,
--             (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)) ,
--             isProp→PathP
--               (λ i → isPropIsEquiv {A = (e ₑ∙ₚ X') i → B} {B = X' i → B}
--                 (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)))
--               (snd (preCompInvol.e' {f = f} B fInvol))
--               (idIsEquiv _) i
--       }

dom-ₑ∙p : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : Type ℓ'}
              → (f : A → A) → (fInvol : isInvolution f) 
                {X : (A → B) ≡ (A' → B)}
                {X' : A ≡ A'}
              → (P : (λ i → X' i → B) ≡ X)
              → (λ i →  ((involEquiv {f = f} fInvol) ₑ∙ₚ X') i → B )
                ≡ ((preCompInvol.e' {f = f} B fInvol) ₑ∙ₚ X)
dom-ₑ∙p {A = A} {A'} {B = B} f fInvol {X} {X' = X'} P j i = 
  let e = (involEquiv {f = f} fInvol)
  in Glue (P j i) (dom-ₑ∙p-sides {A = A} {A'} {B = λ _ _ → B} f fInvol {X} {X' = X'} P j i)



unglue-dom-ₑ∙p : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : Type ℓ'}
              → (f : A → A) → (fInvol : isInvolution f) 
                {X : (A → B) ≡ (A' → B)}
                {X' : A ≡ A'}
              → (P : (λ i → X' i → B) ≡ X)
              → SquareP
                (λ j i →
                dom-ₑ∙p {A = A} {A'} {B = B} f fInvol {X} {X' = X'} P j i
                 ≃  P j i)
                     (λ i → (λ x y → x (fst (glue-invol-ₑ∙p
                          (involEquiv {f = f} fInvol) fInvol X' i) y))
                       , unglueIsEquiv (X' i → B) i1
                          (dom-ₑ∙p-sides {B = λ _ _ → B} f fInvol {X} {X'} P i0 i))
                     (λ i → 
                        fst (unglue-ₑ∙p (preCompInvol.e' {f = f} B fInvol) X i) ,
                       unglueIsEquiv (X i) (i ∨ ~ i)
                          (dom-ₑ∙p-sides {B = λ _ _ → B} f fInvol {X} {X'} P i1 i) )
                     refl 
                     refl

unglue-dom-ₑ∙p {A = A} {A'} {B = B} f fInvol {X} {X' = X'} P j i =
  unglueEquiv (P j i) _
    (dom-ₑ∙p-sides {A = A} {A'} {B = λ _ _ → B} f fInvol {X} {X' = X'} P j i)


-- unglue-dom-ₑ∙p : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : Type ℓ'}
--               → (f : A → A) → (fInvol : isInvolution f) 
--                 {X : (A → B) ≡ (A' → B)}
--                 {X' : A ≡ A'}
--               → (P : (λ i → X' i → B) ≡ X)
--               → SquareP
--                 (λ j i →
--                 dom-ₑ∙p {A = A} {A'} {B = B} f fInvol {X} {X' = X'} P j i
--                  → P j i)
--                      ((λ i x y → x (fst (glue-invol-ₑ∙p
--                           (involEquiv {f = f} fInvol) fInvol X' i) y)))
--                      (congP (λ _ → fst)
--                       (unglue-ₑ∙p (preCompInvol.e' {f = f} B fInvol) X))
--                      refl
--                      refl

-- unglue-dom-ₑ∙p {A = A} {A'} {B = B} f fInvol {X} {X' = X'} P j i =
--   let e = (involEquiv {f = f} fInvol)
--   in fst (unglueEquiv (P j i) _
--          {!!})
--     -- λ {
--     --   (i = i0) → (A → B) , preCompInvol.e' {f = f} B fInvol
--     -- ; (i = i1) → (A' → B) , idEquiv _
--     -- ; (j = i0) → ((e ₑ∙ₚ X') i → B) ,
--     --         (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)) ,
--     --         isProp→PathP
--     --           (λ i → isPropIsEquiv {A = (e ₑ∙ₚ X') i → B} {B = X' i → B}
--     --             (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)))
--     --           (snd (preCompInvol.e' {f = f} B fInvol))
--     --           (idIsEquiv _) i
--     --   })


dom-invol-ₑ∙p : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (isSetA : isSet A)
              → (f : A → A) → (fInvol : isInvolution f) 
                {X : (A → B) ≡ (A → B)}
                {X' : A ≡ A}
              → (P : (λ i → X' i → B) ≡ X)
              → Cube

                  (λ l j → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P ) l j)
                  P
                  (λ i j → invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X' i j
                          → B)
                  (λ i j → invol-ₑ∙p (preCompInvol.e' {f = f} B fInvol)
                      (λ x → funExt λ y → cong x (fInvol y)) X i j)
                  (refl {x = λ l → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P) l i0})
                  (refl {x = λ l → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P) l i1})
dom-invol-ₑ∙p {ℓ = ℓ} {ℓ'} {A = A} {B} isSetA f fInvol {X} {X'} P i l j =
   Glue (P l j ) {i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l}
      λ o → T i l j o , e i l j o , isEqE i l j o

  where
    T : ∀ i l j → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l) (Type (ℓ-max ℓ ℓ'))
    T i l j =
     λ { (i = i0) → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P ) l j 
       ; (i = i1) → P l j
       ; (l = i0) → (invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X' i j → B) 
       ; (l = i1) → invol-ₑ∙p (preCompInvol.e' {f = f} B fInvol)
                      (λ x → funExt λ y → cong x (fInvol y)) X i j
       ; (j = i0) → (A → B)
       ; (j = i1) → (A → B) }

    isSetX' : ∀ j → isSet (X' j)
    isSetX' j = isProp→PathP (λ j → isPropIsSet {A = X' j})
      isSetA isSetA j

    isSetInvol : ∀ i j →
          isSet (invol-ₑ∙p (involEquiv {f = f} fInvol)
                         fInvol X' i j)
    isSetInvol i j =
      isOfHLevelRespectEquiv 2
        (invEquiv (unglue-invol-ₑ∙p (involEquiv {f = f} fInvol)
                         fInvol X' i j))
        (isSetX' j)

    ∘f = preCompInvol.e' {f = f} B fInvol

    e : ∀ i l j → PartialP (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l)
            λ o → T i l j o → P l j 
    e i l j =  λ { (i = i0) → fst (unglue-dom-ₑ∙p f fInvol P l j) ∘
               fst (unglue-dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P) l j) 
       ; (i = i1) → idfun _
       ; (l = i0) → _∘ 
               (isSet→SquareP {A = λ i j → X' j → 
                invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X' i j} (λ i j →
                    isSetΠ λ _ → isSetInvol i j)
                  (λ j → (fst (glue-invol-ₑ∙p
                          (involEquiv {f = f} fInvol) fInvol
                           (involEquiv {f = f} fInvol ₑ∙ₚ X') j))
                           ∘' (fst (glue-invol-ₑ∙p
                          (involEquiv {f = f} fInvol) fInvol X' j)))
                  (λ _ → idfun _)
                  (λ i y → fInvol y i)
                  (λ _ → idfun _) i j)

       ; (l = i1) → fst (unglue-invol-ₑ∙p ∘f
                      (λ x → funExt λ y → cong x (fInvol y)) X i j)
       ; (j = i0) → λ x y → x (fInvol y i)
       ; (j = i1) → idfun _
       }

    isEqEJ0 : (i l : I) → isEquiv {A = A → B} {B = A → B} (λ x y → x (fInvol y i))
    isEqEJ0 i l = isProp→PathP
           (λ i → isPropIsEquiv (λ x y → x (fInvol y i)))
           (snd (∘f ∙ₑ ∘f))
            (idIsEquiv _) i

    isEqEJ1 : (i l : I) → isEquiv {A = A → B} (λ x → x)
    isEqEJ1 _ _ = idIsEquiv _

    isEqI0L0 : _
    isEqI0L0 = isProp→PathP (λ j → isPropIsEquiv (e i0 i0 j 1=1)) _ _

    isEqI0L1 : _
    isEqI0L1 = isProp→PathP (λ j → isPropIsEquiv (e i0 i1 j 1=1)) _ _


    isEqE : ∀ i l j → PartialP (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l)
            λ o → isEquiv (e i l j o) 
    isEqE i l j =
     λ { (i = i0) →
            isProp→SquareP
            (λ l j → isPropIsEquiv (e i0 l j 1=1))
                 (λ _ → snd (compEquiv ∘f ∘f))
                 (λ _ → idIsEquiv _)
                 isEqI0L0
                 isEqI0L1 l j 
       ; (i = i1) → idIsEquiv _
       ; (l = i0) →
            isProp→SquareP
            (λ i j → isPropIsEquiv (e i i0 j 1=1))
                 (λ i → isEqEJ0 i i0)
                 (λ _ → idIsEquiv _)
                 isEqI0L0
                 (λ _ → idIsEquiv _) i j
       ; (l = i1) →
                      isProp→SquareP
            (λ i j → isPropIsEquiv (e i i1 j 1=1))
                 (λ i → isEqEJ0 i i1)
                 (λ i → isEqEJ1 i i1)
                 isEqI0L1
                 (λ _ → idIsEquiv _) i j
       ; (j = i0) → isEqEJ0 i l            
       ; (j = i1) → isEqEJ1 i l      
       }

dom-ₑ∙ₚ-comp²eq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (isSetA : isSet A)
              → (f : A → A) → (fInvol : isInvolution f)
              → (g : A → A) → (gInvol : isInvolution g)
              → (fg-comm : f ∘ g ≡ g ∘ f) → 
                {X : (A → B) ≡ (A → B)}
                {X' : A ≡ A}
              → (P : (λ i → X' i → B) ≡ X)
              → Cube
                  (dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol P ))
                  (dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol P ))
                  (λ i j → ₑ∙ₚ-comp²eq
                     (involEquiv {f = f} fInvol)
                     (involEquiv {f = g} gInvol) X' (equivEq (fg-comm)) i j → B)
                  (ₑ∙ₚ-comp²eq _ _ X (equivEq
                    (funExt λ x → cong (x ∘'_) (sym fg-comm))) )
                  refl
                  refl

dom-ₑ∙ₚ-comp²eq {ℓ} {ℓ'} {B = B} isSetA f fInvol g gInvol fg-comm {X} {X'} P =
   λ i l j →
        Glue (P l j) λ o → T i l j o , E i l j o ,
          isEquivE i l j o  

  where
   T : ∀ i l j → Partial (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
               (Type (ℓ-max ℓ ℓ'))
   T i l j = λ {
     (i = i0) → _
    ;(i = i1) → _
    ;(l = i0) → _
    ;(l = i1) → _
    ;(j = i0) → _
    ;(j = i1) → _
    }

   isSetX' : ∀ j → isSet (X' j)
   isSetX' j = isProp→PathP (λ j → isPropIsSet {A = X' j})
     isSetA isSetA j

   isSet-ₑ∙ₚ-comp²eq : ∀ i j →
         isSet
     (ₑ∙ₚ-comp²eq (involEquiv {f = f} fInvol) (involEquiv {f = g} gInvol) X'
      (equivEq fg-comm) i j)
   isSet-ₑ∙ₚ-comp²eq i j =
     isOfHLevelRespectEquiv 2
       (invEquiv (unglueEquiv (X' j) (i ∨ ~ i ∨ j ∨ ~ j)
         (ₑ∙ₚ-comp²eq-sides
          (involEquiv {f = f} fInvol) (involEquiv {f = g} gInvol) X'
      (equivEq fg-comm) i j)))
       (isSetX' j)


   El0 : ∀ i j → T i i0 j 1=1 → X' j → B
   El0 i j = _∘' 
               (isSet→SquareP {A = λ i j → X' j → 
                ₑ∙ₚ-comp²eq
                     (involEquiv {f = f} fInvol)
                     (involEquiv {f = g} gInvol) X' (equivEq (fg-comm)) i j}
                      (λ i j →
                    isSetΠ λ _ → isSet-ₑ∙ₚ-comp²eq i j)
                    (λ j → (fst (glue-invol-ₑ∙p
                          (involEquiv {f = g} gInvol) gInvol
                           (involEquiv {f = f} fInvol ₑ∙ₚ X') j))
                           ∘' (fst (glue-invol-ₑ∙p
                          (involEquiv {f = f} fInvol) fInvol X' j)))
                  (λ j → (fst (glue-invol-ₑ∙p
                          (involEquiv {f = f} fInvol) fInvol
                           (involEquiv {f = g} gInvol ₑ∙ₚ X') j))
                           ∘' (fst (glue-invol-ₑ∙p
                          (involEquiv {f = g} gInvol) gInvol X' j)))
                  (sym fg-comm)
                  (λ _ → idfun _) i j)

   El1 : ∀ i j → T i i1 j 1=1 → X j
   El1 i j = unglue (j ∨ ~ j ∨ i ∨ ~ i)
       {e = λ o → snd (ₑ∙ₚ-comp²eq-sides
          (preCompInvol.e' {f = f} B fInvol)
          (preCompInvol.e' {f = g} B gInvol) X
       (equivEq
                    (funExt λ x → cong (x ∘'_) (sym fg-comm))) i j o)} 


   E : ∀ i l j → PartialP (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
               (λ o → T i l j o → P l j)
   E i l j = λ {
     (i = i0) →
       fst (unglue-dom-ₑ∙p f fInvol P l j) ∘
               fst (unglue-dom-ₑ∙p g gInvol ((dom-ₑ∙p f fInvol P)) l j)
    ;(i = i1) →
       fst (unglue-dom-ₑ∙p g gInvol P l j) ∘
               fst (unglue-dom-ₑ∙p f fInvol ((dom-ₑ∙p g gInvol P)) l j)
    ;(l = i0) → El0 i j
    ;(l = i1) → El1 i j
    ;(j = i0) → λ x → x ∘ (fg-comm (~ i))
    ;(j = i1) → idfun _
    }

   isEquivEi0 : ∀ l j → isEquiv (E i0 l j 1=1)
   isEquivEi0 l j =
      snd (unglue-dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol P) l j
          ∙ₑ unglue-dom-ₑ∙p f fInvol P l j)

   isEquivEi1 : ∀ l j → isEquiv (E i1 l j 1=1)
   isEquivEi1 l j =
      snd (unglue-dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol P) l j
          ∙ₑ unglue-dom-ₑ∙p g gInvol P l j)



   isEquivE : ∀ i l j → PartialP (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
               (λ o → isEquiv (E i l j o))
   isEquivE i l j =
       λ {
     (i = i0) → isEquivEi0 l j
    ;(i = i1) → isEquivEi1 l j
    ;(l = i0) → isProp→PathP
         (λ i → isPropIsEquiv (E i l j 1=1))
              (isEquivEi0 l j)
              (isEquivEi1 l j) i
    ;(l = i1) → isProp→PathP
         (λ i → isPropIsEquiv (E i l j 1=1))
              (isEquivEi0 l j)
              (isEquivEi1 l j) i
    ;(j = i0) → isProp→PathP
         (λ i → isPropIsEquiv (E i l j 1=1))
              (isEquivEi0 l j)
              (isEquivEi1 l j) i
    ;(j = i1) → isProp→PathP
         (λ i → isPropIsEquiv (E i l j 1=1))
              (isEquivEi0 l j)
              (isEquivEi1 l j) i
              }

dom-ₑ∙ₚ-comp³eq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (isSetA : isSet A)
   → (f : A → A) → (fInvol : isInvolution f)
   → (g : A → A) → (gInvol : isInvolution g)
   → (fg-braid : (f ∘' g ∘' f) ≡ (g ∘' f ∘' g)) 
   →   {X : (A → B) ≡ (A → B)}
                {X' : A ≡ A}
              → (P : (λ i → X' i → B) ≡ X)
              → Cube
                   ((dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol P ))))
                   ((dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol P ))))
                   
                  (λ i j → ₑ∙ₚ-comp³eq
                     (involEquiv {f = f} fInvol)
                     (involEquiv {f = g} gInvol) X' (equivEq fg-braid) i j → B)
                   (ₑ∙ₚ-comp³eq _ _ X
                     (equivEq (funExt λ x → cong (x ∘'_) (fg-braid))))

                  refl
                  refl
dom-ₑ∙ₚ-comp³eq {ℓ} {ℓ'} {A} {B} isSetA f fInvol g gInvol fg-braid {X} {X'} P = 
     λ i l j → Glue (P l j) λ o → T i l j o , E i l j o 

  where
   T : ∀ i l j → Partial (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
               (Type (ℓ-max ℓ ℓ'))
   T i l j = λ {
     (i = i0) → _
    ;(i = i1) → _
    ;(l = i0) → _
    ;(l = i1) → _
    ;(j = i0) → _
    ;(j = i1) → _
    }

   isSetX' : ∀ j → isSet (X' j)
   isSetX' j = isProp→PathP (λ j → isPropIsSet {A = X' j})
     isSetA isSetA j

   isSet-ₑ∙ₚ-comp³eq : ∀ i j →
         isSet
     (ₑ∙ₚ-comp³eq (involEquiv {f = f} fInvol) (involEquiv {f = g} gInvol) X'
      (equivEq fg-braid) i j)
   isSet-ₑ∙ₚ-comp³eq i j =
     isOfHLevelRespectEquiv 2
       (invEquiv (unglueEquiv (X' j) (i ∨ ~ i ∨ j ∨ ~ j)
         (ₑ∙ₚ-comp³eq-sides
          (involEquiv {f = f} fInvol) (involEquiv {f = g} gInvol) X'
      (equivEq fg-braid) i j)))
       (isSetX' j)

   f' : (X : A ≡ A) → ∀ j → X j ≃ (involEquiv {f = f} fInvol ₑ∙ₚ X) j
   f' X j = glue-invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X j

   g' : (X : A ≡ A) → ∀ j → X j ≃ (involEquiv {f = g} gInvol ₑ∙ₚ X) j
   g' X j = glue-invol-ₑ∙p (involEquiv {f = g} gInvol) gInvol X j


   Ei0 : ∀ l j → T i0 l j 1=1 ≃ P l j
   Ei0 l j =     
        (unglue-dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol P)) l j)
     ∙ₑ (unglue-dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol P) l j)
     ∙ₑ (unglue-dom-ₑ∙p f fInvol P l j)


   Ei1 : ∀ l j → T i1 l j 1=1 ≃ P l j
   Ei1 l j =     
        (unglue-dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol P)) l j)
     ∙ₑ (unglue-dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol P) l j)
     ∙ₑ (unglue-dom-ₑ∙p g gInvol P l j)

   El0 : ∀ i j → T i i0 j 1=1 → X' j → B
   El0 i j = _∘' 
               (isSet→SquareP {A = λ i j → X' j → 
                ₑ∙ₚ-comp³eq
                     (involEquiv {f = f} fInvol)
                     (involEquiv {f = g} gInvol) X' (equivEq (fg-braid)) i j}
                      (λ i j →
                    isSetΠ λ _ → isSet-ₑ∙ₚ-comp³eq i j)
                    (λ j →  fst (f' X' j ∙ₑ g' (λ j → ua (f' X' j) i1) j
                                ∙ₑ f' (λ j → ua (g' (λ j → ua (f' X' j) i1) j) i1) j) )
                    (λ j →  fst (g' X' j ∙ₑ f' (λ j → ua (g' X' j) i1) j
                                ∙ₑ g' (λ j → ua (f' (λ j → ua (g' X' j) i1) j) i1) j) )
                  fg-braid
                  (λ _ → idfun _)
                  i j)

   El1 : ∀ i j → T i i1 j 1=1 → X j
   El1 i j = unglue (j ∨ ~ j ∨ i ∨ ~ i)
       {e = λ o → snd (ₑ∙ₚ-comp³eq-sides
          (preCompInvol.e' {f = f} B fInvol)
          (preCompInvol.e' {f = g} B gInvol) X
       (equivEq
                    (funExt λ x → cong (x ∘'_) (fg-braid))) i j o)} 


   E : ∀ i l j → PartialP (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
               (λ o → T i l j o ≃ P l j)
   E i l j = λ {
     (i = i0) → Ei0 l j
    ;(i = i1) → Ei1 l j
    ;(l = i0) → El0 i j ,
         isProp→PathP
         (λ i → isPropIsEquiv (El0 i j))
              (snd (Ei0 l j))
              (snd (Ei1 l j)) i
    ;(l = i1) → El1 i j ,
        isProp→PathP
         (λ i → isPropIsEquiv (El1 i j))
              (snd (Ei0 l j))
              (snd (Ei1 l j)) i
    ;(j = i0) → (_∘' (fg-braid i)) ,
       isProp→PathP
         (λ i → isPropIsEquiv (_∘' (fg-braid i)))
              (snd (Ei0 l j))
              (snd (Ei1 l j)) i
    ;(j = i1) → idfun _ ,
              isProp→PathP
         (λ i → isPropIsEquiv (idfun _))
              (snd (Ei0 l j))
              (snd (Ei1 l j)) i
    }





-- h𝔽in : ∀ n → ℙrm n → hSet ℓ-zero
-- h𝔽in n = EMrec.f w
--  where
--   w : EMrec (Symmetric-Group (Fin n) (isSetFin {n})) isGroupoidHSet
--   EMrec.b w = Fin n , isSetFin {n}
--   EMrec.bloop w g = TypeOfHLevel≡ 2 (ua g)
--   EMrec.bComp w g h =
--      ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--         λ i j →
--           Glue (ua {!ua !} i)
--             λ { (j = i0) → {!!}
--               ; (j = i1) → {!!}
--               }




-- 𝔽in : ∀ n → ℙrm n → Type ℓ-zero
-- 𝔽in  n = fst ∘ h𝔽in n


-- 𝔽h : (A : Type ℓ) → ∀ n → ℙrm n → Type ℓ
-- 𝔽h A n em = 𝔽in n em → A 





-- uaDom≃ : ∀ {ℓ ℓ'} {A B : Type ℓ} (C : Type ℓ') → (e : A ≃ B) →  
--      ua (preCompEquiv {C = C} (invEquiv e))
--        ≡ cong (λ X → X → C) (ua e)
-- uaDom≃ C e = {!!}
--   -- invEq≡→equivFun≡ (invEquiv univalence)
--   --  (equivEq (funExt (λ x →
--   --    fromPathP (funTypeTransp' (idfun _) C ((ua (isoToEquiv e))) x)
--   --     ∙ funExt λ y → cong x (cong (Iso.inv e) (transportRefl y)))))

-- 𝔽h* : (A : Type ℓ) → ∀ n → (p : ℙrm n) → singl (𝔽h A n p )
-- 𝔽h* A n = EMelim.f w
--  where
--  w : EMelim _ λ z → singl (𝔽h A n z)
--  EMelim.isGrpB w = {!!}
--  EMelim.b w = _ , refl
--  EMelim.bPathP w g = ΣPathP
--    ((ua (preCompEquiv {C = A} (invEquiv g))) ,
--      flipSquare (sym (uaDom≃ A g)))
--  EMelim.bSqP w = {!!}
 
-- 𝔽-≡ : (A : Type ℓ) → ∀ n (g : Fin n ≃ Fin n) →
--       PathP (λ i → singl (𝔽h A n (emloop g i)))
--       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
--       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- 𝔽-≡ A n g = ΣPathP
--     (ua ({!!} ∙ₑ preCompEquiv (invEquiv g) ∙ₑ {!Iso-×^-F→ n!})
--    , flipSquare (symP-fromGoal {!  uaDom≃ A g!}))
--  where
--  s : {!!}
--  s = (uaDomIso A {!!})

-- -- 𝕍 : (A : Type ℓ) → ∀ n em → singl (𝔽h A n em)
-- -- 𝕍 A n = EMelim.f w
-- --  where
-- --  w : EMelim _
-- --                      (λ z → singl (𝔽h A n z))
-- --  EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
-- --  EMelim.b w = (A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n)))
-- --  EMelim.bPathP w = 𝔽-≡ A n
-- --  fst (EMelim.bSqP w g h i j) = 𝔽-sq-fst A n g h i j
-- --  snd (EMelim.bSqP w g h i j) k = {!!}

ism : ∀ n → Iso (Perm n) (Iso (Fin n) (Fin n))
ism n = (fst (PermGIsoIso n))

lookTab≡ : ∀ n → (Fin n → A) ≡ (A ×^ n)
lookTab≡ n = ua (isoToEquiv (invIso (Iso-×^-F→ n)))



perm𝔽≡ : ∀ n → (g : Perm n) →
             singl {A = (Fin n → A) ≡ (Fin n → A) }
             (λ i → permFin n g i → A) 
perm𝔽≡ {ℓ} {A = A} n = Relim.f (w {n})
 where
 open Relim

 ∘T : ∀ {n} → (Σ ℕ  λ k → (suc k < n)) → _
 ∘T {n} k = preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k) 


 w : ∀ {n} → Relim (λ z → singl (λ i → permFin n z i → A))
 isSetA w _ = isOfHLevelPlus 2 (isContrSingl _)
 εA w = refl , refl
 fst (∷A (w {n}) k (X , _)) = ∘T {n} k ₑ∙ₚ X
 snd (∷A (w {n}) k (X , P)) =
   dom-ₑ∙p
     (fst (isoToEquiv (adjTIso' {n = n} k)))
     (isInvolution-adjT n k)
     P  
 invoA (w {n}) k (X , P) = ΣPathP
    ((invol-ₑ∙p _ _ X) ,
      dom-invol-ₑ∙p (isSetFin {n = n}) _ _ P)

 braidA (w {n}) k k< (X , P) =
   ΣPathP (ₑ∙ₚ-comp³eq _ _ _
        (equivEq (funExt λ x →
                cong (x ∘'_) 
                  (cong (Iso.fun ∘ permuteIso n) (braid k k< ε))))
      , dom-ₑ∙ₚ-comp³eq (isSetFin {n = n}) _ _ _ _
            (cong (Iso.fun ∘ permuteIso n) (braid k k< ε)) P)
 
 commA (w {n}) k l z (X , P) =
    ΣPathP (
         ₑ∙ₚ-comp²eq _ _ _
             (equivEq (funExt λ x →
                cong (x ∘'_) 
                  (sym ((cong (Iso.fun ∘ permuteIso n) (comm k l z ε))))
         ))

      , dom-ₑ∙ₚ-comp²eq (isSetFin {n = n}) _ _ _ _
            (cong (Iso.fun ∘ permuteIso n) (comm k l z ε)) P)




perm𝔽sq : isGroupoid A → ∀ n → (g h : Perm n)
             → Square
               (fst (perm𝔽≡ {A = A} n g))
               (fst (perm𝔽≡ n (g · h)))
               refl
               (fst (perm𝔽≡ n h))
perm𝔽sq {A = A} isGroupoid-A n g h = Relim.f (w h) g
 module QQQ where
 open Relim

 ∘T : (Σ ℕ  λ k → (suc k < n)) → _
 ∘T k = preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k) 

 isGpdFin→A : isGroupoid (Fin n → A) 
 isGpdFin→A = isGroupoidΠ λ _ → isGroupoid-A

 w : (h : Perm n) → Relim (λ g → 
               Square
               (fst (perm𝔽≡ {A = A} n g))
               (fst (perm𝔽≡ n (g · h)))
               refl
               (fst (perm𝔽≡ n h)))
 isSetA (w h) _ =
   isOfHLevelRetractFromIso 2
     (invIso PathP→comm-Iso)
     (isOfHLevel≡ 3 isGpdFin→A isGpdFin→A _ _)
 εA (w h) j i = (fst (perm𝔽≡ {A = A} n h)) (i ∧ j)
 ∷A (w h) k X j i = (∘T k ₑ∙ₚ X j) i 
 invoA (w h) k {xs} X l j i =
    invol-ₑ∙p ((λ z x → z (adjT n k x)) ,
                  involIsEquiv (λ x i b → x (isInvolution-adjT n k b i)))
                  (λ x i z → x (isInvolution-adjT n k z i)) (X j) l i
 braidA (w h) k k< X l j i =
     ₑ∙ₚ-comp³eq
        (((λ z x → z (adjT n (k , <-weaken {n = n} k<) x)) ,
                  involIsEquiv
                   (λ x i b → x (isInvolution-adjT n (k , <-weaken {n = n} k<) b i))))
        (((λ z x → z (adjT n (suc k , k<) x)) ,
                  involIsEquiv (λ x i b → x (isInvolution-adjT n (suc k , k<) b i))))
        (X j)
         (equivEq (funExt λ x →
        cong (x ∘'_) 
          (cong (Iso.fun ∘ permuteIso n) (braid k k< ε))))
          l i 


 commA (w h) k l' z X l j i =
    ₑ∙ₚ-comp²eq
      (((λ z x → z (adjT n l' x)) ,
                  involIsEquiv (λ x i b → x (isInvolution-adjT n l' b i))))
      (((λ z x → z (adjT n k x)) ,
                  involIsEquiv (λ x i b → x (isInvolution-adjT n k b i))))
      (X j)
       (equivEq (funExt (λ x → cong (x ∘'_)
        (sym ((cong (Iso.fun ∘ permuteIso n) (comm k l' z ε)))) )))
       l i


perm𝔽sq-Snd : (isGroupoid-A : isGroupoid A) → ∀ n → (g h : Perm n)
             → SquareP
                  (λ i j → (𝔽in' n (emcomp g h i j) → A) ≡
                            perm𝔽sq isGroupoid-A n g h i j)
               (flipSquare (snd (perm𝔽≡ {A = A} n g)))
               (flipSquare (snd (perm𝔽≡ {A = A} n (g · h))))
               refl
               (flipSquare (snd (perm𝔽≡ {A = A} n h)))
perm𝔽sq-Snd {A = A} isGroupoid-A n g h = RelimProp.f (w h) g
 where
 open RelimProp

 ∘T : (Σ ℕ  λ k → (suc k < n)) → _
 ∘T k = preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k) 

 isGpdFin→A : isGroupoid (Fin n → A) 
 isGpdFin→A = isGroupoidΠ λ _ → isGroupoid-A

 w : (h : Perm n) → RelimProp (λ g → 
               SquareP
                  (λ i j → (𝔽in' n (emcomp g h i j) → A) ≡
                            perm𝔽sq isGroupoid-A n g h i j)
               (flipSquare (snd (perm𝔽≡ {A = A} n g)))
               (flipSquare (snd (perm𝔽≡ {A = A} n (g · h))))
               (refl)
               (flipSquare (snd (perm𝔽≡ {A = A} n h))))
 isPropA (w h) x =
   isOfHLevelRespectEquiv 1
    (invEquiv (PathP≃Path _ _ _))
      (isOfHLevelRespectEquiv 2
        (invEquiv (PathP≃Path _ _ _))
         ((isOfHLevelRespectEquiv 3
        (invEquiv (PathP≃Path _ _ _))
         (isOfHLevel≡ 3 isGpdFin→A isGpdFin→A ) _ _)) _ _)
 εA (w h) i j l = (snd (perm𝔽≡ {A = A} n h)) l (i ∧ j)
 ∷A (w h) k {xs} X i j l =    
   Glue (X i j l) {i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l}
    λ o → T i j l o , (E i j l o) , isEqE i j l o
   where
    T : ∀ i j l → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l) (Type _)
    T i j l = λ {
         (i = i0) → _
        ;(i = i1) → _
        ;(j = i0) → _ 
        ;(j = i1) → _
        ;(l = i0) → _ 
        ;(l = i1) → _
        }
    Ei0 : ∀ l j →  T i0 j l 1=1 ≃ X i0 j l
    Ei0 l j = (unglue-dom-ₑ∙p
               (fst (isoToEquiv (adjTIso' {n = n} k)))
               (isInvolution-adjT n k)
             (snd (perm𝔽≡ n xs)) l j)

    Ei1 : ∀ l j →  T i1 j l 1=1 ≃ X i1 j l
    Ei1 l j = (unglue-dom-ₑ∙p
               (fst (isoToEquiv (adjTIso' {n = n} k)))
               (isInvolution-adjT n k)
             (snd (perm𝔽≡ n (xs · h))) l j)

    li0Sq : SquareP (λ i j → 𝔽in' n (emcomp xs h i j) → 𝔽in' n (emcomp (k ∷ xs) h i j))
                _ _ _ _
    li0Sq =
       isSet→SquareP (λ i j → isSet→ (snd (h𝔽in' n (emcomp (k ∷ xs) h i j))))
          (λ j x₁ → (fst
                  (glue-invol-ₑ∙p (involEquiv {f = adjT n k} (isInvolution-adjT n k))
                   (isInvolution-adjT n k) (λ i₂ → permFin n (xs) i₂) j)
                  x₁))
                (λ j x₁ → (fst
                  (glue-invol-ₑ∙p (involEquiv {f = adjT n k} (isInvolution-adjT n k))
                   (isInvolution-adjT n k) (λ i₂ → permFin n (xs · h) i₂) j)
                  x₁))
                (λ _ → adjT n k)
                λ _ → idfun _

    E : ∀ i j l → PartialP (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l) (λ o → T i j l o → X i j l)
    E i j l = λ {
         (i = i0) → fst (Ei0 l j)
        ;(i = i1) →  fst (unglue-dom-ₑ∙p
               (fst (isoToEquiv (adjTIso' {n = n} k)))
               (isInvolution-adjT n k)
             (snd (perm𝔽≡ n (xs · h))) l j)
        ;(j = i0) → _∘' (adjT n k)
        ;(j = i1) → idfun _
        ;(l = i0) → _∘' (li0Sq i j)  
        ;(l = i1) → fst (unglue-ₑ∙p (∘T k) (perm𝔽sq isGroupoid-A n (xs) h i) j ) 
        }

    isEqE : ∀ i j l → PartialP (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l) (λ o →
         isEquiv (E i j l o))
    isEqE i j l = λ {
         (i = i0) → snd (Ei0 l j)
        ;(i = i1) → snd (Ei1 l j)
        ;(j = i0) → isProp→PathP
            (λ i → isPropIsEquiv (E i j l 1=1))
            (snd (Ei0 l j))
            (snd (Ei1 l j)) i
        ;(j = i1) → isProp→PathP
            (λ i → isPropIsEquiv (E i j l 1=1))
            (snd (Ei0 l j))
            (snd (Ei1 l j)) i
        ;(l = i0) → isProp→PathP
            (λ i → isPropIsEquiv (E i j l 1=1))
            (snd (Ei0 l j))
            (snd (Ei1 l j)) i  
        ;(l = i1) → isProp→PathP
            (λ i → isPropIsEquiv (E i j l 1=1))
            (snd (Ei0 l j))
            (snd (Ei1 l j)) i 
        }


perm𝔽Si : (isGroupoid A) → ∀ n →  (em : ℙrm' n) →
             singl (𝔽in' n em → A) 
perm𝔽Si {A = A} isGroupoid-A n = EMelim.f w
 where

 w : EMelim (PermG n) (λ z → singl (𝔽in' n z → _))
 EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
 EMelim.b w = (𝔽in' n embase → A) , refl
 EMelim.bPathP w g =  
  let z = perm𝔽≡ n g
  in ΣPathP (fst z , flipSquare (snd z))
 fst (EMelim.bSqP w g h i j) = perm𝔽sq {A = A}  isGroupoid-A n g h i j
 snd (EMelim.bSqP w g h i j) = perm𝔽sq-Snd {A = A} isGroupoid-A n g h i j



perm𝔽 : {A : Type ℓ} → (isGroupoid A) → ∀ n → (em : ℙrm' n) → Type ℓ 
perm𝔽 isGA n = fst ∘ perm𝔽Si isGA n



adjT×^'→ : ∀ {n} → ℕ →
             (A ×^ n) → (A ×^ n)
adjT×^'→ {n = zero} _ x = x
adjT×^'→ {n = suc zero} _ x = x
adjT×^'→ {n = suc (suc n)} zero (x , x' , xs) = (x' , x , xs)
adjT×^'→ {n = suc (suc n)} (suc k) (x , xs) =
   x , adjT×^'→ k xs

isInvo-adjT×^'→ : ∀ {n} → ∀ k → isInvolution (adjT×^'→ {A = A} {n} k) 
isInvo-adjT×^'→ {n = zero} k x = refl
isInvo-adjT×^'→ {n = suc zero} k x = refl
isInvo-adjT×^'→ {n = suc (suc n)} zero x = refl
isInvo-adjT×^'→ {n = suc (suc n)} (suc k) (x , xs) =
 cong (x ,_) (isInvo-adjT×^'→ k xs)


braid-adjT×^'→ : ∀ {n} → ∀ k →  suc (suc k) < n → ∀ v → 
  (adjT×^'→ {A = A} {n} k ∘ adjT×^'→ {A = A} {n} (suc k) ∘ adjT×^'→ {A = A} {n} (k)) v
  ≡ (adjT×^'→ {A = A} {n} (suc k) ∘ adjT×^'→ {A = A} {n} (k) ∘ adjT×^'→ {A = A} {n} (suc k)) v
braid-adjT×^'→ {n = suc (suc (suc n))} zero x _ = refl
braid-adjT×^'→ {n = suc (suc n)} (suc k) x (v , vs) =
  cong (v ,_) (braid-adjT×^'→ k x vs)

comm-adjT×^'→ : ∀ {n} → ∀ k l → (k< : (suc k) < n) (l< : (suc l) < n) → 
  A.commT k l → ∀ v →  
  (adjT×^'→ {A = A} {n} l
    ∘ adjT×^'→ {A = A} {n} k ) v
  ≡ (adjT×^'→ {A = A} {n} k
    ∘ adjT×^'→ {A = A} {n} l ) v
comm-adjT×^'→ {n = suc (suc (suc n))} zero (suc (suc l)) k< l< x v = refl
comm-adjT×^'→ {n = suc (suc n)} (suc k) (suc (suc l)) k< l< x (v , vs) =
   cong (v ,_) (comm-adjT×^'→
    {n = suc n} k (suc l) k< l< x vs)


adjT×^ : ∀ {n} → ℕ →
  Iso (A ×^ n)
      (A ×^ n)
adjT×^ {n} k =
 involIso {f = adjT×^'→ {n} k} (isInvo-adjT×^'→ {n} k)

isEquivAdjT×^ : ∀ n k → isEquiv (adjT×^'→ {A = A} {n = n} k)
isEquivAdjT×^ zero k = idIsEquiv _
isEquivAdjT×^ (suc zero) k = idIsEquiv _
isEquivAdjT×^ (suc (suc n)) zero = snd Σ-swap-01-≃
isEquivAdjT×^ (suc (suc zero)) (suc k) = idIsEquiv _
fst (fst (equiv-proof (isEquivAdjT×^ (suc (suc (suc n))) (suc k)) y)) =
  fst y , fst (fst (equiv-proof (isEquivAdjT×^ (suc (suc n)) (k)) (snd y)))
snd (fst (equiv-proof (isEquivAdjT×^ (suc (suc (suc n))) (suc k)) y)) i  =
  fst y , snd (fst (equiv-proof (isEquivAdjT×^ (suc (suc n)) (k)) (snd y))) i
fst (snd (equiv-proof (isEquivAdjT×^ (suc (suc (suc n))) (suc k)) y) (y' , y'') i) =
  fst (y'' (~ i)) ,
    fst (snd (equiv-proof (isEquivAdjT×^ (suc (suc n)) (k)) (snd y)) (_ , cong snd y'')
      i)
snd (snd (equiv-proof (isEquivAdjT×^ (suc (suc (suc n))) (suc k)) y) (y' , y'') i) j  =
  fst (y'' (~ i ∨ j)) ,
    snd (snd (equiv-proof (isEquivAdjT×^ (suc (suc n)) (k)) (snd y)) (_ , cong snd y'')
      i) j

adjT×^≃ : ∀ {n} → ℕ →
      (A ×^ n) ≃ (A ×^ n)
adjT×^≃ {n} k = involEquiv {f = adjT×^'→ {n} k} (isInvo-adjT×^'→ {n} k)


glue-adjT≃' : ∀ {ℓ} {A : Type ℓ} → ∀ n k
           →
           PathP (λ i → (A ×^ n) → (adjT×^≃ {A = A} {n = n} k ₑ∙ₚ refl) i)
             (adjT×^'→ {n = n} k)
             (idfun _)
glue-adjT≃' {A = A} zero k =
   ua-gluePathExt (adjT×^'→ {A = A} {n = zero} k ,
     involIsEquiv (isInvo-adjT×^'→ {A = A} {n = zero} k))
glue-adjT≃' {A = A} (suc zero) k =
      ua-gluePathExt (adjT×^'→ {A = A} {n = suc zero} k ,
     involIsEquiv (isInvo-adjT×^'→ {A = A} {n = suc zero} k))
-- glue-adjT≃' {A = A} (suc (suc n)) k i x =
--   glue (λ { (i = i0) → {!!} ;
--     (i = i1) → {!!} }) {!!}
glue-adjT≃' {A = A} (suc (suc n)) zero i x =
  glue (λ { (i = i0) → fst (snd x) , fst x , snd (snd x) ;
    (i = i1) → x }) x
glue-adjT≃' {A = A} (suc (suc n)) (suc k) i (x , xs) =
  glue (λ { (i = i0) → x , adjT×^'→ k xs ;
    (i = i1) → x , xs })
    (x , unglue (i ∨ ~ i) (glue-adjT≃' {A = A} (suc n) k i xs))


glue-adjT≃ : ∀ {ℓ} {A : Type ℓ} → ∀ n k
       → (X : (A ×^ n) ≡ (A ×^ n)) →
           PathP (λ i → X i ≃ (adjT×^≃ k ₑ∙ₚ X) i) (adjT×^≃ k)
           (idEquiv (X i1))
glue-adjT≃ {A = A} n k = glue-invol-ₑ∙p {B = A ×^ n} (adjT×^≃ {A = A} {n} k)
   (isInvo-adjT×^'→ {n = n} k) 

-- withAdjTlook : ∀ n → Σ ℕ (λ k₁ → suc k₁ < n) →  A ×^ n → Fin n → A
-- withAdjTlook n x x₁ x₂ = {!n!}

lawAdj : ∀ n k → (f : Fin n → A) → tabulate {n = n}
      (f ∘ adjT n k)
      ≡ adjT×^'→ (fst k) (tabulate f)
lawAdj (suc (suc n)) (zero , snd₁) f = refl
lawAdj (suc (suc n)) (suc k , k<) f =
  cong ((f (zero , _)) ,_) (lawAdj (suc n) (k , k<) (f ∘ sucF) )

lawAdj' : ∀ n k → (v : A ×^ n) →
                lookup v ∘ (adjT n k)
            ≡  lookup (adjT×^'→ {n = n} (fst k) v)
lawAdj' (suc (suc n)) (zero , k<) v =
  funExt (uncurry (cases (λ _ → refl)
    (cases (λ _ → refl) λ _ _ → refl)))
lawAdj' (suc (suc (suc n))) (suc k , k<) v =
  funExt (uncurry (cases (λ _ → refl)
     λ kk y → funExt⁻ (lawAdj' (suc (suc n)) (k , k<) (snd v)) (kk , y)) )


adjT-×-sq'' : ∀ n k → PathP (λ i →
      ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) i →
      ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) i)
        (_∘' adjT n k)
        (adjT×^'→ {n = n} (fst k))
adjT-×-sq'' {A = A} (suc (suc n)) (zero , k<) i x =
 let e = (isoToEquiv (invIso (Iso-×^-F→ {A = A} (suc (suc n)))))
 in ua-glue e i (λ { (i = i0) → x ∘' adjT (suc (suc n)) (zero , k<)  })
       (inS (adjT×^'→ zero (ua-unglue e i x)))
adjT-×-sq'' {A = A} (suc (suc (suc n))) (suc k , k<) i x =
 let e = (isoToEquiv (invIso (Iso-×^-F→ {A = A} (suc (suc (suc n))))))
     e' = (isoToEquiv (invIso (Iso-×^-F→ {A = A} (suc (suc n)))))
     v = ((ua-unglue e i x))
 in ua-glue e i (λ { (i = i0) → x ∘' adjT (suc (suc (suc n))) (suc k , k<)  })
       (inS (fst v ,
          ua-unglue e' i (adjT-×-sq'' {A = A} (suc (suc n)) (k , k<) i
           (ua-glue e' i
             (λ { (i = i0) → x ∘' sucF}) (inS (snd v))))))

adjT-×-sq : ∀ n k → PathP (λ i →
      ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) i ≃
      ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) i)
        (preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k) )
        (adjT×^≃ {n = n} (fst k))
adjT-×-sq n k = ΣPathPProp (isPropIsEquiv) (adjT-×-sq'' n k)

adjT-×-sq-invo : ∀ n k →
 PathP (λ j → isInvolution (fst (adjT-×-sq {A = A} n k j)))
   (λ f → funExt (cong f ∘ isInvolution-adjT n k))
   (isInvo-adjT×^'→ {n = n} (fst k) )
adjT-×-sq-invo {A = A} (suc (suc n)) (zero , k<) =
 let e = (isoToEquiv (invIso (Iso-×^-F→ {A = A} (suc (suc n)))))     
 in λ i x j →
      ua-glue e i 
        (λ { ( i = i0) →
             x ∘ (funExt (isInvolution-adjT (suc (suc n)) (zero , k<)) j) })
             (inS (ua-unglue e i x))
adjT-×-sq-invo {A = A} (suc (suc (suc n))) ((suc k) , k<) =
 let e = (isoToEquiv (invIso (Iso-×^-F→ {A = A} (suc (suc (suc n))))))
     e' = (isoToEquiv (invIso (Iso-×^-F→ {A = A} (suc (suc n)))))
     
 in λ i x j →
      let v = ((ua-unglue e i x))
      in ua-glue e i 
        (λ { ( i = i0) →
             x ∘ (funExt (isInvolution-adjT (suc (suc (suc n))) (suc k , k<)) j) })
             (inS (fst v ,
                ua-unglue e' i
                 ( adjT-×-sq-invo {A = A} (suc (suc n)) (k , k<)
                    i (ua-glue e' i (λ { (i = i0) → x ∘' sucF }) (inS (snd v))) j)
                  ))

adjT-×-sq-braid : ∀ n k k< →
 PathP (λ j → (x : ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j) →
         (adjT-×-sq'' n (k , <-weaken {n = n} k<) j
      ∘' adjT-×-sq'' n (suc k , k<) j
      ∘' adjT-×-sq'' n (k , <-weaken {n = n} k<) j) x ≡
      (adjT-×-sq'' n (suc k , k<) j
      ∘' adjT-×-sq'' n (k , <-weaken {n = n} k<) j
      ∘' adjT-×-sq'' n (suc k , k<) j) x)
   (λ x → cong (x ∘'_) 
          (cong (Iso.fun ∘ permuteIso n) (braid k k< ε)))
   (braid-adjT×^'→ {A = A} {n = n} k k<)
adjT-×-sq-braid {A = A} (suc (suc (suc n))) zero  k< =
 let e = (isoToEquiv (invIso (Iso-×^-F→ {A = A} (suc (suc (suc n))))))     
 in λ i x j →
      ua-glue e i 
        (λ { ( i = i0) → x ∘ adjT-braid (suc (suc (suc n))) zero k< j })
             (inS (braid-adjT×^'→ {A = A} {n = (suc (suc (suc n)))}
              zero k< (ua-unglue e i x) j))
adjT-×-sq-braid {A = A} (suc (suc (suc (suc n)))) (suc k)  k< =
 let e = (isoToEquiv (invIso (Iso-×^-F→ {A = A} (suc (suc (suc (suc n)))))))
     e' = (isoToEquiv (invIso (Iso-×^-F→ {A = A} (suc (suc (suc n))))))
     
 in λ i x j →
      let v = ((ua-unglue e i x))
      in ua-glue e i 
        (λ { ( i = i0) → x ∘ adjT-braid (suc (suc (suc (suc n)))) (suc k) k< j})
             (inS (fst v ,
                ua-unglue e' i
                 ( adjT-×-sq-braid {A = A} (suc (suc (suc n))) k  k<
                    i (ua-glue e' i (λ { (i = i0) → x ∘' sucF }) (inS (snd v))) j)
                  ))

adjT-×-sq-commTy : {A : Type ℓ} → ℕ → Type ℓ
adjT-×-sq-commTy {A = A} n = ∀ k l → (z : A.commT (fst k) (fst l)) →
 PathP (λ j → (x : ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j) →
         (adjT-×-sq'' n l j ∘' adjT-×-sq'' n k j) x ≡
      (adjT-×-sq'' n k j ∘' adjT-×-sq'' n l j) x)
   (λ x → cong (x ∘'_) 
          (cong (Iso.fun ∘ permuteIso n) (sym (comm k l z ε))))
   (comm-adjT×^'→ {A = A} (fst k) (fst l) (snd k) (snd l) z)

adjT-×-sq-comm : ∀ n → adjT-×-sq-commTy {A = A} n
adjT-×-sq-comm {A = A} =
  ℕ.elim (uncurry (λ _ ()))
   s'
 where
 s' : (n : ℕ) → adjT-×-sq-commTy n → adjT-×-sq-commTy (suc n)
 s' (suc (suc (suc n))) _ (zero , k<) (suc (suc l) , l<) z =
  let e = (isoToEquiv (invIso (Iso-×^-F→ {A = A} (suc (suc (suc (suc n)))))))
      e' = (isoToEquiv (invIso (Iso-×^-F→ {A = A} (suc (suc n)))))
  in λ i x j →
      let (v0 , v1 , v) = ua-unglue e i x
      in glue
           (λ { (i = i0) → 
                  x ∘ funExt (adjT-comm (suc (suc (suc (suc n))))
                                   (zero , k<) (suc (suc l) , l<) z) ( ~ j)
              ; (i = i1) → _
              }) (v1 , v0 ,
                   ua-unglue e' i (adjT-×-sq'' (suc (suc n)) ((l , l<))
                            i ( ua-glue e' i
                                 (λ { (i = i0) → x ∘ sucF ∘ sucF})
                                  (inS ((snd (snd (ua-unglue e i x))))))))

 s' (suc (suc (suc n))) S (suc k , k<) (suc (suc (suc l)) , l<) z =
   λ i x j →
      let v = ((unglue (i ∨ ~ i) x))
      in glue 
        (λ { ( i = i0) → x ∘ funExt (adjT-comm (suc (suc (suc (suc n))))
                      (suc k , k<) (suc (suc (suc l)) , l<) z) (~ j)
             ;(i = i1) → _
             })
             ((fst v ,
                unglue (i ∨ ~ i)
                (S (k , k<) (suc (suc l) , l<) z i
                     (glue (λ { (i = i0) → x ∘' sucF
                               ; (i = i1) → _}) ((snd v))) j)))
   
 


𝕍Si : (isGrpA : isGroupoid A) → ∀ n →  (em : ℙrm' n) →
             singl (perm𝔽 isGrpA n em) 
𝕍Si {A = A} isGrpA n = EMelim.f w
 where

 𝕍≡ : ∀ n → (g : Perm n) →
              singlP (λ i →
                ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) i
              ≡ ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) i)
              --{A = (A ×^ n) ≡ (A ×^ n) }
              (fst (perm𝔽≡ n g)) 
 𝕍≡ n = Relim.f (w)
  where
  open Relim

  w : Relim _
  isSetA w _ = isOfHLevelPlus 2 (isContrSinglP _ _)
  εA w = refl , λ i → refl
  fst (∷A w k (X , _)) = adjT×^≃ (fst k) ₑ∙ₚ X
  snd (∷A w k {xs} (_ , P)) i =  adjT-×-sq n k i ₑ∙ₚ P i
      
  fst (invoA w k (X , _) i) =
    invol-ₑ∙p (adjT×^≃ (fst k))
     (isInvo-adjT×^'→ {n = n} (fst k)) X i
  snd (invoA w k (_ , P) i) j =
     invol-ₑ∙p (adjT-×-sq n k j)
      (adjT-×-sq-invo n k j)
      (P j) i 
  fst (braidA w k k< (X , _) i) =
    ₑ∙ₚ-comp³eq (adjT×^≃ k) (adjT×^≃ (suc k)) X
      (equivEq (funExt (braid-adjT×^'→ k k<))) i
  snd (braidA w k k< (_ , P) i) j =
    ₑ∙ₚ-comp³eq (adjT-×-sq n (k , <-weaken {n = n} k<) j)
                  (adjT-×-sq n (suc k , k<) j) (P j)
      (equivEq (funExt (adjT-×-sq-braid n k k< j)) ) i
  fst (commA w k l z (X , _) i) =
      ₑ∙ₚ-comp²eq (adjT×^≃ (fst l)) (adjT×^≃ (fst k)) X
        (equivEq (funExt (comm-adjT×^'→ _ _ (snd k) (snd l) z))) i
  snd (commA w k l z (_ , P) i) j =
      ₑ∙ₚ-comp²eq (adjT-×-sq n l j) (adjT-×-sq n k j) (P j)
        (equivEq (funExt (adjT-×-sq-comm n k l z j))) i


 isGpdA×^ : isGroupoid (A ×^ n)
 isGpdA×^ = isOfHLevel×^ n 3 isGrpA

 wSqFst : (h : Perm n) → Relim
   λ g → Square
     (fst (𝕍≡ n g))
     (fst (𝕍≡ n (g · h)))
     refl
     (fst (𝕍≡ n h))
 Relim.isSetA (wSqFst h) g = isOfHLevelRetractFromIso 2
     (invIso PathP→comm-Iso)
     (isOfHLevel≡ 3 isGpdA×^ isGpdA×^ _ _)
 Relim.εA (wSqFst h) i j = fst (𝕍≡ n h) (j ∧ i)
 Relim.∷A (wSqFst h) k {xs} X j i = (adjT×^≃ (fst k) ₑ∙ₚ X j) i 
 Relim.invoA (wSqFst h) k X l j i = 
    invol-ₑ∙p (adjT×^≃ (fst k))
                (isInvo-adjT×^'→ {n = n} (fst k))
                (X j) l i
 Relim.braidA (wSqFst h) k k< X l j i =
   ₑ∙ₚ-comp³eq (adjT×^≃ k) (adjT×^≃ (suc k)) (X j)
     (equivEq (funExt (braid-adjT×^'→ k k<))) l i
 Relim.commA (wSqFst h) k l z X l' j i =
   ₑ∙ₚ-comp²eq (adjT×^≃ (fst l)) (adjT×^≃ (fst k)) (X j)
        (equivEq (funExt (comm-adjT×^'→ _ _ (snd k) (snd l) z))) l' i

 wSqSnd : (h : Perm n) → RelimProp
   λ g → SquareP (λ i j → perm𝔽 isGrpA n (emcomp g h i j) ≡ Relim.f (wSqFst h) g i j)
     (flipSquare (snd (𝕍≡ n g)))
     (flipSquare (snd (𝕍≡ n (g · h))))
     refl
     (flipSquare (snd (𝕍≡ n h)))

 RelimProp.isPropA (wSqSnd h) g =
      isOfHLevelRespectEquiv 1
    (invEquiv (PathP≃Path _ _ _))
      (isOfHLevelRespectEquiv 2
        (invEquiv (PathP≃Path _ _ _))
         ((isOfHLevelRespectEquiv 3
        (invEquiv (PathP≃Path _ _ _))
         (isOfHLevel≡ 3 (isGroupoidΠ λ _ → isGrpA) isGpdA×^ ) _ _)) _ _)
 RelimProp.εA (wSqSnd h) j i = flipSquare (snd (𝕍≡ n h)) (j ∧ i)
 RelimProp.∷A (wSqSnd h) k {xs} X j i l =
   (adjT-×-sq n k l ₑ∙ₚ λ i → X j i l) i
 
 w : EMelim (PermG n) (λ z → singl (perm𝔽 isGrpA n z))
 EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
 EMelim.b w = A ×^ n , ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))
 EMelim.bPathP w g =
   let z = 𝕍≡ n g
   in ΣPathP (fst z , flipSquare (snd z))
 fst (EMelim.bSqP w g h i j) = Relim.f (wSqFst h) g i j
 snd (EMelim.bSqP w g h i j) = RelimProp.f (wSqSnd h) g i j

module 𝕍 {A : Type ℓ} (isGrpA : isGroupoid A) where

  𝕍 : ∀ {n} →  (em : ℙrm' n) → Type ℓ
  𝕍 {n} = fst ∘ 𝕍Si isGrpA n             

  isGrp𝕍 : ∀ {n} →  (em : ℙrm' n) → isGroupoid (𝕍 em)
  isGrp𝕍 {n} em = subst isGroupoid (snd (perm𝔽Si isGrpA n em) ∙ snd (𝕍Si isGrpA n em))
       (isGroupoidΠ λ _ → isGrpA)             


