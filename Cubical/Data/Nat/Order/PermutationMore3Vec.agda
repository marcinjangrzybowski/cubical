{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.PermutationMore3Vec where

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


ₑ∙ₚ-comp³eq :  ∀ {ℓ} {A B : Type ℓ}
            → (e : A ≃ A) → (f : A ≃ A) → (p : A ≡ B) 
            → e ∙ₑ f ∙ₑ e ≡ f ∙ₑ e ∙ₑ f 
            →  e ₑ∙ₚ f ₑ∙ₚ e ₑ∙ₚ p ≡ f ₑ∙ₚ e ₑ∙ₚ f ₑ∙ₚ p  
ₑ∙ₚ-comp³eq {A = A} {B} e f p x j i =
   Glue (p i)
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
braid-adjT×^'→ {n = suc (suc (suc (suc n)))} (suc k) x (v , vs) =
  cong (v ,_) (braid-adjT×^'→ k x vs)

adjT×^ : ∀ {n} → ℕ →
  Iso (A ×^ n)
      (A ×^ n)
adjT×^ {n} k =
 involIso {f = adjT×^'→ {n} k} (isInvo-adjT×^'→ {n} k)

adjT×^≃ : ∀ {n} → ℕ →
      (A ×^ n) ≃ (A ×^ n)
adjT×^≃ {n} k =
 involEquiv {f = adjT×^'→ {n} k} (isInvo-adjT×^'→ {n} k)


comm-adjT×^'→ : ∀ {n} → ∀ k l → (k< : (suc k) < n) (l< : (suc l) < n) → 
  A.commT k l → ∀ v →  
  (adjT×^'→ {A = A} {n} l
    ∘ adjT×^'→ {A = A} {n} k ) v
  ≡ (adjT×^'→ {A = A} {n} k
    ∘ adjT×^'→ {A = A} {n} l ) v
comm-adjT×^'→ {n = suc (suc (suc (suc n)))} zero (suc (suc l)) k< l< x v = refl
comm-adjT×^'→ {n = suc (suc (suc (suc n)))} (suc k) (suc (suc l)) k< l< x (v , vs) =
   cong (v ,_) (comm-adjT×^'→
    {n = suc (suc (suc n))} k (suc l) k< l< x vs)



Vec≃→Fin×≃ : ∀ n → (𝟚.Bool ×^ n) ≃ (𝟚.Bool ×^ n) → Fin× n ≃ Fin× n
Vec≃→Fin×≃ n e =
  (uncurry λ x y → fst e x , {!!} ) , {!!}

permFin : ∀ n → Perm n → Fin× n ≡ Fin× n 
permFin n = Rrec.f (w)
 where


 w : Rrec {n = n} (Fin× n ≡ Fin× n)
 Rrec.isSetA (w) = {!!} --isOfHLevel≡ 2 (isSetFin {n = n}) (isSetFin {n = n})
 Rrec.εA w = refl
 Rrec.∷A (w) k X = {!!} ₑ∙ₚ X
 Rrec.invoA (w) = {!!}      
 Rrec.braidA (w) k k< _ = {!!}
    --    ₑ∙ₚ-comp³eq _ _ _
    -- (equivEq (cong (Iso.fun ∘ permuteIso n) (braid k k< ε)))
 Rrec.commA w k l x X = {!!}
     -- ₑ∙ₚ-comp²eq _ _ _
     --   ((equivEq (cong (Iso.fun ∘ permuteIso n) (comm k l x ε))))



-- w∷ : ∀ n → Σ ℕ (λ k → suc k < n) → Fin n ≡ Fin n → Fin n ≡ Fin n
-- w∷ n k = (adjT'≃ {n = n} k) ₑ∙ₚ_

-- w∷≃ : ∀ n k → (X : Fin n ≡ Fin n) 
--        → ∀ j → w∷ n k X j ≃ X j
-- w∷≃ n k X j = unglue-ₑ∙p (adjT'≃ {n = n} k) X j


-- w∷invo : ∀ n k X → w∷ n k (w∷ n k X) ≡ X  
-- w∷invo n k X i j = invol-ₑ∙p (adjT'≃ {n = n} k) (isInvolution-adjT n k) X i j 

-- w∷invo-unglue≃ : ∀ n k X → ∀ i j → w∷invo n k X i j ≃ X j
-- w∷invo-unglue≃ n k X i j =
--    unglue-invol-ₑ∙p (adjT'≃ {n = n} k) (isInvolution-adjT n k) X i j 

-- permFin : ∀ n → Perm n → Fin n ≡ Fin n 
-- permFin n = Rrec.f (w)
--  where


--  w : Rrec {n = n} (Fin n ≡ Fin n)
--  Rrec.isSetA (w) = isOfHLevel≡ 2 (isSetFin {n = n}) (isSetFin {n = n})
--  Rrec.εA w = refl
--  Rrec.∷A (w) = w∷ n
--  Rrec.invoA (w) = w∷invo n      
--  Rrec.braidA (w) k k< _ =
--        ₑ∙ₚ-comp³eq _ _ _
--     (equivEq (cong (Iso.fun ∘ permuteIso n) (braid k k< ε)))
--  Rrec.commA w k l x X =
--      ₑ∙ₚ-comp²eq _ _ _
--        ((equivEq (cong (Iso.fun ∘ permuteIso n) (comm k l x ε))))

-- ℙrm : ℕ → Type
-- ℙrm n = EM₁ (Symmetric-Group (Fin n) (isSetFin {n}))

-- ℙrm' : ℕ → Type
-- ℙrm' n = EM₁ (PermG n)



-- h𝔽in' : ∀ n → ℙrm' n → hSet ℓ-zero
-- h𝔽in' n = EMrec.f w
--  where
--   w : EMrec _ isGroupoidHSet
--   EMrec.b w = _ , isSetFin {n}
--   EMrec.bloop w g = 
--     TypeOfHLevel≡ 2 (permFin n g)
--   EMrec.bComp w g h = 
--     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--       (RelimProp.f {n = n} w∷compR g)

--    where
--    w∷compR : RelimProp
--       (λ z → Square (permFin n z) (permFin n (z · h)) refl (permFin n h))
--    RelimProp.isPropA w∷compR _ =
--       isOfHLevelRetractFromIso
--          1
--          (invIso PathP→comm-Iso)
--            (isOfHLevel≡ 2 (isSetFin {n = n}) (isSetFin {n = n})
--              _ _ )
--    RelimProp.εA w∷compR i j = permFin n h (i ∧ j)
--    RelimProp.∷A w∷compR k {xs} X j = (adjT'≃ {n = n} k) ₑ∙ₚ (X j)


-- 𝔽in' : ∀ n → ℙrm' n → Type ℓ-zero
-- 𝔽in'  n = fst ∘ h𝔽in' n 



-- -- dom-ₑ∙p : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : Type ℓ'}
-- --               → (f : A → A) → (fInvol : isInvolution f) 
-- --                 {X : (A → B) ≡ (A' → B)}
-- --                 {X' : A ≡ A'}
-- --               → (P : (λ i → X' i → B) ≡ X)
-- --               → (λ i →  ((involEquiv {f = f} fInvol) ₑ∙ₚ X') i → B )
-- --                 ≡ ((preCompInvol.e' {f = f} B fInvol) ₑ∙ₚ X)
-- -- dom-ₑ∙p {A = A} {A'} {B = B} f fInvol {X} {X' = X'} P j i = 
-- --   let e = (involEquiv {f = f} fInvol)
-- --   in Glue (P j i)
-- --     λ {
-- --       (i = i0) → (A → B) , preCompInvol.e' {f = f} B fInvol

-- --     ; (i = i1) → (A' → B) , idEquiv _
-- --     ; (j = i0) → ((e ₑ∙ₚ X') i → B) ,
-- --             (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)) ,
-- --             isProp→PathP
-- --               (λ i → isPropIsEquiv {A = (e ₑ∙ₚ X') i → B} {B = X' i → B}
-- --                 (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)))
-- --               (snd (preCompInvol.e' {f = f} B fInvol))
-- --               (idIsEquiv _) i
-- --       }


-- -- unglue-dom-ₑ∙p : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : Type ℓ'}
-- --               → (f : A → A) → (fInvol : isInvolution f) 
-- --                 {X : (A → B) ≡ (A' → B)}
-- --                 {X' : A ≡ A'}
-- --               → (P : (λ i → X' i → B) ≡ X)
-- --               → SquareP
-- --                 (λ j i →
-- --                 dom-ₑ∙p {A = A} {A'} {B = B} f fInvol {X} {X' = X'} P j i
-- --                  → P j i)
-- --                      ((λ i x y → x (fst (glue-invol-ₑ∙p
-- --                           (involEquiv {f = f} fInvol) fInvol X' i) y)))
-- --                      (congP (λ _ → fst)
-- --                       (unglue-ₑ∙p (preCompInvol.e' {f = f} B fInvol) X))
-- --                      refl
-- --                      refl

-- -- unglue-dom-ₑ∙p {A = A} {A'} {B = B} f fInvol {X} {X' = X'} P j i =
-- --   let e = (involEquiv {f = f} fInvol)
-- --   in fst (unglueEquiv (P j i) _
-- --     λ {
-- --       (i = i0) → (A → B) , preCompInvol.e' {f = f} B fInvol
-- --     ; (i = i1) → (A' → B) , idEquiv _
-- --     ; (j = i0) → ((e ₑ∙ₚ X') i → B) ,
-- --             (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)) ,
-- --             isProp→PathP
-- --               (λ i → isPropIsEquiv {A = (e ₑ∙ₚ X') i → B} {B = X' i → B}
-- --                 (λ x y → x (fst (glue-invol-ₑ∙p e fInvol X' i) y)))
-- --               (snd (preCompInvol.e' {f = f} B fInvol))
-- --               (idIsEquiv _) i
-- --       })


-- -- dom-invol-ₑ∙p : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (isSetA : isSet A)
-- --               → (f : A → A) → (fInvol : isInvolution f) 
-- --                 {X : (A → B) ≡ (A → B)}
-- --                 {X' : A ≡ A}
-- --               → (P : (λ i → X' i → B) ≡ X)
-- --               → Cube

-- --                   (λ l j → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P ) l j)
-- --                   P
-- --                   (λ i j → invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X' i j
-- --                           → B)
-- --                   (λ i j → invol-ₑ∙p (preCompInvol.e' {f = f} B fInvol)
-- --                       (λ x → funExt λ y → cong x (fInvol y)) X i j)
-- --                   (refl {x = λ l → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P) l i0})
-- --                   (refl {x = λ l → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P) l i1})
-- -- dom-invol-ₑ∙p {ℓ = ℓ} {ℓ'} {A = A} {B} isSetA f fInvol {X} {X'} P i l j =
-- --    Glue (P l j ) {i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l}
-- --       λ o → T i l j o , e i l j o , isEqE i l j o

-- --   where
-- --     T : ∀ i l j → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l) (Type (ℓ-max ℓ ℓ'))
-- --     T i l j =
-- --      λ { (i = i0) → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P ) l j 
-- --        ; (i = i1) → P l j
-- --        ; (l = i0) → (invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X' i j → B) 
-- --        ; (l = i1) → invol-ₑ∙p (preCompInvol.e' {f = f} B fInvol)
-- --                       (λ x → funExt λ y → cong x (fInvol y)) X i j
-- --        ; (j = i0) → (A → B)
-- --        ; (j = i1) → (A → B) }

-- --     isSetX' : ∀ j → isSet (X' j)
-- --     isSetX' j = isProp→PathP (λ j → isPropIsSet {A = X' j})
-- --       isSetA isSetA j

-- --     isSetInvol : ∀ i j →
-- --           isSet (invol-ₑ∙p (involEquiv {f = f} fInvol)
-- --                          fInvol X' i j)
-- --     isSetInvol i j =
-- --       isOfHLevelRespectEquiv 2
-- --         (invEquiv (unglue-invol-ₑ∙p (involEquiv {f = f} fInvol)
-- --                          fInvol X' i j))
-- --         (isSetX' j)

-- --     ∘f = preCompInvol.e' {f = f} B fInvol

-- --     e : ∀ i l j → PartialP (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l)
-- --             λ o → T i l j o → P l j 
-- --     e i l j =  λ { (i = i0) → unglue-dom-ₑ∙p f fInvol P l j ∘
-- --                unglue-dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P) l j 
-- --        ; (i = i1) → idfun _
-- --        ; (l = i0) → _∘ 
-- --                (isSet→SquareP {A = λ i j → X' j → 
-- --                 invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X' i j} (λ i j →
-- --                     isSetΠ λ _ → isSetInvol i j)
-- --                   (λ j → (fst (glue-invol-ₑ∙p
-- --                           (involEquiv {f = f} fInvol) fInvol
-- --                            (involEquiv {f = f} fInvol ₑ∙ₚ X') j))
-- --                            ∘' (fst (glue-invol-ₑ∙p
-- --                           (involEquiv {f = f} fInvol) fInvol X' j)))
-- --                   (λ _ → idfun _)
-- --                   (λ i y → fInvol y i)
-- --                   (λ _ → idfun _) i j)

-- --        ; (l = i1) → fst (unglue-invol-ₑ∙p ∘f
-- --                       (λ x → funExt λ y → cong x (fInvol y)) X i j)
-- --        ; (j = i0) → λ x y → x (fInvol y i)
-- --        ; (j = i1) → idfun _
-- --        }

-- --     isEqEJ0 : (i l : I) → isEquiv {A = A → B} {B = A → B} (λ x y → x (fInvol y i))
-- --     isEqEJ0 i l = isProp→PathP
-- --            (λ i → isPropIsEquiv (λ x y → x (fInvol y i)))
-- --            (snd (∘f ∙ₑ ∘f))
-- --             (idIsEquiv _) i

-- --     isEqEJ1 : (i l : I) → isEquiv {A = A → B} (λ x → x)
-- --     isEqEJ1 _ _ = idIsEquiv _

-- --     isEqI0L0 : _
-- --     isEqI0L0 = isProp→PathP (λ j → isPropIsEquiv (e i0 i0 j 1=1)) _ _

-- --     isEqI0L1 : _
-- --     isEqI0L1 = isProp→PathP (λ j → isPropIsEquiv (e i0 i1 j 1=1)) _ _


-- --     isEqE : ∀ i l j → PartialP (i ∨ ~ i ∨ j ∨ ~ j ∨ l ∨ ~ l)
-- --             λ o → isEquiv (e i l j o) 
-- --     isEqE i l j =
-- --      λ { (i = i0) →
-- --             isProp→SquareP
-- --             (λ l j → isPropIsEquiv (e i0 l j 1=1))
-- --                  (λ _ → snd (compEquiv ∘f ∘f))
-- --                  (λ _ → idIsEquiv _)
-- --                  isEqI0L0
-- --                  isEqI0L1 l j 
-- --        ; (i = i1) → idIsEquiv _
-- --        ; (l = i0) →
-- --             isProp→SquareP
-- --             (λ i j → isPropIsEquiv (e i i0 j 1=1))
-- --                  (λ i → isEqEJ0 i i0)
-- --                  (λ _ → idIsEquiv _)
-- --                  isEqI0L0
-- --                  (λ _ → idIsEquiv _) i j
-- --        ; (l = i1) →
-- --                       isProp→SquareP
-- --             (λ i j → isPropIsEquiv (e i i1 j 1=1))
-- --                  (λ i → isEqEJ0 i i1)
-- --                  (λ i → isEqEJ1 i i1)
-- --                  isEqI0L1
-- --                  (λ _ → idIsEquiv _) i j
-- --        ; (j = i0) → isEqEJ0 i l            
-- --        ; (j = i1) → isEqEJ1 i l      
-- --        }

-- -- dom-ₑ∙ₚ-comp²eq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (isSetA : isSet A)
-- --               → (f : A → A) → (fInvol : isInvolution f)
-- --               → (g : A → A) → (gInvol : isInvolution g)
-- --               → (fg-comm : f ∘ g ≡ g ∘ f) → 
-- --                 {X : (A → B) ≡ (A → B)}
-- --                 {X' : A ≡ A}
-- --               → (P : (λ i → X' i → B) ≡ X)
-- --               → Cube
-- --                   (dom-ₑ∙p g gInvol (dom-ₑ∙p f fInvol P ))
-- --                   (dom-ₑ∙p f fInvol (dom-ₑ∙p g gInvol P ))
-- --                   (λ i j → ₑ∙ₚ-comp²eq
-- --                      (involEquiv {f = f} fInvol)
-- --                      (involEquiv {f = g} gInvol) X' (equivEq (fg-comm)) i j → B)
-- --                   (ₑ∙ₚ-comp²eq _ _ X (equivEq
-- --                     (funExt λ x → cong (x ∘'_) (sym fg-comm))) )
-- --                   refl
-- --                   refl

-- --                   -- (λ l j → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P ) l j)
-- --                   -- P
-- --                   -- (λ i j → invol-ₑ∙p (involEquiv {f = f} fInvol) fInvol X' i j
-- --                   --         → B)
-- --                   -- (λ i j → invol-ₑ∙p (preCompInvol.e' {f = f} B fInvol)
-- --                   --     (λ x → funExt λ y → cong x (fInvol y)) X i j)
-- --                   -- (refl {x = λ l → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P) l i0})
-- --                   -- (refl {x = λ l → dom-ₑ∙p f fInvol (dom-ₑ∙p f fInvol P) l i1})
-- -- dom-ₑ∙ₚ-comp²eq {ℓ} {ℓ'} {B = B} isSetA f fInvol g gInvol fg-comm {X} {X'} P =
-- --    λ i l j →
-- --         Glue (P l j) λ o → T i l j o , E i l j o ,
-- --           {!!}  

-- --   where
-- --    T : ∀ i l j → Partial (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
-- --                (Type (ℓ-max ℓ ℓ'))
-- --    T i l j = λ {
-- --      (i = i0) → _
-- --     ;(i = i1) → _
-- --     ;(l = i0) → _
-- --     ;(l = i1) → _
-- --     ;(j = i0) → _
-- --     ;(j = i1) → _
-- --     }

-- --    isSetX' : ∀ j → isSet (X' j)
-- --    isSetX' j = isProp→PathP (λ j → isPropIsSet {A = X' j})
-- --      isSetA isSetA j

-- --    isSet-ₑ∙ₚ-comp²eq : ∀ i j →
-- --          isSet
-- --      (ₑ∙ₚ-comp²eq (involEquiv {f = f} fInvol) (involEquiv {f = g} gInvol) X'
-- --       (equivEq fg-comm) i j)
-- --    isSet-ₑ∙ₚ-comp²eq i j =
-- --      isOfHLevelRespectEquiv 2
-- --        (invEquiv (unglueEquiv (X' j) (i ∨ ~ i ∨ j ∨ ~ j)
-- --          (ₑ∙ₚ-comp²eq-sides
-- --           (involEquiv {f = f} fInvol) (involEquiv {f = g} gInvol) X'
-- --       (equivEq fg-comm) i j)))
-- --        (isSetX' j)

-- --    E : ∀ i l j → PartialP (l ∨ ~ l ∨ i ∨ ~ i ∨ j ∨ ~ j)
-- --                (λ o → T i l j o → P l j)
-- --    E i l j = λ {
-- --      (i = i0) →
-- --        unglue-dom-ₑ∙p f fInvol P l j ∘
-- --                unglue-dom-ₑ∙p g gInvol ((dom-ₑ∙p f fInvol P)) l j
-- --     ;(i = i1) →
-- --        unglue-dom-ₑ∙p g gInvol P l j ∘
-- --                unglue-dom-ₑ∙p f fInvol ((dom-ₑ∙p g gInvol P)) l j
-- --     ;(l = i0) → _∘ 
-- --                (isSet→SquareP {A = λ i j → X' j → 
-- --                 ₑ∙ₚ-comp²eq
-- --                      (involEquiv {f = f} fInvol)
-- --                      (involEquiv {f = g} gInvol) X' (equivEq (fg-comm)) i j}
-- --                       (λ i j →
-- --                     isSetΠ λ _ → isSet-ₑ∙ₚ-comp²eq i j)
-- --                     (λ j → (fst (glue-invol-ₑ∙p
-- --                           (involEquiv {f = g} gInvol) gInvol
-- --                            (involEquiv {f = f} fInvol ₑ∙ₚ X') j))
-- --                            ∘' (fst (glue-invol-ₑ∙p
-- --                           (involEquiv {f = f} fInvol) fInvol X' j)))
-- --                   (λ j → (fst (glue-invol-ₑ∙p
-- --                           (involEquiv {f = f} fInvol) fInvol
-- --                            (involEquiv {f = g} gInvol ₑ∙ₚ X') j))
-- --                            ∘' (fst (glue-invol-ₑ∙p
-- --                           (involEquiv {f = g} gInvol) gInvol X' j)))
-- --                   (sym fg-comm)
-- --                   (λ _ → idfun _) i j)
-- --     ;(l = i1) →  unglue (j ∨ ~ j ∨ i ∨ ~ i)
-- --        {e = λ o → snd (ₑ∙ₚ-comp²eq-sides
-- --           (preCompInvol.e' {f = f} B fInvol)
-- --           (preCompInvol.e' {f = g} B gInvol) X
-- --        (equivEq
-- --                     (funExt λ x → cong (x ∘'_) (sym fg-comm))) i j o)} 
-- --     ;(j = i0) → λ x → x ∘ (fg-comm (~ i))
-- --     ;(j = i1) → idfun _
-- --     }






-- -- -- h𝔽in : ∀ n → ℙrm n → hSet ℓ-zero
-- -- -- h𝔽in n = EMrec.f w
-- -- --  where
-- -- --   w : EMrec (Symmetric-Group (Fin n) (isSetFin {n})) isGroupoidHSet
-- -- --   EMrec.b w = Fin n , isSetFin {n}
-- -- --   EMrec.bloop w g = TypeOfHLevel≡ 2 (ua g)
-- -- --   EMrec.bComp w g h =
-- -- --      ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- --         λ i j →
-- -- --           Glue (ua {!ua !} i)
-- -- --             λ { (j = i0) → {!!}
-- -- --               ; (j = i1) → {!!}
-- -- --               }




-- -- -- 𝔽in : ∀ n → ℙrm n → Type ℓ-zero
-- -- -- 𝔽in  n = fst ∘ h𝔽in n


-- -- -- 𝔽h : (A : Type ℓ) → ∀ n → ℙrm n → Type ℓ
-- -- -- 𝔽h A n em = 𝔽in n em → A 





-- -- -- uaDom≃ : ∀ {ℓ ℓ'} {A B : Type ℓ} (C : Type ℓ') → (e : A ≃ B) →  
-- -- --      ua (preCompEquiv {C = C} (invEquiv e))
-- -- --        ≡ cong (λ X → X → C) (ua e)
-- -- -- uaDom≃ C e = {!!}
-- -- --   -- invEq≡→equivFun≡ (invEquiv univalence)
-- -- --   --  (equivEq (funExt (λ x →
-- -- --   --    fromPathP (funTypeTransp' (idfun _) C ((ua (isoToEquiv e))) x)
-- -- --   --     ∙ funExt λ y → cong x (cong (Iso.inv e) (transportRefl y)))))

-- -- -- 𝔽h* : (A : Type ℓ) → ∀ n → (p : ℙrm n) → singl (𝔽h A n p )
-- -- -- 𝔽h* A n = EMelim.f w
-- -- --  where
-- -- --  w : EMelim _ λ z → singl (𝔽h A n z)
-- -- --  EMelim.isGrpB w = {!!}
-- -- --  EMelim.b w = _ , refl
-- -- --  EMelim.bPathP w g = ΣPathP
-- -- --    ((ua (preCompEquiv {C = A} (invEquiv g))) ,
-- -- --      flipSquare (sym (uaDom≃ A g)))
-- -- --  EMelim.bSqP w = {!!}
 
-- -- -- 𝔽-≡ : (A : Type ℓ) → ∀ n (g : Fin n ≃ Fin n) →
-- -- --       PathP (λ i → singl (𝔽h A n (emloop g i)))
-- -- --       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- --       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- -- 𝔽-≡ A n g = ΣPathP
-- -- --     (ua ({!!} ∙ₑ preCompEquiv (invEquiv g) ∙ₑ {!Iso-×^-F→ n!})
-- -- --    , flipSquare (symP-fromGoal {!  uaDom≃ A g!}))
-- -- --  where
-- -- --  s : {!!}
-- -- --  s = (uaDomIso A {!!})

-- -- -- -- 𝕍 : (A : Type ℓ) → ∀ n em → singl (𝔽h A n em)
-- -- -- -- 𝕍 A n = EMelim.f w
-- -- -- --  where
-- -- -- --  w : EMelim _
-- -- -- --                      (λ z → singl (𝔽h A n z))
-- -- -- --  EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
-- -- -- --  EMelim.b w = (A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n)))
-- -- -- --  EMelim.bPathP w = 𝔽-≡ A n
-- -- -- --  fst (EMelim.bSqP w g h i j) = 𝔽-sq-fst A n g h i j
-- -- -- --  snd (EMelim.bSqP w g h i j) k = {!!}

-- -- ism : ∀ n → Iso (Perm n) (Iso (Fin n) (Fin n))
-- -- ism n = (fst (PermGIsoIso n))

-- -- lookTab≡ : ∀ n → (Fin n → A) ≡ (A ×^ n)
-- -- lookTab≡ n = ua (isoToEquiv (invIso (Iso-×^-F→ n)))



-- -- perm𝔽≡ : ∀ n → (g : Perm n) →
-- --              singl {A = (Fin n → A) ≡ (Fin n → A) }
-- --              (λ i → permFin n g i → A) 
-- -- perm𝔽≡ {ℓ} {A = A} n = Relim.f (w {n})
-- --  where
-- --  open Relim

-- --  ∘T : ∀ {n} → (Σ ℕ  λ k → (suc k < n)) → _
-- --  ∘T {n} k = preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k) 


-- --  w : ∀ {n} → Relim (λ z → singl (λ i → permFin n z i → A))
-- --  isSetA w _ = isOfHLevelPlus 2 (isContrSingl _)
-- --  εA w = refl , refl
-- --  fst (∷A (w {n}) k (X , _)) = ∘T {n} k ₑ∙ₚ X
-- --  snd (∷A w k (X , P)) = dom-ₑ∙p _ _ P  
-- --  invoA (w {n}) k (X , P) = ΣPathP
-- --     ((invol-ₑ∙p _ _ X) ,
-- --       dom-invol-ₑ∙p (isSetFin {n = n}) _ _ P)

-- --  braidA (w {n}) k k< (X , P) =
-- --    ΣPathP (ₑ∙ₚ-comp³eq _ _ _
-- --         (equivEq (funExt λ x →
-- --                 cong (x ∘'_) 
-- --                   (cong (Iso.fun ∘ permuteIso n) (braid k k< ε))))
-- --       , {!!})
 
-- --  commA (w {n}) k l z (X , P) =
-- --     ΣPathP (
-- --          ₑ∙ₚ-comp²eq _ _ _
-- --              (equivEq (funExt λ x →
-- --                 cong (x ∘'_) 
-- --                   (sym ((cong (Iso.fun ∘ permuteIso n) (comm k l z ε))))
-- --          ))

-- --       , dom-ₑ∙ₚ-comp²eq (isSetFin {n = n}) _ _ _ _
-- --             (cong (Iso.fun ∘ permuteIso n) (comm k l z ε)) P)




-- -- perm𝔽sq : ∀ n → isGroupoid A → (g h : Perm n)
-- --              → Square
-- --                (fst (perm𝔽≡ {A = A} n g))
-- --                (fst (perm𝔽≡ n (g · h)))
-- --                refl
-- --                (fst (perm𝔽≡ n h))
-- -- perm𝔽sq {A = A} n isGroupoid-A g h = Relim.f (w h) g
-- --  where
-- --  open Relim

-- --  ∘T : (Σ ℕ  λ k → (suc k < n)) → _
-- --  ∘T k = preCompInvol.e' {f = adjT n k} A (isInvolution-adjT n  k) 

-- --  w : (h : Perm n) → Relim (λ g → 
-- --                Square
-- --                (fst (perm𝔽≡ {A = A} n g))
-- --                (fst (perm𝔽≡ n (g · h)))
-- --                refl
-- --                (fst (perm𝔽≡ n h)))
-- --  isSetA (w h) _ =
-- --    {!!}
-- --  εA (w h) j i = (fst (perm𝔽≡ {A = A} n h)) (i ∧ j)
-- --  ∷A (w h) k X j i = (∘T k ₑ∙ₚ X j) i 
-- --  invoA (w h) k {xs} X l j i =
-- --     invol-ₑ∙p ((λ z x → z (adjT n k x)) ,
-- --                   involIsEquiv (λ x i b → x (isInvolution-adjT n k b i)))
-- --                   (λ x i z → x (isInvolution-adjT n k z i)) (X j) l i
-- --  braidA (w h) k k< X l j i = {!!}
 
-- --      -- ₑ∙ₚ-comp³eq
-- --      --  _ _
-- --      --  (X j)
-- --      --   (equivEq (funExt λ x →
-- --      --            cong (x ∘'_) 
-- --      --              (cong (Iso.fun ∘ permuteIso n) (braid k k< ε))))
-- --      --   l i

-- --  commA (w h) k l' z X l j i =
-- --     ₑ∙ₚ-comp²eq
-- --       (((λ z x → z (adjT n l' x)) ,
-- --                   involIsEquiv (λ x i b → x (isInvolution-adjT n l' b i))))
-- --       (((λ z x → z (adjT n k x)) ,
-- --                   involIsEquiv (λ x i b → x (isInvolution-adjT n k b i))))
-- --       (X j)
-- --        (equivEq (funExt (λ x → cong (x ∘'_)
-- --         (sym ((cong (Iso.fun ∘ permuteIso n) (comm k l' z ε)))) )))
-- --        l i




 
-- -- -- -- --  w∷' : ∀ n → ∀ k → (Fin n → A) ≡ (Fin n → A) →  (Fin n → A) ≡ (Fin n → A)
-- -- -- -- --  w∷' n k = (preCompEquiv (adjT'≃ {n = n} k)) ₑ∙ₚ_
   
-- -- -- -- --  w∷≃' : ∀ n k → (X : (Fin n → A) ≡ (Fin n → A)) 
-- -- -- -- --         → ∀ j → w∷' n k X j ≃ X j
-- -- -- -- --  w∷≃' n k X j = unglue-ₑ∙p (preCompEquiv (adjT'≃ {n = n} k)) X j
-- -- -- -- --    -- unglueEquiv (X j)
-- -- -- -- --    --   (j ∨ ~ j)
-- -- -- -- --    --   (λ { (j = i0) → (_ , preCompEquiv (adjT'≃ {n = n} k))
-- -- -- -- --    --      ; (j = i1) → (_ , idEquiv _) })

-- -- -- -- --  w∷'P : ∀ n k xs → (X : (Fin n → A) ≡ (Fin n → A))
-- -- -- -- --          → (λ i → permFin n xs i → A) ≡ X
-- -- -- -- --         → (λ i → permFin n (k ∷ xs) i → A) ≡ w∷' n k X
-- -- -- -- --                 -- (w∷≃' n k X j)
-- -- -- -- --  w∷'P n k xs X P j i = {!dom-ₑ∙p (adjT n k) (isInvolution-adjT n k) P j i!}
-- -- -- -- --   -- let z = preCompEquiv {C = A} (invEquiv (w∷≃ n k (permFin n xs) i))
-- -- -- -- --   --     -- z' = w∷≃' n k X i
-- -- -- -- --   --     v = preCompEquiv {C = A} (adjT'≃ {n = n} k)
-- -- -- -- --   -- in Glue (P j i) 
-- -- -- -- --   --      λ { (i = i0) → _ , fst v
-- -- -- -- --   --           , isPropIsEquiv _ (snd z) (snd v) j
-- -- -- -- --   --         ; (i = i1) → _ , idfun _
-- -- -- -- --   --           , isPropIsEquiv _ (snd z) (idIsEquiv _) j 
-- -- -- -- --   --         ; (j = i0) → _ , z
-- -- -- -- --   --         -- ; (j = i1) → w∷' n k X i , z'
-- -- -- -- --   --         }

-- -- -- -- --  -- w∷'P≃ : ∀ n k xs → (X : (Fin n → A) ≡ (Fin n → A))
-- -- -- -- --  --         → (P : (λ i → permFin n xs i → A) ≡ X)
-- -- -- -- --  --         → ∀ j i → w∷'P n k xs X P j i ≃ P j i 
-- -- -- -- --  -- w∷'P≃ n k xs X P j i = {!dom-invol-ₑ∙p !}
-- -- -- -- --   -- let z = preCompEquiv {C = A} (invEquiv (w∷≃ n k (permFin n xs) i))
-- -- -- -- --   --     -- z' = w∷≃' n k X i
-- -- -- -- --   --     v = preCompEquiv {C = A} (adjT'≃ {n = n} k)
-- -- -- -- --   -- in unglueEquiv (P j i) (i ∨ ~ i ∨ ~ j) 
-- -- -- -- --   --      λ { (i = i0) → _ , fst v
-- -- -- -- --   --           , isPropIsEquiv _ (snd z) (snd v) j
-- -- -- -- --   --         ; (i = i1) → _ , idfun _
-- -- -- -- --   --           , isPropIsEquiv _ (snd z) (idIsEquiv _) j 
-- -- -- -- --   --         ; (j = i0) → _ , z
-- -- -- -- --   --         -- ; (j = i1) → w∷' n k X i , z'
-- -- -- -- --   --         }

-- -- -- -- --  -- sqJ1-lem* : ∀ n k xs X P → Square {A = (Fin n → A) → Fin n → A}
-- -- -- -- --  --          (λ _ → idfun _)
-- -- -- -- --  --          (λ _ → idfun _)
-- -- -- -- --  --          (λ l → fst (w∷'P≃ n k (k ∷ xs)
-- -- -- -- --  --                    (w∷' n k X) (w∷'P n k xs X P) l i1))
-- -- -- -- --  --          (λ l → fst (invEquiv ((w∷'P≃ n k xs X P) l i1)))
-- -- -- -- --  -- sqJ1-lem* (suc (suc n)) (k , k<) xs X P = congP (λ _ → funExt)
-- -- -- -- --  --   (funExt λ f → congP (λ _ → cong uncurry)
-- -- -- -- --  --     (flipSquare {!!}) )


-- -- -- -- --  -- sqJ1-lem : ∀ n k xs X P → Square {A = (Fin n → A) → Fin n → A}
-- -- -- -- --  --          (λ _ → idfun _)
-- -- -- -- --  --          (λ _ → idfun _)
-- -- -- -- --  --          (λ l → fst (w∷'P≃ n k (k ∷ xs)
-- -- -- -- --  --                    (w∷' n k X) (w∷'P n k xs X P) l i1))
-- -- -- -- --  --          (λ l → fst (invEquiv ((w∷'P≃ n k xs X P) l i1)))
-- -- -- -- --  -- sqJ1-lem (suc (suc n)) (k , k<) xs X P = {!P!}


-- -- -- -- --  w : ∀ n → Relim λ (g : Perm n)
-- -- -- -- --               → singl {A = (Fin n → A) ≡ (Fin n → A) }
-- -- -- -- --              (λ i → permFin n g i → A)
-- -- -- -- --  isSetA (w n) _ = isOfHLevelPlus 2 (isContrSingl _)
-- -- -- -- --  fst (εA (w n)) = refl
-- -- -- -- --  snd (εA (w n)) = refl
-- -- -- -- --  fst (∷A (w n) k (X , _)) = w∷' n k X
-- -- -- -- --  snd (∷A (w n) k {xs} (X , P)) = w∷'P n k xs X P

-- -- -- -- --  fst (invoA (w n) k {xs} (X , _) i) j =
-- -- -- -- --    invol-ₑ∙p (preCompEquiv (adjT'≃ {n = n} k))
-- -- -- -- --       (λ x → funExt λ y → cong x (isInvolution-adjT n k y)) X i j 

-- -- -- -- --  snd (invoA (w n) k {xs} (X , P) i) = 
-- -- -- -- --    {!!}
-- -- -- -- --    -- dom-invol-ₑ∙p ? (adjT n k) (isInvolution-adjT n k) P i
-- -- -- -- --    -- {!!}
-- -- -- -- --   -- let z : ∀ i j → Σ ((w∷invo n k (permFin n xs) i j → A) → permFin n xs j → A)
-- -- -- -- --   --           isEquiv
-- -- -- -- --   --     z i j = preCompEquiv {A = permFin n xs j}
-- -- -- -- --   --                      {B = w∷invo n k (permFin n xs) i j} {C = A}
-- -- -- -- --   --                      (invEquiv (w∷invo-unglue≃ n k (permFin n xs) i j ))
-- -- -- -- --   --     zz : ∀ l j → Σ (w∷'P n k (k ∷ xs) (w∷' n k X) (w∷'P n k xs X P) l j → P l j)
-- -- -- -- --   --            isEquiv
-- -- -- -- --   --     zz l j = w∷'P≃ n k (k ∷ xs) (w∷' n k X)
-- -- -- -- --   --                 (w∷'P n k xs X P) l j
-- -- -- -- --   --                ∙ₑ w∷'P≃ n k xs X P l j

-- -- -- -- --   --     fj0 : I → I → (Fin n → A) → Fin n → A
-- -- -- -- --   --     fj0 i l = (λ x x₁ → x
-- -- -- -- --   --                            (isSet→isSet' (isSetFin {n})
                                
-- -- -- -- --   --                              (λ l → adjT n k (adjT n k x₁)) (λ _ → x₁)
-- -- -- -- --   --                              (λ i →
-- -- -- -- --   --                               invEq (w∷invo-unglue≃ n k (permFin n xs) i i0) x₁ )
-- -- -- -- --   --                               (λ i → isInvolution-adjT n k x₁ i) i l))
-- -- -- -- --   --     prfJ0I1 = (isPropIsEquiv _
-- -- -- -- --   --                   (snd (z i1 i0)) (idIsEquiv (Fin n → A)))
-- -- -- -- --   --     prfJ1I1 = (isPropIsEquiv _ (snd (z i1 i1))
-- -- -- -- --   --            (isPropIsEquiv (fst (w∷≃' n k (w∷' n k X) i1 ∙ₑ w∷≃' n k X i1))
-- -- -- -- --   --                               (snd (w∷≃' n k (w∷' n k X) i1 ∙ₑ w∷≃' n k X i1))
-- -- -- -- --   --                               (idIsEquiv (Fin n → A)) i1))


-- -- -- -- --   -- in Glue (P l j)
-- -- -- -- --   --       (λ { (j = i0) →  (Fin n → A) ,
-- -- -- -- --   --                          ?
-- -- -- -- --   --        ,
-- -- -- -- --   --          ?
-- -- -- -- --   --          -- isProp→SquareP (λ i l → isPropIsEquiv (fj0 i l))
-- -- -- -- --   --          --      (isProp→PathP (λ i → isPropIsEquiv (fj0 i i0))
-- -- -- -- --   --          --       (snd (zz i0 i0))
-- -- -- -- --   --          --                     (snd (z i1 i0)))
-- -- -- -- --   --          --      (isProp→PathP ((λ i → isPropIsEquiv (fj0 i i1)))
-- -- -- -- --   --          --        _ _) 
-- -- -- -- --   --          --       (λ l → snd (zz l i0))
-- -- -- -- --   --          --        prfJ0I1
-- -- -- -- --   --          --       i l
-- -- -- -- --   --          ; (j = i1) → (Fin n → A) ,
-- -- -- -- --   --                        ?
-- -- -- -- --   --                       -- (λ x x₁ → x (compPathRefl {x = x₁} (~ l) i))
                        
-- -- -- -- --   --                       ,
-- -- -- -- --   --                         ?
-- -- -- -- --   --                     --     isProp→SquareP (λ i l →
-- -- -- -- --   --                     --       isPropIsEquiv
-- -- -- -- --   --                     --         (λ x x₁ → x (compPathRefl {x = x₁} (~ l) i)))
-- -- -- -- --   --                     --       _
-- -- -- -- --   --                     --       (λ i → isPropIsEquiv (fst (w∷≃' n k (w∷' n k X) i1 ∙ₑ                               w∷≃' n k X i1))
-- -- -- -- --   --                     -- (snd (w∷≃' n k (w∷' n k X) i1 ∙ₑ w∷≃' n k X i1))
-- -- -- -- --   --                     -- (idIsEquiv (Fin n → A)) i)
-- -- -- -- --   --                     --     _
-- -- -- -- --   --                     --     prfJ1I1
-- -- -- -- --   --                     --       i l
-- -- -- -- --   --          ; (i = i0) → _  , zz l j 
-- -- -- -- --   --          ; (i = i1) → P l j , idfun (P l j) ,
-- -- -- -- --   --                 ?
-- -- -- -- --   --                -- isProp→SquareP (λ j l → isPropIsEquiv (idfun (P l j)))
-- -- -- -- --   --                --    (λ j → snd (z i1 j))
-- -- -- -- --   --                --    (λ j → idIsEquiv (P i1 j))
-- -- -- -- --   --                --    prfJ0I1
-- -- -- -- --   --                --    (isPropIsEquiv _ (snd (z i1 i0)) (idIsEquiv (P i1 i1)))
-- -- -- -- --   --                --    j l
-- -- -- -- --   --          ; (l = i0) → (w∷invo n k (permFin n xs) i j → A) ,
-- -- -- -- --   --                         fst (z i j)
-- -- -- -- --   --                         , ?
-- -- -- -- --   --                           -- isProp→SquareP
-- -- -- -- --   --                           --   (λ i j → isPropIsEquiv (fst (z i j)))
-- -- -- -- --   --                           --  (isProp→PathP
-- -- -- -- --   --                           --   ((λ i → isPropIsEquiv (fst (z i i0))))
-- -- -- -- --   --                           --   (snd (zz i0 i0))
-- -- -- -- --   --                           --    (snd (z i1 i0)))
-- -- -- -- --   --                           --  ((isProp→PathP
-- -- -- -- --   --                           --   ((λ i → isPropIsEquiv (fst (z i i1))))
-- -- -- -- --   --                           --   (snd (zz i0 i1))
-- -- -- -- --   --                           --    (snd (z i1 i1))))
-- -- -- -- --   --                           --  (λ j → snd (zz i0 j))
-- -- -- -- --   --                           --  (λ j → snd (z i1 j)) i j
           
                   
-- -- -- -- --   --          })
-- -- -- -- --  braidA (w n) = {!!}
-- -- -- -- --  commA (w n) = {!!}


-- -- -- -- -- -- perm𝔽sq : ∀ n → (g h : Perm n)
-- -- -- -- -- --              → Square
-- -- -- -- -- --                (fst (perm𝔽≡ {A = A} n g))
-- -- -- -- -- --                (fst (perm𝔽≡ n (g · h)))
-- -- -- -- -- --                refl
-- -- -- -- -- --                (fst (perm𝔽≡ n h))
-- -- -- -- -- -- perm𝔽sq {A = A} n g h = Relim.f (w h) g
-- -- -- -- -- --  where
-- -- -- -- -- --  open Relim

-- -- -- -- -- --  w∷* : (h : Perm n) → ∀ k → {xs : Perm n} →
-- -- -- -- -- --      Square (fst (perm𝔽≡ {A = A} n xs)) (fst (perm𝔽≡ n (xs · h))) refl
-- -- -- -- -- --       (fst (perm𝔽≡ n h)) →
-- -- -- -- -- --       Square (fst (perm𝔽≡ {A = A}  n (k ∷ xs))) (fst (perm𝔽≡ n ((k ∷ xs) · h)))
-- -- -- -- -- --       refl (fst (perm𝔽≡ n h))
-- -- -- -- -- --  w∷* h k {xs} X i j =
-- -- -- -- -- --    Glue (X i j)
-- -- -- -- -- --      λ { (j = i0) → (Fin n → A) ,
-- -- -- -- -- --         isoToEquiv (equiv→Iso (invEquiv (adjT'≃ {n = n} k)) (idEquiv A))
-- -- -- -- -- --       ; (j = i1) → fst (perm𝔽≡ {A = A} n h) i , idEquiv _ }

-- -- -- -- -- --  w∷*≃ : (h : Perm n) → ∀ k → (xs : Perm n) → ∀ X →
-- -- -- -- -- --     ∀ i j → w∷* h  k {xs} X i j ≃ X i j
-- -- -- -- -- --  w∷*≃ h k xs X i j =
-- -- -- -- -- --    unglueEquiv (X i j) (~ j ∨ j)
-- -- -- -- -- --      (λ { (j = i0) → (Fin n → A) ,
-- -- -- -- -- --         isoToEquiv (equiv→Iso (invEquiv (adjT'≃ {n = n} k)) (idEquiv A))
-- -- -- -- -- --       ; (j = i1) → fst (perm𝔽≡ {A = A} n h) i , idEquiv _ }) 

-- -- -- -- -- --  w : (h : Perm n) → Relim (λ g → 
-- -- -- -- -- --                Square
-- -- -- -- -- --                (fst (perm𝔽≡ {A = A} n g))
-- -- -- -- -- --                (fst (perm𝔽≡ n (g · h)))
-- -- -- -- -- --                refl
-- -- -- -- -- --                (fst (perm𝔽≡ n h)))
-- -- -- -- -- --  isSetA (w h) = {!!}
-- -- -- -- -- --  εA (w h) i j = fst (perm𝔽≡ {A = A} n h) (i ∧ j)
-- -- -- -- -- --  ∷A (w h) = w∷* h

-- -- -- -- -- --  invoA (w h) k {xs} X l i j =
-- -- -- -- -- --   let z :  ∀ i j → w∷* h k {k ∷ xs} (w∷* h k {xs} X) i j ≃ X i j
-- -- -- -- -- --       z i j = w∷*≃ h k (k ∷ xs) (w∷* h k {xs} X) i j
-- -- -- -- -- --           ∙ₑ w∷*≃ h k (xs) X i j
-- -- -- -- -- --   in Glue (X i j)
-- -- -- -- -- --      λ { (l = i0) → _ , z i j
-- -- -- -- -- --        ; (l = i1) → X i j , idEquiv _
-- -- -- -- -- --        ; (j = i0) → (Fin n → A)
-- -- -- -- -- --            , (λ x k' →
-- -- -- -- -- --              x (isInvolution-adjT n k k' l))
-- -- -- -- -- --            , isProp→SquareP
-- -- -- -- -- --                (λ i l → isPropIsEquiv (λ x k' → x (isInvolution-adjT n k k' l)))
-- -- -- -- -- --                   (λ i → snd (z i i0))
-- -- -- -- -- --                   (λ _ → idIsEquiv _)
-- -- -- -- -- --                   (isProp→PathP (λ _ → isPropIsEquiv _) _ _ )
-- -- -- -- -- --                   (isProp→PathP (λ _ → isPropIsEquiv _) _ _ ) i l

-- -- -- -- -- --        ; (j = i1) → _ , idfun _ ,
-- -- -- -- -- --              isProp→SquareP
-- -- -- -- -- --                (λ i l → isPropIsEquiv (idfun (X i i1)))
-- -- -- -- -- --                   (λ i → snd (z i i1))
-- -- -- -- -- --                   (λ _ → idIsEquiv _)
-- -- -- -- -- --                   (isPropIsEquiv _ _ _)
-- -- -- -- -- --                   (isPropIsEquiv _ _ _)
-- -- -- -- -- --                   i l
-- -- -- -- -- --            }


-- -- -- -- -- --  braidA (w h) = {!!}
-- -- -- -- -- --  commA (w h) = {!!}

-- -- -- -- -- --  -- w : Relim (λ g → (h : Perm n)
-- -- -- -- -- --  --             → Square
-- -- -- -- -- --  --               (fst (perm𝔽≡ {A = A} n g))
-- -- -- -- -- --  --               (fst (perm𝔽≡ n (g · h)))
-- -- -- -- -- --  --               refl
-- -- -- -- -- --  --               (fst (perm𝔽≡ n h)))
-- -- -- -- -- --  -- isSetA w = {!!}
-- -- -- -- -- --  -- εA w h i j = fst (perm𝔽≡ {A = A} n h) (i ∧ j)
-- -- -- -- -- --  -- ∷A w k X h i j =
-- -- -- -- -- --  --      Glue (X h i j) 
-- -- -- -- -- --  --    λ { (j = i0) → (Fin n → A) ,
-- -- -- -- -- --  --        isoToEquiv (equiv→Iso (invEquiv (adjT'≃ {n = n} k)) (idEquiv A))
-- -- -- -- -- --  --      ; (j = i1) → fst (perm𝔽≡ {A = A} n h) i , idEquiv _ }

-- -- -- -- -- --  -- invoA w k X i = {!!}
-- -- -- -- -- --  -- braidA w = {!!}
-- -- -- -- -- --  -- commA w = {!!}

-- -- -- -- -- -- perm𝔽 : ∀ n → (em : ℙrm' n) →
-- -- -- -- -- --              singl (𝔽in' n em → A) 
-- -- -- -- -- -- perm𝔽 {A = A} n = EMelim.f w
-- -- -- -- -- --  where

-- -- -- -- -- --  w : EMelim (PermG n) (λ z → singl (𝔽in' n z → _))
-- -- -- -- -- --  EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
-- -- -- -- -- --  EMelim.b w = (𝔽in' n embase → A) , refl
-- -- -- -- -- --  EMelim.bPathP w g =  
-- -- -- -- -- --   let z = perm𝔽≡ n g
-- -- -- -- -- --   in ΣPathP (fst z , flipSquare (snd z))
-- -- -- -- -- --  fst (EMelim.bSqP w g h i j) = perm𝔽sq {A = A} n g h i j
-- -- -- -- -- --  snd (EMelim.bSqP w g h i j) = {!!}




-- -- -- -- -- -- adjT×^'→ : ∀ {n} → ℕ →
-- -- -- -- -- --              (A ×^ n) → (A ×^ n)
-- -- -- -- -- -- adjT×^'→ {n = zero} _ x = x
-- -- -- -- -- -- adjT×^'→ {n = suc zero} _ x = x
-- -- -- -- -- -- adjT×^'→ {n = suc (suc n)} zero (x , x' , xs) = (x' , x , xs)
-- -- -- -- -- -- adjT×^'→ {n = suc (suc n)} (suc k) (x , xs) =
-- -- -- -- -- --    x , adjT×^'→ k xs

-- -- -- -- -- -- isInvo-adjT×^'→ : ∀ {n} → ∀ k → isInvolution (adjT×^'→ {A = A} {n} k) 
-- -- -- -- -- -- isInvo-adjT×^'→ {n = zero} k x = refl
-- -- -- -- -- -- isInvo-adjT×^'→ {n = suc zero} k x = refl
-- -- -- -- -- -- isInvo-adjT×^'→ {n = suc (suc n)} zero x = refl
-- -- -- -- -- -- isInvo-adjT×^'→ {n = suc (suc n)} (suc k) (x , xs) =
-- -- -- -- -- --  cong (x ,_) (isInvo-adjT×^'→ k xs)


-- -- -- -- -- -- braid-adjT×^'→ : ∀ {n} → ∀ k →  suc (suc k) < n → ∀ v → 
-- -- -- -- -- --   (adjT×^'→ {A = A} {n} k ∘ adjT×^'→ {A = A} {n} (suc k) ∘ adjT×^'→ {A = A} {n} (k)) v
-- -- -- -- -- --   ≡ (adjT×^'→ {A = A} {n} (suc k) ∘ adjT×^'→ {A = A} {n} (k) ∘ adjT×^'→ {A = A} {n} (suc k)) v
-- -- -- -- -- -- braid-adjT×^'→ {n = suc (suc (suc n))} zero x _ = refl
-- -- -- -- -- -- braid-adjT×^'→ {n = suc (suc (suc (suc n)))} (suc k) x (v , vs) =
-- -- -- -- -- --   cong (v ,_) (braid-adjT×^'→ k x vs)

-- -- -- -- -- -- adjT×^ : ∀ {n} → ℕ →
-- -- -- -- -- --   Iso (A ×^ n)
-- -- -- -- -- --       (A ×^ n)
-- -- -- -- -- -- adjT×^ {n} k =
-- -- -- -- -- --  involIso {f = adjT×^'→ {n} k} (isInvo-adjT×^'→ {n} k)

-- -- -- -- -- -- adjT×^≃ : ∀ {n} → ℕ →
-- -- -- -- -- --       (A ×^ n) ≃ (A ×^ n)
-- -- -- -- -- -- adjT×^≃ {n} k =
-- -- -- -- -- --  involEquiv {f = adjT×^'→ {n} k} (isInvo-adjT×^'→ {n} k)


-- -- -- -- -- -- comm-adjT×^'→ : ∀ {n} → ∀ k l → (k< : (suc k) < n) (l< : (suc l) < n) → 
-- -- -- -- -- --   A.commT k l → ∀ v →  
-- -- -- -- -- --   (adjT×^'→ {A = A} {n} l
-- -- -- -- -- --     ∘ adjT×^'→ {A = A} {n} k ) v
-- -- -- -- -- --   ≡ (adjT×^'→ {A = A} {n} k
-- -- -- -- -- --     ∘ adjT×^'→ {A = A} {n} l ) v
-- -- -- -- -- -- comm-adjT×^'→ {n = suc (suc (suc (suc n)))} zero (suc (suc l)) k< l< x v = refl
-- -- -- -- -- -- comm-adjT×^'→ {n = suc (suc (suc (suc n)))} (suc k) (suc (suc l)) k< l< x (v , vs) =
-- -- -- -- -- --    cong (v ,_) (comm-adjT×^'→
-- -- -- -- -- --     {n = suc (suc (suc n))} k (suc l) k< l< x vs)


-- -- -- -- -- -- lawAdj : ∀ n k → (f : Fin n → A) → tabulate {n = n}
-- -- -- -- -- --       (f ∘ adjT n k)
-- -- -- -- -- --       ≡ adjT×^'→ (fst k) (tabulate f)
-- -- -- -- -- -- lawAdj (suc (suc n)) (zero , snd₁) f = refl
-- -- -- -- -- -- lawAdj (suc (suc n)) (suc k , k<) f =
-- -- -- -- -- --   cong ((f (zero , _)) ,_) (lawAdj (suc n) (k , k<) (f ∘ sucF) )

-- -- -- -- -- -- lawAdj' : ∀ n k → (v : A ×^ n) →
-- -- -- -- -- --                 lookup v ∘ (adjT n k)
-- -- -- -- -- --             ≡  lookup (adjT×^'→ {n = n} (fst k) v)
-- -- -- -- -- -- lawAdj' (suc (suc n)) (zero , k<) v =
-- -- -- -- -- --   funExt (uncurry (cases (λ _ → refl)
-- -- -- -- -- --     (cases (λ _ → refl) λ _ _ → refl)))
-- -- -- -- -- -- lawAdj' (suc (suc (suc n))) (suc k , k<) v =
-- -- -- -- -- --   funExt (uncurry (cases (λ _ → refl)
-- -- -- -- -- --      λ kk y → funExt⁻ (lawAdj' (suc (suc n)) (k , k<) (snd v)) (kk , y)) )

-- -- -- -- -- -- lawAdj-invo : ∀ n k → (f : Fin n → A) →
-- -- -- -- -- --     Square
-- -- -- -- -- --       (lawAdj n k (f ∘ adjT n k))
-- -- -- -- -- --       (sym (isInvo-adjT×^'→ (fst k) (tabulate f)))
-- -- -- -- -- --       (cong (tabulate ∘' (f ∘'_)) (funExt (isInvolution-adjT n k)))
-- -- -- -- -- --       (cong′ (adjT×^'→ (fst k)) (lawAdj n k f))
 
-- -- -- -- -- -- lawAdj-invo (suc (suc n)) (zero , k<) f =
-- -- -- -- -- --   congP (λ i → cong ((f (0 , tt)) ,_))
-- -- -- -- -- --     (congP (λ i → cong ((f (1 , tt)) ,_))
-- -- -- -- -- --       (congP (λ i → cong (tabulate ∘' (f ∘'_)))
-- -- -- -- -- --        (isSet→isSet' (isSet→ (isSetFin {n = (suc (suc n))}))
-- -- -- -- -- --          _ _ _ _)))
-- -- -- -- -- -- lawAdj-invo (suc (suc (suc n))) (suc k , k<) f =
-- -- -- -- -- --    congP (λ i → cong ((f (0 , tt)) ,_))
-- -- -- -- -- --      (lawAdj-invo (suc (suc n)) (k , k<) (f ∘ sucF))

-- -- -- -- -- -- lawAdj'-invo : ∀ n k → (v : A ×^ n) →
-- -- -- -- -- --     Square
-- -- -- -- -- --       (cong′ (_∘ adjT n k) (lawAdj' n k v)) 
-- -- -- -- -- --       (sym (cong (lookup) (isInvo-adjT×^'→ (fst k) v)))      
-- -- -- -- -- --       ( funExt (cong (lookup v) ∘ (isInvolution-adjT n k)))
-- -- -- -- -- --       (lawAdj' n k (adjT×^'→ (fst k) v))

-- -- -- -- -- -- lawAdj'-invo (suc (suc n)) (zero , k<) v =
-- -- -- -- -- --   congP (λ _ → cong′ uncurry)
-- -- -- -- -- --     (refl A.sqP→ refl A.sqP→
-- -- -- -- -- --       congP (λ _ → cong′ (curry ∘ (lookup (snd (snd v)) ∘_ )))
-- -- -- -- -- --          (flipSquare ((isSet→ (isSetFin {n = n}))
-- -- -- -- -- --             _ _ _ _)))
  
-- -- -- -- -- -- lawAdj'-invo (suc (suc (suc n))) (suc k , k<) v =
-- -- -- -- -- --   congP (λ _ → cong′ uncurry)
-- -- -- -- -- --     (refl A.sqP→
-- -- -- -- -- --       congP (λ _ → cong′ curry)
-- -- -- -- -- --         (lawAdj'-invo (suc (suc n)) (k , k<) (snd v)))


-- -- -- -- -- -- lawAdj'-braidDiag' : ∀ n k k< → (v : A ×^ n) → ∀ m m< →
-- -- -- -- -- --   (lookup ((adjT×^'→ (suc k) ∘ adjT×^'→ k) v) ∘
-- -- -- -- -- --        adjT n (k , <-weaken {n = n} k<))
-- -- -- -- -- --       (m , m<)
-- -- -- -- -- --       ≡
-- -- -- -- -- --       (lookup ((adjT×^'→ k ∘ adjT×^'→ (suc k)) v) ∘ adjT n (suc k , k<))
-- -- -- -- -- --       (m , m<)
-- -- -- -- -- -- lawAdj'-braidDiag' (suc (suc (suc n))) zero k< v =
-- -- -- -- -- --   cases (λ _ → refl) (cases (λ _ → refl) (cases (λ _ → refl) λ _ _ → refl))  
-- -- -- -- -- -- lawAdj'-braidDiag' (suc (suc (suc (suc n)))) (suc k) k< v =
-- -- -- -- -- --  cases (λ _ → refl) (lawAdj'-braidDiag' (suc (suc (suc n))) k k< (snd v))

-- -- -- -- -- -- lawAdj'-braidDiag : ∀ n k k< → (v : A ×^ n) → ∀ m m< →
-- -- -- -- -- --   (lookup
-- -- -- -- -- --        ((adjT×^'→ (suc k) ∘ adjT×^'→ k) (adjT×^'→ (suc k) (adjT×^'→ k v)))
-- -- -- -- -- --        ∘ adjT n (k , <-weaken {n = n} k<))
-- -- -- -- -- --       (m , m<)
-- -- -- -- -- --       ≡
-- -- -- -- -- --       (lookup
-- -- -- -- -- --        ((adjT×^'→ k ∘ adjT×^'→ (suc k)) (adjT×^'→ (suc k) (adjT×^'→ k v)))
-- -- -- -- -- --        ∘ adjT n (suc k , k<))
-- -- -- -- -- --       (m , m<)
-- -- -- -- -- -- lawAdj'-braidDiag (suc (suc (suc n))) zero k< v =
-- -- -- -- -- --   cases (λ _ → refl) (cases (λ _ → refl) (cases (λ _ → refl) λ _ _ → refl))  
-- -- -- -- -- -- lawAdj'-braidDiag (suc (suc (suc (suc n)))) (suc k) k< v =
-- -- -- -- -- --  cases (λ _ → refl) (lawAdj'-braidDiag (suc (suc (suc n))) k k< (snd v))


-- -- -- -- -- -- lawAdj'-braidL' : ∀ n k k< → (v : A ×^ n) → ∀ m m<
-- -- -- -- -- --   → 
-- -- -- -- -- --     Square
-- -- -- -- -- --       ((funExt⁻ (lawAdj' n (k , <-weaken {n = n} k<)
-- -- -- -- -- --         ((adjT×^'→ (suc k) ∘ adjT×^'→ k) v)) (m , m<)))
      
-- -- -- -- -- --       (funExt⁻ (lawAdj' n (suc k , k<) _) (m , m<))      
-- -- -- -- -- --       (lawAdj'-braidDiag' n k k< v m m<)
-- -- -- -- -- --       (λ i → lookup (braid-adjT×^'→ k k< v
-- -- -- -- -- --        i) (m , m<))
-- -- -- -- -- -- lawAdj'-braidL' (suc (suc (suc n))) zero k< v =
-- -- -- -- -- --   cases (λ _ → refl) (cases (λ _ → refl)
-- -- -- -- -- --    (cases (λ _ → refl) λ _ _ → refl))
-- -- -- -- -- -- lawAdj'-braidL' (suc (suc (suc (suc n)))) (suc k) k< v =
-- -- -- -- -- --   cases (λ _ → refl)
-- -- -- -- -- --    (lawAdj'-braidL' (suc (suc (suc n))) k k< (snd v))

-- -- -- -- -- -- lawAdj'-braidR'-diag : ∀ n k (k< : suc (suc (suc k)) ≤ n)
-- -- -- -- -- --  → (v : A ×^ n) → ∀ m m< m<' 
-- -- -- -- -- --   → lookup (adjT×^'→ k v)
-- -- -- -- -- --       ((A.sucFun (A.adjTransposition k) ∘ A.adjTransposition k) m , m<)
-- -- -- -- -- --       ≡
-- -- -- -- -- --       lookup (adjT×^'→ (suc k) v)
-- -- -- -- -- --       (A.adjTransposition k (A.sucFun (A.adjTransposition k) m) , m<')
-- -- -- -- -- -- lawAdj'-braidR'-diag (suc (suc (suc n))) zero k< v =
-- -- -- -- -- --   cases (λ _ _ → refl)
-- -- -- -- -- --    (cases (λ _ _ → refl)
-- -- -- -- -- --      (cases (λ _ _ → refl) λ m m< m<' i →
-- -- -- -- -- --       lookup (snd (snd (snd v))) (m , isProp≤ {suc m} {n} m< m<' i)))

-- -- -- -- -- -- lawAdj'-braidR'-diag (suc (suc (suc n))) (suc k) k< v =
-- -- -- -- -- --   cases (λ _ _ → refl)
-- -- -- -- -- --    (lawAdj'-braidR'-diag (suc (suc (n))) (k) k< (snd v))

-- -- -- -- -- -- lawAdj'-braidR' : ∀ n k k< → (v : A ×^ n) → ∀ m m< m<'
-- -- -- -- -- --   → 
-- -- -- -- -- --     Square
-- -- -- -- -- --       ((funExt⁻ (lawAdj' n (k , <-weaken {n = n} k<)
-- -- -- -- -- --         _) (_ , m<)))
      
-- -- -- -- -- --       (funExt⁻ (lawAdj' n (suc k , k<) _)
-- -- -- -- -- --        (_ , m<'))
-- -- -- -- -- --        (λ i → lookup {A = A} v
-- -- -- -- -- --          (≡Fin {n = n} {_ , adjT< n k
-- -- -- -- -- --              ((A.sucFun (A.adjTransposition k) ∘ A.adjTransposition k) m)
-- -- -- -- -- --              (<-weaken {n = n} k<) m<}
-- -- -- -- -- --              {_ , adjT< n (suc k)
-- -- -- -- -- --           (A.adjTransposition k (A.sucFun (A.adjTransposition k) m)) k< m<'}
-- -- -- -- -- --            (λ i → A.adjTranspositionBraid k i m) i))
-- -- -- -- -- --       (lawAdj'-braidR'-diag n k k< v m m< m<')


-- -- -- -- -- -- -- lookup v (permuteF' n (braid k k< xs z) (k' , k'<))

-- -- -- -- -- -- lawAdj'-braidR' (suc (suc (suc n))) zero k< v =
-- -- -- -- -- --   cases (λ _ _ → refl)
-- -- -- -- -- --    (cases (λ _ _ → refl)
-- -- -- -- -- --      (cases (λ _ _ → refl)
-- -- -- -- -- --        λ m m< m<' →
-- -- -- -- -- --          congP (λ _ → cong (lookup (snd (snd (snd v)))))
-- -- -- -- -- --            (isSet→isSet' (isSetFin {n = n}) _ _ _ _)))


-- -- -- -- -- -- lawAdj'-braidR' (suc (suc (suc (suc n)))) (suc k) k< v =
-- -- -- -- -- --   cases (λ _ _ → refl)
-- -- -- -- -- --    (lawAdj'-braidR' (suc (suc (suc n))) (k) k< (snd v))

-- -- -- -- -- -- lawAdj'-braidL : ∀ n k k< → (v : A ×^ n) → ∀ m m<
-- -- -- -- -- --   → 
-- -- -- -- -- --     Square
-- -- -- -- -- --       ((funExt⁻ (lawAdj' n (k , <-weaken {n = n} k<) _) (m , m<)))
-- -- -- -- -- --       (funExt⁻ (lawAdj' n (suc k , k<) _) (m , m<))      
-- -- -- -- -- --       (lawAdj'-braidDiag n k k< v m m<)
-- -- -- -- -- --       (λ i → lookup (braid-adjT×^'→ k k< (adjT×^'→ (suc k) (adjT×^'→ k v))
-- -- -- -- -- --        i) (m , m<))
-- -- -- -- -- -- lawAdj'-braidL (suc (suc (suc n))) zero k< v =
-- -- -- -- -- --   cases (λ _ → refl) (cases (λ _ → refl)
-- -- -- -- -- --    (cases (λ _ → refl) λ _ _ → refl))
-- -- -- -- -- -- lawAdj'-braidL (suc (suc (suc (suc n)))) (suc k) k< v =
-- -- -- -- -- --   cases (λ _ → refl)
-- -- -- -- -- --    (lawAdj'-braidL (suc (suc (suc n))) k k< (snd v))


-- -- -- -- -- -- lawAdj'-braidCenter : ∀ n k k< → (v : A ×^ n) → ∀ m m< m<' m<''
-- -- -- -- -- --   → 
-- -- -- -- -- --     Square
-- -- -- -- -- --       (funExt⁻ (lawAdj' {A = A} n (suc k , m<'') _) _)
-- -- -- -- -- --       (funExt⁻ (lawAdj' {A = A} n (k , m<') _) _)
-- -- -- -- -- --       (lawAdj'-braidR'-diag n k k< v m _ _)
-- -- -- -- -- --       (lawAdj'-braidDiag' n k k< v m m<)
-- -- -- -- -- -- lawAdj'-braidCenter (suc (suc (suc n))) zero k< v =
-- -- -- -- -- --   cases (λ _  _ _ → refl) (cases (λ _  _ _ → refl)
-- -- -- -- -- --    (cases (λ _ _ _ → refl) λ _ _ _ _ →
-- -- -- -- -- --         congP (λ _ → cong (lookup (snd (snd (snd v)))))
-- -- -- -- -- --            (isSet→isSet' (isSetFin {n = n}) _ _ _ _)))

-- -- -- -- -- -- lawAdj'-braidCenter (suc (suc (suc (suc n)))) (suc k) k< v =
-- -- -- -- -- --   cases (λ _ _ _ → refl)
-- -- -- -- -- --    (lawAdj'-braidCenter (suc (suc (suc n))) k k< (snd v))

-- -- -- -- -- -- lawAdj'-comm-Diag : ∀ n k l k< l< (z : A.commT k l) → (v : A ×^ n) → ∀ m m<
-- -- -- -- -- --   → (lookup (adjT×^'→ k v) ∘ adjT n (l , l<)) (m , m<) ≡
-- -- -- -- -- --       (lookup (adjT×^'→ l v) ∘ adjT n (k , k<)) (m , m<)
-- -- -- -- -- -- lawAdj'-comm-Diag (suc (suc (suc (suc n)))) zero (suc (suc l)) k< l< z v =
-- -- -- -- -- --       cases (λ _ → refl)
-- -- -- -- -- --      (cases (λ _ → refl)
-- -- -- -- -- --        λ m m<
-- -- -- -- -- --         → funExt⁻ (lawAdj' (suc (suc n)) (l , l<) (snd (snd v))) (m , m<) )

-- -- -- -- -- -- lawAdj'-comm-Diag (suc (suc (suc (suc n)))) (suc k) (suc (suc (suc l))) k< l< z v = cases (λ _ → refl)
-- -- -- -- -- --   (lawAdj'-comm-Diag (suc (suc (suc n))) k (suc (suc l)) k< l< z (snd v))

-- -- -- -- -- -- lawAdj'-commR' : ∀ n k l k< l< z → (v : A ×^ n) → ∀ m m<
  
-- -- -- -- -- --   → 
-- -- -- -- -- --     Square 
-- -- -- -- -- --       ((funExt⁻ (lawAdj' n (l , l<) _) (m , m<)))
-- -- -- -- -- --       (funExt⁻ (lawAdj' n (k , k<) _) (m , m<))      
-- -- -- -- -- --       (lawAdj'-comm-Diag n k l k< l< z v m m<)
-- -- -- -- -- --       λ i → lookup (comm-adjT×^'→ k l k< l< z v i)
-- -- -- -- -- --         (m , m<)
-- -- -- -- -- -- lawAdj'-commR' (suc (suc (suc (suc n)))) zero (suc (suc l)) k< l< z v =
-- -- -- -- -- --   cases
-- -- -- -- -- --     (λ _ → refl)
-- -- -- -- -- --     (cases (λ _ → refl)
-- -- -- -- -- --       λ m m< i j →
-- -- -- -- -- --         lawAdj' (suc (suc n)) (l , l<) (snd (snd v)) (i ∨ j) (m , m<))
-- -- -- -- -- -- lawAdj'-commR' (suc (suc (suc (suc (suc n))))) (suc k) (suc (suc (suc l))) k< l< z v = cases (λ _ → refl)
-- -- -- -- -- --        (lawAdj'-commR' (suc (suc (suc (suc n)))) k (suc (suc l)) k< l< z (snd v))

-- -- -- -- -- -- lawAdj'-commL' : ∀ n k l k< l< z → (v : A ×^ n) → ∀ m m< 
-- -- -- -- -- --   → 
-- -- -- -- -- --     Square 
-- -- -- -- -- --       (funExt⁻ (lawAdj' n (k , k<) _) _)
-- -- -- -- -- --       (funExt⁻ (lawAdj' n (l , l<) _) _)
-- -- -- -- -- --       (cong′ (lookup v) (
-- -- -- -- -- --             ≡Fin {n = n} --{k = _ , m<'} {_ , m<''}
-- -- -- -- -- --              (sym (funExt⁻ (A.adjTranspositionComm k l z) m))))
-- -- -- -- -- --       (lawAdj'-comm-Diag n k l k< l< z v m m<)
-- -- -- -- -- -- lawAdj'-commL' (suc (suc (suc (suc n)))) zero (suc (suc l)) k< l< z v =
-- -- -- -- -- --   cases (λ _ → refl)
-- -- -- -- -- --    (cases (λ _ → refl)
-- -- -- -- -- --      λ m m< →  flipSquare (
-- -- -- -- -- --      congP (λ _ → cong′ (lookup (snd (snd v))))
-- -- -- -- -- --            (isSet→isSet' (isSetFin {n = (suc (suc n))})
-- -- -- -- -- --              (cong (A.adjTransposition l m ,_) _)
-- -- -- -- -- --              (cong (A.adjTransposition l m ,_) _)
-- -- -- -- -- --              (cong (A.adjTransposition l m ,_) _)
-- -- -- -- -- --              (cong (A.adjTransposition l m ,_) _)) ◁
-- -- -- -- -- --        λ i j →
-- -- -- -- -- --         (lawAdj' (suc (suc n)) (l , l<) (snd (snd v)) (i ∧ j) (m , m<))))
-- -- -- -- -- -- lawAdj'-commL' (suc (suc (suc (suc (suc n))))) (suc k) (suc (suc (suc l))) k< l< z v = cases (λ _ → refl)
-- -- -- -- -- --   (lawAdj'-commL' (suc (suc (suc (suc n)))) k (suc (suc l)) k< l< z (snd v))

-- -- -- -- -- -- -- permute→×^ : ∀ n → (p : Perm n) → 
-- -- -- -- -- -- --     singl {A = (A ×^ n) → (A ×^ n)}
-- -- -- -- -- -- --       (λ v → tabulate (lookup v ∘ permuteF n p))
-- -- -- -- -- -- -- permute→×^ {A = A} n = Relim.f (w n)
-- -- -- -- -- -- --   where

-- -- -- -- -- -- --    open Relim

   
-- -- -- -- -- -- --    w : ∀ n → Relim {n = n}
-- -- -- -- -- -- --       (λ z → singl {A = (A ×^ n) → (A ×^ n)}
-- -- -- -- -- -- --           (λ v → tabulate {A = A} {n = n}
-- -- -- -- -- -- --            (lookup {n = n} v ∘ permuteF n z)))
-- -- -- -- -- -- --    isSetA (w n) _ = isOfHLevelPlus 2 (isContrSingl _)
-- -- -- -- -- -- --    εA (w n) = (idfun _) , (funExt (Iso.leftInv (Iso-×^-F→ n)))
-- -- -- -- -- -- --    fst (∷A (w n) k {xs} (X , XP)) = (adjT×^'→ (fst k) ∘ X)
-- -- -- -- -- -- --    snd (∷A (w n) k {xs} (X , XP)) =      
-- -- -- -- -- -- --       funExt
-- -- -- -- -- -- --         (λ v →
-- -- -- -- -- -- --          lawAdj n k (lookup v ∘ permuteF n xs))
-- -- -- -- -- -- --           ∙ cong′ (adjT×^'→ (fst k) ∘_) XP
        
-- -- -- -- -- -- --    invoA (w n) k {xs} (f , p') =
-- -- -- -- -- -- --      -- TODO ; simplify
-- -- -- -- -- -- --      ΣPathP
-- -- -- -- -- -- --      (funExt (λ v → isInvo-adjT×^'→ (fst k) (f v)) ,
-- -- -- -- -- -- --       ((cong′ (
-- -- -- -- -- -- --          (funExt
-- -- -- -- -- -- --         (λ v →
-- -- -- -- -- -- --          lawAdj n k _)) ∙_)
-- -- -- -- -- -- --           (cong-∙ (adjT×^'→ (fst k) ∘_) _ _) ∙
-- -- -- -- -- -- --            assoc _ _ _)
-- -- -- -- -- -- --             ◁ comm→PathP (pp ∙ assoc _ _ _)))
-- -- -- -- -- -- --      where

-- -- -- -- -- -- --       ppL : (v : A ×^ n) →
-- -- -- -- -- -- --          _
-- -- -- -- -- -- --       ppL v = PathP∙∙→compPathR
-- -- -- -- -- -- --         (flipSquare (lawAdj-invo {A = A} n k (lookup v ∘
-- -- -- -- -- -- --             permuteF n xs)))

-- -- -- -- -- -- --       pp1 = _
-- -- -- -- -- -- --       pp : _
-- -- -- -- -- -- --       pp = cong′ (_∙ p') (cong funExt (funExt (ppL))
-- -- -- -- -- -- --         ∙ doubleCompPath-elim
-- -- -- -- -- -- --            (funExt ((λ x i →
-- -- -- -- -- -- --             lawAdj n k ((λ x₁ → lookup x (permuteF n xs x₁))
-- -- -- -- -- -- --               ∘ adjT n k) i))) _ _)
-- -- -- -- -- -- --         ∙ sym (assoc pp1 _ _)
-- -- -- -- -- -- --         ∙ cong′ (pp1 ∙_)
-- -- -- -- -- -- --           (homotopyNatural
-- -- -- -- -- -- --                (λ a → cong (_∘' a) (funExt (isInvo-adjT×^'→ (fst k))))
-- -- -- -- -- -- --                 p') 
     
-- -- -- -- -- -- --    braidA (w n) = {!!}
-- -- -- -- -- -- --    commA (w n) = {!!}


-- -- -- -- -- -- singl≡ExtIso : ∀ n → (p : Perm n) →
-- -- -- -- -- --   (f : (A ×^ n) → (A ×^ n)) →
-- -- -- -- -- --    (∀ v k k< →
-- -- -- -- -- --         (lookup v ((permuteF' n p) (k , k<)))
-- -- -- -- -- --            ≡ lookup (f v) (k , k<)) ≃ ( tabulate ∘'
-- -- -- -- -- --       (_∘ (permuteF' n p) )
-- -- -- -- -- --       ∘' lookup  ≡ f)
-- -- -- -- -- -- singl≡ExtIso {ℓ} {A = A} n p f =
-- -- -- -- -- --   (pathToEquiv
-- -- -- -- -- --     ( cong′ {A = (A ×^ n) → Type ℓ} (λ X → ∀ x → X x)
    
-- -- -- -- -- --         (funExt (λ x →
-- -- -- -- -- --           (λ i →
-- -- -- -- -- --             ((k : ℕ) (k< : suc k ≤ n) →
-- -- -- -- -- --         (Iso.rightInv (Iso-×^-F→ n)) (lookup x ∘ permuteF' n p) (~ i)
-- -- -- -- -- --        ((k , k<))
-- -- -- -- -- --        ≡ lookup (f x) (k , k<)))
-- -- -- -- -- --           ∙ (funExt₂Path) ∙
-- -- -- -- -- --           ua (invEquiv (congEquiv
-- -- -- -- -- --             (isoToEquiv (compIso (Iso-×^-F→ n) curryIso)))) 
-- -- -- -- -- --           )))) ∙ₑ funExtEquiv 

-- -- -- -- -- -- permute→×^' : ∀ n → (p : Perm n) → 
-- -- -- -- -- --     Σ ((A ×^ n) → (A ×^ n))
-- -- -- -- -- --      λ f → ∀ v k k< →
-- -- -- -- -- --         (lookup v ((permuteF' n p) (k , k<)))
-- -- -- -- -- --            ≡ lookup (f v) (k , k<)
-- -- -- -- -- -- permute→×^' {A = A} n = Relim.f (w n)
-- -- -- -- -- --  where
-- -- -- -- -- --   open Relim


-- -- -- -- -- --   h∷ : ∀ n xs k → 
-- -- -- -- -- --      ∀ v  k' k'< →
-- -- -- -- -- --        ((lookup {n = n} v ∘ permuteF' n (k ∷ xs)) ( k' , k'<)) ≡
-- -- -- -- -- --        ((lookup (adjT×^'→ (fst k) v) ∘ permuteF' n xs) ( k' , k'<)) 
-- -- -- -- -- --   h∷ n xs k v k' k'< i = 
-- -- -- -- -- --     (lawAdj' {A = A} n k v i) (permuteF' n xs (k' , k'<))

-- -- -- -- -- --   w : ∀ n → Relim {n = n} λ p → Σ ((A ×^ n) → (A ×^ n))
-- -- -- -- -- --      λ f → ∀ v k k< →
-- -- -- -- -- --         (lookup v ((permuteF' n p) (k , k<)))
-- -- -- -- -- --            ≡ lookup (f v) (k , k<)
-- -- -- -- -- --   isSetA (w n) p =
-- -- -- -- -- --      isOfHLevelRetractFromIso
-- -- -- -- -- --          2
-- -- -- -- -- --          (Σ-cong-iso-snd (equivToIso ∘ singl≡ExtIso n p))
-- -- -- -- -- --               (isOfHLevelPlus 2 (isContrSingl
-- -- -- -- -- --          ( tabulate {A = A} {n = n} ∘ ((_∘ permuteF' n p ))
-- -- -- -- -- --            ∘ lookup {A = A} {n = n})))
-- -- -- -- -- --   εA (w n) = (idfun _) , λ _ _ _ → refl
-- -- -- -- -- --   fst (∷A (w n) k {xs} (X , _)) = X ∘ adjT×^'→ (fst k)
-- -- -- -- -- --   snd (∷A (w n) k {xs} (X , XP)) v k' k< =
-- -- -- -- -- --     h∷ n xs k v k' k< ∙ XP (adjT×^'→ (fst k) v) k' k<
-- -- -- -- -- --   invoA (w n) k {xs} (X , XP) = 
-- -- -- -- -- --     ΣPathP
-- -- -- -- -- --     ((funExt
-- -- -- -- -- --      (λ v → cong X (isInvo-adjT×^'→ (fst k) v))) ,
-- -- -- -- -- --       funExt λ v → funExt λ m → funExt λ m< → 
-- -- -- -- -- --         sym (doubleCompPath-elim' _ _ _) ◁
-- -- -- -- -- --          λ i j →
-- -- -- -- -- --            hcomp
-- -- -- -- -- --             (λ l →
-- -- -- -- -- --               λ { (j = i0) →
-- -- -- -- -- --                     lawAdj'-invo n k v i (~ l) (permuteF' n xs (m , m<))
                   
-- -- -- -- -- --                  ; (j = i1) → XP (isInvo-adjT×^'→ (fst k) v i ) m m< l
-- -- -- -- -- --                  ; (i = i1) → invSides-filler
-- -- -- -- -- --                    (λ i →
-- -- -- -- -- --                      (lookup (isInvo-adjT×^'→ (fst k) v (~ i))
-- -- -- -- -- --                (permuteF' n xs (m , m<))))
-- -- -- -- -- --                  (XP v m m<) (j) (~ l) 
-- -- -- -- -- --                  })
-- -- -- -- -- --            (invSides-filler
-- -- -- -- -- --              (λ i → lookup (isInvo-adjT×^'→ (fst k) v i)
-- -- -- -- -- --                (permuteF' n xs (m , m<)))
-- -- -- -- -- --                 (sym (h∷ n xs k (adjT×^'→ (fst k) v) m m<)) (~ i) j)) 
-- -- -- -- -- --   braidA (w n) k k< {xs} (X , XP) =
-- -- -- -- -- --     ΣPathP (funExt (λ v → cong X (braid-adjT×^'→ k k< v))  ,
-- -- -- -- -- --      funExt₃ λ v k' k'< → 
-- -- -- -- -- --        λ i →
-- -- -- -- -- --           (lawAdj'-braidR' n k k< v _ _
-- -- -- -- -- --              (adjT< n k _ (<-weaken {suc (suc k)} {n} k<)
-- -- -- -- -- --                   (adjT< n (suc k) _
-- -- -- -- -- --                     k<
-- -- -- -- -- --                   (snd (permuteF' n xs (k' , k'<))))) i
-- -- -- -- -- --              ∙ (lawAdj'-braidCenter n _ _ _ _ _ _ _ i)
-- -- -- -- -- --              ∙ ( lawAdj'-braidL' n k k< v _ _ i )
-- -- -- -- -- --             ∙ XP (braid-adjT×^'→ k k< v i) k' k'<))
-- -- -- -- -- --   commA (w n) k l z {xs} (X , XP) =
-- -- -- -- -- --     ΣPathP (funExt (cong X ∘ (comm-adjT×^'→ (fst k) (fst l) (snd k) (snd l) z))
-- -- -- -- -- --      , λ i v k' k'< →
-- -- -- -- -- --        (lawAdj'-commL' n (fst k) (fst l) (snd k) (snd l) z v _ _ i
-- -- -- -- -- --        ∙ lawAdj'-commR' n (fst k) (fst l) (snd k) (snd l) z v _ _ i ∙
-- -- -- -- -- --          XP (comm-adjT×^'→ (fst k) (fst l) (snd k) (snd l) z v i) k' k'<))




-- -- -- -- -- -- permute→×^'-≡ : ∀ n g → fst (permute→×^' {A = A} n g) ≡
-- -- -- -- -- --     tabulate ∘ (( _∘ permuteF' n g)) ∘ lookup 
-- -- -- -- -- -- permute→×^'-≡ {A = A} n g =
-- -- -- -- -- --      sym ((fst ((singl≡ExtIso n g) _)) (snd (permute→×^' {A = A} n g)))    

-- -- -- -- -- -- lawAdjP : ∀ n k →
-- -- -- -- -- --   PathP (λ j → lookTab≡ {A = A} n j → lookTab≡ {A = A} n j)
-- -- -- -- -- --      (_∘ (adjT n k))
-- -- -- -- -- --      (adjT×^'→ (fst k))
-- -- -- -- -- -- lawAdjP {A = A} n k =
-- -- -- -- -- --       cong ((_∘ adjT n k) ∘_)
-- -- -- -- -- --      (sym (funExt (Iso.leftInv (invIso (Iso-×^-F→ {A = A} n)))))
-- -- -- -- -- --    ◁ z ▷
-- -- -- -- -- --    cong (_∘ adjT×^'→ (fst k))
-- -- -- -- -- --      (funExt (Iso.rightInv (invIso (Iso-×^-F→ {A = A} n))))

-- -- -- -- -- --  where
-- -- -- -- -- --   e = (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))

-- -- -- -- -- --   -- z' : PathP (λ j → lookTab≡ {A = A} n j → lookTab≡ {A = A} n j)
-- -- -- -- -- --   --       ?
-- -- -- -- -- --   -- z' i x = {!!}


-- -- -- -- -- --   z : PathP (λ j → lookTab≡ {A = A} n j → lookTab≡ {A = A} n j)
-- -- -- -- -- --      ((_∘ adjT n k) ∘ lookup {A = A} {n = n} ∘ tabulate {A = A} {n = n})
-- -- -- -- -- --      (tabulate ∘ lookup ∘ adjT×^'→ (fst k))
-- -- -- -- -- --   z i x = ua-gluePathExt e i ( lawAdj' n k (( ua-ungluePathExt e i) x) i)
  



-- -- -- -- -- -- -- -- Perm𝕍 : ∀ {ℓ} {A : Type ℓ} n → (em : ℙrm' n) →
-- -- -- -- -- -- -- --   Σ (Type ℓ) λ T → (𝔽in' n em → A) → T
-- -- -- -- -- -- -- -- Perm𝕍 {A = A} n = EMelim.f w
-- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- --  open Relim

-- -- -- -- -- -- -- --  w : EMelim (PermG n) (λ z → Σ (Type _) (λ T → (𝔽in' n z → _) → T))
-- -- -- -- -- -- -- --  EMelim.isGrpB w = {!!}
-- -- -- -- -- -- -- --  fst (EMelim.b w) = A ×^ n 
-- -- -- -- -- -- -- --  snd (EMelim.b w) = tabulate 
-- -- -- -- -- -- -- --  EMelim.bPathP w g = {!!}
-- -- -- -- -- -- -- --  EMelim.bSqP w = {!!}

-- -- -- -- -- -- F≡ : ∀ n (g : Perm n) → singlP
-- -- -- -- -- --    (λ j → lookTab≡ {A = A} n j
-- -- -- -- -- --         ≡ lookTab≡ {A = A} n j)
-- -- -- -- -- --                    (λ i → fst (perm𝔽≡ {A = A} n g) i) 

-- -- -- -- -- -- F≡ {A = A} n = Relim.f (w n)
-- -- -- -- -- --  where
-- -- -- -- -- --  open Relim

-- -- -- -- -- --  w : ∀ n → Relim λ (g : Perm n)
-- -- -- -- -- --               → singlP (λ j → lookTab≡ {A = A} n j ≡ lookTab≡ {A = A} n j)
-- -- -- -- -- --                                (λ i → fst (perm𝔽≡ {A = A} n g) i)
-- -- -- -- -- --  isSetA (w n) _ = isOfHLevelPlus 2 (isContrSinglP _ _)
-- -- -- -- -- --  εA (w n) = refl , λ j i → lookTab≡ {A = A} n j 
-- -- -- -- -- --  fst (∷A (w n) k (X , _)) = (adjT×^≃ (fst k) ₑ∙ₚ X)  
-- -- -- -- -- --  snd (∷A (w n) k (X , P)) i =
-- -- -- -- -- --      (lawAdjP n k i  ,
-- -- -- -- -- --        isProp→PathP (λ i → isPropIsEquiv (lawAdjP n k i))
-- -- -- -- -- --            (isoToIsEquiv (equiv→Iso (invEquiv (adjT'≃ {n = n} k)) (idEquiv A)))
-- -- -- -- -- --            (isoToIsEquiv (involIso (isInvo-adjT×^'→ (fst k))))
-- -- -- -- -- --            i  )   ₑ∙ₚ P i
-- -- -- -- -- --  fst (invoA (w n) k x' l) =
-- -- -- -- -- --    {!!}
-- -- -- -- -- --  snd (invoA (w n) k x' l) i j = {!!}
-- -- -- -- -- --  braidA (w n) = {!!}
-- -- -- -- -- --  commA (w n) = {!!}

-- -- -- -- -- -- -- -- -- -- F≡ : ∀ n (g : Perm n) → singlP (λ j → lookTab≡ {A = A} n j ≡ lookTab≡ {A = A} n j)
-- -- -- -- -- -- -- -- -- --                                (λ i → permFin n g i → A) 

-- -- -- -- -- -- -- -- -- -- F≡ n = Relim.f (w n)
-- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- --  open Relim

-- -- -- -- -- -- -- -- -- --  w : ∀ n → Relim λ (g : Perm n)
-- -- -- -- -- -- -- -- -- --               → singlP (λ j → lookTab≡ {A = A} n j ≡ lookTab≡ {A = A} n j)
-- -- -- -- -- -- -- -- -- --                                (λ i → permFin n g i → A)
-- -- -- -- -- -- -- -- -- --  isSetA (w n) _ = isOfHLevelPlus 2 (isContrSinglP _ _)
-- -- -- -- -- -- -- -- -- --  fst (εA (w n)) = refl
-- -- -- -- -- -- -- -- -- --  snd (εA (w n)) i j = {!!}
-- -- -- -- -- -- -- -- -- --  ∷A (w n) = {!!}
-- -- -- -- -- -- -- -- -- --  invoA (w n) = {!!}
-- -- -- -- -- -- -- -- -- --  braidA (w n) = {!!}
-- -- -- -- -- -- -- -- -- --  commA (w n) = {!!}



-- -- -- -- -- -- -- -- -- -- isEquiv-permute→×^' : ∀ n g → isEquiv (fst (permute→×^' {A = A} n g))
-- -- -- -- -- -- -- -- -- -- isEquiv-permute→×^' {A = A} n g =
-- -- -- -- -- -- -- -- -- --  let p = funExt λ x → 
-- -- -- -- -- -- -- -- -- --        let zz = funExt (uncurry ((snd (permute→×^' {A = A} n g)) x))
-- -- -- -- -- -- -- -- -- --        in isoFunInjective (Iso-×^-F→ n) _ _
-- -- -- -- -- -- -- -- -- --          ( Iso.rightInv (Iso-×^-F→ n) _ ∙  zz)

-- -- -- -- -- -- -- -- -- --  in subst isEquiv p
-- -- -- -- -- -- -- -- -- --           (snd (isoToEquiv (Iso-×^-F→ n)
-- -- -- -- -- -- -- -- -- --              ∙ₑ preCompEquiv (isoToEquiv (invIso (permuteIso n g)))
-- -- -- -- -- -- -- -- -- --              ∙ₑ isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- -- -- -- -- -- -- -- -- -- 







-- -- -- -- -- -- -- -- -- -- isEquiv-permute→×^' : ∀ n g → isEquiv (fst (permute→×^' {A = A} n g))
-- -- -- -- -- -- -- -- -- -- isEquiv-permute→×^' {A = A} n = RelimProp.f (w n)
-- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- --  open Relim

-- -- -- -- -- -- -- -- -- --  w : ∀ n → RelimProp {n = n} λ g → isEquiv (fst (permute→×^' {A = A} n g))
-- -- -- -- -- -- -- -- -- --  RelimProp.isPropA (w n) _ = isPropIsEquiv _
-- -- -- -- -- -- -- -- -- --  RelimProp.εA (w n) = idIsEquiv _
-- -- -- -- -- -- -- -- -- --  RelimProp.∷A (w n) k x = snd (compEquiv (isoToEquiv (adjT×^ (fst k))) (_ , x))
 

-- -- -- -- -- -- -- -- -- -- -- module _ (isGroupoidA : isGroupoid A) where

-- -- -- -- -- -- -- -- -- -- --  𝔽-≡-lem : ∀ n (g : Perm n) →
-- -- -- -- -- -- -- -- -- -- --           PathP (λ j → ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j →
-- -- -- -- -- -- -- -- -- -- --                           ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j)
-- -- -- -- -- -- -- -- -- -- --                   (idfun _)
-- -- -- -- -- -- -- -- -- -- --                   (fst (permute→×^' n g))
-- -- -- -- -- -- -- -- -- -- --  𝔽-≡-lem n = Relim.f (w n)
-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --   open Relim

-- -- -- -- -- -- -- -- -- -- --   zz : ∀ j → ∀ n → ℕ → (ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j →
-- -- -- -- -- -- -- -- -- -- --                          ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j)
-- -- -- -- -- -- -- -- -- -- --                → (ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j →
-- -- -- -- -- -- -- -- -- -- --                          ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j)
-- -- -- -- -- -- -- -- -- -- --   zz j n k f =
-- -- -- -- -- -- -- -- -- -- --       (ua-gluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j
-- -- -- -- -- -- -- -- -- -- --           ∘ Iso.fun (Iso-×^-F→ {A = A} n) ∘ adjT×^'→ k)
-- -- -- -- -- -- -- -- -- -- --      ∘ ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j

-- -- -- -- -- -- -- -- -- -- --   w : ∀ n → Relim {n = n} λ g →
-- -- -- -- -- -- -- -- -- -- --          PathP (λ j → ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j →
-- -- -- -- -- -- -- -- -- -- --                           ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j)
-- -- -- -- -- -- -- -- -- -- --                   (idfun _)
-- -- -- -- -- -- -- -- -- -- --                   (fst (permute→×^' n g))
-- -- -- -- -- -- -- -- -- -- --   isSetA (w n) = {!!}
-- -- -- -- -- -- -- -- -- -- --   εA (w n) j x = x
-- -- -- -- -- -- -- -- -- -- --   ∷A (w (suc (suc n))) (zero , k<) x j =
-- -- -- -- -- -- -- -- -- -- --     {!zz j (suc (suc n)) zero !}
-- -- -- -- -- -- -- -- -- -- --   ∷A (w (suc (suc n))) (suc k , k<) x = {!!}
-- -- -- -- -- -- -- -- -- -- --   invoA (w n) = {!!}
-- -- -- -- -- -- -- -- -- -- --   braidA (w n) = {!!}
-- -- -- -- -- -- -- -- -- -- --   commA (w n) = {!!}

-- -- -- -- -- -- -- -- -- -- --  --   {!!}
-- -- -- -- -- -- -- -- -- -- --  -- where
-- -- -- -- -- -- -- -- -- -- --  --  zz : PathP (λ j → ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j →
-- -- -- -- -- -- -- -- -- -- --  --                         ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j)
-- -- -- -- -- -- -- -- -- -- --  --                    {!!}
-- -- -- -- -- -- -- -- -- -- --  --                    {!!}
-- -- -- -- -- -- -- -- -- -- --  --  zz j = 
-- -- -- -- -- -- -- -- -- -- --  --         (ua-gluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j
-- -- -- -- -- -- -- -- -- -- --  --          ∘ {!Iso.fgu(invIso (Iso-×^-F→ {A = A} n))!})
-- -- -- -- -- -- -- -- -- -- --  --     ∘ ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j

-- -- -- -- -- -- -- -- -- -- -- unglue-∷ : (A : Type ℓ) → ∀ n (g : Perm n) k →
-- -- -- -- -- -- -- -- -- -- --   PathP
-- -- -- -- -- -- -- -- -- -- --     (λ i → 𝔽in' n (emloop g i) → 𝔽in' n (emloop (k ∷ g) i))
-- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- --     -- (adjT n k)
-- -- -- -- -- -- -- -- -- -- --     -- (idfun _)
-- -- -- -- -- -- -- -- -- -- -- unglue-∷ A n = Relim.f {n = n} (w n)
-- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- --  open Relim

-- -- -- -- -- -- -- -- -- -- --  w : ∀ n → Relim (λ (g : Perm n) → ∀ k
-- -- -- -- -- -- -- -- -- -- --              → PathP
-- -- -- -- -- -- -- -- -- -- --                (λ i → 𝔽in' n (emloop g i) → 𝔽in' n (emloop (k ∷ g) i))
-- -- -- -- -- -- -- -- -- -- --                (adjT n k)
-- -- -- -- -- -- -- -- -- -- --                (idfun _))
-- -- -- -- -- -- -- -- -- -- --  w n = {!!}

-- -- -- -- -- -- -- -- -- --   -- ua-gluePathExt ((isoToEquiv (permuteIso n (k ∷ g)))) i ∘
-- -- -- -- -- -- -- -- -- --   --   ua-ungluePathExt (isoToEquiv (permuteIso n g)) i

-- -- -- -- -- -- -- -- -- -- -- 𝔽-≡-lem : (A : Type ℓ) → ∀ n (g : Perm n) →
-- -- -- -- -- -- -- -- -- -- --     PathP (λ i → (𝔽in' n (emloop g i) → A) → A ×^ n)
-- -- -- -- -- -- -- -- -- -- --            (fst (permute→×^' {A = A} n g) ∘ tabulate)
-- -- -- -- -- -- -- -- -- -- --            tabulate
-- -- -- -- -- -- -- -- -- -- -- 𝔽-≡-lem A n = {!!}
-- -- -- -- -- -- -- -- -- --  -- Relim.f {n = n} (w n)
-- -- -- -- -- -- -- -- -- --  -- where
-- -- -- -- -- -- -- -- -- --  -- open Relim

-- -- -- -- -- -- -- -- -- --  -- w : ∀ n → Relim
-- -- -- -- -- -- -- -- -- --  --      (λ z →
-- -- -- -- -- -- -- -- -- --  --         PathP (λ i → (𝔽in' n (emloop z i) → A) → A ×^ n)
-- -- -- -- -- -- -- -- -- --  --         (fst (permute→×^' n z) ∘ tabulate) tabulate)
-- -- -- -- -- -- -- -- -- --  -- isSetA (w n) = {!!}
-- -- -- -- -- -- -- -- -- --  -- εA (w n) = {!!}
-- -- -- -- -- -- -- -- -- --  -- ∷A (w (suc (suc n))) (zero , k<) {xs} X = 
-- -- -- -- -- -- -- -- -- --  --  let z = {!!}
-- -- -- -- -- -- -- -- -- --  --  in {!!}
-- -- -- -- -- -- -- -- -- --  -- ∷A (w (suc (suc (suc n)))) (suc k , k<) {xs} X = {!!}

-- -- -- -- -- -- -- -- -- -- -- {!adjT×^'→ (fst k) !}
-- -- -- -- -- -- -- -- -- --  -- invoA (w n) = {!!}
-- -- -- -- -- -- -- -- -- --  -- braidA (w n) = {!!}
-- -- -- -- -- -- -- -- -- --  -- commA (w n) = {!!}
 
-- -- -- -- -- -- -- -- -- --  -- isSetA w = {!!}
-- -- -- -- -- -- -- -- -- --  -- εA w i = {!(ua-ungluePathExt (isoToEquiv (permuteIso n ε))) i!}
-- -- -- -- -- -- -- -- -- --  -- ∷A w = {!!}
-- -- -- -- -- -- -- -- -- --  -- invoA w = {!!}
-- -- -- -- -- -- -- -- -- --  -- braidA w = {!!}
-- -- -- -- -- -- -- -- -- --  -- commA w = {!!}


-- -- -- -- -- -- -- -- -- -- 𝔽-≡ : (A : Type ℓ) → ∀ n (g : Perm n) →
-- -- -- -- -- -- -- -- -- --       Square 
-- -- -- -- -- -- -- -- -- --       (ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- -- -- -- -- -- -- -- --       (ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- -- -- -- -- -- -- -- --       (λ i → 𝔽h' A n (emloop g i))
-- -- -- -- -- -- -- -- -- --       (ua (_ , isEquiv-permute→×^' n g))
-- -- -- -- -- -- -- -- -- -- 𝔽-≡ A n = RelimProp.f w
-- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- --  w : RelimProp
-- -- -- -- -- -- -- -- -- --        (λ z →
-- -- -- -- -- -- -- -- -- --           Square (ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- -- -- -- -- -- -- -- --           (ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- -- -- -- -- -- -- -- --           (λ i → 𝔽h' A n (emloop z i)) (ua (_ , isEquiv-permute→×^' n z)))
-- -- -- -- -- -- -- -- -- --  RelimProp.isPropA w = {!!}
-- -- -- -- -- -- -- -- -- --  RelimProp.εA w i j = {!!}
-- -- -- -- -- -- -- -- -- --  RelimProp.∷A w k {xs} x i j =
-- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- --    -- Glue (x i j) {i ∨ ~ i ∨ j ∨ ~ j}
-- -- -- -- -- -- -- -- -- --    --      (λ { (i = i0) → x i0 j ,
-- -- -- -- -- -- -- -- -- --    --               ua-gluePathExt (isoToEquiv (invIso (Iso-×^-F→ n))) j ∘ 
-- -- -- -- -- -- -- -- -- --    --               (lookup ∘ fst (isoToEquiv (adjT×^ (fst k))) )
-- -- -- -- -- -- -- -- -- --    --               ∘ ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ n))) j  , {!!}
-- -- -- -- -- -- -- -- -- --    --         ; (i = i1) → x i1 j , {!!} , {!!}
-- -- -- -- -- -- -- -- -- --    --         ; (j = i0) → (𝔽in' n (emloop (k ∷ xs) i) → A) ,
-- -- -- -- -- -- -- -- -- --    --             (λ y → y ∘ invEq (w∷≃ n k (permFin n (xs)) i))
-- -- -- -- -- -- -- -- -- --    --            ,
-- -- -- -- -- -- -- -- -- --    --             {!!}
-- -- -- -- -- -- -- -- -- --    --         ; (j = i1) → x i i1 ,
-- -- -- -- -- -- -- -- -- --    --           tabulate ∘ lookup ∘ fst (isoToEquiv (adjT×^ (fst k))) , {!!}
-- -- -- -- -- -- -- -- -- --    --         }) 


-- -- -- -- -- -- -- -- -- -- --   let (e , p')  = permute→×^' {A = A} n g
-- -- -- -- -- -- -- -- -- -- --       p = funExt λ x → 
-- -- -- -- -- -- -- -- -- -- --        let zz = funExt (uncurry (p' x))
-- -- -- -- -- -- -- -- -- -- --        in isoFunInjective (Iso-×^-F→ n) _ _
-- -- -- -- -- -- -- -- -- -- --          ( Iso.rightInv (Iso-×^-F→ n) _ ∙  zz)

-- -- -- -- -- -- -- -- -- -- --       g≃ : {!!}
-- -- -- -- -- -- -- -- -- -- --       g≃ = (_ , isEquiv-permute→×^' n g)

-- -- -- -- -- -- -- -- -- -- --       -- g⁻≃ : {!!}
-- -- -- -- -- -- -- -- -- -- --       -- g⁻≃ = (_ , isEquiv-permute→×^' {A = A} n (inv g))

-- -- -- -- -- -- -- -- -- -- --       pp : PathP (λ i → (𝔽in' n (emloop g i) → A) → A ×^ n)
-- -- -- -- -- -- -- -- -- -- --                  (fst (permute→×^' {A = A} n g) ∘ tabulate)
-- -- -- -- -- -- -- -- -- -- --                  tabulate
-- -- -- -- -- -- -- -- -- -- --       pp = cong (_∘ (tabulate)) (permute→×^'-≡ n g)
-- -- -- -- -- -- -- -- -- -- --                ◁ (λ i →    
           
-- -- -- -- -- -- -- -- -- -- --              λ a → tabulate
-- -- -- -- -- -- -- -- -- -- --                  (  (Iso.rightInv (Iso-×^-F→ {A = A} n))
-- -- -- -- -- -- -- -- -- -- --                     ((a ∘ ((ua-gluePathExt ((isoToEquiv (permuteIso n g)) ) i)))) i
-- -- -- -- -- -- -- -- -- -- --                         ∘ permuteF' n g  ))
-- -- -- -- -- -- -- -- -- -- --                   ▷ ( cong′ (tabulate ∘'_)
-- -- -- -- -- -- -- -- -- -- --                        (funExt  λ k → 
-- -- -- -- -- -- -- -- -- -- --                           cong (k ∘_) (funExt (Iso.rightInv (permuteIso n g)))  )  )

-- -- -- -- -- -- -- -- -- -- --   in ΣPathP (ua g≃  ,

-- -- -- -- -- -- -- -- -- -- --        λ i j →
-- -- -- -- -- -- -- -- -- -- --         Glue
-- -- -- -- -- -- -- -- -- -- --           (A ×^ n) {~ i ∨ i ∨ ~ j ∨ j}
-- -- -- -- -- -- -- -- -- -- --           λ {(i = i0) → ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j ,
-- -- -- -- -- -- -- -- -- -- --                        fst g≃  ∘
-- -- -- -- -- -- -- -- -- -- --                         (ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))))
-- -- -- -- -- -- -- -- -- -- --                           j
-- -- -- -- -- -- -- -- -- -- --                        --   fst (permute→×^' {A = A} n g) ∘
-- -- -- -- -- -- -- -- -- -- --                        --  ua-ungluePathExt
-- -- -- -- -- -- -- -- -- -- --                        --   (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))
-- -- -- -- -- -- -- -- -- -- --                        --   j
-- -- -- -- -- -- -- -- -- -- --                          --  ua-ungluePathExt
-- -- -- -- -- -- -- -- -- -- --                          -- (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))
-- -- -- -- -- -- -- -- -- -- --                          -- j ∘
-- -- -- -- -- -- -- -- -- -- --                          --   {!!}
-- -- -- -- -- -- -- -- -- -- --                        -- ua-ungluePathExt
-- -- -- -- -- -- -- -- -- -- --                        --   (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))
-- -- -- -- -- -- -- -- -- -- --                        --   j ∘ ?
-- -- -- -- -- -- -- -- -- -- --                          ,
-- -- -- -- -- -- -- -- -- -- --                        {!!}
-- -- -- -- -- -- -- -- -- -- --             ;(i = i1) → ua ((isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))) j ,
-- -- -- -- -- -- -- -- -- -- --                           -- {!!}
-- -- -- -- -- -- -- -- -- -- --                          (ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))
-- -- -- -- -- -- -- -- -- -- --                              j ) 
-- -- -- -- -- -- -- -- -- -- --                          --   ∘ fst (permute→×^' {A = A} n (inv g)) ∘ ua-ungluePathExt
                         
-- -- -- -- -- -- -- -- -- -- --                          -- (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))
-- -- -- -- -- -- -- -- -- -- --                          -- j
                         
-- -- -- -- -- -- -- -- -- -- --                          ,
-- -- -- -- -- -- -- -- -- -- --                        {!!}
-- -- -- -- -- -- -- -- -- -- --             ;(j = i0) → (𝔽in' n (emloop g i) → A) ,
-- -- -- -- -- -- -- -- -- -- --                         pp i ,
-- -- -- -- -- -- -- -- -- -- --                        -- pp i ,
-- -- -- -- -- -- -- -- -- -- --                        {!!}
-- -- -- -- -- -- -- -- -- -- --             ;(j = i1) → ua g≃ i ,
-- -- -- -- -- -- -- -- -- -- --                        ua-ungluePathExt g≃ i
-- -- -- -- -- -- -- -- -- -- --                       -- ua-gluePathExt g⁻≃ i
-- -- -- -- -- -- -- -- -- -- --                       --  -- ∘ fst (permute→×^' {A = A} n (inv g))
-- -- -- -- -- -- -- -- -- -- --                       --  ∘ ua-ungluePathExt g≃ i
-- -- -- -- -- -- -- -- -- -- --                        ,
-- -- -- -- -- -- -- -- -- -- --                       {!!}
-- -- -- -- -- -- -- -- -- -- --              }

-- -- -- -- -- -- -- -- -- -- -- -------------

-- -- -- -- -- -- -- -- -- -- --        -- λ i j →
-- -- -- -- -- -- -- -- -- -- --        --  Glue
-- -- -- -- -- -- -- -- -- -- --        --    (ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j) {i ∨ ~ i ∨ ~ j ∨ j}
-- -- -- -- -- -- -- -- -- -- --        --    λ {(i = i0) → ua (isoToEquiv (invIso (Iso-×^-F→ n))) j ,
-- -- -- -- -- -- -- -- -- -- --        --          idEquiv _
-- -- -- -- -- -- -- -- -- -- --        --      ;(i = i1) → ua (isoToEquiv (invIso (Iso-×^-F→ n))) j
-- -- -- -- -- -- -- -- -- -- --        --          , {! !}
-- -- -- -- -- -- -- -- -- -- --        --          , {!!}
-- -- -- -- -- -- -- -- -- -- --        --      ;(j = i0) → (𝔽in' n (emloop g i) → A) ,
-- -- -- -- -- -- -- -- -- -- --        --          (_∘ ua-gluePathExt (isoToEquiv (permuteIso n g)) i) 
-- -- -- -- -- -- -- -- -- -- --        --             ,
-- -- -- -- -- -- -- -- -- -- --        --         {!!}
-- -- -- -- -- -- -- -- -- -- --        --      ;(j = i1) → {!!} ,
-- -- -- -- -- -- -- -- -- -- --        --            {!!} 
-- -- -- -- -- -- -- -- -- -- --        --             ,
-- -- -- -- -- -- -- -- -- -- --        --         {!!}
-- -- -- -- -- -- -- -- -- -- --        --       }


-- -- -- -- -- -- -- -- -- -- -- ------------

-- -- -- -- -- -- -- -- -- -- --        -- λ i j →
-- -- -- -- -- -- -- -- -- -- --        --  Glue
-- -- -- -- -- -- -- -- -- -- --        --    (A ×^ n) {i ∨ ~ i ∨ ~ j}
-- -- -- -- -- -- -- -- -- -- --        --    λ {(i = i0) → ua (isoToEquiv (invIso (Iso-×^-F→ n))) j ,
                
-- -- -- -- -- -- -- -- -- -- --        --          fst (permute→×^' n g)
-- -- -- -- -- -- -- -- -- -- --        --           ∘ ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ n))) j
-- -- -- -- -- -- -- -- -- -- --        --         , {!!}
-- -- -- -- -- -- -- -- -- -- --        --      ;(i = i1) → ua (isoToEquiv (invIso (Iso-×^-F→ n))) j ,
-- -- -- -- -- -- -- -- -- -- --        --         ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ n))) j
-- -- -- -- -- -- -- -- -- -- --        --          , {!!}
-- -- -- -- -- -- -- -- -- -- --        --      ;(j = i0) → (𝔽in' n (emloop g i) → A) ,
-- -- -- -- -- -- -- -- -- -- --        --          {!!}
-- -- -- -- -- -- -- -- -- -- --        --          -- {!(Iso.fun (invIso (Iso-×^-F→ n)))!} ∘ (_∘ ua-gluePathExt (isoToEquiv (permuteIso n g)) i)
-- -- -- -- -- -- -- -- -- -- --        --             ,
-- -- -- -- -- -- -- -- -- -- --        --         {!!}
-- -- -- -- -- -- -- -- -- -- --        --       }
-- -- -- -- -- -- -- -- -- -- --        )





-- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽-sq-fst : (A : Type ℓ) → (isGroupoid A) → ∀ n → (g h : Perm n) → 
-- -- -- -- -- -- -- -- -- -- -- -- --   Square
-- -- -- -- -- -- -- -- -- -- -- -- --     (congP (λ _ → fst) (𝔽-≡ A n g))
-- -- -- -- -- -- -- -- -- -- -- -- --     (congP (λ _ → fst) (𝔽-≡ A n (g · h)))
-- -- -- -- -- -- -- -- -- -- -- -- --     refl
-- -- -- -- -- -- -- -- -- -- -- -- --     (congP (λ _ → fst) (𝔽-≡ A n h) )
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽-sq-fst {ℓ} A isGrpA n = Relim.f (w n)
-- -- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- -- --   open Relim

-- -- -- -- -- -- -- -- -- -- -- -- --   w∷ : ∀ n → I → (k : Σ ℕ (λ k₁ → suc k₁ < n)) {xs : Perm n} →
-- -- -- -- -- -- -- -- -- -- -- -- --       ((h : Perm n) →
-- -- -- -- -- -- -- -- -- -- -- -- --        Square (congP (λ _ → fst) (𝔽-≡ A n xs))
-- -- -- -- -- -- -- -- -- -- -- -- --        (congP (λ _ → fst) (𝔽-≡ A n (xs · h))) refl
-- -- -- -- -- -- -- -- -- -- -- -- --        (congP (λ _ → fst) (𝔽-≡ A n h))) →
-- -- -- -- -- -- -- -- -- -- -- -- --       (h : Perm n) → I → I → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- --       -- Square (congP (λ _ → fst) (𝔽-≡ A n (k ∷ xs)))
-- -- -- -- -- -- -- -- -- -- -- -- --       -- (congP (λ _ → fst) (𝔽-≡ A n (k ∷ (xs · h)))) refl
-- -- -- -- -- -- -- -- -- -- -- -- --       -- (congP (λ _ → fst) (𝔽-≡ A n h))
-- -- -- -- -- -- -- -- -- -- -- -- --   w∷ n l k {xs} X h =
-- -- -- -- -- -- -- -- -- -- -- -- --     λ i j →
-- -- -- -- -- -- -- -- -- -- -- -- --           hfill
-- -- -- -- -- -- -- -- -- -- -- -- --            (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- --             (i = i0) → ua-CompFill'∙ₑ
-- -- -- -- -- -- -- -- -- -- -- -- --               ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k))))
-- -- -- -- -- -- -- -- -- -- -- -- --               (_ , isEquiv-permute→×^' n (xs)) l j 
-- -- -- -- -- -- -- -- -- -- -- -- --            ;(i = i1) →
-- -- -- -- -- -- -- -- -- -- -- -- --                 ua-CompFill'∙ₑ
-- -- -- -- -- -- -- -- -- -- -- -- --               ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k))))
-- -- -- -- -- -- -- -- -- -- -- -- --               (_ , isEquiv-permute→×^' n (xs · h)) l j
-- -- -- -- -- -- -- -- -- -- -- -- --            ;(j = i0) → 
-- -- -- -- -- -- -- -- -- -- -- -- --              (ua (isoToEquiv (adjT×^ {A = A} {n = n} (fst k))) (~ l)) --A ×^ n
-- -- -- -- -- -- -- -- -- -- -- -- --            ;(j = i1) → fst (𝔽-≡ A n h i)   --z i l
-- -- -- -- -- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- -- -- -- -- --               (inS (X h i j))
-- -- -- -- -- -- -- -- -- -- -- -- --               l
 
-- -- -- -- -- -- -- -- -- -- -- -- --   w : ∀ n → Relim {n = n}
-- -- -- -- -- -- -- -- -- -- -- -- --         λ g → (h : Perm n) → 
-- -- -- -- -- -- -- -- -- -- -- -- --             Square
-- -- -- -- -- -- -- -- -- -- -- -- --               (congP (λ _ → fst) (𝔽-≡ A n g))
-- -- -- -- -- -- -- -- -- -- -- -- --               (congP (λ _ → fst) (𝔽-≡ A n (g · h)))
-- -- -- -- -- -- -- -- -- -- -- -- --               (refl {x = A ×^ n})
-- -- -- -- -- -- -- -- -- -- -- -- --               (congP (λ _ → fst) (𝔽-≡ A n h))
-- -- -- -- -- -- -- -- -- -- -- -- --   isSetA (w n) x =
-- -- -- -- -- -- -- -- -- -- -- -- --     isSetΠ λ _ → isOfHLevelRetractFromIso 2
-- -- -- -- -- -- -- -- -- -- -- -- --       (invIso PathP→comm-Iso)
-- -- -- -- -- -- -- -- -- -- -- -- --       (isOfHLevel≡ 3
-- -- -- -- -- -- -- -- -- -- -- -- --         (isOfHLevel×^ n 3 isGrpA)
-- -- -- -- -- -- -- -- -- -- -- -- --         (isOfHLevel×^ n 3 isGrpA)
-- -- -- -- -- -- -- -- -- -- -- -- --         _ _)
    
-- -- -- -- -- -- -- -- -- -- -- -- --   εA (w n) h = ua-CompFill _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- --   ∷A (w n) k {xs} X h i j = w∷ n i1 k {xs} X h i j
-- -- -- -- -- -- -- -- -- -- -- -- --   invoA (w n) k {xs} X l h i j = 
-- -- -- -- -- -- -- -- -- -- -- -- --     hcomp
-- -- -- -- -- -- -- -- -- -- -- -- --      (λ m →
-- -- -- -- -- -- -- -- -- -- -- -- --        λ {  (l = i1) → w∷ n (~ m) k {xs} X h i j
-- -- -- -- -- -- -- -- -- -- -- -- --            ;(i = i0) → i0Cu l (~ m) j 
-- -- -- -- -- -- -- -- -- -- -- -- --            ;(i = i1) →
-- -- -- -- -- -- -- -- -- -- -- -- --               let ff : ∀ l m →
-- -- -- -- -- -- -- -- -- -- -- -- --                        involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- -- -- -- -- -- -- -- -- -- -- --                          (isInvo-adjT×^'→ (fst k)) l (~ m) → A ×^ n
-- -- -- -- -- -- -- -- -- -- -- -- --                   ff = λ l m → (fst (permute→×^' n (xs · h)) ∘
-- -- -- -- -- -- -- -- -- -- -- -- --                        (λ x →
-- -- -- -- -- -- -- -- -- -- -- -- --                          ua-unglue ((involEquiv
-- -- -- -- -- -- -- -- -- -- -- -- --                         {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- -- -- -- -- -- -- -- -- -- -- --                           (isInvo-adjT×^'→ (fst k)))) l
-- -- -- -- -- -- -- -- -- -- -- -- --                            (unglue (m ∨ ~ m) x))) 
-- -- -- -- -- -- -- -- -- -- -- -- --               in Glue (A ×^ n)
-- -- -- -- -- -- -- -- -- -- -- -- --                   (λ { (j = i0) →
-- -- -- -- -- -- -- -- -- -- -- -- --                      (involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- -- -- -- -- -- -- -- -- -- -- --                     (isInvo-adjT×^'→ {n = n} (fst k)) l) (~ m) ,
-- -- -- -- -- -- -- -- -- -- -- -- --                      ff l m ,
-- -- -- -- -- -- -- -- -- -- -- -- --                      isProp→SquareP (λ l m →
-- -- -- -- -- -- -- -- -- -- -- -- --                          isPropIsEquiv (ff l m))
-- -- -- -- -- -- -- -- -- -- -- -- --                        refl
-- -- -- -- -- -- -- -- -- -- -- -- --                        (isProp→PathP
-- -- -- -- -- -- -- -- -- -- -- -- --                           (λ l → isPropIsEquiv (ff l i1))
-- -- -- -- -- -- -- -- -- -- -- -- --                             _ _)
-- -- -- -- -- -- -- -- -- -- -- -- --                        (isProp→PathP
-- -- -- -- -- -- -- -- -- -- -- -- --                           (λ m → isPropIsEquiv (ff i0 m))
-- -- -- -- -- -- -- -- -- -- -- -- --                             (isEquiv-permute→×^' n (k ∷ (xs · h)))
-- -- -- -- -- -- -- -- -- -- -- -- --                             (isEquiv-permute→×^' n (k ∷ k ∷ (xs · h))))
-- -- -- -- -- -- -- -- -- -- -- -- --                        (symP (isProp→PathP
-- -- -- -- -- -- -- -- -- -- -- -- --                          ((λ m → isPropIsEquiv (ff i1 (~ m))))
-- -- -- -- -- -- -- -- -- -- -- -- --                            (isEquiv-permute→×^' n (xs · h))
-- -- -- -- -- -- -- -- -- -- -- -- --                             (isEquiv-permute→×^' n (k ∷ (xs · h)))))
-- -- -- -- -- -- -- -- -- -- -- -- --                        l m
-- -- -- -- -- -- -- -- -- -- -- -- --                      ; (j = i1) → (_ , idEquiv _)
-- -- -- -- -- -- -- -- -- -- -- -- --                  })
-- -- -- -- -- -- -- -- -- -- -- -- --            ;(j = i0) →
-- -- -- -- -- -- -- -- -- -- -- -- --              involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- -- -- -- -- -- -- -- -- -- -- --                (isInvo-adjT×^'→ {n = n} (fst k)) l (~ m)
               
-- -- -- -- -- -- -- -- -- -- -- -- --            ;(j = i1) → fst (𝔽-≡ A n h i)
-- -- -- -- -- -- -- -- -- -- -- -- --            ;(l = i0) →
-- -- -- -- -- -- -- -- -- -- -- -- --               (w∷ n (m) k {k ∷ xs}
-- -- -- -- -- -- -- -- -- -- -- -- --           (λ h i j → w∷ n i1 k {xs} X h i j) h i j)
             
-- -- -- -- -- -- -- -- -- -- -- -- --           })
-- -- -- -- -- -- -- -- -- -- -- -- --           (w∷ n i1 k {xs} X h i j)
       

-- -- -- -- -- -- -- -- -- -- -- -- --     where

-- -- -- -- -- -- -- -- -- -- -- -- --       i0CuP : SquareP
-- -- -- -- -- -- -- -- -- -- -- -- --            (λ l m → involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- -- -- -- -- -- -- -- -- -- -- --              (isInvo-adjT×^'→ {A = A} {n = n} (fst k)) l m → (A ×^ n))
-- -- -- -- -- -- -- -- -- -- -- -- --             (λ m → fst (permute→×^' n (k ∷ xs)) ∘
-- -- -- -- -- -- -- -- -- -- -- -- --                ua-ungluePathExt
-- -- -- -- -- -- -- -- -- -- -- -- --                  ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k)))) m)
-- -- -- -- -- -- -- -- -- -- -- -- --             (λ m → fst (permute→×^' n (xs)) ∘
-- -- -- -- -- -- -- -- -- -- -- -- --                ua-ungluePathExt
-- -- -- -- -- -- -- -- -- -- -- -- --                  ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k)))) (~ m))
-- -- -- -- -- -- -- -- -- -- -- -- --             (cong (fst (permute→×^' n xs) ∘_)
-- -- -- -- -- -- -- -- -- -- -- -- --                (funExt (isInvo-adjT×^'→ {n = n} (fst k))))
-- -- -- -- -- -- -- -- -- -- -- -- --             (refl {x = fst (permute→×^' n (k ∷ xs)) ∘
-- -- -- -- -- -- -- -- -- -- -- -- --                          ua-ungluePathExt (isoToEquiv (adjT×^ (fst k))) i1})
-- -- -- -- -- -- -- -- -- -- -- -- --       i0CuP l m x =
-- -- -- -- -- -- -- -- -- -- -- -- --         let x' = unglue (m ∨ ~ m) x
-- -- -- -- -- -- -- -- -- -- -- -- --             x'' =  ua-unglue ((involEquiv
-- -- -- -- -- -- -- -- -- -- -- -- --                    {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- -- -- -- -- -- -- -- -- -- -- --                      (isInvo-adjT×^'→ (fst k)))) l x'
-- -- -- -- -- -- -- -- -- -- -- -- --         in fst (permute→×^' n (xs)) x''

-- -- -- -- -- -- -- -- -- -- -- -- --       i0Cu : PathP (λ l → Square
-- -- -- -- -- -- -- -- -- -- -- -- --                     ((congP (λ _ → fst) (𝔽-≡ A n (invo k xs l))))
-- -- -- -- -- -- -- -- -- -- -- -- --                     ((congP (λ _ → fst) (𝔽-≡ A n (k ∷ xs))))
                    
-- -- -- -- -- -- -- -- -- -- -- -- --                     (involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- -- -- -- -- -- -- -- -- -- -- --                (isInvo-adjT×^'→ {n = n} (fst k)) l)
-- -- -- -- -- -- -- -- -- -- -- -- --                     refl)
-- -- -- -- -- -- -- -- -- -- -- -- --           (symP (ua-CompFill'∙ₑ
-- -- -- -- -- -- -- -- -- -- -- -- --               ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k))))
-- -- -- -- -- -- -- -- -- -- -- -- --               (_ , isEquiv-permute→×^' n (k ∷ xs)))  )
-- -- -- -- -- -- -- -- -- -- -- -- --           ((ua-CompFill'∙ₑ
-- -- -- -- -- -- -- -- -- -- -- -- --               ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k))))
-- -- -- -- -- -- -- -- -- -- -- -- --               (_ , isEquiv-permute→×^' n (xs))))
-- -- -- -- -- -- -- -- -- -- -- -- --       i0Cu l m j =
-- -- -- -- -- -- -- -- -- -- -- -- --        Glue (A ×^ n)
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ { (j = i0) → (
-- -- -- -- -- -- -- -- -- -- -- -- --              (involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- -- -- -- -- -- -- -- -- -- -- --                (isInvo-adjT×^'→ {n = n} (fst k)) l) m
-- -- -- -- -- -- -- -- -- -- -- -- --              , (i0CuP l m) ,
-- -- -- -- -- -- -- -- -- -- -- -- --                  isProp→SquareP
-- -- -- -- -- -- -- -- -- -- -- -- --                    (λ l m → isPropIsEquiv (i0CuP l m))
-- -- -- -- -- -- -- -- -- -- -- -- --                    (isProp→PathP (λ l → isPropIsEquiv (i0CuP l i0)) _ _)
-- -- -- -- -- -- -- -- -- -- -- -- --                    (refl)
-- -- -- -- -- -- -- -- -- -- -- -- --                    (symP ((isProp→PathP
-- -- -- -- -- -- -- -- -- -- -- -- --                       (λ m → isPropIsEquiv (i0CuP i0 (~ m)))
-- -- -- -- -- -- -- -- -- -- -- -- --                       (isEquiv-permute→×^' n (k ∷ xs))
-- -- -- -- -- -- -- -- -- -- -- -- --                       (snd ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k)))
-- -- -- -- -- -- -- -- -- -- -- -- --                        ∙ₑ (_ , isEquiv-permute→×^' n (k ∷ xs)))))))
-- -- -- -- -- -- -- -- -- -- -- -- --                   (isProp→PathP
-- -- -- -- -- -- -- -- -- -- -- -- --                       (λ m → isPropIsEquiv (i0CuP i1 (m)))
-- -- -- -- -- -- -- -- -- -- -- -- --                       (isEquiv-permute→×^' n xs)
-- -- -- -- -- -- -- -- -- -- -- -- --                       (snd ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k)))
-- -- -- -- -- -- -- -- -- -- -- -- --                        ∙ₑ (_ , isEquiv-permute→×^' n xs))))
-- -- -- -- -- -- -- -- -- -- -- -- --                      l m)
-- -- -- -- -- -- -- -- -- -- -- -- --             ; (j = i1) → (_ , idEquiv _)
-- -- -- -- -- -- -- -- -- -- -- -- --             })
      
-- -- -- -- -- -- -- -- -- -- -- -- --   braidA (w n) k k< x' = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --   commA (w n) k l z x' = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽-sq-snd : (A : Type ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- --    → (isGroupoidA : isGroupoid A) → ∀ n → (g h : Perm n) → 
-- -- -- -- -- -- -- -- -- -- -- -- --   SquareP (λ i j → 𝔽h' A n (emcomp g h i j) ≡
-- -- -- -- -- -- -- -- -- -- -- -- --      𝔽-sq-fst A isGroupoidA n g h i j)
-- -- -- -- -- -- -- -- -- -- -- -- --     (congP (λ _ → snd) (𝔽-≡ A n g))
-- -- -- -- -- -- -- -- -- -- -- -- --     (congP (λ _ → snd) (𝔽-≡ A n (g · h)))
-- -- -- -- -- -- -- -- -- -- -- -- --     refl
-- -- -- -- -- -- -- -- -- -- -- -- --     (congP (λ _ → snd) (𝔽-≡ A n h) )
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽-sq-snd {ℓ} A isGrpA n = RelimProp.f (w n)
-- -- -- -- -- -- -- -- -- -- -- -- --  where

-- -- -- -- -- -- -- -- -- -- -- -- --  open RelimProp

-- -- -- -- -- -- -- -- -- -- -- -- --  w : ∀ n → RelimProp {n = n}
-- -- -- -- -- -- -- -- -- -- -- -- --         λ g → (h : Perm n) → 
-- -- -- -- -- -- -- -- -- -- -- -- --   SquareP (λ i j → 𝔽h' A n (emcomp g h i j) ≡
-- -- -- -- -- -- -- -- -- -- -- -- --      𝔽-sq-fst A isGrpA n g h i j)
-- -- -- -- -- -- -- -- -- -- -- -- --     (congP (λ _ → snd) (𝔽-≡ A n g))
-- -- -- -- -- -- -- -- -- -- -- -- --     (congP (λ _ → snd) (𝔽-≡ A n (g · h)))
-- -- -- -- -- -- -- -- -- -- -- -- --     refl
-- -- -- -- -- -- -- -- -- -- -- -- --     (congP (λ _ → snd) (𝔽-≡ A n h) )
-- -- -- -- -- -- -- -- -- -- -- -- --  isPropA (w n) _ = isPropΠ λ _ →
-- -- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --  εA (w n) h i j = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     -- Glue {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     --   {{!j ∨ ~ j ∨ i ∨ ~ i!}}
-- -- -- -- -- -- -- -- -- -- -- -- --     --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --  ∷A (w n) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ua-ungluePathExt∙ₑ : ∀ {ℓ} {A B C : Type ℓ} (e : A ≃ B) (f : B ≃ C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → PathP (λ i → ua (e ∙ₑ f) i → ua (f) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (fst e) (idfun _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ua-ungluePathExt∙ₑ {A = A} {B = B} {C = C} e f i x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    glue {A = C} {i ∨ ~ i}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ { (i = i0) → e .fst x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; (i = i1) → x })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (ua-unglue (e ∙ₑ f) i x) --(ua-unglue (e ∙ₑ f) i x)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ua-ungluePathExt∙ₑ' : ∀ {ℓ} {A B C : Type ℓ} (e : A ≃ B) (f : B ≃ C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → ∀ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → PathP (λ i → ua (fst f ∘ fst e , p) i → ua (f) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (fst e) (idfun _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ua-ungluePathExt∙ₑ' {A = A} {B = B} {C = C} e f p i x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    glue {A = C} {i ∨ ~ i}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ { (i = i0) → e .fst x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; (i = i1) → x })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (ua-unglue (_ , p) i x) --(ua-unglue (e ∙ₑ f) i x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ua-gluePathExt∙ₑ' : ∀ {ℓ} {A B C : Type ℓ} (e : A ≃ B) (f : B ≃ C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → ∀ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → PathP (λ i → ua (f) i → ua (fst f ∘ fst e , p) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (invEq e) (idfun _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ua-gluePathExt∙ₑ' {A = A} {B = B} {C = C} e f p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ◁ (λ i → ua-gluePathExt (fst f ∘ fst e , p) i ∘
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          invEq ((fst f ∘ fst e , p)) ∘ ua-ungluePathExt f i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ▷ funExt (secEq (fst f ∘ fst e , p))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- glue {A = C} {i ∨ ~ i}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       (λ { (i = i0) → e .fst x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          ; (i = i1) → x })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       (ua-unglue (_ , p) i x) --(ua-unglue (e ∙ₑ f) i x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ua-gluePathExtLem : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ua-gluePathExtLem = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ua-gluePathExt∙ₑ : ∀ {ℓ} {A B : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (e : A → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (eInvol : isInvolution e)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (f : A ≃ B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → PathP (λ i → ua (f) i → ua (involEquiv {f = e} eInvol ∙ₑ f) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (e) (idfun _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- (idfun _)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ua-gluePathExt∙ₑ {A = A} {B = B} e eInvol f =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     funExt (λ x → cong e (sym (retEq f x) ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ◁ (λ i → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ua-gluePathExt (involEquiv {f = e} eInvol ∙ₑ f) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∘' e ∘ invEq f ∘ ua-ungluePathExt f i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ▷ funExt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         λ x → secEq (involEquiv {f = e} eInvol ∙ₑ f) x
      
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- glue {A = B} {i ∨ ~ i}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       (λ { (i = i0) → x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          ; (i = i1) → {!f x!} })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          (unglue  {!i ∨ ~ i!} x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          -- (ua-unglue (involEquiv {f = e} eInvol)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          --   i {!!}) --(ua-unglue (e ∙ₑ f) i x)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- Z : Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --       (ua e)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --       (ua (e ∙ₑ f))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --       refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --       (ua f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- Z i j =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    Glue (ua f i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --      (λ { (j = i0) → (A ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --           ua-gluePathExt f i ∘ fst e ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --           isProp→PathP (λ i → isPropIsEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --             (ua-gluePathExt f i ∘ fst e))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --               (snd e)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --               (snd (e ∙ₑ f)) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --         )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --         ; (j = i1) → (ua f i , idEquiv (ua f i)) })

-- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝕍 : (A : Type ℓ) → (isGroupoid A) → ∀ n em → singl (𝔽h' A n em)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝕍 A isGroupoidA n = EMelim.f w
-- -- -- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   w : EMelim _
-- -- -- -- -- -- -- -- -- -- -- -- -- --                       (λ z → singl (𝔽h' A n z))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   EMelim.b w = (A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   EMelim.bPathP w = 𝔽-≡ A n
-- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (EMelim.bSqP w g h i j) = 𝔽-sq-fst A isGroupoidA n g h i j
-- -- -- -- -- -- -- -- -- -- -- -- -- --   snd (EMelim.bSqP w g h i j) k = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (A : Type ℓ) where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- zzz : ∀ n g → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      ∀ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --         A →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --         fst (𝕍 A n (emloop g i)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --         fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --         (𝕍 A (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --          (gh→em₂→ (Perm n , snd (PermG n)) (sucPerm , sucPermGH n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --           (emloop g i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- zzz n g i a =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --    ua-gluePathExt (fst (permute→×^' {A = A} (suc n) (sucPerm g) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --         , isEquiv-permute→×^' (suc n) (sucPerm g) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --         i ∘'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     (a ,_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     ∘' ua-ungluePathExt (fst (permute→×^' {A = A} n g) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       isEquiv-permute→×^' n g) i


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Relim

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ww'* : ∀ n → ∀ (g : Perm n) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ww'* = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ww'' : ∀ n → Relim {n = n} λ (g : Perm n) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            map-× (idfun A) (fst (permute→×^' n g)) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fst (permute→×^' (suc n) (sucPerm g))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           -- PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           -- (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           --    A × fst (𝔽-≡ A n g i) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           --   fst (𝔽-≡ A (suc n) (sucPerm g) i) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           --      (idfun _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           --      (idfun _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isSetA (ww'' n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   εA (ww'' n) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∷A (ww'' (suc n)) k X = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ i x → X i (fst x , adjT×^'→ (fst k) (snd x)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   invoA (ww'' (suc n)) k X i j x = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      X j (fst x , isInvo-adjT×^'→ (fst k) (snd x) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   braidA (ww'' (suc (suc (suc n)))) k k< X i j x = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      X j (fst x , braid-adjT×^'→ k k< (snd x) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   commA (ww'' (suc (suc (suc n)))) k (suc l , l<) z X i j x = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     X j (fst x , comm-adjT×^'→ (fst k) (suc l) (snd k) l< z (snd x) (i))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ww''' : ∀ n → ∀ g →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              -- (ua ( (Σ-cong-equiv-snd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              --     λ _ → (_ , isEquiv-permute→×^' n g))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              -- (λ i → A × (fst (𝔽-≡ A n g i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (ua (≃-× (idEquiv _) (_ , isEquiv-permute→×^' n g)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (congP (λ _ → fst) (𝔽-≡ A (suc n) (sucPerm g)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ww''' n g =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     cong ua (equivEq (Relim.f (ww'' n) g))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ww* : ∀ n → ∀ (g : Perm n) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (ua (≃-× (idEquiv _) (_ , isEquiv-permute→×^' n g))) i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              fst (𝔽-≡ A (suc n) (sucPerm g) i) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ x → x) λ x → x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ww* n g = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    transport-fillerExt refl ◁ congP (λ _ → transport) (flipSquare (ww''' n g)) ▷
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      sym (transport-fillerExt refl)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ww'* : ∀ n → ∀ (g : Perm n) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              A →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              fst (𝔽-≡ A n g i) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              fst (𝔽-≡ A (suc n) (sucPerm g) i) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           _,_ _,_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ww'* n g i a x = ww* n g i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (glue {A = A ×^ (suc n)} {i ∨ ~ i}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ { (i = i0) → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ; (i = i1) → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          }) (a , ua-unglue (_ , isEquiv-permute→×^' n g) i x))



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕍∷R : ∀ n → EMelim _ (λ (p : ℙrm' n) → A → fst (𝕍 A n p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             → fst (𝕍 A (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                               (gh→em₂→ _ (_ , sucPermGH _) p)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   EMelim.isGrpB (𝕍∷R n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   EMelim.b (𝕍∷R n) = _,_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   EMelim.bPathP (𝕍∷R n) = ww'* n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   EMelim.bSqP (𝕍∷R n) g h = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  𝕍∷ : ∀ n → (p : ℙrm' n) → A → fst (𝕍 A n p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            → fst (𝕍 A (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              (gh→em₂→ _ (_ , sucPermGH _) p))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  𝕍∷ n = EMelim.f (𝕍∷R n)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- to𝕍R : RElim λ (x : FMSet2 A) → Σ _ (fst ∘ 𝕍 A (len2 x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.[]* to𝕍R = embase , tt*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- (to𝕍R RElim.∷* x) (e , xs) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   -- (gh→em₂→ {!!} (_ , sucPermGH _) e ) , {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.comm* to𝕍R = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.comm-inv* to𝕍R = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.hexDiag* to𝕍R = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.hexU* to𝕍R = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.hexL* to𝕍R = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.trunc* to𝕍R = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- to𝕍 : (x : FMSet2 A) → Σ _ (fst ∘ 𝕍 A (len2 x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- to𝕍 = RElim.f to𝕍R
     


    
