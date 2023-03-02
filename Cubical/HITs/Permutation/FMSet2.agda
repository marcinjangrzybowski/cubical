{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.FMSet2 where

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

-- open import Cubical.Data.Nat.Order.Permutation 

-- open import Cubical.Data.FinData.GTrun

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)

open import Cubical.HITs.ListedFiniteSet.Base2

open import Cubical.HITs.Permutation.Base renaming (ℙrm to ℙrm* ; sucℙrm to sucℙrm*)


private
  variable
    ℓ : Level
    A : Type ℓ


ℙrm = ℙrm* {𝟚.true}
sucℙrm = sucℙrm* {𝟚.true}


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

toFM2⊤ : Σ _ ℙrm → FMSet2 Unit
toFM2⊤ x = R𝕡rec.f {n = (fst x)} (RtoFM2⊤ (fst x)) {_} {trunc} (snd x)


comp0 : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
     Square {A = ℙrm (2 + n)}
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
     Square {A = ℙrm n}
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
R𝕡elimSet.isSetA (fromFM2comm n) _ = 𝕡squash _ _ _
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
R𝕡elimProp.isPropA (fromFM2comm-inv n) _ = 𝕡squash _ _ _ _ _
R𝕡elimProp.abase (fromFM2comm-inv n) = 𝕡invol _

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
      (𝕡squash _ _ _ _ _) ;
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
RElim.trunc* RfromFM2⊤' _ = 𝕡squash _

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
 isOfHLevelRetractFromIso 2 (PathPIsoPath _ _ _) (𝕡squash _ _ _)
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
