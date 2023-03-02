{-# OPTIONS --safe  #-}  --experimental-lossy-unification
module Cubical.HITs.ListedFiniteSet.Base3CPermu where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Path

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Data.Unit
import Cubical.Data.Bool as 𝟚

open import Cubical.Functions.Logic as L
open import Cubical.Foundations.Function

open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.Data.FinData.Properties

open import Cubical.Data.Nat.Order.Recursive

open import Cubical.Relation.Binary

open import Cubical.HITs.ListedFiniteSet.Base3C

open import Cubical.HITs.Permutation.Base renaming
  (𝕡squash to 𝕡squash'
  ; ℙrm to ℙrm*)
open import Cubical.HITs.Permutation.Group

open import Cubical.HITs.GroupoidTruncation as GT using (∥_∥₃ ; ∣_∣₃ ; squash₃) 

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Type ℓ

ℙrm : ℕ → Type
ℙrm = ℙrm* {trunc = 𝟚.true}

𝕡squash : ∀ {n} → isGroupoid (ℙrm n)
𝕡squash = 𝕡squash' {trunc = 𝟚.true} _  

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
  commm _ _ _ _
R𝕡rec.alooop (RtoFM2⊤ (suc (suc (suc n)))) (suc zero , k<) (zero , l<) =
  sym (commm _ _ _ _)

R𝕡rec.acomp (RtoFM2⊤ (suc n)) (suc k , k<) (suc l , l<) i j =
 tt ∷2 R𝕡rec.acomp (RtoFM2⊤ n) (k , k<) (l , l<) i j
R𝕡rec.acomp (RtoFM2⊤ (suc n)) (zero , k<) (zero , l<) i j =
  R𝕡rec.aloop (RtoFM2⊤ (suc n)) (0 , isProp≤ {m = 1} {n = n} k< l< i) j
 
R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc zero , l<) =
  commp _ _ _ _
R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc (suc l) , l<) i j =
  comm _ _ ((R𝕡rec.aloop (RtoFM2⊤ (suc n)) (l , l<) (~ i ∨ j))) (i ∨ j)
R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (suc zero , k<) (zero , l<) =
  symP (commp _ _ _ _)
R𝕡rec.acomp (RtoFM2⊤ (suc (suc (suc n)))) (suc (suc k) , k<) (zero , l<) i j =
    comm _ _ (R𝕡rec.aloop (RtoFM2⊤ (suc n)) (k , k<) (i ∨ j)) (~ i ∨  j)

R𝕡rec.acomm (RtoFM2⊤ (suc n)) (suc k , k<) (suc l , l<) x i j = 
  tt ∷2 R𝕡rec.acomm (RtoFM2⊤ (n)) (k , k<) (l , l<)
    (pred-commT k l x) i j
R𝕡rec.ainvol (RtoFM2⊤ (suc (suc n))) (zero , k<) = comm-inv _ _ _
R𝕡rec.ainvol (RtoFM2⊤ (suc (suc (suc n)))) (suc k , k<) =
  cong (cong (tt  ∷2_)) (R𝕡rec.ainvol (RtoFM2⊤ (suc (suc n))) (k , k<))
R𝕡rec.acomm (RtoFM2⊤ (suc (suc (suc n)))) (zero , k<) (suc (suc l) , l<) x i j =
  comm-inv tt tt
    (R𝕡rec.ainvol (RtoFM2⊤ (suc n)) (l , l<) (~ j) i) (~ j) (~ i)

R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc n)))) zero k< =
  hex _ _ _ _

R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc (suc n))))) (suc k) k< i j =
 tt ∷2 R𝕡rec.abraid (RtoFM2⊤ (suc (suc (suc n)))) k k< i j


toFM2⊤ : Σ _ ℙrm → FMSet2 Unit
toFM2⊤ x = R𝕡rec.f {n = (fst x)} (RtoFM2⊤ (fst x)) {squashA = trunc} (snd x)


comp0 : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
     Square {A = ℙrm (suc (suc n))}
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
     hcomp {A = ℙrm (suc (suc n))} (λ l → λ {
    (i = i0) → comp0 n (k , k<) l j
   ;(i = i1) → comp1 (suc (suc n)) (zero , _) (suc (suc k) , k<) l j
   ;(j = i0) → 𝕡loop (suc (suc k) , k<) (i ∨ ~ l)
   ;(j = i1) → 𝕡loop (suc (suc k) , k<) (i ∧ l)
   }) (𝕡looop (zero , _) (suc (suc k) , k<) j)

alooopcommm : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
      PathP
      (λ i →
         sucℙrm {b = 𝟚.true}
           (suc (suc n)) (sucℙrm (suc n) (sucℙrm n (𝕡loop k i))) ≡
         sucℙrm (suc (suc n)) (sucℙrm (suc n) (sucℙrm n (𝕡loop k i))))
      (𝕡looop (zero , tt) (1 , tt)) (𝕡looop (zero , tt) (1 , tt)) 
alooopcommm n (k , k<) =
  whiskSq.sq' _
    (λ i j → 𝕡loop (suc (suc (suc k)) , k<) i)
    (λ i j → 𝕡comp (zero , _) (1 , _) i (~ j))
    (λ i j → 𝕡comp (zero , _) (1 , _) i (~ j))
    (congP (λ _ → symP) (aloopcommm (suc n) (suc k , k<)))
    (congSq (sucℙrm (suc (suc n))) (congP (λ _ → symP) (aloopcommm n (k , k<))))


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

fromFM2commm : (n : ℕ) → R𝕡elimSet {n = n} (λ (y : ℙrm n) →
      (sucℙrm (suc (suc n)) (sucℙrm (suc n) (sucℙrm n y))) ≡
      (sucℙrm (suc (suc n)) (sucℙrm (suc n) (sucℙrm n y))))
R𝕡elimSet.isSetA (fromFM2commm n) _ = 𝕡squash _ _
R𝕡elimSet.abase (fromFM2commm n) = 𝕡looop (zero , _) (1 , _)
R𝕡elimSet.aloop (fromFM2commm n) = alooopcommm n
R𝕡elimSet.alooop (fromFM2commm n) k l i j =
   hcomp
   (λ l' → λ {
     (i = i0) → alooopcommm n k (~ l') j
    ;(i = i1) → alooopcommm n l (~ l') j
    ;(j = i0) → sucℙrm (suc (suc n))
                 (sucℙrm (suc n) (sucℙrm n (𝕡comp k l i (~ l'))))
    ;(j = i1) → sucℙrm (suc (suc n))
                 (sucℙrm (suc n) (sucℙrm n (𝕡comp k l i (~ l'))))
     }) (𝕡looop (zero , tt) (1 , tt) j)


fromFM2comm-inv : (n : ℕ) → R𝕡elimProp {n = n}
  (λ (p : ℙrm n) →
     R𝕡elimSet.f (fromFM2comm n) p
  ≡ sym (R𝕡elimSet.f (fromFM2comm n) p))
R𝕡elimProp.isPropA (fromFM2comm-inv n) _ = 𝕡squash _ _ _ _
R𝕡elimProp.abase (fromFM2comm-inv n) = 𝕡invol _

fromFM2comm-comp : (n : ℕ) → R𝕡elimProp {n = n}
  λ (b : ℙrm n) →
      Square
      (R𝕡elimSet.f (fromFM2comm (suc n))
       (sucℙrm n b))
      (congP (λ _ → sucℙrm (suc (suc n)))
       (R𝕡elimSet.f (fromFM2comm n) b))
      (R𝕡elimSet.f (fromFM2commm n) b) refl
R𝕡elimProp.isPropA (fromFM2comm-comp n) _ =
 isOfHLevelRetractFromIso 1 (invIso PathP→comm-Iso)
  (𝕡squash _ _ _ _)
R𝕡elimProp.abase (fromFM2comm-comp n) =
  𝕡comp (0 , _) (1 , _)

fromFM2comm-hex : (n : ℕ) → R𝕡elimProp {n = n}
  λ (z : ℙrm n) → 
         Square
         (congP (λ _ → sucℙrm (suc (suc n)))
          (R𝕡elimSet.f (fromFM2comm n) z))
         (R𝕡elimSet.f (fromFM2comm (suc n))
          (sucℙrm n z))
         (R𝕡elimSet.f (fromFM2commm n) z)
         (R𝕡elimSet.f (fromFM2commm n) z)
R𝕡elimProp.isPropA (fromFM2comm-hex n) _ =
  isOfHLevelRetractFromIso 1 (invIso PathP→comm-Iso)
  (𝕡squash _ _ _ _)
R𝕡elimProp.abase (fromFM2comm-hex n) = 𝕡braid _ _

RfromFM2⊤' : RElim {A = Unit} {T = Unit} λ xs → ℙrm (length2 xs)
RElim.[]* RfromFM2⊤' = 𝕡base
RElim._∷*_ RfromFM2⊤' _ = sucℙrm _
RElim.comm* RfromFM2⊤' _ _ = (R𝕡elimSet.f (fromFM2comm _))
RElim.comm-inv* RfromFM2⊤' _ _ = R𝕡elimProp.f (fromFM2comm-inv _)
RElim.commm* RfromFM2⊤' _ _ _ = R𝕡elimSet.f (fromFM2commm _) 
RElim.commp* RfromFM2⊤' _ _ _ = R𝕡elimProp.f (fromFM2comm-comp _)
RElim.hex* RfromFM2⊤' _ _ _ = R𝕡elimProp.f (fromFM2comm-hex _)


fromFM2⊤ : FMSet2 Unit → Σ ℕ ℙrm
fromFM2⊤ xs = (length2 xs) , (RElim.ff RfromFM2⊤' (λ _ _ → 𝕡squash) xs )


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

RfromToFM2⊤ : RElimSet (λ z → toFM2⊤ (fromFM2⊤ z) ≡ z) 
RElimSet.[]* RfromToFM2⊤ = refl
(RfromToFM2⊤ RElimSet.∷* tt) {xs} X =
  uncurry sucℙrm-lem (fromFM2⊤ xs) ∙ cong (tt ∷2_) X
  
RElimSet.comm* RfromToFM2⊤ tt tt {xs} X i j =
 hcomp
   (λ l → primPOr (j ∨ ~ j) ((i ∨ ~ i))
      (primPOr j (~ j) (λ _ → comm tt tt (X l) i)
        λ _ → toFM2⊤ (fromFM2⊤ (comm tt tt xs i)))
      λ _ → (uncurry sucℙrm-lem (fromFM2⊤ (tt ∷2 xs)) ∙
         cong′ (tt ∷2_) (compPath-filler (uncurry sucℙrm-lem (fromFM2⊤ xs))
                    (cong′ (tt ∷2_) X) l)) j)

  (R𝕡elimProp.f {n = (fst (fromFM2⊤ xs))}
    (comm*-lem (fst (fromFM2⊤ xs))) (snd (fromFM2⊤ xs)) i j)


RElimSet.trunc* RfromToFM2⊤ _ = trunc _ _

fromToFM2⊤ : retract fromFM2⊤ toFM2⊤
fromToFM2⊤ = RElimSet.f RfromToFM2⊤


RtoFromFM2⊤-fst : ∀ n → R𝕡elimSet {n = n} (λ z → length2 (toFM2⊤ (n , z)) ≡ n)
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
R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc n)))) (zero , k<) (suc zero , l<) = refl

R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc (suc n))))) (zero , k<) (suc (suc l) , l<) i j =
 suc (suc (R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc (suc n))) (l , l<) (~ i) j))
R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc n)))) (suc zero , k<) (zero , l<) = refl

R𝕡elimSet.alooop (RtoFromFM2⊤-fst (suc (suc (suc (suc n))))) (suc (suc k) , k<) (zero , l<) i j = suc (suc ((R𝕡elimSet.aloop (RtoFromFM2⊤-fst (suc (suc n))) (k , k<) i j)))


-- -- ∷2-lem-fst : ∀ xs → (fromFM2⊤ (tt ∷2 xs)) ≡
-- --    (suc (fst (fromFM2⊤ xs)) , uncurry sucℙrm (fromFM2⊤ xs))

base≡ : ∀ n → PathP (λ i → ℙrm (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) i))
      (RElim.ff RfromFM2⊤' (λ _ _ → 𝕡squash) (fm2base n)) 𝕡base
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
looop≡ (suc (suc (suc n))) (zero , tt) (suc zero , tt) i j =
  (R𝕡elim.f
          (R𝕡elimSet.fR (fromFM2commm (R𝕡elimSet.abase (RtoFromFM2⊤-fst n) j)))
         ((base≡ n) j ) i)

looop≡ (suc (suc (suc (suc n)))) kk@(zero , k<) ll@(suc (suc l) , l<) =
  flipSquareP ((λ j i →
      (((R𝕡elim.f
            (R𝕡elimSet.fR (fromFM2comm _))
            (loop≡ (suc (suc n)) (l , l<) (~ i) j) i))) ) ▷
             fromFM2comm-diag (suc (suc n)) l l<)
   
looop≡ (suc (suc (suc n))) (suc zero , _) (zero , _) =
   flipSquareP
    (flipSquareP
     (symP (looop≡ (suc (suc (suc n))) (zero , tt) (suc zero , tt))) ▷
      sym (𝕡looop-invol _ (1 , _) (0 , _)))
  
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

Iso-FM2⊤-Σℙrm : Iso FM2⊤ (Σ _ ℙrm)
Iso.fun Iso-FM2⊤-Σℙrm = fromFM2⊤
Iso.inv Iso-FM2⊤-Σℙrm = toFM2⊤
Iso.rightInv Iso-FM2⊤-Σℙrm = toFromFM2⊤
Iso.leftInv Iso-FM2⊤-Σℙrm = fromToFM2⊤

FM2⊤≃Σℙrm : FM2⊤ ≃ (Σ _ ℙrm)
FM2⊤≃Σℙrm = isoToEquiv Iso-FM2⊤-Σℙrm
