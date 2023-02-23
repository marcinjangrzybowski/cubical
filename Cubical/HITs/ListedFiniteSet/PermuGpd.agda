{-# OPTIONS --safe  #-}  --experimental-lossy-unification
module Cubical.HITs.ListedFiniteSet.PermuGpd where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Nat as ℕ

open import Cubical.Data.Nat.Order.Recursive as OR

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool

open import Cubical.Data.List

open import Cubical.Functions.Logic as Lo
open import Cubical.Foundations.Function

open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Functions.Involution

open import Cubical.Foundations.Equiv.PathSplit

open import Cubical.Foundations.Path

open import Cubical.Foundations.Structure

open import Cubical.Data.Maybe as Mb

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.HITs.ListedFiniteSet.Base2

open import Cubical.Data.Nat.FinGenAut2 as A

import Cubical.Data.Nat.Order.Permutation as P

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Algebra.SymmetricGroup

open import Cubical.HITs.EilenbergMacLane1 as  EM

open import Cubical.HITs.ListedFiniteSet.Sum

open import Cubical.Data.Nat.Order.PermutationMore3


Perm₂ : Type
Perm₂ = FMSet2 Unit


Mb^ : ℕ → (hSet ℓ-zero) → (hSet ℓ-zero) 
Mb^ zero x₁ = x₁
Mb^ (suc x) b' =
  let b = Mb^ x b'
  in Maybe (fst b) , isOfHLevelMaybe zero (snd b)

swap0and1Mf : (b : hSet ℓ-zero) → fst (Mb^ 2 b) → fst (Mb^ 2 b)  
swap0and1Mf b nothing = just nothing
swap0and1Mf b (just nothing) = nothing
swap0and1Mf b (just (just x)) = (just (just x))

isInvolutionSwap0and1M : (b : hSet ℓ-zero) →
  isInvolution (swap0and1Mf b)
isInvolutionSwap0and1M b = (Mb.elim _ refl (Mb.elim _ refl λ _ → refl) )

swap0and1M : (b : hSet ℓ-zero) → fst (Mb^ 2 b) ≃ fst (Mb^ 2 b)  
swap0and1M b = involEquiv {f = swap0and1Mf b}
   (isInvolutionSwap0and1M b)

swap0and2Mf : (b : hSet ℓ-zero) → fst (Mb^ 3 b) → fst (Mb^ 3 b)  
swap0and2Mf b nothing = (just (just nothing))
swap0and2Mf b (just nothing) = just nothing
swap0and2Mf b (just (just nothing)) = nothing
swap0and2Mf b (just (just (just x))) = (just (just (just x)))

isInvolutionSwap0and2M : (b : hSet ℓ-zero) →
  isInvolution (swap0and2Mf b)
isInvolutionSwap0and2M b =
  (Mb.elim _ refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)) )


swap0and2M : (b : hSet ℓ-zero) → fst (Mb^ 3 b) ≃ fst (Mb^ 3 b)  
swap0and2M b = involEquiv {f = swap0and2Mf b}
   (isInvolutionSwap0and2M b)

-- congMUA : (b : hSet ℓ-zero) →
--              cong Maybe (ua (swap0and1M b)) ≡
--               ua (congMaybeEquiv (swap0and1M b)) 
-- congMUA b = isInjectiveTransport
--   (funExt (Mb.elim _ refl λ _ → refl))

-- glueSwap01 :  (b : hSet ℓ-zero) →
--       PathP (λ i₁ → (Maybe (Maybe (fst b))) → ua (swap0and1M b) i₁)
--          (fst (swap0and1M b)) (idfun _)
-- glueSwap01 b = funExt λ x → ua-gluePath _ {!!}
--    -- glue   (λ { (i = i0) → swap0and1⊎f x
--    --                        ; (i = i1) → x
--    --                        }) (swap0and1⊎fInvol x i)


invoFinR : (b : hSet ℓ-zero) →
         (ua (swap0and1M b)) ≡
           sym (ua (swap0and1M b)) 
invoFinR b i j =
   Glue (ua (swap0and1M b) i)
       λ { (j = i0) → Maybe (Maybe (fst b)) ,
                         ΣPathPProp
                            {A = λ i → (Maybe (Maybe (fst b)))
                                    → ua (swap0and1M b) i}
                                {B = λ i → isEquiv}
                             {u = swap0and1M b}
                             {v = idEquiv _}
                           isPropIsEquiv
                           (funExt λ x → ua-gluePath _
                             (isInvolutionSwap0and1M b x)) i

       ; (j = i1) → Maybe (Maybe (fst b)) ,
                     ΣPathPProp {A = λ i → (Maybe (Maybe (fst b)))
                                    → ua (swap0and1M b) i}
                                {B = λ i → isEquiv}
                              {u = idEquiv _}
                              {v = swap0and1M b}
                              isPropIsEquiv 
                               ((funExt λ x →
                                    ua-gluePath _
                                  refl))
                               i
                               }
-- Fin : ℕ → Type
-- Fin n = Σ ℕ λ k → k < n


-- Fin₂' : RElim {A = Unit} (λ _ → hSet ℓ-zero) -- isGroupoidHSet
-- RElim.[]* Fin₂' = Fin 0 , isSetFin {0}
-- (Fin₂' RElim.∷* x) {xs} x₁ = {!Fin (suc (len2 xs))!}
-- RElim.comm* Fin₂' = {!!}
-- RElim.comm-inv* Fin₂' = {!!}
-- RElim.hexDiag* Fin₂' = {!!}
-- RElim.hexU* Fin₂' = {!!}
-- RElim.hexL* Fin₂' = {!!}
-- RElim.trunc* Fin₂' = {!!}
-- -- RRec.[]* Fin₂' = Fin 0 , isSetFin {0}
-- -- RRec._∷*_ Fin₂' = {!!}
-- -- RRec.comm* Fin₂' = {!!}
-- -- RRec.comm-inv* Fin₂' = {!!}
-- -- RRec.hexDiag* Fin₂' = {!!}
-- -- RRec.hexU* Fin₂' = {!!}
-- -- RRec.hexL* Fin₂' = {!!}

Fin₂R : RRec {A = Unit} {B = hSet ℓ-zero} isGroupoidHSet
RRec.[]* Fin₂R = ⊥.⊥ , isProp→isSet isProp⊥
(Fin₂R RRec.∷* x) b = Maybe (fst b) , isOfHLevelMaybe zero (snd b)
RRec.comm* Fin₂R x y b = TypeOfHLevel≡ 2 (ua (swap0and1M b))
RRec.comm-inv* Fin₂R x y b =
  ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
    (invoFinR b)
RRec.hexDiag* Fin₂R x y z b =
  TypeOfHLevel≡ 2 (ua (swap0and2M b))
RRec.hexU* Fin₂R x y z b =
   ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
    (comm→PathP (isInjectiveTransport (funExt
      (Mb.elim _ refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl))))))  
RRec.hexL* Fin₂R x y z b =
  ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
    (comm→PathP (isInjectiveTransport (funExt
      (Mb.elim _ refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl))))))


hFin₂ : Perm₂ → hSet ℓ-zero
hFin₂ = RRec.f Fin₂R


Fin₂ : Perm₂ → Type
Fin₂ = fst ∘ RRec.f Fin₂R



isSetFin₂ : (x : Perm₂) → isSet (Fin₂ x)
isSetFin₂ = snd ∘ RRec.f Fin₂R


nPerm₂ : ℕ → Perm₂ 
nPerm₂ n = iter n (_ ∷2_ ) []

Fin₂' : ℕ → Type
Fin₂' = fst ∘ RRec.f Fin₂R ∘ nPerm₂




isSetFin₂' = snd ∘ RRec.f Fin₂R ∘ nPerm₂


Fin₂'→Fin : ∀ n → (Fin₂' n) → (Fin n)
Fin₂'→Fin (suc n) nothing = zero , _
Fin₂'→Fin (suc n) (just x) = sucF (Fin₂'→Fin n x)

Fin→Fin₂' : ∀ n → (Fin n) → (Fin₂' n)
Fin→Fin₂' (suc n) (zero , snd₁) = nothing
Fin→Fin₂' (suc n) (suc fst₁ , snd₁) = just (Fin→Fin₂' n (fst₁ , snd₁))

IsoFin₂'Fin : ∀ n → Iso (Fin₂' n) (Fin n)
Iso.fun (IsoFin₂'Fin n) = Fin₂'→Fin n
Iso.inv (IsoFin₂'Fin n) = Fin→Fin₂' n
Iso.rightInv (IsoFin₂'Fin (suc n)) (zero , snd₁) = refl
Iso.rightInv (IsoFin₂'Fin (suc n)) (suc fst₁ , snd₁) =
  cong sucF (Iso.rightInv (IsoFin₂'Fin (n)) (fst₁ , snd₁))
Iso.leftInv (IsoFin₂'Fin (suc n)) nothing = refl
Iso.leftInv (IsoFin₂'Fin (suc n)) (just x) =
 cong just (Iso.leftInv (IsoFin₂'Fin n) x) 


isOfLen : ∀ {ℓ} {A} → List {ℓ} A → Perm₂ → Type
isOfLen x x₁ = True (discreteℕ (length x) (len2 x₁))

PermGp : Type₀
PermGp = Σ ℕ λ n → EM₁ (P.PermG n) 


commK : ∀ n → Σ ℕ (λ k₁ → suc k₁ < n) → nPerm₂ n ≡ nPerm₂ n
commK (suc (suc n)) (zero , k<) = comm _ _ _
commK (suc (suc (suc n))) (suc k , k<) =
  cong (tt ∷2_) (commK (suc (suc n)) (k , k<))

diagK : ∀ n → Σ ℕ (λ k₁ → suc (suc k₁) < n) → nPerm₂ n ≡ nPerm₂ n
diagK (suc (suc (suc n))) (zero , _) = hexDiag _ _ _ _
diagK (suc (suc (suc (suc n)))) (suc k , k<) =
  cong (tt ∷2_) (diagK (suc (suc (suc n))) (k , k<))

commKInv : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
                commK n k ≡ (sym (commK n k))
commKInv (suc (suc n)) (zero , k<) = comm-inv _ _ _
commKInv (suc (suc (suc n))) (suc k , k<) =
  cong (cong (tt ∷2_)) (commKInv (suc (suc n)) (k , k<))

p≡sym[p]→PathP : ∀ {ℓ} {A : Type ℓ} {x : A} → {p : x ≡ x} →
                  p ≡ sym p
                  → Square p refl refl p
p≡sym[p]→PathP P =  P ◁ λ i j → P i0 (i ∨ ~ j)

commKInv' : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
                Square (commK n k) refl refl (commK n k)
                 
commKInv' n k = p≡sym[p]→PathP (commKInv n k)

commDiagU : ∀ n k k< →
  Square (commK n (suc k , k<)) (diagK n (k , k<))
         (commK n ( k , <-weaken {n = n} k<))
         (commK n ( k , <-weaken {n = n} k<))
commDiagU (suc (suc (suc n))) zero k< =
  hexU _ _ _ _
commDiagU (suc (suc (suc (suc n)))) (suc k) k< i j =
 _ ∷2 commDiagU (suc (suc (suc n))) k k< i j 

commDiagL : ∀ n k k< →
  Square (diagK n (k , k<)) (commK n ( k , <-weaken {n = n} k<))
         (commK n (suc k , k<))
         (commK n (suc k , k<)) 
commDiagL (suc (suc (suc n))) zero k< =
  hexL _ _ _ _
commDiagL (suc (suc (suc (suc n)))) (suc k) k< i j =
 _ ∷2 commDiagL (suc (suc (suc n))) k k< i j 

commKComm : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
              (t : commT (fst k) (fst l)) →
             Square
                (commK n k)
                (commK n k)
                (commK n l)
                (commK n l)
commKComm (suc (suc (suc (suc n)))) (zero , k<) (suc (suc l) , l<) t i j =
   comm _ _ (commK (suc (suc n)) (l , l<) i) j
commKComm (suc (suc (suc (suc (suc n))))) (suc k , k<) (suc (suc (suc l)) , l<) t i j =
   _ ∷2 commKComm (suc (suc (suc (suc n)))) (k , k<) (suc (suc l) , l<) t i j 

fromPG≡ : ∀ n → P.Rrec {n = n} (nPerm₂ n ≡ nPerm₂ n)
P.Rrec.isSetA (fromPG≡ n) = trunc _ _
P.Rrec.εA (fromPG≡ n) = refl
P.Rrec.∷A (fromPG≡ n) k = commK n k ∙_

P.Rrec.invoA (fromPG≡ n) k x =
   sym (doubleCompPath-elim' _ _ _) ◁
    λ i j → 
   hcomp
    (λ k' → λ { (i = i1) → invSides-filler (commK n k) x j (~ k')
           ; (j = i0) → commK n k (~ k')
           ; (j = i1) → x k'
           }) (commKInv n k i j)

P.Rrec.braidA (fromPG≡ n) k k< x i j =
   ((λ i → (commKInv' n (k , <-weaken {n = n} k<) i)
          ∙ commDiagU n k k< i ∙
            (λ j → commK n (k , <-weaken {n = n}  k<) (j ∨  i)) ∙ x) ∙
    (λ i → (λ j → (commK n (suc k , k<)) (j ∧ i)) ∙ commDiagL n k k< i
         ∙ (λ j → (commKInv' n (suc k , k<) j) i) ∙ x)) i j

P.Rrec.commA (fromPG≡ n) k l t p i j =
  ((λ j → doubleCompPath-filler (sym (commK n k)) refl (commK n l) j i)
     ∙ PathP→compPathR' refl (commKComm n k l t) i ∙ p) j


fromPGsq : ∀ n → P.RelimProp(λ g → (h : P.Perm n) → 
   P.Rrec.f (fromPG≡ n) g ∙ (λ i → P.Rrec.f (fromPG≡ n) h i) ≡
      P.Rrec.f (fromPG≡ n)
      (g P.· h)
       )
P.RelimProp.isPropA (fromPGsq n) _ =
 isPropΠ λ _ → trunc _ _ _ _
P.RelimProp.εA (fromPGsq n) h = sym (lUnit _)
P.RelimProp.∷A (fromPGsq (suc (suc n))) k {xs} X h = 
   sym (assoc _ _ _)
   ∙ cong (P.Rrec.∷A (fromPG≡ (suc (suc n))) k) (X h)  

fromPG'R : ∀ n → EMrec (P.PermG n) {B = Perm₂} trunc
EMrec.b (fromPG'R n) = nPerm₂ n
EMrec.bloop (fromPG'R n) = P.Rrec.f (fromPG≡ n)
EMrec.bComp (fromPG'R n) =
   λ g h → compPath-filler _ _ ▷
     P.RelimProp.f (fromPGsq n) g h 

fromPG' : ∀ n → EM₁ (P.PermG n) → Perm₂
fromPG' n = EMrec.f (fromPG'R n)


wEMfunct : ∀ {ℓ ℓ'} → {A : Group ℓ} {B : Group ℓ'}
    → GroupHom A B → EMrec A (emsquash {Group = B})
EMrec.b (wEMfunct _) = embase
EMrec.bloop (wEMfunct fh) = emloop ∘ fst fh
EMrec.bComp (wEMfunct fh) g h =
  compPath-filler _ _ ▷
       (sym (emloop-comp _ _ _)
        ∙ cong emloop (sym (IsGroupHom.pres· (snd fh) g h)))


EMfunct : ∀ {ℓ ℓ'} → {A : Group ℓ} {B : Group ℓ'}
    → GroupHom A B → EM₁ A → EM₁ B
EMfunct {A = AG} {B = B , Bgs} fh =
  EMrec.f {grpB = emsquash}
    (wEMfunct fh)


isPropSqP : ∀ {ℓ} {A : I → I → Type ℓ} (Agrp : ∀ i j → isGroupoid (A i j))
           →
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
           → isProp (SquareP A a₀₋ a₁₋ a₋₀ a₋₁)
isPropSqP Agrp a₀₋ a₁₋ a₋₀ a₋₁ x y =
  λ k i j → (isSet→SquareP (λ i j → Agrp i j (x i j) (y i j))
             (λ j _ → x i0 j) (λ j _ → x i1 j) (λ i _ → x i i0) λ i _ → x i i1)
               i j k






toPGcomm : ∀ n → EM₁ (P.PermG n) → EM₁ (P.PermG (suc n))
toPGcomm n = EMfunct (P.sucPerm , P.sucPermGH n) 

toPGcommW : ∀ n → EM₁ (P.PermG n) → EM₁ (P.PermG (suc n))
toPGcommW n = EMfunct (P.weakPerm n , P.weakPermGH n) 

toPGcommWΣ : Σ ℕ (EM₁ ∘ P.PermG) → Σ ℕ (EM₁ ∘ P.PermG)
toPGcommWΣ x = _ , toPGcommW _ (snd x)


toPG'R1 : ∀ n → EMelimSet (P.PermG n)
      (λ z → 
         toPGcomm (suc n) (toPGcomm n z) ≡
         toPGcomm (suc n) (toPGcomm n z))
EMelimSet.isSetB (toPG'R1 n) _ = emsquash _ _
EMelimSet.b (toPG'R1 n) = emloop (P.η (zero , _))
EMelimSet.bPathP (toPG'R1 n) g =
   comm→PathP (
  sym (emloop-comp _ _ _) ∙∙
    cong emloop (sym (P.sucPermComm g))
    ∙∙ emloop-comp _ _ _)

toPG'R1f : ∀ (n : ℕ) → (∀ z → 
         toPGcomm (suc n) (toPGcomm n z) ≡
         toPGcomm (suc n) (toPGcomm n z))
toPG'R1f n =  EMelimSet.f (toPG'R1 n)

toPG'R2 : ∀ n → EMelimProp (P.PermG n)
      (λ z →
         SquareP (λ i j → EM₁ (P.PermG (suc (suc n))))
         (EMelimSet.f (toPG'R1 n) z)
         (symP (EMelimSet.f (toPG'R1 n) z)) refl refl)
EMelimProp.isPropB (toPG'R2 n) _ = isPropSqP (λ _ _ → emsquash) _ _ _ _
EMelimProp.b (toPG'R2 n) = emloop-sym _ _

toPG'R2f : ∀ n → _
toPG'R2f n = EMelimProp.f (toPG'R2 n)



toPG'R3base : ∀ n → toPGcomm (suc (suc n)) (toPGcomm (suc n) (toPGcomm n embase))
      ≡ toPGcomm (suc (suc n)) (toPGcomm (suc n) (toPGcomm n embase))
toPG'R3base n = 
   (emloop (P.η (zero , _)) ∙∙
       emloop (P.η (suc zero , _))
       ∙∙ emloop (P.η (zero , _)))


toPG'R3loop : ∀ n → P.RelimProp
      (λ z →
         PathP
         (λ i →
            toPGcomm (suc (suc n)) (toPGcomm (suc n) (toPGcomm n (emloop z i)))
            ≡
            toPGcomm (suc (suc n))
            (toPGcomm (suc n) (toPGcomm n (emloop z i))))
         (toPG'R3base n) (toPG'R3base n))
P.RelimProp.isPropA (toPG'R3loop n) _ =
  isPropSqP (λ _ _ → emsquash) _ _ _ _
P.RelimProp.εA (toPG'R3loop n) = 
   sym (emloop-doubleComp _ _ _ _) ◁
     (flipSquare ( emloop-1g _ ◁
       (λ i _ → emloop ((0 , tt) P.∷ (1 , tt) P.∷ (0 , tt) P.∷ P.ε) i)
       ▷ sym (emloop-1g _)))
   ▷ emloop-doubleComp _ _ _ _
P.RelimProp.∷A (toPG'R3loop (suc (suc n))) (k , k<) {xs} X =
  flipSquare (  emloop-comp _ (P.η (suc (suc (suc k)) , k<))
    (P.sucPerm  (P.sucPerm  (P.sucPerm xs))) ◁
      (λ i →  ss i ∙ flipSquare X i)
    ▷ sym (emloop-comp _ (P.η (suc (suc (suc k)) , k<))
    (P.sucPerm  (P.sucPerm  (P.sucPerm xs)))))

  where
    ss : Square
             (emloop ((P.η (suc (suc (suc k)) , k<))))
             (emloop (P.η (suc (suc (suc k)) , k<)))
             (λ i →
         hcomp
         (doubleComp-faces (emloop ((0 , tt) P.∷ P.ε))
          (emloop ((0 , tt) P.∷ P.ε)) i)
         (emloop ((1 , tt) P.∷ P.ε) i))
        (λ i →
         hcomp
         (doubleComp-faces (emloop ((0 , tt) P.∷ P.ε))
          (emloop ((0 , tt) P.∷ P.ε)) i)
         (emloop ((1 , tt) P.∷ P.ε) i))
    ss = flipSquare
      (sym (emloop-doubleComp _ _ _ _) ◁
       comm→PathP
        (sym (emloop-comp _ _ _) ◁ cong emloop
               (sym ( cong (λ z → (zero , _) P.∷ ((suc zero) , _) P.∷ z)
                    (P.comm _ _ _ _)
                  ∙∙ cong ((P.η (zero , _)) P.·_) (P.comm _ _ _ _) 
                  ∙∙ P.comm _ _ _ _))

         ▷ emloop-comp _ _ _)
       ▷ emloop-doubleComp _ _ _ _)

toPG'R3 : ∀ n → EMelimSet (P.PermG n)
      (λ (b : EM₁ (P.PermG n)) →
      toPGcomm (suc (suc n))
      (toPGcomm (suc n) (toPGcomm n b))
      ≡
      toPGcomm (suc (suc n))
      (toPGcomm (suc n) (toPGcomm n b)))
EMelimSet.isSetB (toPG'R3 n) _ = emsquash _ _
EMelimSet.b (toPG'R3 n) = toPG'R3base n
EMelimSet.bPathP (toPG'R3 n) =
  P.RelimProp.f (toPG'R3loop n)


toPG'R4 : ∀ n → EMelimProp (P.PermG n)
      (λ z →
         SquareP (λ i j → EM₁ (P.PermG (suc (suc (suc n)))))
         (congP (λ _ → toPGcomm (suc (suc n)))
          (toPG'R1f n z))
         (EMelimSet.f (toPG'R3 n) z)
         (toPG'R1f (suc n) (toPGcomm n z))
         (toPG'R1f (suc n) (toPGcomm n z)))
EMelimProp.isPropB (toPG'R4 n) _ = isPropSqP (λ _ _ → emsquash) _ _ _ _
EMelimProp.b (toPG'R4 n) =
  ( doubleCompPath-filler (sym (emloop (P.η (0 , _)))) _ _ ▷
     cong {x = (sym (emloop (P.η (0 , _))))} {y = (emloop (P.η (0 , _)))}
       (λ p → p ∙∙ (emloop (P.η (1 , _))) ∙∙ (emloop (P.η (0 , _))))
       (sym (emloop-sym _ _)))


toPG'R5 : ∀ n → EMelimProp (P.PermG n)
      (λ z →
         SquareP (λ i j → EM₁ (P.PermG (suc (suc (suc n)))))
         (EMelimSet.f (toPG'R3 n) z)
         (toPG'R1f (suc n) (toPGcomm n z))
         (congP (λ _ → toPGcomm (suc (suc n)))
          (toPG'R1f n z))
         (congP (λ _ → toPGcomm (suc (suc n)))
          (toPG'R1f n z)))
EMelimProp.isPropB (toPG'R5 n) _ = isPropSqP (λ _ _ → emsquash) _ _ _ _
EMelimProp.b (toPG'R5 n) = 
  ( ((sym (emloop-doubleComp _ _ _ _) ∙∙
        cong emloop (P.braid _ _ _)
        ∙∙ emloop-doubleComp _ (P.η (1 , _)) (P.η (0 , _)) _) ∙
         cong (λ x → emloop ((P.η (1 , _))) ∙∙ emloop ((P.η (0 , _))) ∙∙ x)
          (emloop-sym _ _)  )
        
     ◁ symP (doubleCompPath-filler (emloop ((1 , tt) P.∷ P.ε)) _ _))
toPG'R : RElim {A = Unit} (λ z → EM₁ (P.PermG (len2 z)))
RElim.[]* toPG'R = embase
(toPG'R RElim.∷* x) {xs} = toPGcomm (len2 xs)
RElim.comm* toPG'R _ _ {xs} = toPG'R1f (len2 xs)


RElim.comm-inv* toPG'R x y {xs} = toPG'R2f (len2 xs)
RElim.hexDiag* toPG'R _ _ _ {xs} = EMelimSet.f (toPG'R3 (len2 xs))
RElim.hexU* toPG'R _ _ _ {xs} = EMelimProp.f (toPG'R4 (len2 xs))
RElim.hexL* toPG'R _ _ _ {xs} = EMelimProp.f (toPG'R5 (len2 xs))
RElim.trunc* toPG'R _ = emsquash



toPG' : (e : Perm₂) → EM₁ (P.PermG (len2 e))
toPG' = RElim.f toPG'R

-- PGlenR : ∀ n → EMelimProp (P.PermG n)
--       (λ z → len2 (EMrec.f (fromPG'R n) z) ≡ n)
-- EMelimProp.isPropB (PGlenR n) _ = isSetℕ _ _
-- EMelimProp.b (PGlenR zero) = refl
-- EMelimProp.b (PGlenR (suc n)) = cong suc (EMelimProp.b (PGlenR n))

-- PGlen : ∀ x y → len2 (EMrec.f (fromPG'R x) y) ≡ x
-- PGlen n = EMelimProp.f (PGlenR n)

PGRetRLem1RLem : ∀ n → P.RelimProp {n = n}
      (λ z →
         (P.Rrec.f (fromPG≡ (suc n)) (P.Rrec.f (P.sucPermR n) z)) ≡
         (cong (tt ∷2_) (P.Rrec.f (fromPG≡ n) z)))
P.RelimProp.isPropA (PGRetRLem1RLem n) _ = trunc _ _ _ _
P.RelimProp.εA (PGRetRLem1RLem n) = refl
P.RelimProp.∷A (PGRetRLem1RLem (suc (suc n))) k X =
    cong (_ ∙_) X ∙
     sym (cong-∙ (tt ∷2_) _ _)

PGRetRLem1R : ∀ n → EMelimSet (P.Perm n , snd (P.PermG n))
      (λ z →
         uncurry fromPG' (suc n , EMfunct (P.sucPerm , P.sucPermGH n) z) ≡
         tt ∷2 uncurry fromPG' (n , z))
EMelimSet.isSetB (PGRetRLem1R n) _ = trunc _ _
EMelimSet.b (PGRetRLem1R n) = refl
EMelimSet.bPathP (PGRetRLem1R n) = flipSquare ∘ P.RelimProp.f (PGRetRLem1RLem n)

PGretRLem1 : ∀ n → ∀ e →
   uncurry fromPG' (suc n ,
     EMfunct (P.sucPerm , P.sucPermGH n) e) ≡
      tt ∷2 uncurry fromPG' (n , e)
PGretRLem1 n = EMelimSet.f (PGRetRLem1R n)

ssLem : ∀ n → EMelimProp (P.PermG n)
      (λ z →
         PathP
         (λ i →
            uncurry fromPG' (suc (suc n) , toPG'R1f n z i) ≡
            comm tt tt (uncurry fromPG' (n , z)) i)
         (PGretRLem1 (suc n) (toPGcomm n z) ∙
          cong (_∷2_ tt) (PGretRLem1 n z))
         (PGretRLem1 (suc n) (toPGcomm n z) ∙
          cong (_∷2_ tt) (PGretRLem1 n z)))
EMelimProp.isPropB (ssLem n) _ =
  isPropSqP (λ _ _ → trunc) _ _ _ _
EMelimProp.b (ssLem n) i j = 
  hcomp (λ k → λ { (j = i1) → (comm tt tt (iter n (_∷2_ tt) []) i)
                  ; (j = i0) (i = i1) → tt ∷2 tt ∷2 iter n (_∷2_ tt) []
                  ; (j = i0) (i = i0) → tt ∷2 tt ∷2 iter n (_∷2_ tt) []
                  })
    (comm tt tt (iter n (_∷2_ tt) []) i)


PGretR : RElimSet' (λ z → uncurry fromPG' (len2 z , toPG' z) ≡ z)
RElimSet'.[]* PGretR = refl
(PGretR RElimSet'.∷* x) {xs} x₁ =
  PGretRLem1 (len2 xs) (toPG' xs) ∙ cong (x ∷2_) x₁
RElimSet'.comm* PGretR x y {xs} b =
  cong (PGretRLem1 (suc (len2 xs)) (toPG' (x ∷2 xs)) ∙_)
    (cong-∙ (x ∷2_) _ _) 
      ∙ assoc _ _ _
    ◁
     (λ i → EMelimProp.f (ssLem (len2 xs)) (toPG' xs) i ∙ λ j → comm x y (b j) i)
   ▷ sym (assoc _ _ _) ∙
      cong (PGretRLem1 (suc (len2 xs)) (toPG' (y ∷2 xs)) ∙_)
     (sym (cong-∙ (y ∷2_) _ _))

RElimSet'.trunc* PGretR _ = trunc _ _

PGret : retract (λ x → len2 x , toPG' x) (uncurry fromPG')
PGret = RElimSet'.f PGretR


PGSecBase : ∀ n → Path (Σ ℕ (λ v → EM₁ (P.PermG v)))
      (len2 (EMrec.f (fromPG'R n) embase) ,
       RElim.f toPG'R (EMrec.f (fromPG'R n) embase))
      (n , embase)
PGSecBase zero = refl
PGSecBase (suc n) =
  let p = PGSecBase n
  in ΣPathP (cong (suc ∘ fst) p , cong (toPGcomm _ ∘ snd) p)

PGSecBase-fst : ∀ n → len2 (iter n (_∷2_ tt) []) ≡ n
PGSecBase-fst zero = refl
PGSecBase-fst (suc n) = cong suc (PGSecBase-fst n)

-- PGSecBase-snd' : ∀ n → 
--       (RElim.f toPG'R (iter n (_∷2_ tt) []))
--       ≡ embase
-- PGSecBase-snd' zero = refl
-- PGSecBase-snd' (suc n) = {!PGSecBase-snd' n!}


-- PGSecBase-snd : ∀ n → transp (λ i → EM₁ (P.PermG (PGSecBase-fst n i))) i0
--       (RElim.f toPG'R (iter n (_∷2_ tt) []))
--       ≡ embase
-- PGSecBase-snd n = {!!}

-- PGSecBase' : ∀ n → Path (Σ ℕ (λ v → EM₁ (P.PermG v)))
--       (len2 (EMrec.f (fromPG'R n) embase) ,
--        RElim.f toPG'R (EMrec.f (fromPG'R n) embase))
--       (n , embase)
-- PGSecBase' n = ΣPathP ((PGSecBase-fst n) , (toPathP {!!}))

-- PGSecBase-snd : ∀ n → PathP (λ i → EM₁ (P.PermG (PGSecBase-fst n i)))
--       (RElim.f toPG'R (iter n (_∷2_ tt) [])) embase
-- PGSecBase-snd zero = refl
-- PGSecBase-snd (suc n) = {!PGSecBase-snd n!}

-- PGSecBase : ∀ n → Path (Σ ℕ (λ v → EM₁ (P.PermG v)))
--       (len2 (EMrec.f (fromPG'R n) embase) ,
--        RElim.f toPG'R (EMrec.f (fromPG'R n) embase))
--       (n , embase)
-- PGSecBase n = ΣPathP (PGSecBase-fst n , {!!})

-- zero = refl
-- PGSecBase (suc zero) = refl
-- PGSecBase (suc (suc n)) = 
--   let p = PGSecBase (suc n)
--   in ΣPathP ({!!} , {!!})


zzzPredFin₂ : ∀ n → Fin₂ (fromPG' (suc (suc n)) embase) → Fin₂ (fromPG' (suc n) embase)
zzzPredFin₂ n nothing = nothing
zzzPredFin₂ n (just x) = x


CoverM : ∀ {ℓ} {A : Type ℓ} → Maybe A → hProp ℓ-zero
CoverM nothing = Lo.⊤
CoverM (just _) = Lo.⊥

zzzTy : ∀ n → (Fin₂ (fromPG' n embase) → Fin₂ (fromPG' n embase)) → hProp ℓ-zero
zzzTy zero f = Lo.⊤
zzzTy (suc zero) f = CoverM (f nothing)
zzzTy (suc (suc n)) f =
  CoverM (f nothing)
    ⊓ zzzTy (suc n) (zzzPredFin₂ n ∘ f ∘ just)

Fin'' : ∀ n → Type
Fin'' n = fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥))

isSetFin'' : ∀ n → isSet (Fin'' n)
isSetFin'' n = snd (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥))


-- nPerm₂≡Fin : {!!}
-- nPerm₂≡Fin = {!!}

-- encodeFin₂ : ∀ n x → nPerm₂ n ≡ x → (Fin₂ (nPerm₂ n) ≃ Fin₂ x)
-- encodeFin₂ n x p = pathToEquiv (cong Fin₂ p)

-- decodeFin₂' : {!!}
-- decodeFin₂' = {!!}

-- decodeFin₂ : ∀ n x → (Fin₂ (nPerm₂ n) ≃ Fin₂ x) → nPerm₂ n ≡ x
-- decodeFin₂ = {!!}



-- decodeFin₂ zero = {!!}
-- decodeFin₂ (suc n) = {!!}

-- IsRefl : ∀ n → nPerm₂ n ≡ nPerm₂ n  → hProp ℓ-zero
-- IsRefl n p = zzzTy n (subst Fin₂ p)

-- IsRefl→≡refl : ∀ n → ∀ p → ⟨ IsRefl n p ⟩ → p ≡ refl
-- IsRefl→≡refl = {!!}

-- -- IsRefl' : ∀ n → ∀ x →  nPerm₂ n ≡ x → hProp ℓ-zero
-- -- IsRefl' zero = RElimSet'.f w 
-- --   where
-- --     w : RElimSet' (λ z → nPerm₂ zero ≡ z → hProp ℓ-zero)
-- --     RElimSet'.[]* w = λ _ → Lo.⊤
-- --     RElimSet'._∷*_ w = λ _ _ _ → Lo.⊥
-- --     RElimSet'.comm* w x y b = {!!}
-- --     RElimSet'.trunc* w = {!!}
-- -- IsRefl' (suc n) =  RElimSet'.f w
-- --   where
-- --     w : RElimSet' (λ z → nPerm₂ (suc n) ≡ z → hProp ℓ-zero)
-- --     RElimSet'.[]* w p = ⊥.rec (snotz (cong (len2) p))
-- --     (w RElimSet'.∷* x) {xs} x₁ x₂ =
-- --       IsRefl' n xs {!!}
-- --     RElimSet'.comm* w = {!!}
-- --     RElimSet'.trunc* w = {!!}

-- -- zzzTy n (transport (cong Fin₂ p))

-- -- fromIsRefl' : ∀ n → ∀ p → ⟨ IsRefl n p ⟩ → p ≡ refl
-- -- fromIsRefl' zero p x = {!!}
-- -- fromIsRefl' (suc n) p x = {!!}


-- -- -- fromIsRefl : ∀ n → ∀ p → fst (IsRefl n p) → p ≡ refl
-- -- -- fromIsRefl n p x = {!!}


-- -- -- IsReflJ : ∀ n → Path (EM₁ (P.PermG n)) embase embase → hProp ℓ-zero 
-- -- -- IsReflJ n p = zzzTy n (transport (cong (Fin₂ ∘ fromPG' _) p))


-- -- -- -- MaybePath.Cover (f nothing) nothing × zzzTy n {!f ∘ just!}

-- -- -- IsRefl : ∀ n → Path (EM₁ (P.PermG n)) embase embase → hProp ℓ-zero 
-- -- -- IsRefl n p = zzzTy n (transport (cong (Fin₂ ∘ fromPG' _) p))



-- -- -- fromIsRefl' : ∀ n → ∀ (p : Path (EM₁ (P.PermG n)) embase embase)
-- -- --                  → {!!} → p ≡ refl
-- -- -- fromIsRefl' n p x = {!isInjectiveTransport ?!}

-- -- -- fromIsRefl : ∀ n → ∀ p → fst (IsRefl n p) → p ≡ refl
-- -- -- fromIsRefl n p x = {!!}

-- -- -- MaybePath.Cover
-- -- --     (transport (cong (Fin₂ ∘ fromPG' _) p) nothing)
-- -- --     nothing

-- -- -- PGSecBase' : ∀ n → Path (Σ ℕ (λ v → EM₁ (P.PermG v)))
-- -- --       (len2 (EMrec.f (fromPG'R n) embase) ,
-- -- --        RElim.f toPG'R (EMrec.f (fromPG'R n) embase))
-- -- --       (n , embase)
-- -- -- PGSecBase' = {!!}



-- -- -- nPermEmbaseSuc : ∀ n → toPG' (nPerm₂ (suc n)) ≡ toPGcomm _ (toPG' (nPerm₂ n)) 
-- -- -- nPermEmbaseSuc zero = refl
-- -- -- nPermEmbaseSuc (suc n) = cong (toPGcomm _) (nPermEmbaseSuc n)

-- -- -- nPermEmbase : ∀ n → toPG' (nPerm₂ n) ≡ embase
-- -- -- nPermEmbase zero = refl
-- -- -- nPermEmbase (suc n) =
-- -- --    nPermEmbaseSuc n
-- -- --    ∙ cong (toPGcomm _) (nPermEmbase n)


-- -- -- zzzW : ∀ n → embase ≡ toPGcommW _ (toPG' (nPerm₂ n))
-- -- -- zzzW zero = refl
-- -- -- zzzW (suc n) = cong (toPGcommW _) (sym (nPermEmbase (suc n)))


-- -- -- PGSecBaseSuc : ∀ n → snd (PGSecBase (suc n) i0) ≡
-- -- --                       snd (toPGcommWΣ (PGSecBase n i0))
-- -- -- PGSecBaseSuc zero = refl
-- -- -- PGSecBaseSuc (suc n) =
-- -- --   nPermEmbase (suc (suc n)) ∙∙ refl
-- -- --     ∙∙  cong (toPGcommW _) (sym (nPermEmbase (suc n)))

-- -- -- zzzwww : ∀ n → SquareP (λ _ i₁ →
-- -- --             EM₁ (P.PermG (suc (fst (cong toPGcommWΣ (PGSecBase n) i₁)))))
-- -- --      ((cong (toPGcommW _ ∘ toPGcommW _ ∘ snd) (PGSecBase n)))
-- -- --      (cong (toPGcommW _ ∘ snd) (PGSecBase (suc n)))
-- -- --      {!!} --(cong (toPGcommW _) {!sym (nPermEmbase (suc n))!})
-- -- --      λ _ → embase
-- -- -- zzzwww n k i₁ = {!!}

-- -- -- PGSecBaseSucSQ : ∀ n → Square
-- -- --               (cong (toPGcommWΣ) (PGSecBase n))
-- -- --               (PGSecBase (suc n))
-- -- --               (ΣPathP (refl , sym (PGSecBaseSuc n)))
-- -- --               refl
-- -- -- PGSecBaseSucSQ zero = refl
-- -- -- fst (PGSecBaseSucSQ (suc n) i i₁) = suc (fst (PGSecBaseSucSQ n i i₁))
-- -- -- snd (PGSecBaseSucSQ (suc n) i i₁) =
-- -- --   hcomp
-- -- --      (λ k → λ {
-- -- --           (i₁ = i1) → embase
-- -- --          ;(i = i0) → zzzwww n k i₁
-- -- --          ;(i = i1) → {!!}
-- -- --        })
-- -- --      (toPGcommW _ (snd (PGSecBaseSucSQ n i i₁)))



PGsecFLemRε : ∀ n → PathP
      (λ i →
         Path (Σ ℕ (λ v → EM₁ (P.PermG v)))
         (len2 (nPerm₂ n) , RElim.f toPG'R (nPerm₂ n)) (n , emloop P.ε i))
      (PGSecBase n) (PGSecBase n)
PGsecFLemRε zero i j = zero , (emloop-1g _) (~ j) i
PGsecFLemRε (suc n) i j =
     suc (fst (PGsecFLemRε n i j)) ,
    (EMfunct ((P.sucPerm ,
              P.sucPermGH _)) (snd (PGsecFLemRε n i j)))


-- toPg∙ : (x y z : Perm₂) → (p : x ≡ y) → (q : y ≡ z) →
--              {!cong (!} ≡ {!!}
-- toPg∙ = {!!}



cong-∙∙' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y z w v : A} (f : A → B) (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
          → cong f (p ∙∙ q ∙∙ r) ≡ (cong f p) ∙∙ (cong f q) ∙∙ (cong f r)
cong-∙∙' f p q r i j =
  hcomp
    (λ k → λ {
       (i = i0) → f (doubleCompPath-filler p q r k j)
      ;(j = i0) → f (p (~ k))
      ;(j = i1) → f (r k)
      }) (f (q j))
     

-- sss'0 : ∀ n → Square
--       (λ i →
--          len2 (commK (suc (suc n)) (zero , tt) i) ,
--          toPG' (commK (suc (suc n)) (zero , tt) i))
--       (λ i → suc (suc n) , emloop (P.η (zero , tt)) i)
--       {!!}
--       {!!}
-- sss'0 = {!!}

-- sss' : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n))
--         → Square {A = Σ ℕ (λ v → EM₁ (P.PermG v))}
           
--            (λ i → len2 (commK n k i) , toPG' (commK n k i))
--            (λ i → n , (emloop (P.η k) i))
--            {!!}
--            {!!}
-- sss' (suc (suc zero)) (zero , k<) = {!!}
-- sss' (suc (suc (suc n))) (zero , k<) = {!!}
-- sss' (suc (suc n)) (suc k , k<) = {!!}


-- weakSucRefl : ∀ n → PathP (λ i → EM₁ (P.PermG (len2 (EMrec.f (fromPG'R (suc n)) embase))))
--       (RElim.f toPG'R (EMrec.f (fromPG'R (suc n)) embase))
--       (snd
--        (toPGcommWΣ
--         (len2 (EMrec.f (fromPG'R n) embase) ,
--          RElim.f toPG'R (EMrec.f (fromPG'R n) embase))))
-- weakSucRefl zero = refl
-- weakSucRefl (suc n) = {!!}

-- baseWeak : ∀ n → Square
--                   (PGSecBase (suc n))
--                   (cong toPGcommWΣ (PGSecBase n))
--                   (ΣPathP (refl {x = len2 (EMrec.f (fromPG'R (suc n)) embase)} ,
--                     weakSucRefl n))
--                   refl
-- baseWeak = {!!}




-- sss*0 : ∀ n → 
--          Square {A = Σ ℕ (λ v → EM₁ (P.PermG v))}
--            -- (PGSecBase n)
--            -- (PGSecBase n)
--            (λ i → len2 (commK (suc (suc n)) (zero , _) i) ,
--               toPG' (commK (suc (suc n)) (zero , _) i))
--            (λ i → (suc (suc n)) , (emloop (P.η (zero , _)) i))
--            (PGSecBase (suc (suc n)))
--            (PGSecBase (suc (suc n)))
-- sss*0 = ℕ.elim
--   refl
--   λ n X i j → {!X!}
--   --       hcomp
--   --    (λ l → λ {
--   --      (i = i0) → {!!}
--   --     ;(i = i1) → toPGcommWΣ (X i1 j)
--   --     ;(j = i0) → {!!}
--   --     ;(j = i1) → {!!}
--   --     }
--   --      )
--   --    (toPGcommWΣ (X i j))

--   -- where
--   --   sqLem : ∀ n → Square {A = Σ ℕ (λ v → EM₁ (P.PermG v))}
                         
--   --                      (cong toPGcommWΣ ((PGSecBase (suc (suc n)))))
--   --                      ((PGSecBase (suc (suc (suc n)))))
--   --                      {!!}
--   --                      refl
                       
--   --   sqLem = {!!}


-- sss*Fst : ∀ n → ∀ k<
--         → Square {A = ℕ }
--            -- (PGSecBase n)
--            -- (PGSecBase n)
--            (λ i → len2 (commK n (zero , k<) i))
--            (λ i → n )
--            (cong fst (PGSecBase n))
--            (cong fst (PGSecBase n))
-- sss*Fst (suc (suc zero)) k< i j = 2
-- sss*Fst (suc (suc (suc n))) k< i j = suc (sss*Fst (suc (suc n)) k< i j)

-- toPG'-nPerm₂ : ∀ n → toPG' (nPerm₂ (suc (suc n))) ≡ embase
-- toPG'-nPerm₂ zero = refl
-- toPG'-nPerm₂ (suc n) = {!toPG'-nPerm₂ n!}

-- Sss* : ∀ n → ∀ k< →
--              cong toPG' (commK (suc (suc n)) (zero , k<))
--                ≡ ( {! (cong snd (PGSecBase (suc (suc n))))!} ∙∙ emloop (P.η (zero , _)) ∙∙ {!!})
-- Sss* = {!!}

-- sss*T : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < suc (suc n)))
--         → Square {A = EM₁ (P.PermG (len2 (iter (suc (suc n)) (_∷2_ tt) [])))}
--            -- (PGSecBase n)
--            -- (PGSecBase n) 
--            ((fromPathP (cong toPG' (commK (suc (suc n)) k))))
--              --(λ i → len2 (commK n k i) , toPG' (commK n k i))
--            (emloop (P.η {!k!}))
--            (cong (transport
--            (λ i → EM₁ (P.PermG (len2 (commK (suc (suc n)) k i)))))
--            (toPG'-nPerm₂ n))
--             -- (sym (substComposite  (EM₁ ∘ P.PermG)
--             --   (cong  len2 (commK n k)) (cong fst (PGSecBase n))
--             --     ((toPG' (nPerm₂ n))))
--             --    ∙ {!!})
--            (toPG'-nPerm₂ n)
-- sss*T n k = {!!}


-- sss* : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n))
--         → Square {A = Σ ℕ (λ v → EM₁ (P.PermG v))}
--            -- (PGSecBase n)
--            -- (PGSecBase n)
--            (λ i → len2 (commK n k i) , toPG' (commK n k i))
--            (λ i → n , (emloop (P.η k) i))
--            (PGSecBase n)
--            (PGSecBase n)
-- sss* (suc n) k = compPathR→PathP {!!}


-- sss*' : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n))
--         → PathP (λ i → Path (EM₁ (P.PermG (PGSecBase-fst n i)))
--            {!!} {!!})
--            {!!} {!!}
-- sss*' (suc n) k = {!!}

-- -- ℕ.cases (λ { (_ , ()) })
-- --   (ℕ.cases (λ { (_ , ()) })
-- --     (ℕ.elim
-- --       {!!}
-- --       {!!}))            
-- -- -- sss* (suc (suc zero)) (zero , k<) = refl
-- -- -- sss* (suc (suc (suc n))) (zero , k<) i j =
-- -- --    hcomp
-- -- --      (λ l → λ {
-- -- --        (i = i0) → {!!}
-- -- --       ;(i = i1) → {!toPGcommWΣ (sss* (suc (suc n)) (zero , tt) l j)!}
-- -- --       ;(j = i0) → {!!}
-- -- --       ;(j = i1) → {!!}
-- -- --       }
-- -- --        )
-- -- --      {!!}

-- --    -- where
-- --    --   ssPrev : Square
-- --    --              (λ i →
-- --    --                 len2 (commK (suc (suc n)) (zero , tt) i) ,
-- --    --                 toPG' (commK (suc (suc n)) (zero , tt) i))
-- --    --              (λ i → suc (suc n) , emloop (P.η (zero , tt)) i)
-- --    --              (PGSecBase (suc (suc n))) (PGSecBase (suc (suc n)))
-- --    --   ssPrev = sss* (suc (suc n)) (zero , tt)

-- --    --   ssPrevW : Square
-- --    --                 {!!}                   
-- --    --                 (λ i → suc (suc (suc n)) , emloop (P.η (zero , tt)) i)
-- --    --                 {!!}
-- --    --                 {!!}
-- --    --   ssPrevW i j = toPGcommWΣ (ssPrev i j)

-- --   -- toPGcommWΣ {!sss* (suc (suc n)) (zero , _) i j!}
-- --   -- congP (λ _ → ΣPathP) (ΣPathP {!!})
  
-- --   --toPGcommW
-- -- --   congP (λ _ → ΣPathP) (ΣPathP (congP (λ _ → cong (suc ∘ fst)) (sss* (suc (suc n)) (zero , tt)) ,
-- -- --     {!!}))
-- -- --   where
-- -- --     ss' : SquareP (λ z i →
-- -- --                      EM₁ (P.PermG (suc (fst (sss* (suc (suc n)) (zero , tt) z i)))))
-- -- --            (λ i →
-- -- --               toPG' {!!})
-- -- --            (λ i → {!toPGcomm ((fst (sss* (suc (suc n)) (zero , tt) i1 i)))
-- -- --                   (snd ((sss* (suc (suc n)) (zero , tt)) i1 i))!})
-- -- --            {!!}
-- -- --            {!!}
-- -- --     ss' z i = toPGcomm ((fst (sss* (suc (suc n)) (zero , tt) z i)))
-- -- --                   (snd ((sss* (suc (suc n)) (zero , tt)) z i))


-- -- --     ss : SquareP (λ z i →
-- -- --                      EM₁ (P.PermG (suc (fst (sss* (suc (suc n)) (zero , tt) z i)))))
-- -- --            (λ i → toPG' (commK (suc (suc (suc n))) (zero , k<) i))
-- -- --            (λ i → emloop (P.η (zero , k<)) i)
-- -- --            (λ i →
-- -- --                toPGcomm (fst (PGSecBase (suc (suc n)) i))
-- -- --                (snd (PGSecBase (suc (suc n)) i)))
-- -- --            λ i →
-- -- --                toPGcomm (fst (PGSecBase (suc (suc n)) i))
-- -- --                (snd (PGSecBase (suc (suc n)) i))
-- -- --     ss z i = {!!}
    
-- -- -- sss* (suc (suc (suc n))) (suc k , k<) = {!!}


-- PGsecFLemR∷ : ∀ n → (k : Σ ℕ (λ k₁ → suc k₁ < n)) {xs : P.Perm n} →
--       Square        
--        (PGSecBase n) (PGSecBase n)
--        (λ i → (len2 (P.Rrec.f (fromPG≡ n) xs i) ,
--           RElim.f toPG'R (P.Rrec.f (fromPG≡ n) xs i)))
--         (λ i → (n , emloop xs i)) →
--       Square
--       (PGSecBase n) (PGSecBase n)
--       ( λ i →  (len2 (P.Rrec.f (fromPG≡ n) (k P.∷ xs) i) ,
--       RElim.f toPG'R ((commK n k ∙ P.Rrec.f (fromPG≡ n) xs) i)))
--       λ i → (n , emloop (k P.∷ xs) i)
-- PGsecFLemR∷ n k {xs} X i j =
--     hcomp
--       (λ l → λ {
--            (i = i0) → PGSecBase n j
--           ;(i = i1) → X l j
--           ;(j = i0) →  
--             (λ (x : Perm₂) → _,_ {B = (λ v → EM₁ (P.PermG v))} (len2 x) (toPG' x))
--               (compPath-filler (commK n k) (P.Rrec.f (fromPG≡ n) xs) l i)
--           ;(j = i1) → n , emcomp (P.η k) xs l i 
--            })
--              (sss* n k j i)


-- PGsecFLemR : ∀ n → P.RelimProp
--       (λ z →
--          PathP
--          (λ i →
--             Path (Σ ℕ (λ v → EM₁ (P.PermG v)))
--             (len2 (P.Rrec.f (fromPG≡ n) z i) ,
--              RElim.f toPG'R (P.Rrec.f (fromPG≡ n) z i))
--             (n , emloop z i))
--          (PGSecBase n) (PGSecBase n))
-- P.RelimProp.isPropA (PGsecFLemR n) _ =
--   isPropSqP (λ _ _ →
--     isOfHLevelΣ 3 (isSet→isGroupoid isSetℕ) (λ _ → emsquash)) _ _ _ _
-- P.RelimProp.εA (PGsecFLemR n) = PGsecFLemRε n
-- P.RelimProp.∷A (PGsecFLemR n) = PGsecFLemR∷ n 


-- PGSecF : (n : ℕ) → EMelimSet (P.PermG n) (λ (y : EM₁ (P.PermG n)) →
--       (Path (Σ ℕ (λ v → EM₁ (P.PermG v))) (len2 (EMrec.f (fromPG'R n) y) ,
--        RElim.f toPG'R (EMrec.f (fromPG'R n) y))
--         (n , y)))
-- EMelimSet.isSetB (PGSecF n) _ =
--   isOfHLevelΣ 3 (isSet→isGroupoid isSetℕ) (λ _ → emsquash) _ _
-- EMelimSet.b (PGSecF n) = PGSecBase n
-- EMelimSet.bPathP (PGSecF n) = P.RelimProp.f (PGsecFLemR n)
-- --(PGsecFLemR n)

-- PGsec : section (λ x → len2 x , toPG' x) (uncurry fromPG')
-- PGsec = uncurry λ n → EMelimSet.f (PGSecF n)


  
-- PGiso : Iso Perm₂ (Σ ℕ (EM₁ ∘ P.PermG ))
-- Iso.fun PGiso x = _ , toPG' x
-- Iso.inv PGiso = uncurry fromPG'
-- Iso.rightInv PGiso = PGsec
-- Iso.leftInv PGiso = PGret


PermGIso : ∀ n → GroupIso (P.PermG n) (SetIso-Group _ (isSetFin₂ (nPerm₂ n)))
PermGIso n = subst (GroupIso (P.PermG n))
  (cong (uncurry SetIso-Group)
    (Σ≡Prop (λ _ → isPropIsSet) (sym (isoToPath (IsoFin₂'Fin n)))))
      (P.PermGIsoIso n)

-- -- -- PermGIsoCommK : ∀ n k → Iso.inv (fst (PermGIso n))
-- -- --    (pathToEquiv (cong Fin₂ (commK n k))) ≡ P.η k 
-- -- -- PermGIsoCommK = {!!}


-- -- -- sym-emloopK : ∀ n k → (emloop {Group = (P.PermG n)} (P.η k))
-- -- --                  ≡ sym (emloop {Group = (P.PermG n)} (P.η k))
                      
-- -- -- sym-emloopK n k = emloop-sym (P.PermG n) (P.η k)





-- -- secCong' : ∀ n → (x y : EM₁ (P.PermG n)) →
-- --     hasSection (cong {x = x} {y = y} (fromPG' n))
-- -- secCong' n = {!PGret!}

-- -- PG≃PS : isPathSplitEquiv (uncurry  fromPG')
-- -- isPathSplitEquiv.sec PG≃PS = (λ x → _ , toPG' x) , PGret
-- -- isPathSplitEquiv.secCong PG≃PS = {!secCong' ?!}



secCongF : ∀ n → (x y : EM₁ (P.PermG n)) →
    (EMrec.f (fromPG'R n) x ≡ EMrec.f (fromPG'R n) y → x ≡ y)
secCongF n = EMelimSet.f w
  where

    module iso = Iso (fst (PermGIso n))
    open IsGroupHom (snd (PermGIso n))


    w : EMelimSet (P.PermG n)
          (λ z →
             (y : EM₁ (P.PermG n)) →
             EMrec.f (fromPG'R n) z ≡ EMrec.f (fromPG'R n) y → z ≡ y)
    EMelimSet.isSetB w _ = isSetΠ2 λ _ _ → emsquash _ _
    EMelimSet.b w = EMelimSet.f ww
      where
        ww : EMelimSet (P.PermG n)
               (λ z →
                  nPerm₂ n
                    ≡ EMrec.f (fromPG'R n) z → embase ≡ z)
        EMelimSet.isSetB ww _ = isSetΠ λ _ → emsquash _ _
        EMelimSet.b ww x =
           emloop (iso.inv (equivToIso (pathToEquiv (cong Fin₂ x))))
        EMelimSet.bPathP ww = P.RelimProp.f www
          where


            qqq : ∀ xs k →
             PathP
              (λ i → nPerm₂ n ≡ P.Rrec.f (fromPG≡ n) xs i → embase ≡ emloop xs i)
              (λ x → emloop (iso.inv
                  (equivToIso (pathToEquiv (λ i → Fin₂ (x i))))))
              (λ x → emloop (iso.inv
                   (equivToIso (pathToEquiv (λ i → Fin₂ (x i)))))) →
              PathP
              (λ i →
                 iter n (_∷2_ tt) [] ≡
                 hcomp
                 (doubleComp-faces (λ _ → iter n (_∷2_ tt) [])
                  (P.Rrec.f (fromPG≡ n) xs) i)
                 (commK n k i) →
                 Path (EM₁ (P.PermG n)) embase (emloop (k P.∷ xs) i))
              (λ x →
                 emloop
                 (Iso.inv (fst (PermGIso n))
                  (equivToIso
                    (pathToEquiv (λ i → fst (RRec.f Fin₂R (x i)))))))
              (λ x →
                 emloop
                 (Iso.inv (fst (PermGIso n))
                  (equivToIso
                    (pathToEquiv (λ i → fst (RRec.f Fin₂R (x i)))))))
            qqq xs k s = funExtDep qw
              -- λ {x₀} {x₁} p → {!s' {x₀} {x₁}!} 

              where
                s' : _ 
                s' = funExtDep⁻ s

                qw : {x₀ : iter n (_∷2_ tt) [] ≡ iter n (_∷2_ tt) []}
                      {x₁ : iter n (_∷2_ tt) [] ≡ nPerm₂ n}
                      (p
                       : PathP
                         (λ z →
                            iter n (_∷2_ tt) [] ≡
                            hcomp
                            (doubleComp-faces (λ _ → iter n (_∷2_ tt) [])
                             (P.Rrec.f (fromPG≡ n) xs) z)
                            (commK n k z))
                         x₀ x₁) →
                          Square
                            ((emloop {Group = P.PermG n}
                              (iso.inv
                                (equivToIso (pathToEquiv
                                (λ i → fst (RRec.f Fin₂R (x₀ i))))))))
                            ((emloop
                              (iso.inv
                               (equivToIso (pathToEquiv
                                (λ i → fst (RRec.f Fin₂R (x₁ i))))))))
                            refl
                            (emloop (k P.∷ xs))

                qw {x₀} {x₁} p =
                    flipSquare ((flipSquare s*)
                      ▷ sym (emloop-comp (P.PermG n) (P.η k) xs))

                  where

                    p′ : Square
                           x₀
                           x₁
                           (λ i → iter n (_∷2_ tt) [])
                           ((λ i → commK n k i) ∙ (P.Rrec.f (fromPG≡ n) xs))
                    p′ = p
 
                    p* : Square
                           (x₀ ∙ commK n k)
                           x₁
                           (λ i → iter n (_∷2_ tt) [])
                           (P.Rrec.f (fromPG≡ n) xs)
                    p* i j =
                      hcomp
                        (λ k' → λ {
                           (i = i1) → p i j
                          ;(j = i0) → p i j
                          ;(j = i1) → compPath-filler' (commK n k)
                              (P.Rrec.f (fromPG≡ n) xs) (~ k') i
                          })
                        (p i j)

                    s'app :
                      Square x₀ x₁ refl (P.Rrec.f (fromPG≡ n) xs) → 
                             Square
                               (emloop (iso.inv
                                 (equivToIso
                                   (pathToEquiv (λ i → Fin₂ (x₀ i))))))
                               (emloop (iso.inv
                                 (equivToIso 
                                 (pathToEquiv (λ i → Fin₂ (x₁ i))))))
                               refl
                               λ i → emloop xs i
                    s'app = s' {x₀} {x₁}



                    s'app* : 
                             Square
                               (emloop (iso.inv
                                 (equivToIso (pathToEquiv
                                  (λ i → Fin₂ ((x₀ ∙ commK n k) i))))))
                               (emloop (iso.inv
                                 (equivToIso
                                   (pathToEquiv (λ i → Fin₂ (x₁ i))))))
                               refl
                               (emloop xs)
                    s'app* = s' {x₀ ∙ commK n k} {x₁} p*

                    s*i0i0 :  (iso.inv
                                 (equivToIso
                                   (pathToEquiv (cong Fin₂ x₀)))
                                   P.· iso.inv (equivToIso(pathToEquiv (cong Fin₂ (commK n k)))))
                               ≡ (((iso.inv (equivToIso (pathToEquiv
                                  (λ i → Fin₂ ((x₀ ∙ commK n k) i)))))))
                    s*i0i0 k' = {!!}

                    s*i0 : Square
                              ((emloop (iso.inv (equivToIso(pathToEquiv
                                  (λ i → Fin₂ ((x₀ ∙ commK n k) i)))))))
                              (emloop (iso.inv (equivToIso(pathToEquiv (λ i → Fin₂ (x₀ i))))))
                              refl
                              (sym (emloop (P.η k)))
                    s*i0 i j = hcomp (λ k' → λ {
                         (i = i0) → emloop (s*i0i0 k') j
                       ; (i = i1) → 
                           (emloop (iso.inv (equivToIso(pathToEquiv (λ i → Fin₂ (x₀ i)))))) j
                       ; (j = i0) → embase
                       ; (j = i1) → emloop-sym (P.PermG n) (P.η k) k' i
                        })  
                        {!!}
                      -- (emcomp (iso.inv (equivToIso
                      --   (pathToEquiv (λ i → Fin₂ (x₀ i)))))
                      --  (P.η k) i j   )


                    s* : Square
                           (emloop (iso.inv (equivToIso(pathToEquiv (λ i → Fin₂ (x₀ i))))))
                           (emloop (iso.inv (equivToIso(pathToEquiv (λ i → Fin₂ (x₁ i))))))
                           refl
                           (emloop (P.η k) ∙ emloop xs)
                           
                    s* i j = hcomp (λ k' → λ {
                         (i = i0) → s*i0 k' j
                       ; (i = i1) → (s'app* i j)
                       ; (j = i0) → (s'app* i j)
                       ; (j = i1) → compPath-filler'
                          (emloop (P.η k)) (emloop xs) k' i
                        }) (s'app* i j)

            www : P.RelimProp
                    (λ z →
                       PathP
                       (λ i →
                          EMrec.f (fromPG'R n) embase
                        ≡ EMrec.f (fromPG'R n) (emloop z i) →
                          embase ≡ emloop z i)
                       (EMelimSet.b ww) (EMelimSet.b ww))
            P.RelimProp.isPropA www _ = {!!}
            P.RelimProp.εA www i x i₁ =
              hcomp (λ k → λ {
                 (i = i0) →
                    emloop (iso.inv (equivToIso (pathToEquiv (λ i₂ → Fin₂ (x i₂))))) i₁
                 ;(i = i1) →
                    emloop (iso.inv (equivToIso(pathToEquiv (λ i₂ → Fin₂ (x i₂))))) i₁
                 ;(i₁ = i0) → embase
                 ;(i₁ = i1) → emloop-1g (P.Perm n , snd (P.PermG n)) (~ k) i
                 }) (emloop (iso.inv (equivToIso(pathToEquiv (λ i₂ → Fin₂ (x i₂))))) i₁)
            P.RelimProp.∷A www k {xs} = qqq xs k

    EMelimSet.bPathP w = {!!}
     -- P.RelimProp.f ww

     --  where
     --    ww : P.RelimProp
     --           (λ z →
     --              PathP
     --              (λ i →
     --                 (y : EM₁ (P.PermG n)) →
     --                 EMrec.f (fromPG'R n) (emloop z i) ≡ EMrec.f (fromPG'R n) y →
     --                 emloop z i ≡ y)
     --              (EMelimSet.b w) (EMelimSet.b w))
     --    P.RelimProp.isPropA ww = {!!}
     --    P.RelimProp.εA ww = funExt λ x → funExt λ x₁ →
     --       flipSquare (emloop-1g (P.Perm n , snd (P.PermG n)) ◁
     --          flipSquare (refl {x = EMelimSet.b w x x₁}))
     --    P.RelimProp.∷A ww k {xs} X = funExt (EMelimProp.f wwz)
     --      where
     --       wwz : EMelimProp (P.PermG n)
     --               (λ z →
     --                  PathP
     --                  (λ z₁ →
     --                     EMrec.f (fromPG'R n) (emloop (k P.∷ xs) z₁) ≡
     --                     EMrec.f (fromPG'R n) z →
     --                     emloop (k P.∷ xs) z₁ ≡ z)
     --                  (EMelimSet.b w z) (EMelimSet.b w z))
     --       EMelimProp.isPropB wwz = {!!}
     --       EMelimProp.b wwz = {!!}
     --         --  funExtDep qq

             -- where

             --  qq : {x₀ x₁ : nPerm₂ n ≡ nPerm₂ n}
             --       (p
             --        : PathP (λ z → (commK n k ∙ P.Rrec.f (fromPG≡ n) xs) z ≡ nPerm₂ n)
             --          x₀ x₁) →
             --       Square
             --         ((emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₀ i))))))
             --         ((emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₁ i))))))
             --         (emloop (k P.∷ xs))
             --         refl
                   
             --       -- PathP (λ i → emloop (k P.∷ xs) i ≡ embase)
             --       -- (emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₀ i)))))
             --       -- (emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₁ i)))))
             --  qq {x₀} {x₁} p =
             --     flipSquare (
             --       (emloop-comp (P.PermG n) (P.η k) xs)
             --         ◁ flipSquare qqOk)

             --    where
             --      p′ : Square
             --            x₀
             --            x₁
             --            (commK n k ∙ P.Rrec.f (fromPG≡ n) xs)
             --            refl
             --      p′ = p


             --      zz : Square
             --             x₀
             --             x₁
             --             (λ i → P.Rrec.f (fromPG≡ n) xs i)
             --             refl
             --              →
             --             Square
             --             (EMelimSet.b w embase x₀)
             --             (EMelimSet.b w embase x₁)
             --             (emloop xs)
             --             refl

             --      zz = funExtDep⁻ (funExt⁻ X embase) {x₀} {x₁}

             --      zzApp : Square
             --           (EMelimSet.b w embase (x₀ ∙ commK n k))
             --           (EMelimSet.b w embase x₁)
             --           (emloop xs)
             --           refl
             --      zzApp = funExtDep⁻ (funExt⁻ X embase) {x₀ ∙ commK n k} {x₁}
             --       {!!}

             --      qqOk : Square
             --               (EMelimSet.b w embase x₀)
             --               (EMelimSet.b w embase x₁)
             --               (emloop (P.η k) ∙ emloop xs)
             --               refl
                           
             --      qqOk = {!!}

sec* : ∀ n → section (cong (fromPG' n)) (secCongF n embase embase)
sec* n b = ww

  where
    ww : Square (cong (fromPG' n) (secCongF n embase embase b))
           b refl refl
    ww = {!!}


secCong' : ∀ n → (x y : EM₁ (P.PermG n)) →
    hasSection (cong {x = x} {y = y} (fromPG' n))
fst (secCong' n x y) = secCongF n x y
snd (secCong' n x y) = {!!}

PG≃PS : isPathSplitEquiv (uncurry fromPG')
isPathSplitEquiv.sec PG≃PS = (λ x → _ , toPG' x) , PGret
isPathSplitEquiv.secCong PG≃PS = {!!}
   


-- -- module _ {ℓ} {A : Type ℓ} where 

-- --   toPerm₂ : FMSet2 A → Perm₂
-- --   toPerm₂ [] = []
-- --   toPerm₂ (x ∷2 x₁) = (_ ∷2 toPerm₂ x₁)
-- --   toPerm₂ (comm x y x₁ i) = (comm _ _ (toPerm₂ x₁) i)
-- --   toPerm₂ (comm-inv x y x₁ i i₁) = (comm-inv _ _ (toPerm₂ x₁) i i₁)
-- --   toPerm₂ (hexDiag x y z x₁ i) = (hexDiag _ _ _ (toPerm₂ x₁) i)
-- --   toPerm₂ (hexU x y z x₁ i i₁) = (hexU _ _ _ (toPerm₂ x₁) i i₁)
-- --   toPerm₂ (hexL x y z x₁ i i₁) = (hexL _ _ _ (toPerm₂ x₁) i i₁)
-- --   toPerm₂ (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
-- --     (trunc _ _ _ _
-- --      (λ i j → toPerm₂ (x₃ i j)) ((λ i j → toPerm₂ (y₁ i j))) i i₁ x₄)


-- -- -- module _ {ℓ} (A : Type ℓ) (isGrpA : isGroupoid A) where 

-- -- --   toPerm₂ : FMSet2 A → Perm₂
-- -- --   toPerm₂ [] = []
-- -- --   toPerm₂ (x ∷2 x₁) = (_ ∷2 toPerm₂ x₁)
-- -- --   toPerm₂ (comm x y x₁ i) = (comm _ _ (toPerm₂ x₁) i)
-- -- --   toPerm₂ (comm-inv x y x₁ i i₁) = (comm-inv _ _ (toPerm₂ x₁) i i₁)
-- -- --   toPerm₂ (hexDiag x y z x₁ i) = (hexDiag _ _ _ (toPerm₂ x₁) i)
-- -- --   toPerm₂ (hexU x y z x₁ i i₁) = (hexU _ _ _ (toPerm₂ x₁) i i₁)
-- -- --   toPerm₂ (hexL x y z x₁ i i₁) = (hexL _ _ _ (toPerm₂ x₁) i i₁)
-- -- --   toPerm₂ (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
-- -- --     (trunc _ _ _ _
-- -- --      (λ i j → toPerm₂ (x₃ i j)) ((λ i j → toPerm₂ (y₁ i j))) i i₁ x₄)


-- -- --   commLem :  (x y : A) {C : Type}
-- -- --                (b : C → A) →
-- -- --             ⊎.rec {A = Unit} (λ _ → x) (⊎.rec {A = Unit} (λ _ → y) b) ≡
-- -- --       ⊎.rec (λ _ → y) (⊎.rec (λ _ → x) b) ∘ swap0and1⊎f
-- -- --   commLem x y b i (_⊎_.inl x₁) = x
-- -- --   commLem x y b i (_⊎_.inr (_⊎_.inl x₁)) = y
-- -- --   commLem x y b i (_⊎_.inr (_⊎_.inr x₁)) = b x₁

-- -- --   toF→R : RElim {A = A} (λ z → Fin⊎' z → A)
-- -- --   RElim.[]* toF→R = ⊥.rec*
-- -- --   (toF→R RElim.∷* x) = ⊎.rec λ _ → x
-- -- --   RElim.comm* toF→R x y {xs} b =
-- -- --     commLem x y b ◁ ua→' _ _
    
-- -- --   RElim.comm-inv* toF→R = {!!}
-- -- --   RElim.hexDiag* toF→R = {!!}
-- -- --   RElim.hexU* toF→R = {!!}
-- -- --   RElim.hexL* toF→R = {!!}
-- -- --   RElim.trunc* toF→R = {!!}

-- -- --   toF→ : (x : FMSet2 A) → Fin⊎' x → A
-- -- --   toF→ = RElim.f {!!}

-- -- curry' : ∀ {ℓ ℓ' ℓ''}
-- --   {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
-- --    → ((A × B) → C) → A → B → C
-- -- curry' f x y = f (x , y)


-- -- module _ {ℓ} (A : Type ℓ) where 
-- --   open mkRecTest ℓ



-- --   maybeSucIso : {B : Type₀}
-- --      → Iso (A × (B → A)) (Maybe B → A)
-- --   maybeSucIso = w
-- --     where

-- --        w : Iso (A × (_ → A)) (Maybe _ → A)
-- --        Iso.fun w = uncurry Mb.rec
-- --        Iso.inv w f = (f nothing) , (f ∘ just)
-- --        Iso.rightInv w b = funExt (Mb.elim _ refl λ _ → refl)
-- --        Iso.leftInv w _ = refl

-- --   ∷VecR : {B : Type₀} →
-- --           Σ (Type ℓ) (λ T → T ≃ (B → A))
-- --         → Σ (Type ℓ) (λ T → T ≃ (Maybe B → A))
-- --   ∷VecR (T , e) =
-- --     (A × T) , ≃-× (idEquiv _) e ∙ₑ isoToEquiv (maybeSucIso) 

-- --   ∷VecR' : {B : Type₀} →
-- --           Σ (Type ℓ) (λ T → (B → A) ≃ T )
-- --         → Σ (Type ℓ) (λ T → (Maybe B → A) ≃ T)
-- --   ∷VecR' (T , e) =
-- --     (A × T) ,  isoToEquiv (invIso (maybeSucIso)) ∙ₑ ≃-× (idEquiv _) e

-- --   swap× : (B : Type ℓ) → (A × (A × B)) → (A × (A × B)) 
-- --   swap× _ x = (fst (snd x)) , ((fst x) , (snd (snd x)))

-- --   swapInvol : (B : Type ℓ) → isInvolution {A = (A × (A × B))}
-- --        (swap× B)
-- --   swapInvol _ _ = refl

-- --   swapIso' : (B : Type ℓ) → Iso (A × (A × B)) (A × (A × B))
-- --   swapIso' B = involIso {f = (swap× B)}
-- --    (swapInvol B)

-- --   commInvVecRsq : (B : Type ℓ) →  
-- --      Square (ua (isoToEquiv (swapIso' B)))
-- --       (sym ((ua (isoToEquiv (swapIso' B)))))
-- --        refl refl
-- --   commInvVecRsq B = involPathSym λ z _ → z
    

-- --   -- toF→R : RElim {A = A} (λ z → Fin₂ (toPerm₂ z) → A)
-- --   -- RElim.[]* toF→R = ⊥.rec
-- --   -- RElim._∷*_ toF→R a {xs} = Mb.rec a 
-- --   -- RElim.comm* toF→R = {!!}
-- --   -- RElim.comm-inv* toF→R = {!!}
-- --   -- RElim.hexDiag* toF→R = {!!}
-- --   -- RElim.hexU* toF→R = {!!}
-- --   -- RElim.hexL* toF→R = {!!}
-- --   -- RElim.trunc* toF→R = {!!}

-- --   -- toF→ : (x : FMSet2 A) → Fin₂ (toPerm₂ x) → A
-- --   -- toF→ = RElim.f {!!}


-- --   -- commInvVecRsqFun : (h : hSet ℓ-zero)
-- --   --   (b  : Σ (Type ℓ) (λ T → T ≃ (fst h → A))) →
-- --   --    SquareP (λ i j →  commInvVecRsq (fst b) i j  → (invoFinR h i j → A))
-- --   --        ((ua→ λ a →
-- --   --       toPathP (funExt (Mb.elim _
-- --   --        (transportRefl (fst (snd a)))
-- --   --         (Mb.elim _
-- --   --           (transportRefl (fst a))
-- --   --           λ x → transportRefl _ ∙ cong (fst (snd b) (snd (snd a)))
-- --   --             (transportRefl _))))))
-- --   --        (symP ((ua→ λ a →
-- --   --       toPathP (funExt (Mb.elim _
-- --   --        (transportRefl (fst (snd a)))
-- --   --         (Mb.elim _
-- --   --           (transportRefl (fst a))
-- --   --           λ x → transportRefl _ ∙ cong (fst (snd b) (snd (snd a)))
-- --   --             (transportRefl _)))))))
-- --   --        (refl {x = fst ((snd ∘ ∷VecR ∘ ∷VecR) b)})
-- --   --        (refl {x = fst ((snd ∘ ∷VecR ∘ ∷VecR) b)})
-- --   -- commInvVecRsqFun h b =
-- --   --    {!!}


-- -- -- sqF'-no : ∀ xs → SquareP (λ i j → Fin₂ (comm-inv _ _ xs i j))
-- -- --          (ua-gluePath _ (λ i → just nothing))
-- -- --          (symP (ua-gluePath _ (λ i → nothing)))
-- -- --          (λ _ → nothing)
-- -- --          (λ _ → just nothing)
-- -- -- sqF'-no xs = isSet→SquareP
-- -- --   (λ i j → isSetFin₂ (comm-inv _ _ xs i j)) _ _ _ _



-- --   sqTySingl≃ : (B : I → I → Type₀)
-- --       (A' : I → I → Type ℓ)
-- --       (e' : ∀ i j → (B i j → A) → A' i j)
-- --       {p00 : isEquiv (e' i0 i0)}
-- --       {p01 : isEquiv (e' i0 i1)}
-- --       {p10 : isEquiv (e' i1 i0)}
-- --       {p11 : isEquiv (e' i1 i1)}
-- --       (p0j : PathP (λ j → isEquiv (e' i0 j)) p00 p01 )
-- --       (p1j : PathP (λ j → isEquiv (e' i1 j)) p10 p11 )
-- --       (pi0 : PathP (λ i → isEquiv (e' i i0)) p00 p10 )
-- --       (pi1 : PathP (λ i → isEquiv (e' i i1)) p01 p11 )
-- --       → SquareP
-- --       (λ i j → Σ (Type ℓ) (λ T → (B i j → A) ≃ T))
-- --       (λ j → (A' i0 j) , e' i0 j , p0j j)
-- --       (λ j → (A' i1 j) , e' i1 j , p1j j)
-- --       (λ i → (A' i i0) , e' i i0 , pi0 i)
-- --       (λ i → (A' i i1) , e' i i1 , pi1 i)
-- --   sqTySingl≃ B A' e' p0j p1j pi0 pi1 i j =
-- --     A' i j , (e' i j) , (isSet→SquareP (λ i j → isProp→isSet (isPropIsEquiv (e' i j)))
-- --       p0j p1j pi0 pi1 i j)

-- --   -- ua∘ : ∀ {ℓ} {A A' B B' C : Type ℓ} → (e : {!!}) → (f : {!!})
-- --   --            → {!!}
-- --   -- ua∘ = {!!}

-- --   -- commInvSq : (B : Type ℓ) → Square
-- --   --   (ua (isoToEquiv (swapIso {A = A} {B = A} {C = B})))
-- --   --    (sym ((ua (isoToEquiv (swapIso {A = A} {B = A} {C = B})))))
-- --   --    refl refl
-- --   -- commInvSq B =
-- --   --   {!involPathSym {f = ?} ?!}

-- --   PermVecR : RElim {A = Unit}
-- --                  λ e → Σ (Type ℓ) (λ T → (Fin₂ e → A) ≃ T)
-- --   RElim.[]* PermVecR = Unit* , invEquiv (Unit*≃⊥→A A)
-- --   RElim._∷*_ PermVecR = λ _ → ∷VecR'
-- --   RElim.comm* PermVecR x y {xs} b =
-- --     ΣPathP (ua (isoToEquiv (swapIso' (fst b))) ,
-- --       ΣPathPProp (isPropIsEquiv) zz )
-- --    where
-- --      zz : PathP
-- --             (λ z → (Fin₂ (comm x y xs z) → A)
-- --               → ua (isoToEquiv (swapIso' (fst b))) z)
            
-- --             (fst
-- --              (isoToEquiv (invIso maybeSucIso) ∙ₑ
-- --               ≃-× (idEquiv A) (snd (∷VecR' b))))
-- --             (fst
-- --              (isoToEquiv (invIso maybeSucIso) ∙ₑ
-- --               ≃-× (idEquiv A) (snd (∷VecR' b))))
-- --      zz i g =
-- --       let g' : Maybe (Maybe (fst (RRec.f Fin₂R xs))) → Fin₂ (comm x y xs i)
-- --           g' qq = glue (λ { (i = i0) → qq
-- --                  ; (i = i1) → fst (swap0and1M ((RRec.f Fin₂R xs))) qq })
-- --                 (fst (swap0and1M ((RRec.f Fin₂R xs))) qq)
-- --       in glue (λ { (i = i0) → g nothing , g (just nothing)
-- --                                 , fst (snd b) (λ x₁ → g (just (just x₁)))
-- --                  ; (i = i1) → g nothing , (g (just nothing)
-- --                                 , fst (snd b) (λ x₁ → g _)) })
-- --                 (g (g' (just nothing)) , (g (g' nothing) ,
-- --                   fst (snd b) (g ∘ g' ∘ just ∘ just)))  
-- --   RElim.comm-inv* PermVecR x y {xs} b = 
-- --     sqTySingl≃ _ (λ i j → commInvVecRsq (fst b) i j)
-- --       (λ i j g →
-- --            sqA i j 
-- --             (ua-gluePath ((isoToEquiv (swapIso' (fst b))))
-- --             (λ i₁ → (g (sqF'-ju-no i j)) , (g (sqF'-no i j) ,
-- --                 fst (snd b) (g ∘ sqF'-ju-ju i j)))
-- --             i)
-- --             )
-- --           _ _ _ _

-- --     where 

-- --       sqAside : PathP (λ i → involPath {f = swap× (fst b)} (swapInvol (fst b)) i → A × A × fst b)
-- --                   (λ x₁ → x₁) (swap× (fst b))
-- --       sqAside i x = swap× (fst b) ((ua-unglue
-- --          (isoToEquiv (swapIso' (fst b))) i x))

-- --       sqA : InvolSym.Ty {f = swap× (fst b)} (swapInvol (fst b)) sqAside 
-- --       sqA i j x =
-- --         glue
-- --           (λ { (j = i0) → 
-- --               (swap× (fst b))
-- --                (ua-unglue ((isoToEquiv (swapIso' (fst b)))) i x)
-- --              ; (j = i1) → ua-unglue ((isoToEquiv (swapIso' (fst b)))) i x
               
-- --            })
-- --            ( ua-gluePath (isoToEquiv (swapIso' (fst b))) (λ _ → 
-- --               swap× (fst b)
-- --                (ua-unglue ((isoToEquiv (swapIso' (fst b)))) i x)) i)


-- --       sqF'-no : SquareP (λ i j → Fin₂ (comm-inv x y xs i j))
-- --                (ua-gluePath _ (λ i → just nothing))
-- --                (symP (ua-gluePath _ (λ i → nothing)))
-- --                (λ _ → nothing)
-- --                (λ _ → just nothing)
-- --       sqF'-no = isSet→SquareP
-- --           (λ i j → isSetFin₂ (comm-inv _ _ xs i j)) _ _ _ _

-- --       e = (swap0and1Mf (RRec.f Fin₂R xs) ,
-- --                               involIsEquiv (isInvolutionSwap0and1M (RRec.f Fin₂R xs)))

-- --       sqF'-ju-no : SquareP (λ i j → Fin₂ (comm-inv x y xs i j))
-- --                (ua-gluePath e (λ i → nothing))
-- --                (symP (ua-gluePath _ (λ i → just (nothing))))
-- --                (λ _ → just nothing)
-- --                (λ _ → nothing)
-- --       sqF'-ju-no = isSet→SquareP
-- --           (λ i j → isSetFin₂ (comm-inv _ _ xs i j)) _ _ _ _

-- --       sqF'-ju-ju : SquareP (λ i j → Fin₂ xs → Fin₂ (comm-inv x y xs i j))
-- --                (λ j x → ua-gluePath e {x = just (just x)} {just (just x)} (λ i → just (just x)) j)
-- --                (λ j x → ua-gluePath e {x = just (just x)} {just (just x)} (λ i → just (just x)) (~ j))
-- --                (λ _ x → just (just x))
-- --                (λ _ x → just (just x))
-- --       sqF'-ju-ju = isSet→SquareP
-- --           (λ i j → isSet→ (isSetFin₂ (comm-inv _ _ xs i j)))
-- --             (λ j x → ua-gluePath e {x = just (just x)} {just (just x)} (λ i → just (just x)) j)
-- --             (λ j x → ua-gluePath e {x = just (just x)} {just (just x)} (λ i → just (just x)) (~ j))
-- --                (λ _ x → just (just x))
-- --                (λ _ x → just (just x))



-- --   RElim.hexDiag* PermVecR = {!!}
-- --   RElim.hexU* PermVecR = {!!}
-- --   RElim.hexL* PermVecR = {!!}
-- --   RElim.trunc* PermVecR = {!!}


-- --   PermVec₂ : Perm₂  → Type ℓ
-- --   PermVec₂ = fst ∘ RElim.f PermVecR  


-- --   PermVec : ℕ → Type ℓ
-- --   PermVec = fst ∘ RElim.f PermVecR ∘ nPerm₂ 

-- --   -- fromList : {!!}
-- --   -- fromList = {!!}

-- --   -- ↔Ty : (x y : List A) → nPerm₂ (length x) ≡ nPerm₂ (length y) → Type ℓ
-- --   -- ↔Ty [] [] x₁ = Unit*
-- --   -- ↔Ty [] (x ∷ y) x₁ = ⊥.rec (znots (cong len2 x₁))
-- --   -- ↔Ty (x ∷ x₂) [] x₁ = ⊥.rec (snotz (cong len2 x₁))
-- --   -- ↔Ty (x ∷ x₂) (x₃ ∷ y) x₁ = {!!}


-- --   -- infix 4  _↔_

-- --   -- record _↔_ {ℓ} {A : Type ℓ} (x y : List A) : Type ℓ where
-- --   --   constructor prm
-- --   --   field
-- --   --     F≃ : (Fin (length x) ≃ Fin (length y))
-- --   --     l≡ : ∀ k → lookup x k ≡ lookup y (equivFun F≃ k)

-- --   -- open _↔_


-- --   -- toVecΣ : RElim {A = A} (λ z → PermVec₂ (toPerm₂ z))
-- --   -- RElim.[]* toVecΣ = tt*
-- --   -- (toVecΣ RElim.∷* x) = x ,_
-- --   -- RElim.comm* toVecΣ x y {xs} b =
-- --   --   ua-gluePath _ refl
-- --   -- RElim.comm-inv* toVecΣ x y b _ = {!!}
-- --   -- RElim.hexDiag* toVecΣ = {!!}
-- --   -- RElim.hexU* toVecΣ = {!!}
-- --   -- RElim.hexL* toVecΣ = {!!}
-- --   -- RElim.trunc* toVecΣ = {!!}

-- -- -- -- --   VecMb : ℕ → Type ℓ
-- -- -- -- --   VecMb n = iter n (A ×_) Unit*


-- -- -- -- --   Vec≡ : ∀ n → (VecMb n) ≡ (PermVec n)
-- -- -- -- --   Vec≡ zero = refl
-- -- -- -- --   Vec≡ (suc n) = cong′ (A ×_) (Vec≡ n) 

-- -- -- -- --   VecIso : ∀ n → Iso (VecMb n) (PermVec n)
-- -- -- -- --   VecIso zero = idIso 
-- -- -- -- --   VecIso (suc n) = prodIso idIso (VecIso n)

-- -- -- -- --   _≡ℕ_ : ℕ → ℕ → Type
-- -- -- -- --   zero ≡ℕ zero = Unit
-- -- -- -- --   zero ≡ℕ suc x₁ = ⊥.⊥
-- -- -- -- --   suc x ≡ℕ zero = ⊥.⊥
-- -- -- -- --   suc x ≡ℕ suc x₁ = x ≡ℕ x₁

-- -- -- -- --   ListOfLen : ∀ n → Iso (Σ (List A) λ l → length l ≡ℕ n) (PermVec n)
-- -- -- -- --   ListOfLen zero = w
-- -- -- -- --     where
-- -- -- -- --       w : Iso (Σ (List A) (λ l → length l ≡ℕ zero)) (PermVec zero)
-- -- -- -- --       Iso.fun w _ = _
-- -- -- -- --       Iso.inv w _ = [] , _
-- -- -- -- --       Iso.rightInv w _ = refl
-- -- -- -- --       Iso.leftInv w ([] , snd₁) = refl
      
  
-- -- -- -- --   ListOfLen (suc n) = w
-- -- -- -- --     where
-- -- -- -- --       w : Iso (Σ (List A) (λ l → length l ≡ℕ suc n)) (PermVec (suc n))
-- -- -- -- --       Iso.fun w (x ∷ xs , p) =
-- -- -- -- --         x , Iso.fun (ListOfLen n) (xs , p) 
-- -- -- -- --       Iso.inv w (x , f) =
-- -- -- -- --         let (xs , p)  = Iso.inv (ListOfLen n) f
-- -- -- -- --         in (x ∷ xs , p)
-- -- -- -- --       Iso.rightInv w (x , f) =
-- -- -- -- --         cong (x ,_) (Iso.rightInv (ListOfLen n) f)
-- -- -- -- --       Iso.leftInv w (x ∷ xs , p) =
-- -- -- -- --         cong (λ (xs , p) → x ∷ xs , p)
-- -- -- -- --              (Iso.leftInv (ListOfLen n) (xs , p))




-- -- -- -- -- -- FMI : FMSet2 A → hSet ℓ-zero
-- -- -- -- -- -- FMI =
-- -- -- -- -- --   Elim.f 
-- -- -- -- -- --    (⊥.⊥ , isProp→isSet isProp⊥)
-- -- -- -- -- --    (λ x {xs} b → Maybe (fst b) , isOfHLevelMaybe zero (snd b) )
-- -- -- -- -- --    (λ x y b → TypeOfHLevel≡ 2 (ua (swap0and1M b)))
-- -- -- -- -- --    (λ x y {xs} b →
-- -- -- -- -- --       ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- --         (cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
-- -- -- -- -- --           ∙ uaInvEquiv (swap0and1M b)) )
-- -- -- -- -- --    (λ x y z b → TypeOfHLevel≡ 2 (ua (swap0and2M b)))
-- -- -- -- -- --    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- --                       (∙≡∙→square _ _ _ _
-- -- -- -- -- --                        (isInjectiveTransport
-- -- -- -- -- --                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))


-- -- -- -- -- --    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- --                       (∙≡∙→square _ _ _ _
-- -- -- -- -- --                        (isInjectiveTransport
-- -- -- -- -- --                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))
-- -- -- -- -- --    (λ _ → isGroupoidHSet)



