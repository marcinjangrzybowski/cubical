{-# OPTIONS --cubical  #-}
module Cubical.HITs.NCube.Internalize where


open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum as Sum

open import Cubical.HITs.Interval
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint


open import Cubical.HITs.NCube.IntervalPrim
open import Cubical.HITs.NCube.Cub

open import Cubical.HITs.NCube.BaseVec



data Skel' : (n : ℕ) → (m : ℕ) → Type₀ where
   holeS : ∀ {n m} → Skel' n m 
   compS : ∀ {n m} → (ptBnd : PartialBoundary n) →
                ((ft : PartialBoundaryAtom ptBnd) → Skel' (suc (toℕ (fctDim (fst ft)))) m) 
                → Skel' n m  → Skel' n (suc m)

Skel'-subst : ∀ {n k m} → n ≡ k →  Skel' n m  → Skel' k m
Skel'-subst = subst (λ n → Skel' n _)

skel'-rise : ∀ {n m} → Skel' n m → Skel' n (suc m)
skel'-rise holeS = holeS
skel'-rise (compS ptBnd x x₁) =
   compS ptBnd (skel'-rise ∘ x) (skel'-rise x₁)

skelFace : ∀ {n m} → Skel' n m → (sf : SubFace n)  → Skel' (toℕ (sfDim sf)) m

skelEnd : ∀ {n m} → Skel' (suc n) m → Skel' (n) m
skelEnd x = Skel'-subst sfDim-repeat (skelFace x (just true ∷ repeat nothing))




postulate law1 : ∀ {n} → (ptBnd : PartialBoundary n)
           →  (ft : BdFacet n) →  (ft₁ : _) → (x₃ : fst ptBnd ft ≡ false)
             → toℕ (sfDim ((nothing ∷ (fctProjSF _ _ (snd (atomInj {pb = ptBnd} ft x₃ ft₁))))))
              ≡ suc (toℕ (fctDim (fst ft₁)))
-- law1 = {!!}

postulate trustMe : (n₁ n₂ : ℕ) →  n₁ ≡ n₂

skelFace {m = m} holeS _ = holeS
skelFace {n = n} {m = .(suc _)} (compS ptBnd x x₁) sf  with (sfCase sf)
... | inl x₂ = Skel'-subst (sym x₂) ((compS ptBnd  x x₁))
... | inr (ft , x₂) with (isPba? ptBnd ft)
... | yes p = skel'-rise
        (Skel'-subst (sym (sfDim=ftDim ft) ∙ cong (toℕ ∘ sfDim) x₂)
         (skelEnd (x (ft , p))))
... | no ¬p with notAtomCases ptBnd ft ¬p

... | inl x₃ = 
   let z : (ft₁ : PartialBoundaryAtom (partialBoundaryProj ptBnd ft)) → _ 
       z = λ ft₁ →
           let (a' , xx) = atomInj {pb = ptBnd} ft x₃ ft₁
           in skelFace {n = _} {m = _} (x a')
               (nothing ∷ (fctProjSF _ _ xx))
   in Skel'-subst ((sym (sfDim=ftDim ft) ∙ cong (toℕ ∘ sfDim) x₂)) (
       (compS (partialBoundaryProj ptBnd ft)
      (λ a → Skel'-subst (law1 ptBnd ft a x₃) (z a))
      (Skel'-subst ((sym (cong (toℕ ∘ sfDim) x₂)) ∙ (sfDim=ftDim ft)) (skelFace x₁ sf ))
      ))
... | inr (=t , a , ft-⊂-fst-a) =
      skel'-rise (Skel'-subst (
            trustMe _ _
            ∙ cong (fst ∘ sfDim) x₂ )
       (skelFace (x a) (bdInj (fctProj (fst a) ft (fst ft-⊂-fst-a)))))



fullSkel' : ∀ n m → Skel' n m
fullSkel' n zero = holeS
fullSkel' n (suc m) = compS (full n)
                           (λ ft → fullSkel' (suc (toℕ (fctDim (fst ft)))) m)
                           (fullSkel' _ _)


FcEnc : ∀ {n} → (x : BdFacet n)  → NCube (toℕ (fctDim x)) → NCube n
FcEnc (lid n x) x₁ = end x ∷ x₁
FcEnc (cyl n nothing x₂) (x ∷ x₁) = x ∷ FcEnc x₂ x₁
FcEnc (cyl n (just x) x₂) x₁ = end x ∷ FcEnc x₂ x₁

PbEnc : ∀ {n} → PartialBoundary n → NCube n → Interval'
PbEnc = {!!}

enc : ∀ {ℓ} → {A : Type ℓ} → A
           → (n : ℕ)
           → (PartialBoundary n)
           → NCube n → A
enc {A = A} a n pb c = hcomp' {A = A} (PbEnc pb c) λ _ → a 

enc' : ∀ {ℓ} → {A : Type ℓ} → A
           → (n : ℕ)
           → NCube n → A
enc' {A = A} a n c = hcomp' {A = A} (brd c) λ _ → a 


encTest : ∀ {ℓ} → {A : Type ℓ} → (a : A) → Square {!!} {!!} {!!} {!!}
encTest a =  (insideOf (enc' a 2))

encTest' : ∀ {ℓ} → {A : Type ℓ} → (a : A) → ℕ → Σ (Type ℓ) λ x → x
encTest' a zero = _ , a
encTest' a (suc n) = _ , insideOf {n = n} (enc' {!!} n)


encTest1 : ∀ {ℓ} → {A : Type ℓ} → (a : A) → {!!}
encTest1 a = {!encTest a!}


-- FcEnc : ∀ {n} → BdFacet n → NCube n → Interval'
-- FcEnc (lid n x) (x₁ ∷ x₂) = end x
-- FcEnc (cyl n nothing x₁) (x₂ ∷ x₃) = FcEnc x₁ x₃
-- FcEnc (cyl n (just x) x₁) (x₂ ∷ x₃) = end x ∧' (FcEnc x₁ x₃)

-- data FExpr : Type₀ where
--   iv : ℕ → FExpr
--   _∨'_ : FExpr → FExpr → FExpr
--   ~' : FExpr → FExpr



-- data Code : Type₀ where
--   hcomp' : Code
    


-- reflCode : ∀ {ℓ} → {A : Type ℓ} → A
--            → (n : ℕ) → ∀ m
--            → (Skel' n m)
--            → A
-- reflCode a n m holeS = a
-- reflCode a n .(suc _) (compS ptBnd x₁ x₃) = {!!}




-- -- data Skel {ℓ} (A : Type ℓ) (n : ℕ) : Type ℓ where
-- --    holeS : A → Skel A n 
-- --    compS : Vec (Skel A n) (2^ n) → Skel A n → Skel A n
