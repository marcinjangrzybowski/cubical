{-# OPTIONS --safe  #-} 
module Cubical.HITs.ListedFiniteSet.Base22 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sigma

open import Cubical.Data.FinData.Transpositions

-- open import Cubical.Functions.Logic
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.Function
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Foundations.Univalence


open import Cubical.HITs.EilenbergMacLane1

-- open import Cubical.Data.FinData

open import Cubical.Data.Nat.Order.Recursive

import Cubical.Data.SumFin as F


open import Cubical.HITs.ListedFiniteSet.Base2

-- open import Cubical.Data.FinData.GTrun

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.GroupoidTruncation as GT
open import Cubical.HITs.SetTruncation as ST


open import Cubical.Functions.Involution

open import Cubical.Homotopy.EilenbergMacLane.Properties

open import Cubical.Data.FinSet


open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.SymmetricGroup
open import Cubical.Algebra.Group.Generators

private
  variable
    ℓ : Level
    A B : Type ℓ

-- module LockTest where

--   IsoUnitlockUnit : Iso Unit (lockUnit {ℓ-zero}) 
--   Iso.fun IsoUnitlockUnit _ = unlock
--   Iso.inv IsoUnitlockUnit _ = _
--   Iso.rightInv IsoUnitlockUnit unlock = refl
--   Iso.leftInv IsoUnitlockUnit _ = refl

--   UnitlockUnit≃ : Unit ≃ (lockUnit {ℓ-zero}) 
--   UnitlockUnit≃ = isoToEquiv IsoUnitlockUnit

--   UnitlockUnit≡ : Unit ≡ (lockUnit {ℓ-zero}) 
--   UnitlockUnit≡ = ua (UnitlockUnit≃)


--   lock : {!!}
--   lock = {!!}

--   lockPlus : lockUnit {ℓ-zero} → ℕ → ℕ → ℕ
--   lockPlus unlock n m = n + m

--   UnlockI1 : (b0 b1 : lockUnit {ℓ-zero} → A) → Type
--   UnlockI1 b0 b1 = {!!}

--   zz : {!!}
--   zz = {!lockPlus (transport UnitlockUnit≡ _) 2 3!}

congSq : ∀ {ℓ} {A B : Type ℓ} → {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} (f : A → B)
  → Square (a₀₋) (a₁₋) (a₋₀) (a₋₁)
  → Square (cong f a₀₋) (cong f a₁₋) (cong f a₋₀) (cong f a₋₁)
congSq {a₀₋ = a₀₋} {a₁₋ = a₁₋} {a₋₀ = a₋₀} {a₋₁ = a₋₁}  f sq i j = f (sq i j)
{-# INLINE congSq #-}

-- lemSucUA : ∀ {n} → (e : Fin n ≃ Fin n) → ua (sucPerm e) ≡
--                       {!ua e!} 
-- lemSucUA = {!!}

Mb^ : ℕ → (hSet ℓ-zero) → (hSet ℓ-zero) 
Mb^ zero x₁ = x₁
Mb^ (suc x) b' =
  let b = Mb^ x b'
  in Maybe (fst b) , isOfHLevelMaybe zero (snd b)


swap0and1Mf : (b : hSet ℓ-zero) → fst (Mb^ 2 b) → fst (Mb^ 2 b)  
swap0and1Mf b nothing = just nothing
swap0and1Mf b (just nothing) = nothing
swap0and1Mf b (just (just x)) = (just (just x))

involSwap0and1Mf : ∀ b → isInvolution (swap0and1Mf b)
involSwap0and1Mf b nothing = refl
involSwap0and1Mf b (just nothing) = refl
involSwap0and1Mf b (just (just x)) = refl

swap0and1M : (b : hSet ℓ-zero) → fst (Mb^ 2 b) ≃ fst (Mb^ 2 b)  
swap0and1M b = involEquiv {f = swap0and1Mf b} (involSwap0and1Mf b)

swap0and2Mf : (b : hSet ℓ-zero) → fst (Mb^ 3 b) → fst (Mb^ 3 b)  
swap0and2Mf b nothing = (just (just nothing))
swap0and2Mf b (just nothing) = just nothing
swap0and2Mf b (just (just nothing)) = nothing
swap0and2Mf b (just (just (just x))) = (just (just (just x)))

involSwap0and2Mf : ∀ b → isInvolution (swap0and2Mf b)
involSwap0and2Mf b nothing = refl
involSwap0and2Mf b (just nothing) = refl
involSwap0and2Mf b (just (just nothing)) = refl
involSwap0and2Mf b (just (just (just x))) = refl

swap0and2M : (b : hSet ℓ-zero) → fst (Mb^ 3 b) ≃ fst (Mb^ 3 b)  
swap0and2M b = involEquiv {f = swap0and2Mf b} (involSwap0and2Mf b)

-- congMUA : (b : hSet ℓ-zero) →
--              cong Maybe (ua (swap0and1M b)) ≡
--               ua (congMaybeEquiv (swap0and1M b)) 
-- congMUA b = {!!}
-- isInjectiveTransport
--   (funExt (Mb.elim _ refl λ _ → refl))

Rh𝔽in : RRec {A = A} (isGroupoidHSet {ℓ = ℓ-zero})
RRec.[]* Rh𝔽in = ⊥.⊥ , isProp→isSet isProp⊥
(Rh𝔽in RRec.∷* _) b =  Maybe (fst b) , isOfHLevelMaybe zero (snd b) 
RRec.comm* Rh𝔽in _ _ b = TypeOfHLevel≡ 2 (ua (swap0and1M b))
RRec.comm-inv* Rh𝔽in _ _ b =
  ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
   (involPathSym _)
RRec.hexDiag* Rh𝔽in _ _ _ b = TypeOfHLevel≡ 2 (ua (swap0and2M b))
RRec.hexU* Rh𝔽in _ _ _ b =
  ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
    (∙≡∙→square _ _ _ _
           (isInjectiveTransport
            (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl))))))
RRec.hexL* Rh𝔽in _ _ _ b =
  ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
    (∙≡∙→square _ _ _ _
           (isInjectiveTransport
            (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl))))))



rep : A → ℕ → FMSet2 A
rep a zero = []
rep a (suc n) = a ∷2 rep a n

h𝔽in : FMSet2 A → hSet ℓ-zero
h𝔽in = RRec.f Rh𝔽in

𝔽in : FMSet2 A → Type
𝔽in = fst ∘ h𝔽in

𝔽in∘rep→Fin : ∀ n (a : A) → 𝔽in (rep a n) → Fin n
𝔽in∘rep→Fin (suc n) a nothing = zero , _
𝔽in∘rep→Fin (suc n) a (just x) = sucF (𝔽in∘rep→Fin n a x)

Fin→𝔽in∘rep : ∀ n (a : A) → Fin n → 𝔽in (rep a n)
Fin→𝔽in∘rep (suc n) a (zero , k<) = nothing
Fin→𝔽in∘rep (suc n) a (suc k , k<) = just (Fin→𝔽in∘rep n a (k , k<))

IsoFin𝔽in∘rep : ∀ n (a : A) → Iso (Fin n) (𝔽in (rep a n))
Iso.fun (IsoFin𝔽in∘rep n a) = Fin→𝔽in∘rep n a
Iso.inv (IsoFin𝔽in∘rep n a) = 𝔽in∘rep→Fin n a
Iso.rightInv (IsoFin𝔽in∘rep (suc n) a) nothing = refl
Iso.rightInv (IsoFin𝔽in∘rep (suc n) a) (just x) =
 cong just (Iso.rightInv (IsoFin𝔽in∘rep n a) x)
Iso.leftInv (IsoFin𝔽in∘rep (suc n) a) (zero , k<) = refl
Iso.leftInv (IsoFin𝔽in∘rep (suc n) a) (suc k , k<) =
  ≡Fin {n = suc n}
   (cong (suc ∘ fst) (Iso.leftInv (IsoFin𝔽in∘rep n a) (k , k<)))


𝔽→ : ∀ (A : Type ℓ) → ℕ → Type ℓ
𝔽→ A n = 𝔽in (rep tt n) → A

Σ𝔽→ : ∀ (A : Type ℓ) → Type ℓ
Σ𝔽→ A = Σ _ (𝔽→ A)

module _ {ℓ'} {B : Type ℓ'} {A : Type ℓ} (xs : FMSet2 B) where

 swap01coh : (y : Maybe (Maybe (fst (h𝔽in xs)))) →
      Square
      (λ j →
         swap0and1Mf (h𝔽in xs)
         (involSwap0and1Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs))
          (swap0and1Mf (h𝔽in xs) y) j))
      (λ j →
         involSwap0and1Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs)) y
         (~ j))
      (λ i →
         involSwap0and1Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs))
         (involSwap0and1Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs)) y
          i)
         i)
      (λ i → swap0and1Mf (h𝔽in xs) (swap0and1Mf (h𝔽in xs) y))
 swap01coh nothing = refl
 swap01coh (just nothing) = refl
 swap01coh (just (just x)) = refl

 module PCI = preCompInvol {f = swap0and1Mf (h𝔽in xs)} A 
   (involSwap0and1Mf _) swap01coh

 swap02coh : (y : Maybe (Maybe (Maybe (fst (h𝔽in xs))))) →
      Square
      (λ j →
         swap0and2Mf (h𝔽in xs)
         (involSwap0and2Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs))
          (swap0and2Mf (h𝔽in xs) y) j))
      (λ j →
         involSwap0and2Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs)) y
         (~ j))
      (λ i →
         involSwap0and2Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs))
         (involSwap0and2Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs)) y
          i)
         i)
      (λ i → swap0and2Mf (h𝔽in xs) (swap0and2Mf (h𝔽in xs) y))
 swap02coh nothing = refl
 swap02coh (just nothing) = refl
 swap02coh (just (just nothing)) = refl
 swap02coh (just (just (just x))) = refl

 module PCI' = preCompInvol {f = swap0and2Mf (h𝔽in xs)} A 
   (involSwap0and2Mf _) swap02coh


singlTy : (A : Type ℓ) → Type (ℓ-suc ℓ)
singlTy {ℓ} A = Σ (Σ (Type ℓ) λ T → A → T) (isEquiv ∘ snd)

isContr-singlTy : (A : Type ℓ) → isContr (singlTy A)
isContr-singlTy A = isOfHLevelRespectEquiv 0
  ((Σ-cong-equiv-snd λ _ → invEquivEquiv)  ∙ₑ invEquiv Σ-assoc-≃)
     (EquivContr A) 

Rh𝔽in→ : ∀ {ℓ'} {B : Type ℓ'} → RElim {A = B}
    (λ xs → singlTy (𝔽in xs → A))
RElim.[]* Rh𝔽in→ = (_ , idfun _) , idIsEquiv _
(Rh𝔽in→ RElim.∷* _) _ = (_ , idfun _) , idIsEquiv _
RElim.comm* (Rh𝔽in→ {A = A} {B = B}) _ _ {xs} b = 
 ΣPathPProp (isPropIsEquiv ∘ snd)
  (ΣPathP (PCI.p' {B = B} {A = A} xs , PCI.eq≃ {B = B} {A = A} xs))
RElim.comm-inv* (Rh𝔽in→ {A = A} {B = B}) x y {xs} b =
 ΣSquarePSet (λ _ _ → isProp→isSet ∘ isPropIsEquiv ∘ snd) _ _ _ _
   λ i j → PCI.pS' {B = B} {A = A} xs i j ,
     PCI.eq≃Sym {B = B} {A = A} xs i j

RElim.hexDiag* (Rh𝔽in→ {A = A} {B = B}) _ _ _ {xs} b = 
   ΣPathPProp (isPropIsEquiv ∘ snd)
    (ΣPathP (_ , PCI'.eq≃ {B = B} {A = A} xs))
RElim.hexU* Rh𝔽in→ = {!!}
RElim.hexL* Rh𝔽in→ = {!!}
RElim.trunc* Rh𝔽in→ xs =
  isOfHLevelPlus {n = 0} 3 (isContr-singlTy (𝔽in xs → _))

Rh𝔽in→* : ∀ {ℓ'} {B : Type ℓ'} → RElim {A = B}
    (λ xs → singlTy (𝔽in xs → A))
RElim.[]* Rh𝔽in→* = (_ , idfun _) , idIsEquiv _
(Rh𝔽in→* RElim.∷* _) _ = (_ , idfun _) , idIsEquiv _
RElim.comm* (Rh𝔽in→* {A = A} {B = B}) _ _ {xs} b = {!!}
 ΣPathPProp (isPropIsEquiv ∘ snd)
  (ΣPathP (PCI.p' {B = B} {A = A} xs , PCI.eq≃ {B = B} {A = A} xs))
RElim.comm-inv* (Rh𝔽in→* {A = A} {B = B}) x y {xs} b = {!!}
 -- ΣSquarePSet (λ _ _ → isProp→isSet ∘ isPropIsEquiv ∘ snd) _ _ _ _
 --   λ i j → PCI.pS' {B = B} {A = A} xs i j ,
 --     PCI.eq≃Sym {B = B} {A = A} xs i j

RElim.hexDiag* (Rh𝔽in→* {A = A} {B = B}) _ _ _ {xs} b = {!!} 
   -- ΣPathPProp (isPropIsEquiv ∘ snd)
   --  (ΣPathP (_ , PCI'.eq≃ {B = B} {A = A} xs))
RElim.hexU* Rh𝔽in→* = {!!}
RElim.hexL* Rh𝔽in→* = {!!}
RElim.trunc* Rh𝔽in→* xs =
  isOfHLevelPlus {n = 0} 3 (isContr-singlTy (𝔽in xs → _))





-- -- Rh𝔽in→ : ∀ {ℓ'} {B : Type ℓ'} → RElim {A = B} (λ xs → singl (𝔽in xs → A))
-- -- RElim.[]* Rh𝔽in→ = _ , refl
-- -- (Rh𝔽in→ RElim.∷* _) _ = _ , refl 
-- -- RElim.comm* Rh𝔽in→ _ _ {xs} _ = ΣPathP (_ , flipSquareP (PCI.eq xs))
-- -- fst (RElim.comm-inv* (Rh𝔽in→ {A = A}) x y {xs} b i j) =
-- --   involPathSym {A = Maybe (Maybe (𝔽in xs)) → A}
-- --     {f = _∘ (swap0and1Mf (h𝔽in xs))} (PCI.∘invol xs ) i j
   
-- -- snd (RElim.comm-inv* Rh𝔽in→ x y {xs} b i j) = {!!}
-- -- RElim.hexDiag* Rh𝔽in→ _ _ _ {xs} _ = ΣPathP (_ , flipSquareP (PCI'.eq xs))
-- -- RElim.hexU* Rh𝔽in→ = {!!}
-- -- RElim.hexL* Rh𝔽in→ = {!!}
-- -- RElim.trunc* Rh𝔽in→ = {!!}

-- 𝔽in→ : ∀ {ℓ'} {B : Type ℓ'} → Type ℓ → (FMSet2 B → Type ℓ)
-- 𝔽in→ A = fst ∘ fst ∘ RElim.f (Rh𝔽in→ {A = A})

-- 𝔽in→ev : ∀ {ℓ'} {B : Type ℓ'} → (A : Type ℓ) →
--            (∀ xs → (𝔽in {A = B} xs → A) → 𝔽in→ A xs)
-- 𝔽in→ev A = snd ∘ fst ∘ RElim.f (Rh𝔽in→ {A = A})

-- 𝔽in→ev≃ : ∀ {ℓ'} {B : Type ℓ'} → (A : Type ℓ) →
--            (∀ xs → (𝔽in {A = B} xs → A) ≃ 𝔽in→ A xs)
-- 𝔽in→ev≃ A xs = _  , snd ((RElim.f (Rh𝔽in→ {A = A}) xs))


-- 𝔽in→ev⁻-comm-unglue : (a a' : A) → ∀ xs →
--       PathP
--       (λ i → 𝔽in→ A (comm a a' xs i) → Maybe (Maybe (fst (h𝔽in xs))) → A )
--       (_∘ (swap0and1Mf (h𝔽in xs)))
--       (idfun _)
-- 𝔽in→ev⁻-comm-unglue a a' xs i x = unglue (i ∨ ~ i) x

-- 𝔽in→ev⁻-comm-unglue' : (a a' : A) → ∀ xs →
--       PathP
--       (λ i → (Maybe (Maybe (fst (h𝔽in xs))) → A) → 𝔽in (comm a a' xs i) → A)
--       (_∘ (swap0and1Mf (h𝔽in xs)))
--       (idfun _)
-- 𝔽in→ev⁻-comm-unglue' a a' xs i x y =
--   x (unglue (i ∨ ~ i) y)

-- -- 𝔽in→ev⁻-comm : (a a' : A) → ∀ xs →
-- --       PathP
-- --       (λ i → 𝔽in→ A (comm a a' xs i) → 𝔽in (comm a a' xs i) → A)
-- --       (λ x₁ → x₁) (λ x₁ → x₁)
-- -- 𝔽in→ev⁻-comm a a' xs i x y =
-- --   {!!}


-- -- 𝔽in→ev⁻-commE : (a a' : A) → ∀ xs →
-- --       ∀ i → (x : 𝔽in→ A (comm a a' xs i)) →
-- --          (k : 𝔽in (comm a a' xs i)) → {!!}
-- --       -- PathP
-- --       -- (λ i → 𝔽in→ A (comm a a' xs i) → 𝔽in (comm a a' xs i) → A)
-- --       -- (λ x₁ → x₁) (λ x₁ → x₁)
-- -- 𝔽in→ev⁻-commE a a' xs i x y = RElimSet.f w
-- --  where
-- --  w : RElimSet
-- --        (λ z →
-- --           PathP (λ i → 𝔽in→ _ (comm a a' z i) → 𝔽in (comm a a' z i) → _)
-- --           (λ x₁ → x₁) (λ x₁ → x₁))
-- --  RElimSet.[]* w i x x₁ = {!!}
-- --  RElimSet._∷*_ w = {!!}
-- --  RElimSet.comm* w = {!!}
-- --  RElimSet.hexDiag* w = {!!}
-- --  RElimSet.trunc* w = {!!}

-- -- 𝔽in→ev⁻ : ∀ {ℓ'} {B : Type ℓ'} → (A : Type ℓ) →
-- --            (∀ xs → 𝔽in→ A xs → (𝔽in {A = B} xs → A))
-- -- 𝔽in→ev⁻ {B = B} A = w
-- --  where
-- --  w : (xs : FMSet2 B) → 𝔽in→ A xs → 𝔽in xs → A
-- --  w (x₁ ∷2 xs) x y = x y
-- --  w (comm b b' xs i) x y = {!!}
-- --  w (comm-inv x₁ y₁ xs i i₁) x y = {!!}
-- --  w (hexDiag x₁ y₁ z xs i) x y = {!!}
-- --  w (hexU x₁ y₁ z xs i i₁) x y = {!!}
-- --  w (hexL x₁ y₁ z xs i i₁) x y = {!!}
-- --  w (trunc xs xs₁ x₁ y₁ x₂ y₂ i i₁ x₃) x y = {!!}
 
-- 𝔽in→ev⁻ : ∀ {ℓ'} {B : Type ℓ'} → (A : Type ℓ) →
--            (∀ xs → 𝔽in→ A xs → (𝔽in {A = B} xs → A))
-- 𝔽in→ev⁻ A = RElim.f w
--  where

--  w : RElim (λ z → 𝔽in→ A z → 𝔽in z → A)
--  RElim.[]* w = idfun _
--  (w RElim.∷* a) b x = x
--  -- (w RElim.∷* a) b x nothing = x nothing
--  -- (w RElim.∷* a) b x (just x₁) = {!b (x ∘ just)!}
--  -- RElim.comm* w _ _ {xs} b i x y = {!!}
--  RElim.comm* w _ _ {xs} b =
--    funExt₂ (λ x y → cong x (sym (involSwap0and1Mf _ y)))
--      ◁ λ i x → unglue (i ∨ ~ i) x ∘ (unglue (i ∨ ~ i)) 
--  RElim.comm-inv* w x y {xs} b = {!!}
--  RElim.hexDiag* w = {!!}
--  RElim.hexU* w = {!!}
--  RElim.hexL* w = {!!}
--  RElim.trunc* w = {!!}

-- -- -- -- -- 𝔽in→Eval : ∀ {ℓ'} {B : Type ℓ'} → ∀ xs → 𝔽in→ {B = B} A xs → 𝔽in xs → A
-- -- -- -- -- 𝔽in→Eval {A = A} {B = B} = RElim.f w
-- -- -- -- --  where
-- -- -- -- --  open RElim
 
-- -- -- -- --  w : RElim (λ z → 𝔽in→ _ z → 𝔽in z → _)
-- -- -- -- --  []* w x ()
-- -- -- -- --  (w ∷* x) X b = Mb.rec {!!}  {!!}
-- -- -- -- --  comm* w = {!!}
-- -- -- -- --  comm-inv* w = {!!}
-- -- -- -- --  hexDiag* w = {!!}
-- -- -- -- --  hexU* w = {!!}
-- -- -- -- --  hexL* w = {!!}
-- -- -- -- --  trunc* w = {!!}


-- -- -- module fm2Look {ℓ'} {B : Type ℓ'} (mapF : A → B) (isGroupoidA : isGroupoid A)  where

-- -- --  swap-lem : ∀ (xs : FMSet2 B) (a a' : A)
-- -- --               (f : 𝔽in {A = B} xs → A) →
-- -- --                Mb.rec a (Mb.rec a' f) ∘ (swap0and1Mf (h𝔽in xs)) ≡
-- -- --                 Mb.rec a' (Mb.rec a f)
-- -- --  swap-lem xs a a' f i nothing = a'
-- -- --  swap-lem xs a a' f i (just nothing) = a
-- -- --  swap-lem xs a a' f i (just (just x)) = f x

-- -- --  comm*-P : ∀ (a a' : A) (xs : FMSet2 A)  → (f : 𝔽in (fm2Map mapF xs) → A) →
-- -- --         PathP (λ i → 𝔽in→ A (fm2Map mapF (comm a a' xs i)))
-- -- --           (Mb.rec a (Mb.rec a' f))
-- -- --           (Mb.rec a' (Mb.rec a f))
-- -- --  comm*-P  a a' xs f = ua-gluePath _ (swap-lem (fm2Map mapF xs) a a' f) 


-- -- --  comm*-P-invo-glueSq : (a a' : A) (xs : FMSet2 A) (b : 𝔽in (fm2Map mapF xs) → A) → Square
-- -- --         (λ j → swap-lem (fm2Map mapF xs) a a' b j ∘ swap0and1Mf (h𝔽in (fm2Map mapF xs)))
-- -- --         (λ j → swap-lem (fm2Map mapF xs) a' a b (~ j))
-- -- --         (λ i y → Mb.rec a (Mb.rec a' b) (involSwap0and1Mf (h𝔽in (fm2Map mapF xs)) y i))
-- -- --         refl
-- -- --  comm*-P-invo-glueSq a a' xs b i j nothing = a
-- -- --  comm*-P-invo-glueSq a a' xs b i j (just nothing) = a'
-- -- --  comm*-P-invo-glueSq a a' xs b i j (just (just x)) = b x


-- -- --  comm*-P-invo : ∀ (a a' : A) (xs : FMSet2 A) (b : 𝔽in (fm2Map mapF xs) → A) →
-- -- --        SquareP (λ i j → PCI.pS' {B = B} {A = A} (fm2Map mapF xs) i j)
-- -- --        (comm*-P a a' xs b)
-- -- --        (symP (comm*-P a' a xs b))
-- -- --        (refl {x = Mb.rec a (Mb.rec a' b)})
-- -- --        (refl {x = Mb.rec a' (Mb.rec a b)})
-- -- --  comm*-P-invo a a' xs b i j = 
-- -- --         glue 
-- -- --           (λ { (j = i0) → Mb.rec a (Mb.rec a' b)
-- -- --              ; (j = i1) → Mb.rec a' (Mb.rec a b)
-- -- --            }) (glue
-- -- --      (λ { (i = i0) → swap-lem (fm2Map mapF xs) a a' b j
-- -- --         ; (i = i1) → swap-lem (fm2Map mapF xs) a' a b (~ j)
-- -- --         })
-- -- --      (comm*-P-invo-glueSq a a' xs b i j))


-- -- --  RFM2look' : RElim {A = A} (𝔽in→ A ∘ fm2Map mapF)
-- -- --  RElim.[]* RFM2look' ()
-- -- --  (RFM2look' RElim.∷* a) {xs} f =
-- -- --    Mb.rec a (invEq (𝔽in→ev≃ A (fm2Map mapF xs)) f)
-- -- --  RElim.comm* (RFM2look') a a' {xs} b = 
-- -- --    comm*-P _ _ xs (invEq (𝔽in→ev≃ A ((fm2Map mapF xs))) b)
-- -- --  RElim.comm-inv* (RFM2look') a a' {xs} b = 
-- -- --    comm*-P-invo a a' xs (invEq (𝔽in→ev≃ A (fm2Map mapF xs)) b) 
-- -- --  RElim.hexDiag* RFM2look' _ _ _ b = 
-- -- --    ua-gluePath _
-- -- --    (funExt (Mb.elim _ refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl))))
-- -- --  RElim.hexU* RFM2look' = {!!}
-- -- --  RElim.hexL* RFM2look' = {!!}
-- -- --  RElim.trunc* RFM2look' xs =
-- -- --   isOfHLevelRespectEquiv 3
-- -- --     (𝔽in→ev≃ A (fm2Map mapF xs))
-- -- --      (isGroupoidΠ λ _ → isGroupoidA)

-- -- --  fm2look : (xs : FMSet2 A) → (𝔽in→ A ∘ fm2Map mapF) xs
-- -- --  fm2look = RElim.f RFM2look'

-- -- -- RFM2tab : ∀ {ℓ'} {B : Type ℓ'} →
-- -- --    RElim {A = B} (λ xs → (𝔽in xs → A) → FMSet2 A)
-- -- -- RElim.[]* RFM2tab _ = []
-- -- -- (RFM2tab RElim.∷* _) b f = f nothing ∷2 b (f ∘ just)
-- -- -- RElim.comm* (RFM2tab {A = A} {B = B}) _ _ {xs} b i f = 
-- -- --  let z = f ∘' ua-gluePathExt (PCI.e {B = B} {A = A} xs) i
-- -- --  in comm (z nothing) (z (just nothing)) (b (z ∘ just ∘ just)) i
-- -- -- RElim.comm-inv* (RFM2tab {A = A}) _ _ {xs} b i j f =
-- -- --  let z : Maybe (Maybe (𝔽in xs)) → A
-- -- --      z = f ∘' λ x → glue
-- -- --              (λ { (j = i0) → x
-- -- --                 ; (j = i1) → swap0and1Mf (h𝔽in xs) x })
-- -- --                  (glue (λ { (i = i0) → swap0and1Mf (h𝔽in xs) x
-- -- --                           ; (i = i1) → _ })
-- -- --                  (involSwap0and1Mf (RRec.f Rh𝔽in xs) x (~ j ∧ i)))
-- -- --  in comm-inv (z nothing) (z (just nothing)) (b (z ∘ just ∘ just)) i j
-- -- -- RElim.hexDiag* (RFM2tab {A = A} {B = B}) _ _ _ {xs} b i f =
-- -- --  let z = f ∘' ua-gluePathExt (PCI'.e {B = B} {A = A} xs) i
-- -- --  in hexDiag (z nothing) (z (just nothing)) (z (just (just nothing)))
-- -- --         (b (z ∘ just ∘ just ∘ just)) i
-- -- -- RElim.hexU* RFM2tab = {!!}
-- -- -- RElim.hexL* RFM2tab = {!!}
-- -- -- RElim.trunc* RFM2tab xs = isGroupoidΠ λ _ → trunc

-- -- -- fm2tab : ∀ {ℓ'} {B : Type ℓ'} {A : Type ℓ}
-- -- --  → (xs : FMSet2 B) → (𝔽in xs → A) → FMSet2 A
-- -- -- fm2tab = RElim.f (RFM2tab)

-- -- -- module _ (isGroupoidA : isGroupoid A)  where


-- -- --  -- look∘Rtab≡id : RElimSet' {A = A} λ xs →
-- -- --  --          (f : 𝔽in xs → A) →
-- -- --  --            fm2Look.fm2look {B = A} (λ a → a) isGroupoidA
-- -- --  --                 ((fm2tab xs f)) ≡
-- -- --  --                  {!𝔽in→ev A (fm2Map (λ a → a) xs) ?!}
-- -- --  --                   -- (𝔽in→ev {B = Unit} A
-- -- --  --                   --   (fm2Map (λ _ → tt) {!!})) (f ∘ λ x → {!!})
              
-- -- --  --         -- fm2tab (fm2Map (λ _ → _) xs) (invEq (𝔽in→ev≃ A (fm2Map (λ _ → _) xs))
-- -- --  --         --  (fm2Look.fm2look {B = Unit} (λ _ → _) isGroupoidA xs)) ≡ xs
-- -- --  -- look∘Rtab≡id = {!!}

 

-- -- --  Rtab∘look≡id : RElimSet' {A = A} λ xs →
-- -- --          fm2tab (fm2Map (λ _ → _) xs) (invEq (𝔽in→ev≃ A (fm2Map (λ _ → _) xs))
-- -- --           (fm2Look.fm2look {B = Unit} (λ _ → _) isGroupoidA xs)) ≡ xs
-- -- --  RElimSet'.[]* Rtab∘look≡id = refl
-- -- --  (Rtab∘look≡id RElimSet'.∷* x) = cong′ (x ∷2_)
-- -- --  RElimSet'.comm* Rtab∘look≡id x y {xs} b =
-- -- --    flipSquare (RElimProp'.f w xs ◁ λ j i → comm x y (b j) i )

-- -- -- --   = y ∷2
-- -- -- --     x ∷2
-- -- -- --     fm2tab (fm2Map (λ _ → tt) xs)
-- -- -- --     (invEq (𝔽in→ev≃ A (fm2Map (λ _ → tt) xs))
-- -- -- --      (fm2Look.fm2look (λ _ → tt) isGroupoidA xs))
-- -- -- --   : FMSet2 A
-- -- -- --   (blocked on _1916, belongs to problem 9853)
-- -- -- -- ?7 (i₁ = i0)
-- -- -- --   = x ∷2
-- -- -- --     y ∷2
-- -- -- --     fm2tab (fm2Map (λ _ → tt) xs)
-- -- -- --     (invEq (𝔽in→ev≃ A (fm2Map (λ _ → tt) xs))

-- -- --   where
-- -- --   w : RElimProp' λ xs → Square {A = FMSet2 A} (λ i →
-- -- --          fm2tab (fm2Map (λ _ → tt) (comm x y xs i))
-- -- --          (invEq (𝔽in→ev≃ A (fm2Map (λ _ → tt) (comm x y xs i)))
-- -- --           (fm2Look.fm2look (λ _ → tt) isGroupoidA (comm x y xs i))))
      
-- -- --       (comm x y
-- -- --          (fm2tab (fm2Map (λ _ → tt) xs)
-- -- --           (invEq (𝔽in→ev≃ A (fm2Map (λ _ → tt) xs))
-- -- --            (fm2Look.fm2look (λ _ → tt) isGroupoidA xs))))
-- -- --            refl refl
-- -- --   RElimProp'.[]* w i i₁ = {!invEq (𝔽in→ev≃ A (fm2Map (λ _ → tt) (comm x y xs i)))!}
-- -- --   (w RElimProp'.∷* x) {xs} X = {!!}
-- -- --   RElimProp'.trunc* w xs = {!trunc _ _ _ _!}

-- -- -- -- ———— Boundary ——————————————————————————————————————————————
-- -- -- -- i = i0 ⊢ x ∷2 y ∷2 b j
-- -- -- -- i = i1 ⊢ y ∷2 x ∷2 b j
-- -- -- -- j = i0 ⊢ fm2tab (fm2Map (λ _ → tt) (comm x y xs i))
-- -- -- --          (invEq (𝔽in→ev≃ A (fm2Map (λ _ → tt) (comm x y xs i)))
-- -- -- --           (fm2Look.fm2look (λ _ → tt) isGroupoidA (comm x y xs i)))
-- -- -- -- j = i1 ⊢ comm x y xs i
-- -- -- -- ————————————————————————————————————————————————————————————
-- -- -- -- j   : I
-- -- -- -- i   : I
-- -- -- -- b   : fm2tab (fm2Map (λ _ → tt) xs)
-- -- -- --       (invEq (𝔽in→ev≃ A (fm2Map (λ _ → tt) xs))
-- -- -- --        (fm2Look.fm2look (λ _ → tt) isGroupoidA xs))
-- -- -- --       ≡ xs

-- -- --  RElimSet'.trunc* Rtab∘look≡id _ = trunc _ _

-- -- -- -- -- -- -- -- -- comm*-P : (X : hSet ℓ-zero) → (a a' : A) → (f : fst X → A) →
-- -- -- -- -- -- -- -- --        PathP (λ i → ua (swap0and1M X) i → A)
-- -- -- -- -- -- -- -- --          (Mb.rec a (Mb.rec a' f))
-- -- -- -- -- -- -- -- --          (Mb.rec a' (Mb.rec a f))
-- -- -- -- -- -- -- -- -- comm*-P X a a' f =
-- -- -- -- -- -- -- -- --   ua→ (Mb.elim _ refl (Mb.elim _ refl λ _ → refl) )
-- -- -- -- -- -- -- -- --   -- let z : PathP (λ i₁ → ua (swap0and1M X) i₁ → fst (Mb^ 2 X))
-- -- -- -- -- -- -- -- --   --           (fst (swap0and1M X)) (idfun (fst (Mb^ 2 X)))
-- -- -- -- -- -- -- -- --   --     z = ua-ungluePathExt (swap0and1M X)
-- -- -- -- -- -- -- -- --   --  in {!!}


-- -- -- -- -- -- -- -- -- RFM2look : RElim {A = A} (λ z → 𝔽in z → A)
-- -- -- -- -- -- -- -- -- RElim.[]* RFM2look ()
-- -- -- -- -- -- -- -- -- RElim._∷*_ RFM2look x = Mb.rec x
-- -- -- -- -- -- -- -- -- -- (RFM2look RElim.∷* a) _ nothing = a
-- -- -- -- -- -- -- -- -- -- (RFM2look RElim.∷* _) b (just k) = b k
-- -- -- -- -- -- -- -- -- RElim.comm* RFM2look a a' {xs} b i k = comm*-P (h𝔽in xs) a a' b i k
-- -- -- -- -- -- -- -- -- RElim.comm-inv* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- RElim.hexDiag* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- RElim.hexU* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- RElim.hexL* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- RElim.trunc* RFM2look = {!!}


-- -- -- -- -- -- -- -- -- -- FM2look : (xs : FMSet2 A) → 𝔽in xs → A
-- -- -- -- -- -- -- -- -- -- FM2look {A = A} = RElim.f RFM2look

-- -- -- -- -- -- -- -- -- -- FM2→Σ𝔽→ : FMSet2 A → Σ𝔽→ A
-- -- -- -- -- -- -- -- -- -- FM2→Σ𝔽→ x = {!!}



-- -- -- -- -- -- -- -- -- -- -- FMI : FMSet2 A → hSet ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- FMI =
-- -- -- -- -- -- -- -- -- -- --   Elim.f 
-- -- -- -- -- -- -- -- -- -- --    (⊥.⊥ , isProp→isSet isProp⊥)
-- -- -- -- -- -- -- -- -- -- --    (λ x {xs} b → Maybe (fst b) , isOfHLevelMaybe zero (snd b) )
-- -- -- -- -- -- -- -- -- -- --    (λ x y b → TypeOfHLevel≡ 2 (ua (swap0and1M b)))
-- -- -- -- -- -- -- -- -- -- --    (λ x y {xs} b →
-- -- -- -- -- -- -- -- -- -- --       ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- --         (cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
-- -- -- -- -- -- -- -- -- -- --           ∙ uaInvEquiv (swap0and1M b)) )
-- -- -- -- -- -- -- -- -- -- --    (λ x y z b → TypeOfHLevel≡ 2 (ua (swap0and2M b)))
-- -- -- -- -- -- -- -- -- -- --    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- --                       (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- --                        (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- --                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))


-- -- -- -- -- -- -- -- -- -- --    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- --                       (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- --                        (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- --                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))
-- -- -- -- -- -- -- -- -- -- --    (λ _ → isGroupoidHSet)

-- -- -- -- -- -- -- -- -- -- -- -- FMIfin : ∀ (xs : FMSet2 A) → isFinSet (fst (FMI xs))
-- -- -- -- -- -- -- -- -- -- -- -- FMIfin xs = (len2 xs) , 
-- -- -- -- -- -- -- -- -- -- -- --   (ElimProp.f {B = λ xs → PT.∥ fst (FMI xs) ≃ F.Fin (len2 xs) ∥₁}
-- -- -- -- -- -- -- -- -- -- -- --     PT.∣ idEquiv _ ∣₁
-- -- -- -- -- -- -- -- -- -- -- --      (λ _ {_} →
-- -- -- -- -- -- -- -- -- -- -- --       PT.map
-- -- -- -- -- -- -- -- -- -- -- --        λ e → congMaybeEquiv e
-- -- -- -- -- -- -- -- -- -- -- --           ∙ₑ isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- --               (iso Maybe→SumUnit
-- -- -- -- -- -- -- -- -- -- -- --                    SumUnit→Maybe
-- -- -- -- -- -- -- -- -- -- -- --                    SumUnit→Maybe→SumUnit
-- -- -- -- -- -- -- -- -- -- -- --                    Maybe→SumUnit→Maybe)
          
-- -- -- -- -- -- -- -- -- -- -- --           )
-- -- -- -- -- -- -- -- -- -- -- --        (λ xs → PT.squash₁) xs)

-- -- -- -- -- -- -- -- -- -- -- --   where open SumUnit

-- -- -- -- -- -- -- -- -- -- -- -- ×Vec : (A : Type ℓ) → ℕ → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- ×Vec A zero = Unit*
-- -- -- -- -- -- -- -- -- -- -- -- ×Vec A (suc n) = A × ×Vec A n

-- -- -- -- -- -- -- -- -- -- -- -- tabulate× : ∀ {n} → (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A) → ×Vec A n
-- -- -- -- -- -- -- -- -- -- -- -- tabulate× {n = zero} _ = tt*
-- -- -- -- -- -- -- -- -- -- -- -- tabulate× {n = suc n} x = x nothing , tabulate× (x ∘ just)

-- -- -- -- -- -- -- -- -- -- -- -- lookup× : ∀ {n} → ×Vec A n → (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A) 
-- -- -- -- -- -- -- -- -- -- -- -- lookup× {n = zero} x ()
-- -- -- -- -- -- -- -- -- -- -- -- lookup× {n = suc n} x = Mb.rec (fst x) (lookup× (snd x))

-- -- -- -- -- -- -- -- -- -- -- -- Iso-tabulate×-lookup× : ∀ {n} → Iso (×Vec A n) (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A)
-- -- -- -- -- -- -- -- -- -- -- -- Iso.fun Iso-tabulate×-lookup× = lookup×
-- -- -- -- -- -- -- -- -- -- -- -- Iso.inv Iso-tabulate×-lookup× = tabulate×
-- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (Iso-tabulate×-lookup× {n = zero}) b i ()
-- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (Iso-tabulate×-lookup× {n = suc n}) b i nothing = b nothing
-- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (Iso-tabulate×-lookup× {n = suc n}) b i (just x) =
-- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv (Iso-tabulate×-lookup× {n = n}) (b ∘ just) i x
-- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (Iso-tabulate×-lookup× {n = zero}) a = refl
-- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (Iso-tabulate×-lookup× {n = suc n}) a =
-- -- -- -- -- -- -- -- -- -- -- --  ΣPathP (refl ,
-- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv (Iso-tabulate×-lookup× {n = n}) (snd a))



-- -- -- -- -- -- -- -- -- -- -- swap0and1⊎f : {A B C : Type ℓ} → A ⊎ (B ⊎ C) → B ⊎ (A ⊎ C)  
-- -- -- -- -- -- -- -- -- -- -- swap0and1⊎f (inl x) = (inr (inl x))
-- -- -- -- -- -- -- -- -- -- -- swap0and1⊎f (inr (inl x)) = (inl x)
-- -- -- -- -- -- -- -- -- -- -- swap0and1⊎f (inr (inr x)) = (inr (inr x))

-- -- -- -- -- -- -- -- -- -- -- swap0and1⊎fInvol : {A B C : Type ℓ} → ∀ x → swap0and1⊎f (swap0and1⊎f {A = A} {B} {C} x) ≡ x
-- -- -- -- -- -- -- -- -- -- -- swap0and1⊎fInvol (inl x) = refl
-- -- -- -- -- -- -- -- -- -- -- swap0and1⊎fInvol (inr (inl x)) = refl
-- -- -- -- -- -- -- -- -- -- -- swap0and1⊎fInvol (inr (inr x)) = refl

-- -- -- -- -- -- -- -- -- -- -- swap0and1⊎ :  {A B C : Type ℓ} → A ⊎ (B ⊎ C) ≃ B ⊎ (A ⊎ C)  
-- -- -- -- -- -- -- -- -- -- -- swap0and1⊎ =
-- -- -- -- -- -- -- -- -- -- --   isoToEquiv (iso swap0and1⊎f swap0and1⊎f swap0and1⊎fInvol swap0and1⊎fInvol)


-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎f : {A B C D : Type ℓ} → A ⊎ (B ⊎ (C ⊎ D)) → C ⊎ (B ⊎ (A ⊎ D))  
-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎f (inl x) = (inr (inr (inl x)))
-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎f (inr (inl x)) = (inr (inl x))
-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎f (inr (inr (inl x))) = (inl x)
-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎f (inr (inr (inr x))) = (inr (inr (inr x)))

-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎fInvol : {A B C D : Type ℓ} → ∀ x → swap0and2⊎f (swap0and2⊎f {A = A} {B} {C} {D} x) ≡ x
-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎fInvol (inl x) = refl
-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎fInvol (inr (inl x)) = refl
-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎fInvol (inr (inr (inl x))) = refl
-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎fInvol (inr (inr (inr x))) = refl

-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎ :  {A B C D : Type ℓ} → A ⊎ (B ⊎ (C ⊎ D)) ≃ C ⊎ (B ⊎ (A ⊎ D))
-- -- -- -- -- -- -- -- -- -- -- swap0and2⊎ =
-- -- -- -- -- -- -- -- -- -- --   isoToEquiv (iso swap0and2⊎f swap0and2⊎f swap0and2⊎fInvol swap0and2⊎fInvol)


-- -- -- -- -- -- -- -- -- -- -- module ∈FMSet2 {A : Type ℓ} (grpA : isGroupoid A) where

-- -- -- -- -- -- -- -- -- -- --   toHSet₃ : ∥ Type ℓ ∥₃ → hSet ℓ
-- -- -- -- -- -- -- -- -- -- --   fst (toHSet₃ ∣ x ∣₃) = ∥ x ∥₂
-- -- -- -- -- -- -- -- -- -- --   snd (toHSet₃ ∣ x ∣₃) = ST.squash₂
-- -- -- -- -- -- -- -- -- -- --   toHSet₃ (squash₃ x x₁ p q r s i i₁ i₂) =
-- -- -- -- -- -- -- -- -- -- --     isGroupoidHSet _ _ _ _ (λ j jj → toHSet₃ (r j jj)) (λ j jj → toHSet₃ (s j jj)) i i₁ i₂



-- -- -- -- -- -- -- -- -- -- --   toTy₃ : ∥ Type ℓ ∥₃ → Type ℓ
-- -- -- -- -- -- -- -- -- -- --   toTy₃ x  = fst (toHSet₃ x)
-- -- -- -- -- -- -- -- -- -- --   -- toTy₃ (squash₃ x x₁ p q r s i i₁ i₂) = {!!}


-- -- -- -- -- -- -- -- -- -- --   -- fromTy₃ : ∀ (A B : Type ℓ) (e : A ≃ B) → (isSetA : isSet A) → (isSetB : isSet B)
-- -- -- -- -- -- -- -- -- -- --   --                → (cong ST.∥_∥₂ (ua e))
-- -- -- -- -- -- -- -- -- -- --   --                ≡ ua (setTruncIdempotent≃ isSetA ∙ₑ
-- -- -- -- -- -- -- -- -- -- --   --                   e ∙ₑ
-- -- -- -- -- -- -- -- -- -- --   --                   invEquiv (setTruncIdempotent≃ isSetB))
-- -- -- -- -- -- -- -- -- -- --   -- fromTy₃ x y a xs = {!!} 

-- -- -- -- -- -- -- -- -- -- --   ua→' : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {B : Type ℓ'}
-- -- -- -- -- -- -- -- -- -- --      (f : A₁ → B)
-- -- -- -- -- -- -- -- -- -- --     → PathP (λ i → ua e i → B) (f ∘ fst e) f
-- -- -- -- -- -- -- -- -- -- --   ua→' {e = e} f i a = f ((ua-unglue e i a))
-- -- -- -- -- -- -- -- -- -- --      -- h ((ua-unglue e i a) ) i

-- -- -- -- -- -- -- -- -- -- --   fromTy₃≡ : ∀ {A B C : Type ℓ} (e : A ≃ B) → (isSetA : isSet A) → (isSetB : isSet B)
-- -- -- -- -- -- -- -- -- -- --                  → (f : A → C)
-- -- -- -- -- -- -- -- -- -- --                  → (g : B → C)
-- -- -- -- -- -- -- -- -- -- --                  → PathP (λ i → ua e i → C) f g 
-- -- -- -- -- -- -- -- -- -- --                  → PathP (λ i → toTy₃ ∣ ua e i ∣₃ → C)
-- -- -- -- -- -- -- -- -- -- --                      (f ∘ fst (setTruncIdempotent≃ isSetA))
-- -- -- -- -- -- -- -- -- -- --                      (g ∘ fst (setTruncIdempotent≃ isSetB))
-- -- -- -- -- -- -- -- -- -- --   fromTy₃≡ e isSetA isSetB f g p =
-- -- -- -- -- -- -- -- -- -- --     congP {A = λ z → (b : ua e z) → _}
-- -- -- -- -- -- -- -- -- -- --           {B = λ i _ → (a : ∥ ua e i ∥₂) → _} (λ i → _∘ fst (setTruncIdempotent≃
-- -- -- -- -- -- -- -- -- -- --       ((_▷_ {A = λ i → isSet (ua e i)}
-- -- -- -- -- -- -- -- -- -- --         (λ i → coe0→i (λ i → isSet (ua e i) ) i isSetA) (isPropIsSet _ isSetB)) i))) p

-- -- -- -- -- -- -- -- -- -- --   fromTy₃Sq : ∀ {C : Type ℓ} 
-- -- -- -- -- -- -- -- -- -- --                    (A : I → I → Type ℓ)
-- -- -- -- -- -- -- -- -- -- --                    (isSetA : ∀ i j → isSet (A i j))
-- -- -- -- -- -- -- -- -- -- --                    {a₀₀ : A i0 i0 → C} {a₀₁ : A i0 i1 → C} (a₀₋ : PathP (λ j → A i0 j → C) a₀₀ a₀₁)
-- -- -- -- -- -- -- -- -- -- --                    {a₁₀ : A i1 i0 → C} {a₁₁ : A i1 i1 → C} (a₁₋ : PathP (λ j → A i1 j → C) a₁₀ a₁₁)
-- -- -- -- -- -- -- -- -- -- --                    (a₋₀ : PathP (λ i → A i i0 → C) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1 → C) a₀₁ a₁₁)
-- -- -- -- -- -- -- -- -- -- --                    → (sq : SquareP (λ i j → A i j → C) a₀₋ a₁₋ a₋₀ a₋₁)
-- -- -- -- -- -- -- -- -- -- --                    → (SquareP (λ i j → ∥ A i j ∥₂ → C)
-- -- -- -- -- -- -- -- -- -- --                         (λ j → a₀₋ j ∘ fst (setTruncIdempotent≃ (isSetA i0 j)))
-- -- -- -- -- -- -- -- -- -- --                         (λ j → a₁₋ j ∘ fst (setTruncIdempotent≃ (isSetA i1 j)))
-- -- -- -- -- -- -- -- -- -- --                         (λ j → a₋₀ j ∘ fst (setTruncIdempotent≃ (isSetA j i0)))
-- -- -- -- -- -- -- -- -- -- --                         (λ j → a₋₁ j ∘ fst (setTruncIdempotent≃ (isSetA j i1))))
-- -- -- -- -- -- -- -- -- -- --   fromTy₃Sq A isSetA a₀₋ a₁₋ a₋₀ a₋₁ sq i j =
-- -- -- -- -- -- -- -- -- -- --     sq i j ∘ fst (setTruncIdempotent≃ (isSetA i j))


-- -- -- -- -- -- -- -- -- -- --   -- ∈FM2'' : A → FMSet2 A → ∥ Type ℓ ∥₃ 
-- -- -- -- -- -- -- -- -- -- --   -- ∈FM2'' a = Rec.f
-- -- -- -- -- -- -- -- -- -- --   --      squash₃
-- -- -- -- -- -- -- -- -- -- --   --      ∣ ⊥.⊥* ∣₃
-- -- -- -- -- -- -- -- -- -- --   --      (λ x → GT.map λ b → (x ≡ a) ⊎ b)
-- -- -- -- -- -- -- -- -- -- --   --      (λ x y → GT.elim (λ _ → isSet→isGroupoid (squash₃ _ _))
-- -- -- -- -- -- -- -- -- -- --   --        λ T → cong ∣_∣₃ (ua swap0and1⊎))
-- -- -- -- -- -- -- -- -- -- --   --      (λ x y → GT.elim (λ _ → isSet→isGroupoid (isProp→isSet (squash₃ _ _ _ _)))
-- -- -- -- -- -- -- -- -- -- --   --             λ T → cong (cong ∣_∣₃)
-- -- -- -- -- -- -- -- -- -- --   --              ((cong ua (equivEq (funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --   --                λ _ → refl))))) ∙ uaInvEquiv _))
-- -- -- -- -- -- -- -- -- -- --   --      (λ x y z → GT.elim (λ _ → isSet→isGroupoid (squash₃ _ _))
-- -- -- -- -- -- -- -- -- -- --   --                   λ T → cong ∣_∣₃ (ua swap0and2⊎))
-- -- -- -- -- -- -- -- -- -- --   --      {!!}
-- -- -- -- -- -- -- -- -- -- --   --      -- (λ x y z → 
-- -- -- -- -- -- -- -- -- -- --   --      --    GT.elim (λ _ → {!!})
-- -- -- -- -- -- -- -- -- -- --   --      --    λ T i j → ∣ ∙≡∙→square _ _ _ _ {!!} i j ∣₃
-- -- -- -- -- -- -- -- -- -- --   --      --    )
-- -- -- -- -- -- -- -- -- -- --   --             -- λ T → {!(isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- --   --             --     ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --   --             --    (⊎.elim (λ _ → refl) λ _ → refl))))))!})
-- -- -- -- -- -- -- -- -- -- --   --      {!!}  --GT.elim (λ _ → isSet→isGroupoid (isProp→isSet (squash₃ _ _ _ _)))


-- -- -- -- -- -- -- -- -- -- --   -- ∈FM2'' : ∀ {ℓ'} (B : Type ℓ') (isGrpB : isGroupoid B) → A → FMSet2 A
-- -- -- -- -- -- -- -- -- -- --   --                  → ∥ Σ (Type ℓ)
-- -- -- -- -- -- -- -- -- -- --   --                        (λ T → B → (A → B) → T → B ) ∥₃ 
-- -- -- -- -- -- -- -- -- -- --   -- ∈FM2'' B isGrpB a = {!!}









-- -- -- -- -- -- -- -- -- -- --   swap0and1₃ : {a x y : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- --                  (x ≡ a) ⊎ ∥ (y ≡ a) ⊎ C ∥₂ →
-- -- -- -- -- -- -- -- -- -- --                  (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ 
-- -- -- -- -- -- -- -- -- -- --   swap0and1₃ (inl x) = inr  ∣ inl x ∣₂
-- -- -- -- -- -- -- -- -- -- --   swap0and1₃ (inr ∣ inl x ∣₂) = inl x
-- -- -- -- -- -- -- -- -- -- --   swap0and1₃ (inr ∣ inr x ∣₂) = inr ∣ inr x ∣₂
-- -- -- -- -- -- -- -- -- -- --   swap0and1₃ (inr (squash₂ x x₁ p q i i₁)) =
-- -- -- -- -- -- -- -- -- -- --     ⊎.isSet⊎ (grpA _ _) squash₂ _ _
-- -- -- -- -- -- -- -- -- -- --       (cong (swap0and1₃ ∘ inr) p)
-- -- -- -- -- -- -- -- -- -- --       (cong (swap0and1₃ ∘ inr) q) i i₁

-- -- -- -- -- -- -- -- -- -- --   swap0and1₃invo : {a x y : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- --                  ∀ b → swap0and1₃ {a = a} {x} {y} {C} (swap0and1₃ b) ≡ b 
-- -- -- -- -- -- -- -- -- -- --   swap0and1₃invo = ⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --      (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --         (λ _ → refl)))

-- -- -- -- -- -- -- -- -- -- --   swap0and1Iso₃ : {a x y : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- --                  Iso ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ C ∥₂) 
-- -- -- -- -- -- -- -- -- -- --                      ((y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂)
-- -- -- -- -- -- -- -- -- -- --   Iso.fun swap0and1Iso₃ = swap0and1₃
-- -- -- -- -- -- -- -- -- -- --   Iso.inv swap0and1Iso₃ = swap0and1₃
-- -- -- -- -- -- -- -- -- -- --   Iso.rightInv swap0and1Iso₃ = swap0and1₃invo
-- -- -- -- -- -- -- -- -- -- --   Iso.leftInv swap0and1Iso₃ = swap0and1₃invo

-- -- -- -- -- -- -- -- -- -- --   swap0and1≃₃ : {a x y  : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- --                     ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ C ∥₂) 
-- -- -- -- -- -- -- -- -- -- --                     ≃ ((y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂)
-- -- -- -- -- -- -- -- -- -- --   swap0and1≃₃ = isoToEquiv swap0and1Iso₃



-- -- -- -- -- -- -- -- -- -- --   swap0and2₃ : {a x y z : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- --                  (x ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (z ≡ a) ⊎ C ∥₂ ∥₂ →
-- -- -- -- -- -- -- -- -- -- --                  (z ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ ∥₂ 
-- -- -- -- -- -- -- -- -- -- --   swap0and2₃  =
-- -- -- -- -- -- -- -- -- -- --     ⊎.elim (inr ∘ ∣_∣₂ ∘ inr ∘ ∣_∣₂ ∘ inl )
 
-- -- -- -- -- -- -- -- -- -- --     (ST.rec (⊎.isSet⊎ (grpA _ _) squash₂)
-- -- -- -- -- -- -- -- -- -- --       (⊎.rec ( inr ∘ ∣_∣₂ ∘ inl  )
-- -- -- -- -- -- -- -- -- -- --        (ST.rec (⊎.isSet⊎ (grpA _ _) squash₂) (⊎.rec inl (inr ∘ ∣_∣₂ ∘ inr ∘ ∣_∣₂ ∘ inr )))))


-- -- -- -- -- -- -- -- -- -- --   swap0and2Iso₃ : {a x y z : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- --                  Iso ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (z ≡ a) ⊎ C ∥₂ ∥₂)
-- -- -- -- -- -- -- -- -- -- --                      ((z ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ ∥₂) 
-- -- -- -- -- -- -- -- -- -- --   Iso.fun swap0and2Iso₃ = swap0and2₃
-- -- -- -- -- -- -- -- -- -- --   Iso.inv swap0and2Iso₃ = swap0and2₃
-- -- -- -- -- -- -- -- -- -- --   Iso.rightInv swap0and2Iso₃ =
-- -- -- -- -- -- -- -- -- -- --         ⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --      (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --         ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl) (λ _ → refl))))))
-- -- -- -- -- -- -- -- -- -- --   Iso.leftInv swap0and2Iso₃ =
-- -- -- -- -- -- -- -- -- -- --       ⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --      (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --         ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl) (λ _ → refl))))))


-- -- -- -- -- -- -- -- -- -- --   swap0and2≃₃ : {a x y z : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- --                      ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (z ≡ a) ⊎ C ∥₂ ∥₂)
-- -- -- -- -- -- -- -- -- -- --                   ≃  ((z ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ ∥₂) 
-- -- -- -- -- -- -- -- -- -- --   swap0and2≃₃ = isoToEquiv swap0and2Iso₃

-- -- -- -- -- -- -- -- -- -- --   -- swap0and2≃DiagU : {a x y z : A} {C : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- --   --                       Square 
-- -- -- -- -- -- -- -- -- -- --   --                         (λ i → (y ≡ a) ⊎ toTy₃ ∣ ua (swap0and1≃₃ {a = a} {x} {z} {C}) i ∣₃)
-- -- -- -- -- -- -- -- -- -- --   --                         (λ i → ua (swap0and2≃₃ {a = a} {x} {y} {z} {C}) i)
-- -- -- -- -- -- -- -- -- -- --   --                         (λ i → ua (swap0and1≃₃ {a = a} {y} {x} {∥ (z ≡ a) ⊎ C ∥₂})  i)
-- -- -- -- -- -- -- -- -- -- --   --                         (λ i → ua (swap0and1≃₃ {a = a} {y} {z} {∥ (x ≡ a) ⊎ C ∥₂}) i)
                        
-- -- -- -- -- -- -- -- -- -- --   -- -- swap0and2≃DiagU = ∙-∙≡→square
-- -- -- -- -- -- -- -- -- -- --   -- --   ( (isInjectiveTransport (funExt (
-- -- -- -- -- -- -- -- -- -- --   -- --     ⊎.elim
-- -- -- -- -- -- -- -- -- -- --   -- --       (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --   -- --       {!!}
-- -- -- -- -- -- -- -- -- -- --   -- --       )) ∙ uaCompEquiv _ _) ∙ cong (ua swap0and1≃₃ ∙_)
-- -- -- -- -- -- -- -- -- -- --   -- --     (uaCompEquiv _ _ ∙
-- -- -- -- -- -- -- -- -- -- --   -- --       cong (ua swap0and2≃₃ ∙_) (uaInvEquiv _ )))

-- -- -- -- -- -- -- -- -- -- --   ∈FM2'' : A → FMSet2 A → ∥ Type ℓ ∥₃ 
-- -- -- -- -- -- -- -- -- -- --   ∈FM2'' a = Rec.f
-- -- -- -- -- -- -- -- -- -- --        squash₃
-- -- -- -- -- -- -- -- -- -- --        ∣ ⊥.⊥* ∣₃
-- -- -- -- -- -- -- -- -- -- --        (λ x xs → ∣ (x ≡ a) ⊎ toTy₃ xs ∣₃)
-- -- -- -- -- -- -- -- -- -- --        (λ x y b → cong ∣_∣₃ (ua swap0and1≃₃))
-- -- -- -- -- -- -- -- -- -- --        (λ x y b → cong (cong ∣_∣₃) (cong ua
-- -- -- -- -- -- -- -- -- -- --           (equivEq refl) ∙
-- -- -- -- -- -- -- -- -- -- --            uaInvEquiv
-- -- -- -- -- -- -- -- -- -- --             (swap0and1≃₃ {x = y} {y = x} )))         
-- -- -- -- -- -- -- -- -- -- --        (λ x y z b → cong ∣_∣₃ (ua swap0and2≃₃))
-- -- -- -- -- -- -- -- -- -- --        (λ x y z b → congSq ∣_∣₃ (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- --           (isInjectiveTransport (funExt (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --              (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --                 ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl) (λ _ → refl)))))))) )))
-- -- -- -- -- -- -- -- -- -- --        (λ x y z b → congSq ∣_∣₃ (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- --           (isInjectiveTransport (funExt (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --              (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --                 ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl) (λ _ → refl)))))))) )))

       



-- -- -- -- -- -- -- -- -- -- --   ∈FM2'-isSet : (x : A) → (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --     fst (GT.rec (isSet→isGroupoid isSetHProp) (λ x → isOfHLevel 2 x , isPropIsOfHLevel 2)
-- -- -- -- -- -- -- -- -- -- --                                (∈FM2'' x xs))  
-- -- -- -- -- -- -- -- -- -- --   ∈FM2'-isSet x =
-- -- -- -- -- -- -- -- -- -- --     ElimProp.f
-- -- -- -- -- -- -- -- -- -- --       (isProp→isSet isProp⊥*)
-- -- -- -- -- -- -- -- -- -- --       (λ x₁ {xs} x₂ → ⊎.isSet⊎ (grpA _ _) (snd (toHSet₃ (∈FM2'' x xs))))
-- -- -- -- -- -- -- -- -- -- --       λ xs → snd (GT.rec (isSet→isGroupoid isSetHProp) (λ x → isOfHLevel 2 x , isPropIsOfHLevel 2)
-- -- -- -- -- -- -- -- -- -- --                                (∈FM2'' x xs))

-- -- -- -- -- -- -- -- -- -- --   _∈FM2_ : A → FMSet2 A → Type ℓ
-- -- -- -- -- -- -- -- -- -- --   _∈FM2_ a = toTy₃ ∘ ∈FM2'' a

-- -- -- -- -- -- -- -- -- -- --   l∈ : lockUnit {ℓ-zero} → A → FMSet2 A → Type ℓ
-- -- -- -- -- -- -- -- -- -- --   l∈ unlock a x = a ∈FM2 x

-- -- -- -- -- -- -- -- -- -- --   isSetl∈ : ∀ l a xs →  isSet (l∈ l a xs)
-- -- -- -- -- -- -- -- -- -- --   isSetl∈ unlock a xs = snd (toHSet₃ (∈FM2'' a xs))


-- -- -- -- -- -- -- -- -- -- --   ∈[] : (a : A) → a ∈FM2 [] → ⊥*  
-- -- -- -- -- -- -- -- -- -- --   ∈[] a = ST.rec (isProp→isSet isProp⊥*) (idfun _)

-- -- -- -- -- -- -- -- -- -- --   ∈compute : ∀ x (a : A) (xs : FMSet2 A) → a ∈FM2 (x ∷2 xs) ≃ (x ≡ a) ⊎ (a ∈FM2 xs)  
-- -- -- -- -- -- -- -- -- -- --   ∈compute x a xs = setTruncIdempotent≃ (⊎.isSet⊎ (grpA _ _) (snd (toHSet₃ (∈FM2'' a xs))))

-- -- -- -- -- -- -- -- -- -- --   l∈compute : ∀ l x (a : A) (xs : FMSet2 A) → l∈ l a (x ∷2 xs) ≃ (x ≡ a) ⊎ (l∈ l a xs)  
-- -- -- -- -- -- -- -- -- -- --   l∈compute unlock x a xs =
-- -- -- -- -- -- -- -- -- -- --     setTruncIdempotent≃ (⊎.isSet⊎ (grpA _ _) (snd (toHSet₃ (∈FM2'' a xs))))

-- -- -- -- -- -- -- -- -- -- --   l∈compute' : ∀ l x (a : A) (xs : FMSet2 A) → (l∈ l a (x ∷2 xs)) ≃ (∥ (x ≡ a) ⊎ (l∈ l a xs) ∥₂)  
-- -- -- -- -- -- -- -- -- -- --   l∈compute' unlock x a xs = idEquiv _


-- -- -- -- -- -- -- -- -- -- --   -- ∈compute' : ∀ x (a : A) (xs : FMSet2 A) → a ∈FM2 (x ∷2 xs) → (x ≡ a) ⊎ (a ∈FM2 xs)  
-- -- -- -- -- -- -- -- -- -- --   -- ∈compute' x a xs ∣ x₁ ∣₂ = x₁
-- -- -- -- -- -- -- -- -- -- --   -- ∈compute' x a xs (squash₂ x₁ x₂ p q i i₁) =
-- -- -- -- -- -- -- -- -- -- --   --   ⊎.isSet⊎ (grpA _ _) (snd (toHSet₃ (∈FM2'' a xs)))
-- -- -- -- -- -- -- -- -- -- --   --    _
-- -- -- -- -- -- -- -- -- -- --   --    _ (cong (∈compute' x a xs) p) (cong (∈compute' x a xs) q) i i₁ 

-- -- -- -- -- -- -- -- -- -- --   -- l∈computeSqTy : (lockUnit {ℓ-zero}) →  (x y a : A) (xs : FMSet2 A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- --   -- l∈computeSqTy l x₁ y a xs = {!!}

-- -- -- -- -- -- -- -- -- -- --   -- l∈computeSq : ∀ l x y (a : A) (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --   --              Path (Path (Type ℓ) (l∈ l a (x ∷2 y ∷2 xs))
-- -- -- -- -- -- -- -- -- -- --   --                                  (l∈ l a (y ∷2 x ∷2 xs)))
-- -- -- -- -- -- -- -- -- -- --   --                (λ i → l∈ l a (comm x y xs i))
-- -- -- -- -- -- -- -- -- -- --   --                (ua ( {!!}
-- -- -- -- -- -- -- -- -- -- --   --                  ∙ₑ (swap0and1≃₃ {a = a} {x = x} {y = y} {C = l∈ l a xs}) ∙ₑ
-- -- -- -- -- -- -- -- -- -- --   --                  {!!})) 
-- -- -- -- -- -- -- -- -- -- --   -- l∈computeSq x y a xs = {!!}
-- -- -- -- -- -- -- -- -- -- --   l∈computeSqSide : ∀ l x y (a : A) (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --        l∈ l a (x ∷2 y ∷2 xs) ≃ ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ l∈ l a xs ∥₂)
-- -- -- -- -- -- -- -- -- -- --   l∈computeSqSide l x y a xs =
-- -- -- -- -- -- -- -- -- -- --     l∈compute l x a (y ∷2 xs) ∙ₑ ⊎.⊎-equiv (idEquiv _) (l∈compute' l y a xs)

-- -- -- -- -- -- -- -- -- -- --   l∈computeSqSideP : ∀ l x y (a : A) (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --        (b : (l : lockUnit) → l∈ l a xs → FMSet2 A) → 
-- -- -- -- -- -- -- -- -- -- --        PathP (λ k → ua (l∈computeSqSide l x y a xs) (~ k) → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- --           (λ x₁ →
-- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --                (λ q →
-- -- -- -- -- -- -- -- -- -- --                   x ∷2
-- -- -- -- -- -- -- -- -- -- --                   ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- --                   (ST.rec (⊎.isSet⊎ (grpA y a) (isSetl∈ l a xs))
-- -- -- -- -- -- -- -- -- -- --                    (idfun (Path A y a ⊎ l∈ l a xs)) q))
-- -- -- -- -- -- -- -- -- -- --                x₁)
-- -- -- -- -- -- -- -- -- -- --           λ x₁ →
-- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --             (λ q →
-- -- -- -- -- -- -- -- -- -- --                x ∷2
-- -- -- -- -- -- -- -- -- -- --                ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁) (fst (l∈compute l y a xs) q))
-- -- -- -- -- -- -- -- -- -- --             (fst (l∈compute l x a (y ∷2 xs)) x₁)
-- -- -- -- -- -- -- -- -- -- --   l∈computeSqSideP l x y a xs b =
-- -- -- -- -- -- -- -- -- -- --     symP (ua→ (zz l))
-- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- --         zz : ∀ l → (a₁ : l∈ l a (x ∷2 y ∷2 xs)) →
-- -- -- -- -- -- -- -- -- -- --                   ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --                   (λ q →
-- -- -- -- -- -- -- -- -- -- --                      x ∷2
-- -- -- -- -- -- -- -- -- -- --                      ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁) (fst (l∈compute l y a xs) q))
-- -- -- -- -- -- -- -- -- -- --                   (fst (l∈compute l x a (y ∷2 xs)) a₁)
-- -- -- -- -- -- -- -- -- -- --                   ≡
-- -- -- -- -- -- -- -- -- -- --                   ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --                   (λ q →
-- -- -- -- -- -- -- -- -- -- --                      x ∷2
-- -- -- -- -- -- -- -- -- -- --                      ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- --                      (ST.rec (⊎.isSet⊎ (grpA y a) (isSetl∈ l a xs))
-- -- -- -- -- -- -- -- -- -- --                       (idfun (Path A y a ⊎ l∈ l a xs)) q))
-- -- -- -- -- -- -- -- -- -- --                   (⊎.⊎-equiv (idEquiv (x ≡ a)) (l∈compute' l y a xs) .fst
-- -- -- -- -- -- -- -- -- -- --                    (l∈compute l x a (y ∷2 xs) .fst a₁))
-- -- -- -- -- -- -- -- -- -- --         zz unlock = ST.elim (λ _ → trunc _ _) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --             (ST.elim (λ _ → trunc _ _) (⊎.elim (λ _ → refl) λ _ → refl)))
  
-- -- -- -- -- -- -- -- -- -- --   l∈computeSq : ∀ l x y (a : A) (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --               Square
-- -- -- -- -- -- -- -- -- -- --                  (λ i → l∈ l a (comm x y xs i))
-- -- -- -- -- -- -- -- -- -- --                  (ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = l∈ l a xs}))
-- -- -- -- -- -- -- -- -- -- --                  (ua (l∈computeSqSide l x y a xs))
-- -- -- -- -- -- -- -- -- -- --                  (ua (l∈computeSqSide l y x a xs))
-- -- -- -- -- -- -- -- -- -- --   l∈computeSq unlock x y a xs = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   -- ∈computeSq' : ∀ x y (a : A) (C : Type ℓ) →
-- -- -- -- -- -- -- -- -- -- -- --   --                (cong ST.∥_∥₂ (ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = C})))
-- -- -- -- -- -- -- -- -- -- -- --   --                ≡ ua ( (setTruncIdempotent≃
-- -- -- -- -- -- -- -- -- -- -- --   --                  (⊎.isSet⊎ (grpA _ _) squash₂)) ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- --   --                   (swap0and1≃₃ {a = a} {x = x} {y = y} {C = C}) ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- --   --                   invEquiv (setTruncIdempotent≃
-- -- -- -- -- -- -- -- -- -- -- --   --                  (⊎.isSet⊎ (grpA _ _) squash₂)))
-- -- -- -- -- -- -- -- -- -- -- --   -- ∈computeSq' x y a xs = {!!} 


-- -- -- -- -- -- -- -- -- -- --   involSqLem' :
-- -- -- -- -- -- -- -- -- -- --     (x y : A) {xs : FMSet2 A} → ∀ l → ∀ a →
-- -- -- -- -- -- -- -- -- -- --      (b : (l : lockUnit) → l∈ l a xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --      PathP (λ i → ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = l∈ l a xs }) i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- --       (⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- --             x ∷2
-- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- --             ((ST.rec (⊎.isSet⊎ (grpA y a) (isSetl∈ l a xs)) (idfun _) q))))
-- -- -- -- -- -- -- -- -- -- --       (⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- --             y ∷2
-- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → x ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- --             (ST.rec (⊎.isSet⊎ (grpA x a) (isSetl∈ l a xs)) (idfun _) q)))
         
-- -- -- -- -- -- -- -- -- -- --   involSqLem' x y l a b = ua→ (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --       (ST.elim (λ _ → trunc _ _) (⊎.elim (λ _ → refl) λ _ → comm _ _ _)))

-- -- -- -- -- -- -- -- -- -- --   involSqLem :
-- -- -- -- -- -- -- -- -- -- --     (x y : A) {xs : FMSet2 A} → ∀ l → ∀ a →
-- -- -- -- -- -- -- -- -- -- --      (b : (l : lockUnit) → l∈ l a xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --      PathP (λ i → ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = l∈ l a xs }) i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- --       (⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- --             x ∷2
-- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- --             ((ST.rec (⊎.isSet⊎ (grpA y a) (isSetl∈ l a xs)) (idfun _) q))))
-- -- -- -- -- -- -- -- -- -- --       (⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- --             y ∷2
-- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → x ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- --             (ST.rec (⊎.isSet⊎ (grpA x a) (isSetl∈ l a xs)) (idfun _) q)))
-- -- -- -- -- -- -- -- -- -- --      → PathP (λ z → l∈ l a (comm x y xs z) → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- --       (λ x₂ →
-- -- -- -- -- -- -- -- -- -- --          ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- --             x ∷2
-- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- --             (fst (l∈compute l y a xs) q))
-- -- -- -- -- -- -- -- -- -- --          (fst (l∈compute l x a (y ∷2 xs)) x₂))
-- -- -- -- -- -- -- -- -- -- --       (λ x₂ →
-- -- -- -- -- -- -- -- -- -- --          ⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- --             y ∷2
-- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → x ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- --             (fst (l∈compute l x a xs) q))
-- -- -- -- -- -- -- -- -- -- --          (fst (l∈compute l y a (x ∷2 xs)) x₂))
-- -- -- -- -- -- -- -- -- -- --   involSqLem x y {xs} l a b P i =
-- -- -- -- -- -- -- -- -- -- --     comp (λ k → l∈computeSq l x y a xs (~ k) i → FMSet2 A )
-- -- -- -- -- -- -- -- -- -- --       (λ k → λ {
-- -- -- -- -- -- -- -- -- -- --             (i = i0) → l∈computeSqSideP l x y a xs b k
-- -- -- -- -- -- -- -- -- -- --            ;(i = i1) → l∈computeSqSideP l y x a xs b k
-- -- -- -- -- -- -- -- -- -- --            })
-- -- -- -- -- -- -- -- -- -- --       (P i)

-- -- -- -- -- -- -- -- -- -- --   removeFM2 : ∀ a (xs : FMSet2 A) → ∀ l → l∈ l a xs → FMSet2 A
-- -- -- -- -- -- -- -- -- -- --   removeFM2 a = Elim.f
-- -- -- -- -- -- -- -- -- -- --      (λ {unlock → ⊥.rec* ∘ ∈[] a})
-- -- -- -- -- -- -- -- -- -- --      w
-- -- -- -- -- -- -- -- -- -- --       -- (λ x {xs} f → ⊎.rec (λ _ → xs) ((x ∷2_) ∘ f) ∘ fst (∈compute x a xs))
-- -- -- -- -- -- -- -- -- -- --      -- {!!}
-- -- -- -- -- -- -- -- -- -- --       (λ x y {xs} b → funExt (wP x y {xs} b))
-- -- -- -- -- -- -- -- -- -- --       -- fromTy₃≡ (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs})
-- -- -- -- -- -- -- -- -- -- --       --   _
-- -- -- -- -- -- -- -- -- -- --       --   _ _ _ ((ww x y {xs} b))
-- -- -- -- -- -- -- -- -- -- --        -- )
-- -- -- -- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- -- -- -- --       -- (λ x y {xs} b →
-- -- -- -- -- -- -- -- -- -- --       --   {! fromTy₃Sq ? ? ? ? ? ? ?!}
-- -- -- -- -- -- -- -- -- -- --       --   )
-- -- -- -- -- -- -- -- -- -- --      -- (λ x y b →
-- -- -- -- -- -- -- -- -- -- --      --   congP
-- -- -- -- -- -- -- -- -- -- --      --    (λ j → {!congP (λ i → _∘ fst (setTruncIdempotent≃ ?))!})
-- -- -- -- -- -- -- -- -- -- --      --      {!!})
-- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- --      λ _ → isGroupoidΠ2 λ _ _ → trunc

-- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- --      w : (x : A) {xs : FMSet2 A} →
-- -- -- -- -- -- -- -- -- -- --            ((l : lockUnit) → l∈ l a xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --            (l : lockUnit) → l∈ l a (x ∷2 xs) → FMSet2 A
-- -- -- -- -- -- -- -- -- -- --      w x {xs} x₁ l x₂ = 
-- -- -- -- -- -- -- -- -- -- --        ⊎.rec (λ _ → xs) (λ q → x ∷2 x₁ l q) (fst (l∈compute l x a xs) x₂)

-- -- -- -- -- -- -- -- -- -- --      wP : (x y : A) {xs : FMSet2 A} →
-- -- -- -- -- -- -- -- -- -- --            (b : (l : lockUnit) → l∈ l a xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --             (x₁ : lockUnit) →
-- -- -- -- -- -- -- -- -- -- --                PathP (λ z → l∈ x₁ a (comm x y xs z) → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- --                (w x (w y b) x₁)
-- -- -- -- -- -- -- -- -- -- --                (w y (w x b) x₁)
-- -- -- -- -- -- -- -- -- -- --      wP x y {xs} b x₁ = involSqLem x y x₁ a b (involSqLem' x y {xs} x₁ a b)
      

-- -- -- -- -- -- -- -- -- -- --    -- where
-- -- -- -- -- -- -- -- -- -- --    --   ww : ∀ x y {xs} (b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --    --        PathP (λ i → (xy : ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}) i)
-- -- -- -- -- -- -- -- -- -- --    --             → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- --    --           (⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --    --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- --    --                x ∷2
-- -- -- -- -- -- -- -- -- -- --    --                ⊎.rec (λ _ → xs) (λ x₃ → y ∷2 b x₃) (fst (∈compute y a xs) x₂)))
-- -- -- -- -- -- -- -- -- -- --    --           (⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --    --           (λ x₂ →
-- -- -- -- -- -- -- -- -- -- --    --              y ∷2
-- -- -- -- -- -- -- -- -- -- --    --              ⊎.rec (λ _ → xs) (λ x₃ → x ∷2 b x₃) (fst (∈compute x a xs) x₂)))
-- -- -- -- -- -- -- -- -- -- --    --   ww x y {xs} b = ua→ (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --    --    (ST.elim (λ _ → trunc _ _) (⊎.elim (λ _ → refl) λ _ → comm _ _ _)))


-- -- -- -- -- -- -- -- -- -- --      -- ww' : ∀ (x y : A) → ∀ {xs} (b : a ∈FM2 xs → FMSet2 A) → _
-- -- -- -- -- -- -- -- -- -- --      --    SquareP (λ i j →
-- -- -- -- -- -- -- -- -- -- --      --         {!!})
-- -- -- -- -- -- -- -- -- -- --      --       {!!}
-- -- -- -- -- -- -- -- -- -- --      --       {!!}
-- -- -- -- -- -- -- -- -- -- --      --       refl
-- -- -- -- -- -- -- -- -- -- --      --       refl
-- -- -- -- -- -- -- -- -- -- --      -- ww' x y {xs} b =
-- -- -- -- -- -- -- -- -- -- --      --    fromTy₃Sq {C = FMSet2 A}
-- -- -- -- -- -- -- -- -- -- --      --      (λ i j → (cong ua
-- -- -- -- -- -- -- -- -- -- --      --      (equivEq refl) ∙
-- -- -- -- -- -- -- -- -- -- --      --       uaInvEquiv
-- -- -- -- -- -- -- -- -- -- --      --        (swap0and1≃₃ {x = y} {y = x} )) i j)
-- -- -- -- -- -- -- -- -- -- --      --        (λ i j → {!!}) (ww x y b) (symP (ww y x b)) refl refl
-- -- -- -- -- -- -- -- -- -- --      --         {!!}
     
-- -- -- -- -- -- -- -- -- -- -- --      -- ww'F : ∀ x y {xs} --(b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- --      --          (f : (x ≡ a) ⊎ ∥ (y ≡ a) ⊎ (a ∈FM2 xs) ∥₂ → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- --      --          (g : (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ (a ∈FM2 xs) ∥₂ → FMSet2 A) 
-- -- -- -- -- -- -- -- -- -- -- --      --          (isSetP : ∀ i → isSet (ua (swap0and1≃₃ {a = a} {x = y} {y = x} {C = a ∈FM2 xs}) i))
-- -- -- -- -- -- -- -- -- -- -- --      --          (isSetP' : ∀ i → isSet (ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}) i))
-- -- -- -- -- -- -- -- -- -- -- --      --          → PathP (λ j →
-- -- -- -- -- -- -- -- -- -- -- --      --                 PathP (λ i →
-- -- -- -- -- -- -- -- -- -- -- --      --                 (cong {x = (swap0and1≃₃ {a = a} {x = y} {y = x} {C = a ∈FM2 xs})}
-- -- -- -- -- -- -- -- -- -- -- --      --                                     {y = invEquiv
-- -- -- -- -- -- -- -- -- -- -- --      --                                       ((swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}))}
-- -- -- -- -- -- -- -- -- -- -- --      --                                     ua (equivEq refl)
-- -- -- -- -- -- -- -- -- -- -- --      --                   ∙ uaInvEquiv (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}))
-- -- -- -- -- -- -- -- -- -- -- --      --                     j i
-- -- -- -- -- -- -- -- -- -- -- --      --                  → FMSet2 A )
-- -- -- -- -- -- -- -- -- -- -- --      --                  g f
-- -- -- -- -- -- -- -- -- -- -- --      --              → PathP (λ i → ∥ (cong {x = (swap0and1≃₃ {a = a} {x = y} {y = x} {C = a ∈FM2 xs})}
-- -- -- -- -- -- -- -- -- -- -- --      --                                     {y = invEquiv
-- -- -- -- -- -- -- -- -- -- -- --      --                                       ((swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}))}
-- -- -- -- -- -- -- -- -- -- -- --      --                                     ua (equivEq refl)
-- -- -- -- -- -- -- -- -- -- -- --      --                   ∙ uaInvEquiv (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}))
-- -- -- -- -- -- -- -- -- -- -- --      --                     j i ∥₂ → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- --      --                (g ∘ fst (setTruncIdempotent≃ (isPropIsSet (isSetP i0) (isSetP' i1) j)))
-- -- -- -- -- -- -- -- -- -- -- --      --                (f ∘ fst (setTruncIdempotent≃ (isPropIsSet (isSetP i1) (isSetP' i0) j))))
-- -- -- -- -- -- -- -- -- -- -- --      --             (congP {A = λ z →
-- -- -- -- -- -- -- -- -- -- -- --      --                 (b : ua (swap0and1≃₃ {a = a} {x = y} {y = x} {C = a ∈FM2 xs}) z) → FMSet2 A}
-- -- -- -- -- -- -- -- -- -- -- --      --                    {B = λ i _ →
-- -- -- -- -- -- -- -- -- -- -- --      --                     (a : ∥ ua (swap0and1≃₃ {a = a} {x = y} {y = x} {C = a ∈FM2 xs}) i ∥₂)
-- -- -- -- -- -- -- -- -- -- -- --      --                       → FMSet2 A}
-- -- -- -- -- -- -- -- -- -- -- --      --                 (λ i → _∘ fst (setTruncIdempotent≃ (isSetP i))))
-- -- -- -- -- -- -- -- -- -- -- --      --             (congP {A = λ z →
-- -- -- -- -- -- -- -- -- -- -- --      --                 (b : ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}) (~ z))
-- -- -- -- -- -- -- -- -- -- -- --      --                  → FMSet2 A}
-- -- -- -- -- -- -- -- -- -- -- --      --                    {B = λ i _ →
-- -- -- -- -- -- -- -- -- -- -- --      --                     (a : ∥ ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}) (~ i) ∥₂)
-- -- -- -- -- -- -- -- -- -- -- --      --                       → FMSet2 A}
-- -- -- -- -- -- -- -- -- -- -- --      --                 (λ i → _∘ fst (setTruncIdempotent≃ (isSetP' (~ i)))))
                 
-- -- -- -- -- -- -- -- -- -- -- --      -- ww'F x y f g isSetP isSetP' j i = {!!}


-- -- -- -- -- -- -- -- -- -- -- --      -- ww' :  ∀ x y {xs} (b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- --      --        SquareP (λ i j → a ∈FM2 comm-inv x y xs i j → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- --      --               ?
-- -- -- -- -- -- -- -- -- -- -- --      --               ?
-- -- -- -- -- -- -- -- -- -- -- --      --               refl
-- -- -- -- -- -- -- -- -- -- -- --      --               refl
-- -- -- -- -- -- -- -- -- -- -- --      -- ww' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --   module SetRec∈ {ℓ'} {B : Type ℓ'} (isSetB : isSet B) (a : A)
-- -- -- -- -- -- -- -- -- -- -- -- --               (b∷Here : (x : A) → (FMSet2 A) → (x ≡ a) → B)
-- -- -- -- -- -- -- -- -- -- -- -- --               (_b∷_ : A → B → B)
-- -- -- -- -- -- -- -- -- -- -- -- --               (b∷comm : ∀ x y b → (x b∷ (y b∷ b)) ≡ (y b∷ (x b∷ b))) 
              
-- -- -- -- -- -- -- -- -- -- -- -- --               (bComm : ∀ x y xs → (p : x ≡ a) → b∷Here x (y ∷2 xs) p ≡ (y b∷ b∷Here x xs p))

-- -- -- -- -- -- -- -- -- -- -- -- --                where

-- -- -- -- -- -- -- -- -- -- -- -- --     zz : ∀ x y xs b →
-- -- -- -- -- -- -- -- -- -- -- -- --           PathP (λ i → (xy : ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}) i)  → B)
-- -- -- -- -- -- -- -- -- -- -- -- --            (⊎.rec (b∷Here x (y ∷2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- --           (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             x b∷
-- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (b∷Here y xs) (λ x₂ → y b∷ b)
-- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute y a xs) x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- --           (⊎.rec (b∷Here y (x ∷2 xs)) 
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             y b∷
-- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (b∷Here x xs) (λ x₂ → x b∷ b)
-- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute x a xs) x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- --     zz x y xs b = ua→
-- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.elim (bComm x y xs)
-- -- -- -- -- -- -- -- -- -- -- -- --               (ST.elim (λ _ → isProp→isSet (isSetB _ _))
-- -- -- -- -- -- -- -- -- -- -- -- --                (⊎.elim (sym ∘ bComm y x xs) λ _ → b∷comm x y b)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- ua→ (⊎.elim {!!} {!!})

-- -- -- -- -- -- -- -- -- -- -- -- --     f : ∀ xs → a ∈FM2 xs → B
-- -- -- -- -- -- -- -- -- -- -- -- --     f = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     -- f [] x = ⊥.rec* (∈[] a x)
-- -- -- -- -- -- -- -- -- -- -- -- --     -- f (x ∷2 xs) =
-- -- -- -- -- -- -- -- -- -- -- -- --     --   ⊎.rec (b∷Here x xs) ((x b∷_) ∘ f xs)
-- -- -- -- -- -- -- -- -- -- -- -- --     --   ∘ fst (∈compute x a xs)
-- -- -- -- -- -- -- -- -- -- -- -- --     -- f (comm x y xs i) v = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     -- f (comm-inv x₁ y xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     -- f (hexDiag x₁ y z xs i) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     -- f (hexU x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     -- f (hexL x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     -- f (trunc xs xs₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   commSqCompute∈ : (a : A) → (x y : A) (xs : FMSet2 A) →

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (xFM yFM : FMSet2 A) → (fFM : a ∈FM2 xs → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PathP (λ i → a ∈FM2 comm x y xs i → FMSet2 A) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ α → (⊎.rec (λ _ → xFM) (λ β → ⊎.rec (λ _ → yFM) fFM ((fst (∈compute y a xs)) β))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (fst (∈compute x a (y ∷2 xs)) α)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ α → (⊎.rec (λ _ → yFM) (λ β → ⊎.rec (λ _ → xFM) fFM ((fst (∈compute x a xs)) β))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (fst (∈compute y a (x ∷2 xs)) α)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   commSqCompute∈  a x y xs xFM yFM fFM i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!a ∈FM2 comm x y xs i!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   ss : PathP (λ i → ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = a ∈FM2 xs}) i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --              b0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --              b1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   ss = ua→ {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --   ∈[] : (a : A) → a ∈FM2 [] → ⊥*  
-- -- -- -- -- -- -- -- -- -- -- -- --   ∈[] a = ST.rec (isProp→isSet isProp⊥*) (idfun _)
  
  
-- -- -- -- -- -- -- -- -- -- -- -- --   ∈head : ∀ (x) (xs : FMSet2 A) → x ∈FM2 (x ∷2 xs)   
-- -- -- -- -- -- -- -- -- -- -- -- --   ∈head x xs = invEq (∈compute x x (xs)) (inl refl)


-- -- -- -- -- -- -- -- -- -- -- -- --   -- bringHead : ∀ a (xs : FMSet2 A) → a ∈FM2 xs → Σ (FMSet2 A) λ xs' → xs ≡ a ∷2 xs' 
-- -- -- -- -- -- -- -- -- -- -- -- --   -- bringHead a = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --   removeFM2 : ∀ a (xs : FMSet2 A) → a ∈FM2 xs → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- --   removeFM2 a = Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- --      (⊥.rec* ∘ ∈[] a)
-- -- -- -- -- -- -- -- -- -- -- -- --      (λ x {xs} f → ⊎.rec (λ _ → xs) ((x ∷2_) ∘ f) ∘ fst (∈compute x a xs))
-- -- -- -- -- -- -- -- -- -- -- -- --      ww
-- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --      {!ww'!}
-- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --      λ _ → isGroupoidΠ λ _ → trunc
-- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- --       ww : (x y : A) {xs : FMSet2 A} (b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- --          PathP (λ i → (cong ST.∥_∥₂ (ua (swap0and1≃₃ {a = a} {x} {y} {C = a ∈FM2 xs}) )) i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- --                x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- --                ⊎.rec (λ _ → xs) (λ x₃ → y ∷2 b x₃) (fst (∈compute y a xs) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute x a (y ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- --                y ∷2
-- -- -- -- -- -- -- -- -- -- -- -- --                ⊎.rec (λ _ → xs) (λ x₃ → x ∷2 b x₃) (fst (∈compute x a xs) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute y a (x ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- --       ww x y b = toPathP (funExt (ST.elim {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --         (⊎.elim (λ _ → fromPathP refl) (ST.elim {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --           (⊎.elim (λ _ → fromPathP refl)
-- -- -- -- -- -- -- -- -- -- -- -- --            λ _ → cong₂ _∷2_ (transportRefl _)
-- -- -- -- -- -- -- -- -- -- -- -- --                 (cong₂ _∷2_ (transportRefl _) (transportRefl _ ∙ cong b (transportRefl _)))
-- -- -- -- -- -- -- -- -- -- -- -- --                  ∙ comm _ _ _)))))

-- -- -- -- -- -- -- -- -- -- -- -- --       ww' : (x y z : A) {xs : FMSet2 A} (b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- --          PathP (λ i → a ∈FM2 hexDiag x y z xs i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → y ∷2 z ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- --                x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- --                ⊎.rec (λ _ → z ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- --                (λ x₃ →
-- -- -- -- -- -- -- -- -- -- -- -- --                   y ∷2
-- -- -- -- -- -- -- -- -- -- -- -- --                   ⊎.rec (λ _ → xs) (λ x₄ → z ∷2 b x₄) (fst (∈compute z a xs) x₃))
-- -- -- -- -- -- -- -- -- -- -- -- --                (fst (∈compute y a (z ∷2 xs)) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute x a (y ∷2 z ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → y ∷2 x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- --                z ∷2
-- -- -- -- -- -- -- -- -- -- -- -- --                ⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- --                (λ x₃ →
-- -- -- -- -- -- -- -- -- -- -- -- --                   y ∷2
-- -- -- -- -- -- -- -- -- -- -- -- --                   ⊎.rec (λ _ → xs) (λ x₄ → x ∷2 b x₄) (fst (∈compute x a xs) x₃))
-- -- -- -- -- -- -- -- -- -- -- -- --                (fst (∈compute y a (x ∷2 xs)) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute z a (y ∷2 x ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- --       ww' x y z b = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   removeLaw : ∀ a (xs : FMSet2 A) → (u : a ∈FM2 xs) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --                a ∷2 removeFM2 a xs u ≡ xs
-- -- -- -- -- -- -- -- -- -- -- -- -- --   removeLaw a =
-- -- -- -- -- -- -- -- -- -- -- -- -- --     ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- --      ((⊥.rec* ∘ ∈[] a))
-- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x {xs} x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --      λ _ → isSetΠ λ _ → trunc _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   remove≡ : ∀ a (xs : FMSet2 A) → (u v : a ∈FM2 xs) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                removeFM2 a xs u ≡ removeFM2 a xs v
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   remove≡ a =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊥.rec* ∘ ∈[] a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ x {xs} kk u v →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          zz x {xs} kk (fst (∈compute {x = x} a xs) u)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       (fst (∈compute {x = x} a xs) v))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ _ → isSetΠ2 λ _ _ → trunc _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      zz : (x : A) {xs : FMSet2 A} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((u v : a ∈FM2 xs) → removeFM2 a xs u ≡ removeFM2 a xs v) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (u v : (x ≡ a) ⊎ (a ∈FM2 xs)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⊎.rec (λ _ → xs) ((x ∷2_) ∘ removeFM2 a xs) u ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⊎.rec (λ _ → xs) ((x ∷2_) ∘ removeFM2 a xs) v
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      zz x {xs} kk (inl x₁) (inl x₂) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      zz x {xs} kk (inl x₁) (inr x₂) = sym (removeLaw a xs x₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ∙ (λ i → (x₁ (~ i)) ∷2 (removeFM2 a xs x₂)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      zz x {xs} kk (inr x₁) (inl x₂) = (λ i → (x₂ i) ∷2 (removeFM2 a xs x₁)) ∙ removeLaw a xs x₁ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      zz x {xs} kk (inr x₁) (inr x₂) = cong (x ∷2_) (kk x₁ x₂)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   inj∷2' : (xs ys : FMSet2 A) → (a : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → (p : a ∷2 xs ≡ a ∷2 ys) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   inj∷2' xs ys a p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡⟨ qq ⟩ removeFM2 a (a ∷2 ys) a∈'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡⟨ remove≡ a (a ∷2 ys) a∈' (∈head a ys) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ys ∎

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      a∈' = (subst (_∈FM2_ a) p (∈head a xs))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      qq : xs ≡ removeFM2 a (a ∷2 ys) a∈'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      qq i = removeFM2 a (p i) (coe0→i (λ i → a ∈FM2 (p i)) i (∈head a xs))

    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- removeFM2 a (p i) {!!} 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   zz : (x y : A) {xs : FMSet2 A} (b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          PathP (λ i → a ∈FM2 comm x y xs i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                x ∷2 ⊎.rec (λ _ → xs) (λ x₃ → y ∷2 b x₃) (fst (∈compute a xs) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             (fst (∈compute a (y ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             ⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                y ∷2 ⊎.rec (λ _ → xs) (λ x₃ → x ∷2 b x₃) (fst (∈compute a xs) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             (fst (∈compute a (x ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   zz = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈head : ∀ (x) (xs : FMSet2 A) → x ∈FM2 (x ∷2 xs)   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈head x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    ∣ inl refl ∣₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ y {xs} → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!} 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- _∈FM2'_ : A → FMSet2 A → hSet ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- _∈FM2'_ a = Rec.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      isGroupoidHSet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (⊥.⊥* , isProp→isSet isProp⊥*)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x b → ((x ≡ a) ⊎ fst b) , ⊎.isSet⊎ (grpA _ _) (snd b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y b → TypeOfHLevel≡ 2 (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = fst (b)})))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  (cong ua (equivEq (funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                λ _ → refl))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               ∙ uaInvEquiv (swap0and1⊎ {A = y ≡ a} {B = x ≡ a} {C = fst (b)})))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y z b → TypeOfHLevel≡ 2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (ua (swap0and2⊎ {A = x ≡ a} {B = y ≡ a} {C = z ≡ a} {D = fst (b)})))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y z b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (∙≡∙→square _ _ _ _ (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (⊎.elim (λ _ → refl) λ _ → refl))))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y z b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (∙≡∙→square _ _ _ _ (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (⊎.elim (λ _ → refl) λ _ → refl))))))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- _∈FM2_ : A → FMSet2 A → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- a ∈FM2 xs = fst (a ∈FM2' xs) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈head : ∀ (x) (xs : FMSet2 A) → x ∈FM2 (x ∷2 xs)   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈head x xs = inl refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈computeTest : ∀ {x} {xs : FMSet2 A} (a : A) → a ∈FM2 (x ∷2 xs) ≃ (x ≡ a) ⊎ (a ∈FM2 xs)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈computeTest a = idEquiv _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈comm : ∀ {ℓ'} {B : Type ℓ'} → ∀ x → (x₁ y : A) (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           {b0 : (x₁ ≡ x) ⊎ ((y ≡ x) ⊎ (x ∈FM2 xs)) → B}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         → {b1 : (y ≡ x) ⊎ ((x₁ ≡ x) ⊎ (x ∈FM2 xs)) → B}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           → {!!} --PathP (λ i → x ∈FM2 comm x₁ y xs i → B) b0 b1
            
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈comm {B = B} a x y xs p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ua→ {e = (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = a ∈FM2 xs })}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       {B = λ _ → B} {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- bringHead : ∀ a (xs : FMSet2 A) → a ∈FM2 xs → Σ (FMSet2 A) λ xs' → xs ≡ a ∷2 xs' 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- bringHead a = w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w : (xs : FMSet2 A) → a ∈FM2 xs → Σ (FMSet2 A) λ xs' → xs ≡ a ∷2 xs' 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (_ ∷2 xs') (inl p) = xs' , λ i → p i ∷2 xs'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (x' ∷2 xs) (inr x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       let (xs' , p) = w xs x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       in (x' ∷2 xs') , (cong (x' ∷2_) p ∙ comm _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (comm x₁ y xs i) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (comm-inv x₁ y xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (hexDiag x₁ y z xs i) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (hexU x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (hexL x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (trunc xs xs₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- removeFM2 : ∀ (x) (xs : FMSet2 A) → x ∈FM2 xs → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- removeFM2 x = Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ⊥.rec*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   w'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   λ _ → isGroupoidΠ λ _ → trunc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    w : (x₁ : A) {xs : FMSet2 A} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          (x ∈FM2 xs → FMSet2 A) → x ∈FM2 (x₁ ∷2 xs) → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    w x {xs} x₁ (inl x₂) = xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    w x x₁ (inr x₂) = x₁ x₂

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    w' : (x₁ y : A) {xs : FMSet2 A} (b : x ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           PathP (λ i → x ∈FM2 comm x₁ y xs i → FMSet2 A) (w x₁ (w y b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           (w y (w x₁ b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    w' x₁ y {xs} b = ua→ ?


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w : (xs : FMSet2 A) → x ∈FM2 xs → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (x₁ ∷2 xs) (inl x) = xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (x₁ ∷2 xs) (inr x) = w xs x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (comm x₁ y xs i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (comm-inv x₁ y xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (hexDiag x₁ y z xs i) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (hexU x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (hexL x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (trunc xs xs₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- inj∷2' : ∀ n → (xs : FMSet2 A) → len2 xs ≡ n → (ys : FMSet2 A) → (x : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          → (p : x ∷2 xs ≡ x ∷2 ys) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- inj∷2' xs ys x p = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- subst (λ z → x ∈FM2 z) (∈head x xs) p 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- let (xs' , px) = bringHead x (x ∷2 ys) (subst (x ∈FM2_) p (∈head x xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --     (ys' , py) = bringHead x (x ∷2 xs) (subst (x ∈FM2_) (sym p) (∈head x ys))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --     cLL : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --     cLL = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- in {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  ⊥.rec*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x x₁ → {!⊎.rec ? ?!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x y b i x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x y b i j x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x y z b i x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x y z b i j x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x y z b i j x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  λ _ → isGroupoidΠ λ _ → (isOfHLevelΣ 3 trunc λ _ →  isSet→isGroupoid (trunc _ _))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- _∈FM2_ : FMSet2 A → A → hSet ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- _∈FM2_ = Elim.f 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ _ → (⊥.⊥* , isProp→isSet isProp⊥*))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ x {xs} b a → ((x ≡ a) ⊎ fst (b a)) , ⊎.isSet⊎ (grpA _ _) (snd (b a)) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ x y b → funExt λ a → TypeOfHLevel≡ 2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                         {X = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                         {Y = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = fst (b a)})))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ x y {xs} b i j a →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          {p = TypeOfHLevel≡  2 {X = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                                {Y = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = fst (b a)}))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            {q = refl}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            {r = sym (TypeOfHLevel≡ 2 (ua (swap0and1⊎)))} {s = refl} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (cong ua (equivEq (funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                λ _ → refl))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           ∙ uaInvEquiv (swap0and1⊎ {A = y ≡ a} {B = x ≡ a} {C = fst (b a)}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          i j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --    ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --      (cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --        ∙ uaInvEquiv (swap0and1M b)) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!} -- (λ x y z b → TypeOfHLevel≡ 2 (ua (swap0and2M b)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!} -- (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                    (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                     (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                      (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!} -- (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                    (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                     (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                      (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ _ → isGroupoidΠ λ _ → isGroupoidHSet)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ×Vev≃⊎Fin→ : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ×Vev≃⊎Fin→ = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ : ∀ n → GroupHom (Perm n) (SymData n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ zero = Eliminators.recPG (Eli zero) _ (λ ()) (⊥.rec ∘ ¬PermR'zero)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (suc n) = Eliminators.recPG (Eli n) _ adjTransposition w 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w : _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w (zero invo) = adjTransposition²=idEquiv (+k zero)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w (zero braid) = adjTranspositionBraid
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w (zero (comm x)) = commTranspositions' x


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↔×_ : {A : Type ℓ} → ∀ {n} →  ×Vec A n → ×Vec A n → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↔×_ {n = zero} x x₁ = ⊥*  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↔×_ {n = one} x x₁ = ⊥* 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↔×_ {n = suc (suc n)} (x , y , xs) (x' , y' , xs') =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ((x ≡ y') × (y ≡ x')) ⊎ ((y , xs) ↔× (y' , xs) )




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPaΣ : ∀ {a₀₀ a₀₁ : Σ (hSet ℓ-zero) λ (T , _) → T → A} (a₀₋ : a₀₀ ≡ a₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {a₁₀ a₁₁ : Σ (hSet ℓ-zero) λ (T , _) → T → A} (a₁₋ : a₁₀ ≡ a₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → (s : Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (fst ∘ fst) a₀₋)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (fst ∘ fst) a₁₋)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (fst ∘ fst) a₋₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (fst ∘ fst) a₋₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → SquareP (λ i j → s i j → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong (snd) a₀₋)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (snd) a₁₋)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (snd) a₋₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (snd) a₋₁) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → Square a₀₋ a₁₋ a₋₀ a₋₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPaΣ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FMI* : (Agrp : isGroupoid A) → FMSet2 A → Σ (hSet ℓ-zero) λ (T , _) → T → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FMI* Agrp = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ((⊥.⊥ , isProp→isSet isProp⊥) , ⊥.elim)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x {xs} (b , f) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((Maybe (fst b) , isOfHLevelMaybe zero (snd b)) , Mb.elim _ x f) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x y (b , f) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ΣPathP (TypeOfHLevel≡ 2 (ua (swap0and1M b)) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         toPathP (funExt (Mb.elim _  (transportRefl _) (Mb.elim _ (transportRefl _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            λ _ → transportRefl _ ∙ cong f (transportRefl _))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x y (b , f) → mkPaΣ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ uaInvEquiv (swap0and1M b)) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    λ _ → isGroupoidΣ isGroupoidHSet λ _ → isGroupoidΠ λ _ → Agrp

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupFM2 : (Agrp : isGroupoid A) → (xs : FMSet2 A) → fst (fst (FMI* Agrp xs)) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupFM2 Agrp xs = snd (FMI* Agrp xs)




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupFM2 : (Agrp : isGroupoid A) → (xs : FMSet2 A) → fst (FMI xs) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupFM2 Agrp = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ⊥.elim
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x x₁ → Mb.rec x x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    λ _ → isGroupoidΠ λ _ → Agrp

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Elim.f 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (Fin zero , isSetFin)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ _ {xs} _ → Fin (suc (len2 xs)) , isSetFin)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ x y {xs} _ → TypeOfHLevel≡ 2 (ua swap0and1≃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ x y {xs} _ → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   (cong ua swap0and1≃=invEquivSwap0and1 ∙ uaInvEquiv swap0and1≃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ x y z {xs} _ → TypeOfHLevel≡ 2 (ua swap0and2≃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ x y z {xs} _ → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                     (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                      (({!!} ∙ {!!}) ∙  uaCompEquiv _ _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ _ → isGroupoidHSet)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isPropGrpSq : {A : I → I → Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (∀ i j → isGroupoid (A i j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 → {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               → isProp (SquareP A a₀₋ a₁₋ a₋₀ a₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isPropGrpSq x a₀₋ a₁₋ a₋₀ a₋₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emPerm : (xs : FMSet2 A) → EM₁ (SymData (len2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emPerm =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (Elim.f {B = λ xs → EM₁ (SymData (len2 xs))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      embase
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ _ → gh→em₂→ _ (sucPermFDMorphism _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x y {xs}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        → elimSet (SymData (len2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ _ → emsquash _ _) (emloop swap0and1≃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (lem1 (len2 xs)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x y {xs} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        elimProp _ (λ _ → isPropGrpSq (λ i j → emsquash) _ _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong emloop swap0and1≃=invEquivSwap0and1 ∙ emloop-sym _ swap0and1≃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x y z {xs} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        elimSet (SymData (len2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ _ → emsquash _ _) (emloop swap0and2≃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ((lem2 (len2 xs))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x y z {xs} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         elimProp _ (λ _ → isPropGrpSq (λ i j → emsquash) _ _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ((sym (emloop-comp _ _ _) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 cong emloop (equivEq (refl =→ refl =→ refl =→ refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ∙∙ emloop-comp _ _ _))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x y z {xs} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         elimProp _ (λ _ → isPropGrpSq (λ i j → emsquash) _ _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ((sym (emloop-comp _ _ _) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 cong emloop (equivEq (refl =→ refl =→ refl =→ refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ∙∙ emloop-comp _ _ _))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ _ → emsquash)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      )

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem1 : ∀ n → ∀ g → PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (emloop {Group = SymData (suc (suc n))} (sucPerm (sucPerm g)) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (emloop (sucPerm (sucPerm g)) i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (emloop swap0and1≃) (emloop swap0and1≃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem1 n g =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (sym (emloop-comp _ _ _) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 cong emloop (commSwap0and1SucSuc g)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ∙∙ emloop-comp _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem2 : ∀ n (g : fst (SymData n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (emloop {Group = (SymData (3 + n))} swap0and2≃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (emloop swap0and2≃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (emloop (sucPerm (sucPerm (sucPerm g))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (emloop ((sucPerm (sucPerm (sucPerm g)))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem2 n g = ∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ((sym (emloop-comp _ _ _) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 cong emloop (equivEq (refl =→ refl =→ refl =→ refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ∙∙ emloop-comp _ _ _))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- codes≃ : ∀ n → EM₁ (SymData n) → Σ Type₀ λ A → A ≃ fst (SymData n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- codes≃ n =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimSet _ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (_ , idEquiv _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm : (xs : FMSet2 A) → fst (SymData (len2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm xs = {! !}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paPerm : {xs ys : FMSet2 A} → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    →   Codes (SymData (len2 xs)) (emPerm xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        Codes (SymData (len2 ys)) (emPerm ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --Codes (SymData (len2 ys)) (emPerm ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paPerm {xs = xs} {ys} p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong (λ zs → Codes (SymData (len2 zs)) (emPerm zs)) p 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paPerm' : {xs ys : FMSet2 A} → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    →   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --Codes (SymData (len2 ys)) (emPerm ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paPerm' {xs = xs} {ys} p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!cong (λ zs → Codes (SymData (len2 zs)) (emPerm zs)) p !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- cong (λ zs → Codes (SymData (len2 zs)) (emPerm zs)) p 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zz : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zz = decode _ (emPerm ys) {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emK≃ : ∀ n → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      EM₁ (SymData n) → hSet ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emK≃ n = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emF : ∀ {n} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (x : EM₁ (SymData n)) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emF {n} = fst ∘ EMFam.EM₁HFam isSetFin


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- zzz : (Agrp : isGroupoid A) → (xs : FMSet2 A) → (x : A) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → (emF (emPerm xs) → A) → emF (emPerm (x ∷2 xs)) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- zzz Agrp = Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x _ _ → x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x {xs} f a g → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ _ → isGroupoidΠ3 λ _ _ _ → Agrp 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   pp : emPerm (x ∷2 xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         gh→em₂→ _ (sucPermFDMorphism _) (emPerm xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   pp = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ppp : emF (emPerm (x ∷2 xs)) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          emF (gh→em₂→ _ (sucPermFDMorphism _) (emPerm xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ppp = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupEm : (Agrp : isGroupoid A) → (x : FMSet2 A) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → emF (emPerm x) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupEm Agrp =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ ())
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    λ _ → isGroupoidΠ λ _ → Agrp 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- elimSet _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ x → snd (EMFam.EM₁HFam isSetFin x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  zero {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emK' : ∀ n → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (x : EM₁ (SymData (suc n))) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emK' n =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimSet _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x → snd (EMFam.EM₁HFam isSetFin x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    zero {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paK : {xs ys : FMSet2 A} → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → fst (SymData (len2 ys)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paK {xs = xs} {ys} p = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- zz : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- zz = {!encode (SymData (len2 ys)) ?!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paUnwind : (x y : A) (xs ys : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (p : x ∷2 xs ≡ y ∷2 ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              → Σ (singl xs) λ (xs' , p') → cong (x ∷2_) p' ∙ {!!} ≡ p 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paUnwind = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- headInsert : (x : A) → (xs : FMSet2 A) → (Fin (len2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 → singl (x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- headInsert = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paMid : (x y : A) (xs ys : FMSet2 A) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (p : x ∷2 xs ≡ y ∷2 ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              → Σ (Σ (FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  λ zs → (xs ≡ y ∷2 zs) × (x ∷2 zs ≡ ys))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  λ (zs , (q , r)) → (cong (x ∷2_) q ∙∙ comm x y zs ∙∙ cong (y ∷2_) r) ≡ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paMid = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   inj∷2 : (xs ys : FMSet2 A) → (x : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → x ∷2 xs ≡ x ∷2 ys → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   inj∷2 = ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- (ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    (λ _ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    (λ x x₁ x₂ → {!!} ∘ cong len2  )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    λ _ → isSetΠ2 λ _ _ → trunc _ _ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ x {xs} b →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ x' {ys} b' y' p →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         λ _ → isSetΠ2 λ _ _ → trunc _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ _ → isSetΠ3 λ _ _ _ → trunc _ _ 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Rec.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (isSet→isGroupoid isSetℕ) zero (λ _ → suc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ → refl) (λ _ _ _ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ _ → refl) (λ _ _ _ _ → refl) (λ _ _ _ _ → refl)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RecSet.f isSetℕ zero (λ _ → suc) (λ _ _ _ → refl) (λ _ _ _ _ → refl)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- open import Cubical.HITs.EilenbergMacLane1 as EM

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (A : Type ℓ) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- open import Cubical.Data.List.FinData


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen : ℕ → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen n = Σ (FMSet2 A) λ x → len2 x ≡ n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {A : Type ℓ} where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isSetLofLA : ∀ n → isSet (ListOfLen A n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isSetLofLA n = isOfHLevelListOfLen 0 isSetA n 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen≡ : ∀ {n} → {x y : FMSet2OfLen A n} → fst x ≡ fst y → x ≡ y 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen≡ = Σ≡Prop λ _ → isSetℕ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isGroupoidFMSet2OfLen : ∀ n → isGroupoid (FMSet2OfLen A n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isGroupoidFMSet2OfLen n = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (isOfHLevelΣ 3 trunc λ _ → isSet→isGroupoid (isProp→isSet (isSetℕ _ _)))

