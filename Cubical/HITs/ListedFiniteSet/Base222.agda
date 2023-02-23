{-# OPTIONS --safe  #-} 
module Cubical.HITs.ListedFiniteSet.Base222 where

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

open import Cubical.Data.FinData

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

-- Σsn : {B : A → Type ℓ} → (e : A ≃ A) → Σ A (B ∘ fst e) ≡ Σ A B 
-- Σsn {A = A} {B = B} e i = Σ (ua e i) (B ∘ ua-unglue e i)


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

-- Mb^ : ℕ → (hSet ℓ-zero) → (hSet ℓ-zero) 
-- Mb^ zero x₁ = x₁
-- Mb^ (suc x) b' =
--   let b = Mb^ x b'
--   in Maybe (fst b) , isOfHLevelMaybe zero (snd b)

-- swap0and1Mf : (b : hSet ℓ-zero) → fst (Mb^ 2 b) → fst (Mb^ 2 b)  
-- swap0and1Mf b nothing = just nothing
-- swap0and1Mf b (just nothing) = nothing
-- swap0and1Mf b (just (just x)) = (just (just x))

-- swap0and1M : (b : hSet ℓ-zero) → fst (Mb^ 2 b) ≃ fst (Mb^ 2 b)  
-- swap0and1M b = involEquiv {f = swap0and1Mf b}
--    (Mb.elim _ refl (Mb.elim _ refl λ _ → refl) )

-- swap0and2Mf : (b : hSet ℓ-zero) → fst (Mb^ 3 b) → fst (Mb^ 3 b)  
-- swap0and2Mf b nothing = (just (just nothing))
-- swap0and2Mf b (just nothing) = just nothing
-- swap0and2Mf b (just (just nothing)) = nothing
-- swap0and2Mf b (just (just (just x))) = (just (just (just x)))

-- swap0and2M : (b : hSet ℓ-zero) → fst (Mb^ 3 b) ≃ fst (Mb^ 3 b)  
-- swap0and2M b = involEquiv {f = swap0and2Mf b}
--    (Mb.elim _ refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)) )

-- congMUA : (b : hSet ℓ-zero) →
--              cong Maybe (ua (swap0and1M b)) ≡
--               ua (congMaybeEquiv (swap0and1M b)) 
-- congMUA b = isInjectiveTransport
--   (funExt (Mb.elim _ refl λ _ → refl))

-- FMI : FMSet2 A → hSet ℓ-zero
-- FMI =
--   Elim.f 
--    (⊥.⊥ , isProp→isSet isProp⊥)
--    (λ x {xs} b → Maybe (fst b) , isOfHLevelMaybe zero (snd b) )
--    (λ x y b → TypeOfHLevel≡ 2 (ua (swap0and1M b)))
--    (λ x y {xs} b →
--       ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--         (cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
--           ∙ uaInvEquiv (swap0and1M b)) )
--    (λ x y z b → TypeOfHLevel≡ 2 (ua (swap0and2M b)))
--    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--                       (∙≡∙→square _ _ _ _
--                        (isInjectiveTransport
--                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))


--    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--                       (∙≡∙→square _ _ _ _
--                        (isInjectiveTransport
--                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))
--    (λ _ → isGroupoidHSet)

-- FMIfin : ∀ (xs : FMSet2 A) → isFinSet (fst (FMI xs))
-- FMIfin xs = (len2 xs) , 
--   (ElimProp.f {B = λ xs → PT.∥ fst (FMI xs) ≃ F.Fin (len2 xs) ∥₁}
--     PT.∣ idEquiv _ ∣₁
--      (λ _ {_} →
--       PT.map
--        λ e → congMaybeEquiv e
--           ∙ₑ isoToEquiv
--               (iso Maybe→SumUnit
--                    SumUnit→Maybe
--                    SumUnit→Maybe→SumUnit
--                    Maybe→SumUnit→Maybe)
          
--           )
--        (λ xs → PT.squash₁) xs)

--   where open SumUnit

-- ×Vec : (A : Type ℓ) → ℕ → Type ℓ
-- ×Vec A zero = Unit*
-- ×Vec A (suc n) = A × ×Vec A n

-- tabulate× : ∀ {n} → (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A) → ×Vec A n
-- tabulate× {n = zero} _ = tt*
-- tabulate× {n = suc n} x = x nothing , tabulate× (x ∘ just)

-- lookup× : ∀ {n} → ×Vec A n → (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A) 
-- lookup× {n = zero} x ()
-- lookup× {n = suc n} x = Mb.rec (fst x) (lookup× (snd x))

-- Iso-tabulate×-lookup× : ∀ {n} → Iso (×Vec A n) (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A)
-- Iso.fun Iso-tabulate×-lookup× = lookup×
-- Iso.inv Iso-tabulate×-lookup× = tabulate×
-- Iso.rightInv (Iso-tabulate×-lookup× {n = zero}) b i ()
-- Iso.rightInv (Iso-tabulate×-lookup× {n = suc n}) b i nothing = b nothing
-- Iso.rightInv (Iso-tabulate×-lookup× {n = suc n}) b i (just x) =
--   Iso.rightInv (Iso-tabulate×-lookup× {n = n}) (b ∘ just) i x
-- Iso.leftInv (Iso-tabulate×-lookup× {n = zero}) a = refl
-- Iso.leftInv (Iso-tabulate×-lookup× {n = suc n}) a =
--  ΣPathP (refl ,
--   Iso.leftInv (Iso-tabulate×-lookup× {n = n}) (snd a))


-- ua→P : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {B : (i : I) → (ua e i) → Type ℓ'}
--   {f₀ : ∀ a₀ → B i0 a₀} {f₁ : ∀ a₁ → B i1 a₁}
--   → ((a : A₀) → PathP (λ i → B i (ua-gluePath e (cong (e .fst) (refl {x = a})) i))
--         (f₀ a) (f₁ (e .fst a)))
--   → PathP (λ i → (g : ua e i) → B i g) f₀ f₁
-- ua→P {e = e} {B = B} {f₀ = f₀} {f₁} h i = {!!}
--   -- comp
--   --   (λ k → {!!})
--   --   {!!}
--   --   {!!}

--   -- hcomp
--   --   (λ j → λ
--   --     { (i = i0) → {!f₀ a!} --  B i0 a
--   --     ; (i = i1) → {!f₁ (lem a j)!}  --B i1 (lem a j)
--   --     })
--   --   {!(h (transp (λ j → ua e (~ j ∧ i)) (~ i) a) i)!}  
--   --  --  (h (transp (λ j → ua e (~ j ∧ i)) (~ i) a) i)
--    where
    
--      lem : ∀ a₁ → e .fst (transport (sym (ua e)) a₁) ≡ a₁
--      lem a₁ i = secEq e (transportRefl a₁ i) i

 
--      sqT : Square
--               (λ i → ∀ a → B i (ua-gluePath e (cong (e .fst) (refl {x = a})) i))
--               (λ i → (g : ua e i) → B i g)
--               (λ j → ∀ a₀ → B i0 a₀)
--               {!!} -- (λ j → (g : ua e i) → B i1 (ua-gluePath e (cong (e .fst) (refl {x = g})) j))
              
--      sqT = {!!}

--      -- bb : B i (ua-gluePath e (cong (e .fst) refl) i)
--      -- bb = (h (transp (λ j → ua e (~ j ∧ i)) (~ i) a) i)

swap0and1⊎f : {A B C : Type ℓ} → A ⊎ (B ⊎ C) → B ⊎ (A ⊎ C)  
swap0and1⊎f (inl x) = (inr (inl x))
swap0and1⊎f (inr (inl x)) = (inl x)
swap0and1⊎f (inr (inr x)) = (inr (inr x))

swap0and1⊎fInvol : {A B C : Type ℓ} → ∀ x → swap0and1⊎f (swap0and1⊎f {A = A} {B} {C} x) ≡ x
swap0and1⊎fInvol (inl x) = refl
swap0and1⊎fInvol (inr (inl x)) = refl
swap0and1⊎fInvol (inr (inr x)) = refl

swap0and1⊎ :  {A B C : Type ℓ} → A ⊎ (B ⊎ C) ≃ B ⊎ (A ⊎ C)  
swap0and1⊎ =
  isoToEquiv (iso swap0and1⊎f swap0and1⊎f swap0and1⊎fInvol swap0and1⊎fInvol)


ua→' : ∀ {ℓ'} {A₀ A₁ : Type ℓ} {B : Type ℓ'} → (e : A₀ ≃ A₁)
            (f₁ : A₁ → B)
          → PathP (λ i → ua e i →  B) (f₁ ∘ fst e) f₁
ua→' e f₁ i = f₁ ∘ ua-unglue e i

ua→'' : ∀ {A₀ A₁ : Type ℓ} → (e : A₀ ≃ A₁)
       
          → PathP (λ i → A₀ → ua e i ) (idfun _) (fst e)
ua→'' e i x = ua-glue e i (λ { (i = i0) → x }) (inS (fst e x))

-- ua→''' : ∀ {ℓ'} {A₀ A₁ : Type ℓ} {B : Type ℓ'} → (e : A₀ ≃ A₁)
       
--           → PathP (λ i → A₀ → ua e i ) (idfun _) (fst e)
-- ua→''' e i x = ua-glue e i (λ { (i = i0) → {!!}}) (inS {!!})

glueSwap01 :  (A B C : Type ℓ) →
      PathP (λ i₁ → A ⊎ (B ⊎ C) → ua (swap0and1⊎ {A = B} {A} {C}) i₁)
         (fst swap0and1⊎) (idfun (A ⊎ (B ⊎ C)))
glueSwap01 A B C i x = 
   glue   (λ { (i = i0) → swap0and1⊎f x
                          ; (i = i1) → x
                          }) (swap0and1⊎fInvol x i)

glueSwap01' :  (A B C : Type ℓ) →
      PathP (λ i₁ → B ⊎ (A ⊎ C) → ua swap0and1⊎ i₁)
      (idfun (B ⊎ (A ⊎ C))) (fst swap0and1⊎)
glueSwap01' A B C i x =
   glue   (λ { (i = i0) → x
                          ; (i = i1) → swap0and1⊎f x
                          }) (swap0and1⊎f x)


swap0and1⊎fInvolSq : (A B C : Type ℓ) →
             ua (swap0and1⊎ {A = A} {B} {C}) ≡ sym (ua (swap0and1⊎ {A = B} {A} {C}))
swap0and1⊎fInvolSq A B C i j =
   Glue (ua (swap0and1⊎ {A = B} {A} {C}) i)
                λ { (j = i0) → (A ⊎ (B ⊎ C)) ,
                    ΣPathPProp {A = λ i → (A ⊎ (B ⊎ C)) → ua swap0and1⊎ i}
                                {B = λ i → isEquiv}
                              {u = swap0and1⊎ {A = A} {B} {C}} {v = idEquiv (A ⊎ (B ⊎ C))}
                              isPropIsEquiv (glueSwap01 A B C)
                               i
                  ; (j = i1) → (B ⊎ (A ⊎ C)) ,
                     ΣPathPProp {A = λ i → (B ⊎ (A ⊎ C)) → ua swap0and1⊎ i}
                                {B = λ i → isEquiv}
                              {u = idEquiv (B ⊎ (A ⊎ C))}
                              {v = swap0and1⊎}
                              isPropIsEquiv 
                               (glueSwap01' A B C) i }
                               

commSym∈SqP : (A B C : Type ℓ) →
                   SquareP (λ i j →  swap0and1⊎fInvolSq A B C i j →
                           ua (swap0and1⊎ {A = B} {A} {C}) i)
                            (λ i → ua-unglue (swap0and1⊎ {A = A} {B} {C}) i)
                            (λ i → ua-unglue (swap0and1⊎ {A = B} {A} {C}) (~ i))
                            (glueSwap01 A B C)
                            (glueSwap01' A B C)
commSym∈SqP A B C i j = unglue (j ∨ ~ j)



swap0and2⊎f : {A B C D : Type ℓ} → A ⊎ (B ⊎ (C ⊎ D)) → C ⊎ (B ⊎ (A ⊎ D))  
swap0and2⊎f (inl x) = (inr (inr (inl x)))
swap0and2⊎f (inr (inl x)) = (inr (inl x))
swap0and2⊎f (inr (inr (inl x))) = (inl x)
swap0and2⊎f (inr (inr (inr x))) = (inr (inr (inr x)))

swap0and2⊎fInvol : {A B C D : Type ℓ} → ∀ x → swap0and2⊎f (swap0and2⊎f {A = A} {B} {C} {D} x) ≡ x
swap0and2⊎fInvol (inl x) = refl
swap0and2⊎fInvol (inr (inl x)) = refl
swap0and2⊎fInvol (inr (inr (inl x))) = refl
swap0and2⊎fInvol (inr (inr (inr x))) = refl

swap0and2⊎ :  {A B C D : Type ℓ} → A ⊎ (B ⊎ (C ⊎ D)) ≃ C ⊎ (B ⊎ (A ⊎ D))
swap0and2⊎ =
  isoToEquiv (iso swap0and2⊎f swap0and2⊎f swap0and2⊎fInvol swap0and2⊎fInvol)

sw12SqU : (A B C D : Type ℓ) →
            Square
            (λ i → B ⊎ ua (swap0and1⊎ {A = A} {B = C} {C = D})  i)
            (ua (swap0and2⊎ {A = A} {B = B} {C = C} {D = D}))
            (ua (swap0and1⊎ {A = B} {A} {C ⊎ D}))
            (ua (swap0and1⊎ {A = B} {C} {A ⊎ D}))
sw12SqU A B C D = comm→PathP (isInjectiveTransport (funExt z)) 

  where
    z :  (x : B ⊎ (A ⊎ (C ⊎ D))) →
      transport ((λ i → ua (swap0and1⊎ {A = B} {A} {C ⊎ D}) i)
            ∙ ua (swap0and2⊎ {A = A} {B = B} {C = C} {D = D})) x ≡
      transport ((λ i → B ⊎ ua (swap0and1⊎ {A = A} {B = C} {C = D}) i)
        ∙ (λ i → ua (swap0and1⊎ {A = B} {C} {A ⊎ D}) i)) x
    z (inl x) = refl
    z (inr (inl x)) = refl
    z (inr (inr (inl x))) = refl
    z (inr (inr (inr x))) = refl


-- SqP→ : ∀ {ℓ'} {B : Type ℓ'} → (A : I → I → Type ℓ) (isSetA : ∀ i j → isSet (A i j))
--     {a₀₀ : A i0 i0 → B} {a₀₁ : A i0 i1 → B} (a₀₋ : PathP (λ j → A i0 j → B) a₀₀ a₀₁)
--     {a₁₀ : A i1 i0 → B} {a₁₁ : A i1 i1 → B} (a₁₋ : PathP (λ j → A i1 j → B) a₁₀ a₁₁)
--     (a₋₀ : PathP (λ i → A i i0 → B) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1 → B) a₀₁ a₁₁)
    
--     → SquareP (λ i j → A i j → B) a₀₋ a₁₋ a₋₀ a₋₁
-- SqP→ A isSetA a₀₋ a₁₋ a₋₀ a₋₁ = {!!}


module ⊎Path2 {ℓ} {A : Type ℓ} {B : Type ℓ} {C : Type ℓ} where

  Cover : A ⊎ (B ⊎ C) → A ⊎ (B ⊎ C) → Type ℓ
  Cover (inl x) (inl x₁) = x ≡ x₁
  Cover (inl x) (inr a') = Lift ⊥
  Cover (inr a) (inl x) = Lift ⊥
  Cover (inr (inl x)) (inr (inl x₁)) = x ≡ x₁
  Cover (inr (inl x)) (inr (inr x₁)) = Lift ⊥
  Cover (inr (inr x)) (inr (inl x₁)) = Lift ⊥
  Cover (inr (inr x)) (inr (inr x₁)) = x ≡ x₁

  reflCode : ∀ c → Cover c c
  reflCode (inl _) = refl
  reflCode (inr (inl _)) = refl
  reflCode (inr (inr _)) = refl


  decode'' : ∀ c c' → Cover c c' → c ≡ c'
  decode'' (inl x₁) (inl x₂) = cong inl
  decode'' (inr (inl x₁)) (inr (inl x₂)) = cong (inr ∘ inl)
  decode'' (inr (inr x₁)) (inr (inr x₂)) = cong (inr ∘ inr)

  decode''Sec : ∀ c → decode'' c c (reflCode c) ≡ refl
  decode''Sec (inl x) = refl
  decode''Sec (inr (inl x)) = refl
  decode''Sec (inr (inr x)) = refl

  IsoCoverPath : ∀ {c c'} → Iso (Cover c c') (c ≡ c') 
  Iso.fun (IsoCoverPath ) = decode'' _ _
  Iso.inv (IsoCoverPath {c} {c'}) = J (λ c' _ → Cover c c') (reflCode _)
  
  Iso.rightInv (IsoCoverPath {c} {c'}) = 
    J (λ c' b → decode'' _ _
      (transp (λ i → Cover c (b i)) i0 (reflCode c))
      ≡ b) (cong (decode'' c c) (transportRefl _) ∙
       decode''Sec c)
  Iso.leftInv (IsoCoverPath {inl x} {inl x₁}) =
   J (λ x₁ a → transp (λ i → x ≡ a i) i0 (λ _ → x) ≡ a) (transportRefl _)
  Iso.leftInv (IsoCoverPath {inr (inl x)} {inr (inl x₁)}) =
      J (λ x₁ a → transp (λ i → x ≡ a i) i0 (λ _ → x) ≡ a) (transportRefl _)
  Iso.leftInv (IsoCoverPath {inr (inr x)} {inr (inr x₁)}) =
          J (λ x₁ a → transp (λ i → x ≡ a i) i0 (λ _ → x) ≡ a) (transportRefl _)

  CoverPath≃ : ∀ {c c'} →  (Cover c c') ≃ (c ≡ c') 
  CoverPath≃ = isoToEquiv IsoCoverPath

module ∈FMSet2 {A : Type ℓ} (grpA : isGroupoid A) where


  hSet≡ : {A B : Type ℓ} {isSetA : isSet A} {isSetB : isSet B} → A ≡ B →
              Path (hSet ℓ) (A , isSetA) (B , isSetB)  
  fst (hSet≡ p i) = p i
  snd (hSet≡  {isSetA = isSetA} {isSetB} p i) =
    isProp→PathP
     (λ i → isPropIsSet {A = p i})
     isSetA
     isSetB i

  ∈FM2R : A → RRec (isGroupoidHSet {ℓ = ℓ})
  RRec.[]* (∈FM2R a) = ⊥.⊥* , isProp→isSet isProp⊥*
  RRec._∷*_ (∈FM2R a) = λ x b → ((x ≡ a) ⊎ fst b) , ⊎.isSet⊎ (grpA _ _) (snd b)
  RRec.comm* (∈FM2R a) = (λ x y b → hSet≡ (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = fst (b)})))
  RRec.comm-inv* (∈FM2R a) = (λ x y b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
    (swap0and1⊎fInvolSq (x ≡ a) (y ≡ a) (fst b)))
  RRec.hexDiag* (∈FM2R a) = (λ x y z b → hSet≡
     (ua (swap0and2⊎ {A = x ≡ a} {B = y ≡ a} {C = z ≡ a} {D = fst (b)})))
  RRec.hexU* (∈FM2R a) = (λ x y z b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
         (∙≡∙→square _ _ _ _ (isInjectiveTransport
              ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
             (⊎.elim (λ _ → refl) λ _ → refl))))))))
  RRec.hexL* (∈FM2R a) = (λ x y z b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
         (∙≡∙→square _ _ _ _ (isInjectiveTransport
              ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
             (⊎.elim (λ _ → refl) λ _ → refl))))))))

                 
  _∈FM2_ : A → FMSet2 A → Type ℓ
  a ∈FM2 xs = fst (RRec.f (∈FM2R a) xs)

  ww : ∀ {a} (x : A) {xs : FMSet2 A} → (a ∈FM2 xs → FMSet2 A) → a ∈FM2 (x ∷2 xs) → FMSet2 A
  ww x {xs} x₁ (inl x₂) = xs
  ww x x₁ (inr x₂) = x ∷2 x₁ x₂


  removeFM2 : ∀ a (xs : FMSet2 A) → a ∈FM2 xs → FMSet2 A
  removeFM2 a = RElim.f w

     where


       wComm' : I → (x y : A) {xs : FMSet2 A} (b : a ∈FM2 xs → FMSet2 A) →
           (ww x {y ∷2 xs} (ww y {xs} b)) ≡ 
                (ww y {x ∷2 xs} (ww x {xs} b)) ∘ swap0and1⊎f
       wComm' _ x y {xs} b i (inl x₁) = y ∷2 xs
       wComm' _ x y {xs} b i (inr (inl x₁)) = x ∷2 xs
       wComm' j x y {xs} b i (inr (inr x₁)) = comm-inv x y (b x₁) j i
         
       ji0Sq : (x y : A) {xs : FMSet2 A} (b : a ∈FM2 xs → FMSet2 A) →
                  Square {A = a ∈FM2 (x ∷2 y ∷2 xs) → FMSet2 A}
                     refl
                     (λ k' → wComm' i0 x y {xs} b (~ k'))
                     (λ k x₁ → ww y {x ∷2 xs} (ww x {xs} b) (swap0and1⊎fInvol (swap0and1⊎f x₁) k))
                     λ k x₁ → wComm' i0 x y {xs} b (~ k) (swap0and1⊎fInvol x₁ k)
       ji0Sq x y {xs} b k k' (inl x₁) = y ∷2 xs
       ji0Sq x y {xs} b k k' (inr (inl x₁)) = x ∷2 xs
       ji0Sq x y {xs} b k k' (inr (inr x₁)) = comm x y (b x₁) (~ k' ∨ ~ k)

       ji0Sq' : (x y : A) {xs : FMSet2 A} (b : a ∈FM2 xs → FMSet2 A) →
                  Square {A = a ∈FM2 (y ∷2 x ∷2 xs) → FMSet2 A}
                     (λ i x₁ → wComm' i1 x y {xs} b (~ i) (swap0and1⊎f x₁))
                     refl
                     (λ k x₁ → ww y {x ∷2 xs} (ww x {xs} b) (swap0and1⊎fInvol x₁ k))
                     (sym (wComm' i0 y x {xs} b))
       ji0Sq' x y {xs} b k i (inl x₁) = x ∷2 xs
       ji0Sq' x y {xs} b k i (inr (inl x₁)) = y ∷2 xs
       ji0Sq' x y {xs} b k i (inr (inr x₁)) = comm y x (b x₁) (i ∧ ~ k)

       wHex :  (x y z : A) {xs : FMSet2 A} (b : a ∈FM2 xs → FMSet2 A) →
                ww x {y ∷2 z ∷2 xs} (ww y {z ∷2 xs} (ww z {xs} b))
                  ≡ ww z {y ∷2 x ∷2 xs} (ww y {x ∷2 xs} (ww x {xs} b)) ∘ swap0and2⊎f
       wHex x y z {xs} b i (inl x₁) = comm y z xs i
       wHex x y z {xs} b i (inr (inl x₁)) = comm x z xs i
       wHex x y z {xs} b i (inr (inr (inl x₁))) = comm x y xs i
       wHex x y z b i (inr (inr (inr x₁))) = hexDiag x y z (b x₁) i

       w : RElim λ z → a ∈FM2 z → FMSet2 A
       RElim.[]* w = ⊥.rec*
       RElim._∷*_ w = ww
       (RElim.comm* w) x y {xs} b = wComm' i0 x y {xs} b ◁ ua→' _ _ 
       (RElim.comm-inv* w) x y {xs} b i j = 
         hcomp
           (λ k → λ { (j = i0) → λ x₁ → wComm' i0 x y {xs} b (~ (i ∨ k))
                                          (swap0and1⊎fInvol x₁ (i ∨ k))
                    ; (j = i1) → ji0Sq' x y {xs} b k i 
                    ; (i = i0) → 
                    hcomp
                         (λ k' → λ {
                             (j = i0) → ji0Sq x y {xs} b k k'
                            ;(j = i1) → ww y {x ∷2 xs} (ww x {xs} b) ∘ (funExt swap0and1⊎fInvol k)
                            ;(k = i0) → ua→' swap0and1⊎
                                 ((ww y {x ∷2 xs} (ww x {xs} b))
                                   ∘ swap0and1⊎f ∘ swap0and1⊎f ) j
                                      
                            }) ((ww y {x ∷2 xs} (ww x {xs} b))
                                      ∘ (funExt swap0and1⊎fInvol (k))
                                        ∘ ua-unglue swap0and1⊎ j)
                    })
                 ((wComm' j x y {xs} b (~ i) ∘ unglue (i ∨ ~ i)) ∘ unglue (j ∨ ~ j))
            
       RElim.hexDiag* w x y z b = 
          wHex x y z b ◁ ua→' _ _
       RElim.hexU* w = {!!}
       RElim.hexL* w = {!!}
       RElim.trunc* w = λ _ → isGroupoidΠ λ _ → trunc
    

  removeLaw : ∀ a (xs : FMSet2 A) → (u : a ∈FM2 xs) →
               a ∷2 removeFM2 a xs u ≡ xs
  removeLaw a = RElimSet'.f w
    where

      wwRL : (x : A) {xs : FMSet2 A} →
         ((u : a ∈FM2 xs) → a ∷2 removeFM2 a xs u ≡ xs) →
         (u : a ∈FM2 (x ∷2 xs)) → a ∷2 removeFM2 a (x ∷2 xs) u ≡ x ∷2 xs
      wwRL x {xs} x₁ (inl x₂) i = x₂ (~ i) ∷2 xs 
      wwRL x x₁ (inr x₂) = comm _ _ _ ∙ cong (x ∷2_) (x₁ x₂)

      w : RElimSet' (λ z → (u : a ∈FM2 z) → a ∷2 removeFM2 a z u ≡ z)
      RElimSet'.[]* w ()
      RElimSet'._∷*_ w = wwRL
      RElimSet'.comm* w x y {xs} b = 
        funExtDep (λ p → flipSquare 
                 ( cong (congP λ i → (a ∷2_) ∘ (removeFM2 a (comm x y xs i)))
                          (sym (Iso.leftInv (compIso (PathPIsoPath _ _ _)
                              (invIso (⊎Path2.IsoCoverPath))) p))
                 ◁ flipSquare (z' (invEq (⊎Path2.CoverPath≃) (fromPathP p)))))
         where

           z' : {x₀ : a ∈FM2 (x ∷2 y ∷2 xs)} {x₁ : a ∈FM2 (y ∷2 x ∷2 xs)}
                    (p : ⊎Path2.Cover (transport ((λ z₁ → a ∈FM2 comm x y xs z₁)) x₀) x₁) →
                    PathP
                    (λ i → a ∷2 removeFM2 a (comm x y xs i)
                      (toPathP {A = (λ z₁ → a ∈FM2 comm x y xs z₁)}
                          {x = x₀} {y = x₁} (⊎Path2.decode'' _ _ p) i)
                      ≡ comm x y xs i)
                    ((w RElimSet'.∷* x) ((w RElimSet'.∷* y) b) x₀)
                   ((w RElimSet'.∷* y) ((w RElimSet'.∷* x) b) x₁)
                    
           z' {inl x'} {inr (inl x₁)} p i j =
               hcomp
                 (λ k → λ { (i = i0) → (sym (transportRefl _) ∙ p) (~ k) (~ j) ∷2 y ∷2 xs
                          ; (j = i0) → a ∷2 compPathRefl {x = y ∷2 xs} k i
                          ; (j = i1) → comm (x₁ (~ k ∧ i)) y xs i } )
                       (comm (x₁ (i ∨ ~ j)) y xs (i ∧ j))

           z' {inr (inl x)} {inl x₁} p = {!!}
           z' {inr (inr x)} {inr (inr x₁)} p = {!!}
  
      RElimSet'.trunc* w xs = isSetΠ λ _ → trunc _ _

  removeIsoLem : {a : A}
                 (xs : FMSet2 A) (∈xs : a ∈FM2 xs) →
               transport (λ i → a ∈FM2 removeLaw a xs ∈xs i) (inl (λ _ → a)) ≡ ∈xs
  removeIsoLem {a} = RElimProp'.f r
    where
      r : RElimProp' _
      RElimProp'.[]* r ()
      RElimProp'._∷*_ r =
             (λ a' {xs} f → ⊎.elim
              (λ a₁ → cong inl (fromPathP {A = (λ i → a₁ (~ i) ≡ a)} λ i j → a₁ (j ∨ ~ i)))
        λ y → cong inr
         ( cong (transport (cong (a ∈FM2_) (removeLaw a (xs) y)) ∘ inl) 
            (λ i → transportRefl (transportRefl refl i) i  ))
         ∙ cong inr (f y))
      RElimProp'.trunc* r =       λ xs → isPropΠ λ _ → snd (RRec.f (∈FM2R a) xs) _ _



      
  removeIso : ∀ a → Iso (Σ (FMSet2 A) (a ∈FM2_)) (FMSet2 A )
  Iso.fun (removeIso a) (xs , ∈xs) = removeFM2 a xs ∈xs
  Iso.inv (removeIso a) xs = a ∷2 xs , inl refl
  Iso.rightInv (removeIso a) xs = refl
  Iso.leftInv (removeIso a) (xs , ∈xs) =
   ΣPathP (removeLaw a xs ∈xs , toPathP (removeIsoLem xs ∈xs))

  -- isEqLem : (a : A) → (xs : FMSet2 A) → {!!}
  -- isEqLem a xs = {!!}
  --   where
  --     zz : isContr (fiber (λ z → a ∷2 z , inl (λ _ → a)) (a ∷2 xs , inl (λ _ → a)))
  --     zz = isoToIsEquiv (invIso (removeIso a)) .equiv-proof (a ∷2 xs , inl refl)


--   -- remove≡ : ∀ a (xs : FMSet2 A) → (u v : a ∈FM2 xs) →
--   --              removeFM2 a xs u ≡ removeFM2 a xs v
--   -- remove≡ = {!!}
  
-- --       ∈head : ∀ (x) (xs : FMSet2 A) → x ∈FM2 (x ∷2 xs)   
-- --       ∈head x xs = inl refl

-- --       remove≡ : ∀ a (xs : FMSet2 A) → (u v : a ∈FM2 xs) →
-- --                    removeFM2 a xs u ≡ removeFM2 a xs v
-- --       remove≡ a =
-- --         ElimSet.f
-- --           (λ { (lift ()) })
-- --           (λ x {xs} kk u v → {!ua→ ?!}
-- --              -- zz x {xs} kk (fst (∈compute {x = x} a xs) u)
-- --              --              (fst (∈compute {x = x} a xs) v)
-- --                           )
-- --           {!!}
-- --           {!!}
-- --           λ _ → isSetΠ2 λ _ _ → trunc _ _


-- --       inj∷2' : (xs ys : FMSet2 A) → (a : A)
-- --                → (p : a ∷2 xs ≡ a ∷2 ys) 
-- --                 → xs ≡ ys
-- --       inj∷2' xs ys a p =
-- --          xs
-- --           ≡⟨ qq ⟩ removeFM2 a (a ∷2 ys) a∈'
-- --           ≡⟨ remove≡ a (a ∷2 ys) a∈' (∈head a ys) ⟩
-- --          ys ∎

-- --        where
-- --          a∈' = (subst (_∈FM2_ a) p (∈head a xs))

-- --          qq : xs ≡ removeFM2 a (a ∷2 ys) a∈'
-- --          qq i = removeFM2 a (p i) (coe0→i (λ i → a ∈FM2 (p i)) i (∈head a xs))



-- -- -- -- -- -- --   ∈FM2'' : A → FMSet2 A → Type ℓ

-- -- -- -- -- -- --   isSet∈FM2'' : ∀ a xs → isSet (∈FM2'' a xs)

-- -- -- -- -- -- --   ∈FM2'' a [] = ⊥*
-- -- -- -- -- -- --   ∈FM2'' a (x ∷2 x₁) = (x ≡ a) ⊎ ∈FM2'' a x₁
-- -- -- -- -- -- --   ∈FM2'' a (comm x y xs i) = ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = ∈FM2'' a xs}) i
-- -- -- -- -- -- --   ∈FM2'' a (comm-inv x y xs i i₁) =
-- -- -- -- -- -- --     swap0and1⊎fInvolSq (x ≡ a) (y ≡ a) (∈FM2'' a xs) i i₁
-- -- -- -- -- -- --   ∈FM2'' a (hexDiag x y z xs i) =
-- -- -- -- -- -- --      ua (swap0and2⊎ {A = x ≡ a} {B = y ≡ a} {C = z ≡ a} {D = ∈FM2'' a xs}) i
-- -- -- -- -- -- --   ∈FM2'' a (hexU x y z xs i i₁) = {!!}
-- -- -- -- -- -- --      -- (∙≡∙→square {!!} {!!} {!!} (λ i₂ →
-- -- -- -- -- -- --      --   ua (swap0and2⊎ {A = x ≡ a} {B = y ≡ a} {C = z ≡ a} {D = ∈FM2'' a xs}) i₂)
-- -- -- -- -- -- --      --    (isInjectiveTransport
-- -- -- -- -- -- --      --              ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- --      --             (⊎.elim (λ _ → refl) λ _ → refl))))))) i i₁
-- -- -- -- -- -- --   ∈FM2'' a (hexL x y z xs i i₁) =
-- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- --   ∈FM2'' a (trunc x y p q r s i i₁ i₂) =
-- -- -- -- -- -- --      fst (isGroupoidHSet {ℓ}
-- -- -- -- -- -- --        ((∈FM2'' a x) , (isSet∈FM2'' a x))
-- -- -- -- -- -- --        (∈FM2'' a y , isSet∈FM2'' a y)
-- -- -- -- -- -- --        (λ i → (∈FM2'' a ( p i)) , (isSet∈FM2'' a (p i)))
-- -- -- -- -- -- --        (λ i → (∈FM2'' a ( q i)) , (isSet∈FM2'' a (q i)))
-- -- -- -- -- -- --        (λ i j → (∈FM2'' a ( r i j)) , (isSet∈FM2'' a (r i j)))
-- -- -- -- -- -- --        (λ i j → (∈FM2'' a ( s i j)) , (isSet∈FM2'' a (s i j)))
-- -- -- -- -- -- --        i i₁ i₂)
    
-- -- -- -- -- -- --   isSet∈FM2'' a [] = snd (∈FM2 a [])
-- -- -- -- -- -- --   isSet∈FM2'' a (x ∷2 xs) = {!snd (∈FM2 a (x ∷2 xs))!}
-- -- -- -- -- -- --   isSet∈FM2'' a (comm x y xs i) = {!!}
-- -- -- -- -- -- --   isSet∈FM2'' a (comm-inv x y xs i i₁) = {!!}
-- -- -- -- -- -- --   isSet∈FM2'' a (hexDiag x y z xs i) = {!!}
-- -- -- -- -- -- --   isSet∈FM2'' a (hexU x y z xs i i₁) = {!!}
-- -- -- -- -- -- --   isSet∈FM2'' a (hexL x y z xs i i₁) = {!!}
-- -- -- -- -- -- --   isSet∈FM2'' a (trunc xs xs₁ x y x₁ y₁ i i₁ x₂) = {!!}
  
-- -- -- -- -- -- -- -- --   isSet∈FM2'' a (x ∷2 xs) = ⊎.isSet⊎ (grpA _ _) (isSet∈FM2'' a xs)
-- -- -- -- -- -- -- -- --   isSet∈FM2'' a (comm x y xs i) = 
-- -- -- -- -- -- -- -- --     isProp→PathP
-- -- -- -- -- -- -- -- --       {B = λ i → isSet ((ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = ∈FM2'' a xs}) i))}
-- -- -- -- -- -- -- -- --       (λ i → isPropIsSet
-- -- -- -- -- -- -- -- --       {A = (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = ∈FM2'' a xs}) i)})
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA x a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA y a) (isSet∈FM2'' a xs)))
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA y a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA x a) (isSet∈FM2'' a xs))) i
-- -- -- -- -- -- -- -- --   isSet∈FM2'' a (comm-inv x y xs i j) =
-- -- -- -- -- -- -- -- --     isProp→SquareP
-- -- -- -- -- -- -- -- --       (λ i j → isPropIsSet {A = swap0and1⊎fInvolSq (x ≡ a) (y ≡ a) (∈FM2'' a xs) i j})
-- -- -- -- -- -- -- -- --       refl
-- -- -- -- -- -- -- -- --       refl
-- -- -- -- -- -- -- -- --       (isProp→PathP
-- -- -- -- -- -- -- -- --       {B = λ i → isSet ((ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = ∈FM2'' a xs}) i))}
-- -- -- -- -- -- -- -- --       (λ i → isPropIsSet
-- -- -- -- -- -- -- -- --       {A = (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = ∈FM2'' a xs}) i)})
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA x a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA y a) (isSet∈FM2'' a xs)))
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA y a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA x a) (isSet∈FM2'' a xs))))
-- -- -- -- -- -- -- -- --       (symP ((isProp→PathP
-- -- -- -- -- -- -- -- --           {B = λ i → isSet ((ua (swap0and1⊎ {A = y ≡ a} {B = x ≡ a} {C = ∈FM2'' a xs}) i))}
-- -- -- -- -- -- -- -- --           (λ i → isPropIsSet
-- -- -- -- -- -- -- -- --           {A = (ua (swap0and1⊎ {A = y ≡ a} {B = x ≡ a} {C = ∈FM2'' a xs}) i)})
-- -- -- -- -- -- -- -- --           (⊎.isSet⊎ (grpA y a)
-- -- -- -- -- -- -- -- --              (⊎.isSet⊎ (grpA x a) (isSet∈FM2'' a xs)))
-- -- -- -- -- -- -- -- --           (⊎.isSet⊎ (grpA x a)
-- -- -- -- -- -- -- -- --              (⊎.isSet⊎ (grpA y a) (isSet∈FM2'' a xs))))))
-- -- -- -- -- -- -- -- --       i j
      
-- -- -- -- -- -- -- -- --   isSet∈FM2'' a (hexDiag x y z xs i) =
-- -- -- -- -- -- -- -- --       isProp→PathP
-- -- -- -- -- -- -- -- --       {B = λ i → isSet (ua (swap0and2⊎ {A = x ≡ a} {B = y ≡ a} {C = z ≡ a} {D = ∈FM2'' a xs}) i)}
-- -- -- -- -- -- -- -- --       (λ i → isPropIsSet
-- -- -- -- -- -- -- -- --       {A = (ua (swap0and2⊎ {A = x ≡ a} {B = y ≡ a} {C = z ≡ a} {D = ∈FM2'' a xs}) i)})
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA x a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA y a) (⊎.isSet⊎ (grpA z a) (isSet∈FM2'' a xs))))
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA z a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA y a) (⊎.isSet⊎ (grpA x a) (isSet∈FM2'' a xs)))) i
-- -- -- -- -- -- -- -- --   isSet∈FM2'' a (hexU x y z xs i j) =
-- -- -- -- -- -- -- -- --      isProp→SquareP
-- -- -- -- -- -- -- -- --         (λ i j → isPropIsSet {A = sw12SqU (x ≡ a) (y ≡ a) (z ≡ a) (∈FM2'' a xs) i j})
-- -- -- -- -- -- -- -- --         (isProp→PathP
-- -- -- -- -- -- -- -- --       {B = λ i → isSet ((ua (swap0and1⊎ {A = y ≡ a} {B = x ≡ a} {C = (z ≡ a) ⊎ ∈FM2'' a xs}) i))}
-- -- -- -- -- -- -- -- --       (λ i → isPropIsSet
-- -- -- -- -- -- -- -- --       {A = (ua (swap0and1⊎ {A = y ≡ a} {B = x ≡ a} {C = (z ≡ a) ⊎ ∈FM2'' a xs}) i)})
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA y a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA x a) (⊎.isSet⊎ (grpA z a) (isSet∈FM2'' a xs))))
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA x a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA y a) (⊎.isSet⊎ (grpA z a) (isSet∈FM2'' a xs)))))
-- -- -- -- -- -- -- -- --         (isProp→PathP
-- -- -- -- -- -- -- -- --       {B = λ i → isSet ((ua (swap0and1⊎ {A = y ≡ a} {B = z ≡ a} {C = (x ≡ a) ⊎ ∈FM2'' a xs}) i))}
-- -- -- -- -- -- -- -- --       (λ i → isPropIsSet
-- -- -- -- -- -- -- -- --       {A = (ua (swap0and1⊎ {A = y ≡ a} {B = z ≡ a} {C = (x ≡ a) ⊎ ∈FM2'' a xs}) i)})
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA y a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA z a) (⊎.isSet⊎ (grpA x a) (isSet∈FM2'' a xs))))
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA z a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA y a) (⊎.isSet⊎ (grpA x a) (isSet∈FM2'' a xs)))))
-- -- -- -- -- -- -- -- --       (λ i → ⊎.isSet⊎ (grpA y a)
-- -- -- -- -- -- -- -- --            (isProp→PathP
-- -- -- -- -- -- -- -- --       {B = λ i → isSet ((ua (swap0and1⊎ {A = x ≡ a} {B = z ≡ a} {C = ∈FM2'' a xs}) i))}
-- -- -- -- -- -- -- -- --       (λ i → isPropIsSet
-- -- -- -- -- -- -- -- --       {A = (ua (swap0and1⊎ {A = x ≡ a} {B = z ≡ a} {C = ∈FM2'' a xs}) i)})
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA x a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA z a) (isSet∈FM2'' a xs)))
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA z a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA x a) (isSet∈FM2'' a xs))) i))
-- -- -- -- -- -- -- -- --         (isProp→PathP
-- -- -- -- -- -- -- -- --       {B = λ i → isSet (ua (swap0and2⊎ {A = x ≡ a} {B = y ≡ a} {C = z ≡ a} {D = ∈FM2'' a xs}) i)}
-- -- -- -- -- -- -- -- --       (λ i → isPropIsSet
-- -- -- -- -- -- -- -- --       {A = (ua (swap0and2⊎ {A = x ≡ a} {B = y ≡ a} {C = z ≡ a} {D = ∈FM2'' a xs}) i)})
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA x a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA y a) (⊎.isSet⊎ (grpA z a) (isSet∈FM2'' a xs))))
-- -- -- -- -- -- -- -- --       (⊎.isSet⊎ (grpA z a)
-- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA y a) (⊎.isSet⊎ (grpA x a) (isSet∈FM2'' a xs)))))
-- -- -- -- -- -- -- -- --         i
-- -- -- -- -- -- -- -- --         j
-- -- -- -- -- -- -- -- --   -- isSet∈FM2'' a (hexL x y z xs i i₁) = {!!}
-- -- -- -- -- -- -- -- --   -- isSet∈FM2'' a (trunc xs xs₁ x y x₁ y₁ i i₁ x₂) =
-- -- -- -- -- -- -- -- --   --   {!!}

-- -- -- -- -- -- -- -- -- -- i = i0 ⊢ ⊎.isSet⊎ (grpA x a)
-- -- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA y a) (⊎.isSet⊎ (grpA z a) (isSet∈FM2'' a xs))) x₁
-- -- -- -- -- -- -- -- -- --          y₁ x₂ y₂ = ?3 (grpA = a) (a = x) (x = y) (y = z) (z = xs) (xs = i)
-- -- -- -- -- -- -- -- -- --                     (i = i0) x₁ y₁ x₂ y₂
-- -- -- -- -- -- -- -- -- -- i = i1 ⊢ ⊎.isSet⊎ (grpA z a)
-- -- -- -- -- -- -- -- -- --          (⊎.isSet⊎ (grpA y a) (⊎.isSet⊎ (grpA x a) (isSet∈FM2'' a xs))) x₁
-- -- -- -- -- -- -- -- -- --          y₁ x₂ y₂ = ?3 (grpA = a) (a = x) (x = y) (y = z) (z = xs) (xs = i)
-- -- -- -- -- -- -- -- -- --                     (i = i1) x₁ y₁ x₂ y₂

-- -- -- -- -- -- -- -- -- -- module ∈FMSet2 {A : Type ℓ} (grpA : isGroupoid A) where

-- -- -- -- -- -- -- -- -- --   toHSet₃ : ∥ Type ℓ ∥₃ → hSet ℓ
-- -- -- -- -- -- -- -- -- --   fst (toHSet₃ ∣ x ∣₃) = ∥ x ∥₂
-- -- -- -- -- -- -- -- -- --   snd (toHSet₃ ∣ x ∣₃) = ST.squash₂
-- -- -- -- -- -- -- -- -- --   toHSet₃ (squash₃ x x₁ p q r s i i₁ i₂) =
-- -- -- -- -- -- -- -- -- --     isGroupoidHSet _ _ _ _ (λ j jj → toHSet₃ (r j jj)) (λ j jj → toHSet₃ (s j jj)) i i₁ i₂



-- -- -- -- -- -- -- -- -- --   toTy₃ : ∥ Type ℓ ∥₃ → Type ℓ
-- -- -- -- -- -- -- -- -- --   toTy₃ x  = fst (toHSet₃ x)
-- -- -- -- -- -- -- -- -- --   -- toTy₃ (squash₃ x x₁ p q r s i i₁ i₂) = {!!}


-- -- -- -- -- -- -- -- -- --   -- fromTy₃ : ∀ (A B : Type ℓ) (e : A ≃ B) → (isSetA : isSet A) → (isSetB : isSet B)
-- -- -- -- -- -- -- -- -- --   --                → (cong ST.∥_∥₂ (ua e))
-- -- -- -- -- -- -- -- -- --   --                ≡ ua (setTruncIdempotent≃ isSetA ∙ₑ
-- -- -- -- -- -- -- -- -- --   --                   e ∙ₑ
-- -- -- -- -- -- -- -- -- --   --                   invEquiv (setTruncIdempotent≃ isSetB))
-- -- -- -- -- -- -- -- -- --   -- fromTy₃ x y a xs = {!!} 

-- -- -- -- -- -- -- -- -- --   -- ua→' : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {B : Type ℓ'}
-- -- -- -- -- -- -- -- -- --   --    (f : A₁ → B)
-- -- -- -- -- -- -- -- -- --   --   → PathP (λ i → ua e i → B) (f ∘ fst e) f
-- -- -- -- -- -- -- -- -- --   -- ua→' {e = e} f i a = f ((ua-unglue e i a))
-- -- -- -- -- -- -- -- -- --   --    -- h ((ua-unglue e i a) ) i

-- -- -- -- -- -- -- -- -- --   -- fromTy₃≡ : ∀ {A B C : Type ℓ} (e : A ≃ B) → (isSetA : isSet A) → (isSetB : isSet B)
-- -- -- -- -- -- -- -- -- --   --                → (f : A → C)
-- -- -- -- -- -- -- -- -- --   --                → (g : B → C)
-- -- -- -- -- -- -- -- -- --   --                → PathP (λ i → ua e i → C) f g 
-- -- -- -- -- -- -- -- -- --   --                → PathP (λ i → toTy₃ ∣ ua e i ∣₃ → C)
-- -- -- -- -- -- -- -- -- --   --                    (f ∘ fst (setTruncIdempotent≃ isSetA))
-- -- -- -- -- -- -- -- -- --   --                    (g ∘ fst (setTruncIdempotent≃ isSetB))
-- -- -- -- -- -- -- -- -- --   -- fromTy₃≡ e isSetA isSetB f g p =
-- -- -- -- -- -- -- -- -- --   --   congP {A = λ z → (b : ua e z) → _}
-- -- -- -- -- -- -- -- -- --   --         {B = λ i _ → (a : ∥ ua e i ∥₂) → _} (λ i → _∘ fst (setTruncIdempotent≃
-- -- -- -- -- -- -- -- -- --   --     ((_▷_ {A = λ i → isSet (ua e i)}
-- -- -- -- -- -- -- -- -- --   --       (λ i → coe0→i (λ i → isSet (ua e i) ) i isSetA) (isPropIsSet _ isSetB)) i))) p

-- -- -- -- -- -- -- -- -- --   -- fromTy₃Sq : ∀ {C : Type ℓ} 
-- -- -- -- -- -- -- -- -- --   --                  (A : I → I → Type ℓ)
-- -- -- -- -- -- -- -- -- --   --                  (isSetA : ∀ i j → isSet (A i j))
-- -- -- -- -- -- -- -- -- --   --                  {a₀₀ : A i0 i0 → C} {a₀₁ : A i0 i1 → C} (a₀₋ : PathP (λ j → A i0 j → C) a₀₀ a₀₁)
-- -- -- -- -- -- -- -- -- --   --                  {a₁₀ : A i1 i0 → C} {a₁₁ : A i1 i1 → C} (a₁₋ : PathP (λ j → A i1 j → C) a₁₀ a₁₁)
-- -- -- -- -- -- -- -- -- --   --                  (a₋₀ : PathP (λ i → A i i0 → C) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1 → C) a₀₁ a₁₁)
-- -- -- -- -- -- -- -- -- --   --                  → (sq : SquareP (λ i j → A i j → C) a₀₋ a₁₋ a₋₀ a₋₁)
-- -- -- -- -- -- -- -- -- --   --                  → (SquareP (λ i j → ∥ A i j ∥₂ → C)
-- -- -- -- -- -- -- -- -- --   --                       (λ j → a₀₋ j ∘ fst (setTruncIdempotent≃ (isSetA i0 j)))
-- -- -- -- -- -- -- -- -- --   --                       (λ j → a₁₋ j ∘ fst (setTruncIdempotent≃ (isSetA i1 j)))
-- -- -- -- -- -- -- -- -- --   --                       (λ j → a₋₀ j ∘ fst (setTruncIdempotent≃ (isSetA j i0)))
-- -- -- -- -- -- -- -- -- --   --                       (λ j → a₋₁ j ∘ fst (setTruncIdempotent≃ (isSetA j i1))))
-- -- -- -- -- -- -- -- -- --   -- fromTy₃Sq A isSetA a₀₋ a₁₋ a₋₀ a₋₁ sq i j =
-- -- -- -- -- -- -- -- -- b--   --   sq i j ∘ fst (setTruncIdempotent≃ (isSetA i j))


-- -- -- -- -- -- -- -- -- --   -- ∈FM2'' : A → FMSet2 A → ∥ Type ℓ ∥₃ 
-- -- -- -- -- -- -- -- -- --   -- ∈FM2'' a = Rec.f
-- -- -- -- -- -- -- -- -- --   --      squash₃
-- -- -- -- -- -- -- -- -- --   --      ∣ ⊥.⊥* ∣₃
-- -- -- -- -- -- -- -- -- --   --      (λ x → GT.map λ b → (x ≡ a) ⊎ b)
-- -- -- -- -- -- -- -- -- --   --      (λ x y → GT.elim (λ _ → isSet→isGroupoid (squash₃ _ _))
-- -- -- -- -- -- -- -- -- --   --        λ T → cong ∣_∣₃ (ua swap0and1⊎))
-- -- -- -- -- -- -- -- -- --   --      (λ x y → GT.elim (λ _ → isSet→isGroupoid (isProp→isSet (squash₃ _ _ _ _)))
-- -- -- -- -- -- -- -- -- --   --             λ T → cong (cong ∣_∣₃)
-- -- -- -- -- -- -- -- -- --   --              ((cong ua (equivEq (funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --   --                λ _ → refl))))) ∙ uaInvEquiv _))
-- -- -- -- -- -- -- -- -- --   --      (λ x y z → GT.elim (λ _ → isSet→isGroupoid (squash₃ _ _))
-- -- -- -- -- -- -- -- -- --   --                   λ T → cong ∣_∣₃ (ua swap0and2⊎))
-- -- -- -- -- -- -- -- -- --   --      {!!}
-- -- -- -- -- -- -- -- -- --   --      -- (λ x y z → 
-- -- -- -- -- -- -- -- -- --   --      --    GT.elim (λ _ → {!!})
-- -- -- -- -- -- -- -- -- --   --      --    λ T i j → ∣ ∙≡∙→square _ _ _ _ {!!} i j ∣₃
-- -- -- -- -- -- -- -- -- --   --      --    )
-- -- -- -- -- -- -- -- -- --   --             -- λ T → {!(isInjectiveTransport
-- -- -- -- -- -- -- -- -- --   --             --     ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --   --             --    (⊎.elim (λ _ → refl) λ _ → refl))))))!})
-- -- -- -- -- -- -- -- -- --   --      {!!}  --GT.elim (λ _ → isSet→isGroupoid (isProp→isSet (squash₃ _ _ _ _)))


-- -- -- -- -- -- -- -- -- --   -- ∈FM2'' : ∀ {ℓ'} (B : Type ℓ') (isGrpB : isGroupoid B) → A → FMSet2 A
-- -- -- -- -- -- -- -- -- --   --                  → ∥ Σ (Type ℓ)
-- -- -- -- -- -- -- -- -- --   --                        (λ T → B → (A → B) → T → B ) ∥₃ 
-- -- -- -- -- -- -- -- -- --   -- ∈FM2'' B isGrpB a = {!!}









-- -- -- -- -- -- -- -- -- --   swap0and1₃ : {a x y : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- --                  (x ≡ a) ⊎ ∥ (y ≡ a) ⊎ C ∥₂ →
-- -- -- -- -- -- -- -- -- --                  (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ 
-- -- -- -- -- -- -- -- -- --   swap0and1₃ (inl x) = inr  ∣ inl x ∣₂
-- -- -- -- -- -- -- -- -- --   swap0and1₃ (inr ∣ inl x ∣₂) = inl x
-- -- -- -- -- -- -- -- -- --   swap0and1₃ (inr ∣ inr x ∣₂) = inr ∣ inr x ∣₂
-- -- -- -- -- -- -- -- -- --   swap0and1₃ (inr (squash₂ x x₁ p q i i₁)) =
-- -- -- -- -- -- -- -- -- --     ⊎.isSet⊎ (grpA _ _) squash₂ _ _
-- -- -- -- -- -- -- -- -- --       (cong (swap0and1₃ ∘ inr) p)
-- -- -- -- -- -- -- -- -- --       (cong (swap0and1₃ ∘ inr) q) i i₁

-- -- -- -- -- -- -- -- -- --   swap0and1₃invo : {a x y : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- --                  ∀ b → swap0and1₃ {a = a} {x} {y} {C} (swap0and1₃ b) ≡ b 
-- -- -- -- -- -- -- -- -- --   swap0and1₃invo = ⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --      (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --         (λ _ → refl)))

-- -- -- -- -- -- -- -- -- --   swap0and1Iso₃ : {a x y : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- --                  Iso ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ C ∥₂) 
-- -- -- -- -- -- -- -- -- --                      ((y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂)
-- -- -- -- -- -- -- -- -- --   Iso.fun swap0and1Iso₃ = swap0and1₃
-- -- -- -- -- -- -- -- -- --   Iso.inv swap0and1Iso₃ = swap0and1₃
-- -- -- -- -- -- -- -- -- --   Iso.rightInv swap0and1Iso₃ = swap0and1₃invo
-- -- -- -- -- -- -- -- -- --   Iso.leftInv swap0and1Iso₃ = swap0and1₃invo

-- -- -- -- -- -- -- -- -- --   swap0and1≃₃ : {a x y  : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- --                     ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ C ∥₂) 
-- -- -- -- -- -- -- -- -- --                     ≃ ((y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂)
-- -- -- -- -- -- -- -- -- --   swap0and1≃₃ = isoToEquiv swap0and1Iso₃



-- -- -- -- -- -- -- -- -- --   swap0and2₃ : {a x y z : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- --                  (x ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (z ≡ a) ⊎ C ∥₂ ∥₂ →
-- -- -- -- -- -- -- -- -- --                  (z ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ ∥₂ 
-- -- -- -- -- -- -- -- -- --   swap0and2₃  =
-- -- -- -- -- -- -- -- -- --     ⊎.elim (inr ∘ ∣_∣₂ ∘ inr ∘ ∣_∣₂ ∘ inl )
 
-- -- -- -- -- -- -- -- -- --     (ST.rec (⊎.isSet⊎ (grpA _ _) squash₂)
-- -- -- -- -- -- -- -- -- --       (⊎.rec ( inr ∘ ∣_∣₂ ∘ inl  )
-- -- -- -- -- -- -- -- -- --        (ST.rec (⊎.isSet⊎ (grpA _ _) squash₂) (⊎.rec inl (inr ∘ ∣_∣₂ ∘ inr ∘ ∣_∣₂ ∘ inr )))))


-- -- -- -- -- -- -- -- -- --   swap0and2Iso₃ : {a x y z : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- --                  Iso ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (z ≡ a) ⊎ C ∥₂ ∥₂)
-- -- -- -- -- -- -- -- -- --                      ((z ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ ∥₂) 
-- -- -- -- -- -- -- -- -- --   Iso.fun swap0and2Iso₃ = swap0and2₃
-- -- -- -- -- -- -- -- -- --   Iso.inv swap0and2Iso₃ = swap0and2₃
-- -- -- -- -- -- -- -- -- --   Iso.rightInv swap0and2Iso₃ =
-- -- -- -- -- -- -- -- -- --         ⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --      (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --         ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl) (λ _ → refl))))))
-- -- -- -- -- -- -- -- -- --   Iso.leftInv swap0and2Iso₃ =
-- -- -- -- -- -- -- -- -- --       ⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --      (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --         ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl) (λ _ → refl))))))


-- -- -- -- -- -- -- -- -- --   swap0and2≃₃ : {a x y z : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- --                      ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (z ≡ a) ⊎ C ∥₂ ∥₂)
-- -- -- -- -- -- -- -- -- --                   ≃  ((z ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ ∥₂) 
-- -- -- -- -- -- -- -- -- --   swap0and2≃₃ = isoToEquiv swap0and2Iso₃

-- -- -- -- -- -- -- -- -- --   -- swap0and2≃DiagU : {a x y z : A} {C : Type ℓ} →
-- -- -- -- -- -- -- -- -- --   --                       Square 
-- -- -- -- -- -- -- -- -- --   --                         (λ i → (y ≡ a) ⊎ toTy₃ ∣ ua (swap0and1≃₃ {a = a} {x} {z} {C}) i ∣₃)
-- -- -- -- -- -- -- -- -- --   --                         (λ i → ua (swap0and2≃₃ {a = a} {x} {y} {z} {C}) i)
-- -- -- -- -- -- -- -- -- --   --                         (λ i → ua (swap0and1≃₃ {a = a} {y} {x} {∥ (z ≡ a) ⊎ C ∥₂})  i)
-- -- -- -- -- -- -- -- -- --   --                         (λ i → ua (swap0and1≃₃ {a = a} {y} {z} {∥ (x ≡ a) ⊎ C ∥₂}) i)
                        
-- -- -- -- -- -- -- -- -- --   -- -- swap0and2≃DiagU = ∙-∙≡→square
-- -- -- -- -- -- -- -- -- --   -- --   ( (isInjectiveTransport (funExt (
-- -- -- -- -- -- -- -- -- --   -- --     ⊎.elim
-- -- -- -- -- -- -- -- -- --   -- --       (λ _ → refl)
-- -- -- -- -- -- -- -- -- --   -- --       {!!}
-- -- -- -- -- -- -- -- -- --   -- --       )) ∙ uaCompEquiv _ _) ∙ cong (ua swap0and1≃₃ ∙_)
-- -- -- -- -- -- -- -- -- --   -- --     (uaCompEquiv _ _ ∙
-- -- -- -- -- -- -- -- -- --   -- --       cong (ua swap0and2≃₃ ∙_) (uaInvEquiv _ )))

-- -- -- -- -- -- -- -- -- --   ∈FM2'' : A → FMSet2 A → ∥ Type ℓ ∥₃ 
-- -- -- -- -- -- -- -- -- --   ∈FM2'' a = Rec.f
-- -- -- -- -- -- -- -- -- --        squash₃
-- -- -- -- -- -- -- -- -- --        ∣ ⊥.⊥* ∣₃
-- -- -- -- -- -- -- -- -- --        (λ x xs → ∣ (x ≡ a) ⊎ toTy₃ xs ∣₃)
-- -- -- -- -- -- -- -- -- --        (λ x y b → cong ∣_∣₃ (ua swap0and1≃₃))
-- -- -- -- -- -- -- -- -- --        (λ x y b → cong (cong ∣_∣₃) (cong ua
-- -- -- -- -- -- -- -- -- --           (equivEq refl) ∙
-- -- -- -- -- -- -- -- -- --            uaInvEquiv
-- -- -- -- -- -- -- -- -- --             (swap0and1≃₃ {x = y} {y = x} )))         
-- -- -- -- -- -- -- -- -- --        (λ x y z b → cong ∣_∣₃ (ua swap0and2≃₃))
-- -- -- -- -- -- -- -- -- --        (λ x y z b → congSq ∣_∣₃ (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- --           (isInjectiveTransport (funExt (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --              (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --                 ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl) (λ _ → refl)))))))) )))
-- -- -- -- -- -- -- -- -- --        (λ x y z b → congSq ∣_∣₃ (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- --           (isInjectiveTransport (funExt (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --              (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- --                 ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl) (λ _ → refl)))))))) )))

       



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


-- -- -- -- -- -- -- -- -- -- --   -- ∈compute' : ∀ x (a : A) (xs : FMSet2 A) → a ∈FM2 (x ∷2 xs) → (x ≡ a) ⊎ (a ∈FM2 xs)  
-- -- -- -- -- -- -- -- -- -- --   -- ∈compute' x a xs ∣ x₁ ∣₂ = x₁
-- -- -- -- -- -- -- -- -- -- --   -- ∈compute' x a xs (squash₂ x₁ x₂ p q i i₁) =
-- -- -- -- -- -- -- -- -- -- --   --   ⊎.isSet⊎ (grpA _ _) (snd (toHSet₃ (∈FM2'' a xs)))
-- -- -- -- -- -- -- -- -- -- --   --    _
-- -- -- -- -- -- -- -- -- -- --   --    _ (cong (∈compute' x a xs) p) (cong (∈compute' x a xs) q) i i₁ 


-- -- -- -- -- -- -- -- -- -- --   ∈computeSq : ∀ x y (a : A) (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --                Path (Path (Type ℓ) (a ∈FM2 (x ∷2 y ∷2 xs))
-- -- -- -- -- -- -- -- -- -- --                                    (a ∈FM2 (y ∷2 x ∷2 xs)))
-- -- -- -- -- -- -- -- -- -- --                  (λ i → a ∈FM2 comm x y xs i)
-- -- -- -- -- -- -- -- -- -- --                  (cong ST.∥_∥₂ (ua swap0and1≃₃)) 
-- -- -- -- -- -- -- -- -- -- --   ∈computeSq x y a xs = refl

-- -- -- -- -- -- -- -- -- -- --   -- ∈computeSq' : ∀ x y (a : A) (C : Type ℓ) →
-- -- -- -- -- -- -- -- -- -- --   --                (cong ST.∥_∥₂ (ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = C})))
-- -- -- -- -- -- -- -- -- -- --   --                ≡ ua ( (setTruncIdempotent≃
-- -- -- -- -- -- -- -- -- -- --   --                  (⊎.isSet⊎ (grpA _ _) squash₂)) ∙ₑ
-- -- -- -- -- -- -- -- -- -- --   --                   (swap0and1≃₃ {a = a} {x = x} {y = y} {C = C}) ∙ₑ
-- -- -- -- -- -- -- -- -- -- --   --                   invEquiv (setTruncIdempotent≃
-- -- -- -- -- -- -- -- -- -- --   --                  (⊎.isSet⊎ (grpA _ _) squash₂)))
-- -- -- -- -- -- -- -- -- -- --   -- ∈computeSq' x y a xs = {!!} 


-- -- -- -- -- -- -- -- -- -- --   involSqLem :
-- -- -- -- -- -- -- -- -- -- --     (x y : A) {xs : FMSet2 A} → ∀ x₁ → ∀ a → ∀ xs' →
-- -- -- -- -- -- -- -- -- -- --      PathP (λ i → ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = {!!}}) i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- --       (⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- --             x ∷2
-- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 xs')
-- -- -- -- -- -- -- -- -- -- --             {!!}
-- -- -- -- -- -- -- -- -- -- --             -- (fst (l∈compute x₁ y a xs) q)
-- -- -- -- -- -- -- -- -- -- --             ))
-- -- -- -- -- -- -- -- -- -- --       (⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- --             y ∷2
-- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → x ∷2 xs')
-- -- -- -- -- -- -- -- -- -- --             {!!}
-- -- -- -- -- -- -- -- -- -- --             -- (fst (l∈compute x₁ x a xs) q)
-- -- -- -- -- -- -- -- -- -- --             ))
         
-- -- -- -- -- -- -- -- -- -- --   involSqLem = {!!}

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

-- -- -- -- -- -- -- -- -- -- --      wP' : (x y : A) {xs : FMSet2 A} →
-- -- -- -- -- -- -- -- -- -- --            (b : (l : lockUnit) → l∈ l a xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --             (x₁ : lockUnit) →
-- -- -- -- -- -- -- -- -- -- --             PathP (λ i → (ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = l∈ x₁ a xs}) i)
-- -- -- -- -- -- -- -- -- -- --                        → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- --               (⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --                  (λ q →
-- -- -- -- -- -- -- -- -- -- --                     x ∷2
-- -- -- -- -- -- -- -- -- -- --                     ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b x₁ q₁)
-- -- -- -- -- -- -- -- -- -- --                     ((ST.rec (⊎.isSet⊎ (grpA y a) (isSetl∈ x₁ a xs)) (idfun _) q))))
-- -- -- -- -- -- -- -- -- -- --               (⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --                  (λ q →
-- -- -- -- -- -- -- -- -- -- --                     y ∷2
-- -- -- -- -- -- -- -- -- -- --                     ⊎.rec (λ _ → xs) (λ q₁ → x ∷2 b x₁ q₁)
-- -- -- -- -- -- -- -- -- -- --                     ((ST.rec (⊎.isSet⊎ (grpA x a) (isSetl∈ x₁ a xs)) (idfun _) q))))
-- -- -- -- -- -- -- -- -- -- --      wP' x y {xs} b x₁ = ua→ wP''

-- -- -- -- -- -- -- -- -- -- --        where
-- -- -- -- -- -- -- -- -- -- --         wP'' : ∀ a → _
-- -- -- -- -- -- -- -- -- -- --         wP'' = ⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- --           (ST.elim (λ _ → trunc _ _) (⊎.elim (λ _ → refl) λ _ → comm _ _ _)) 

-- -- -- -- -- -- -- -- -- -- --      wP : (x y : A) {xs : FMSet2 A} →
-- -- -- -- -- -- -- -- -- -- --            (b : (l : lockUnit) → l∈ l a xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- --             (x₁ : lockUnit) →
-- -- -- -- -- -- -- -- -- -- --                PathP (λ z → l∈ x₁ a (comm x y xs z) → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- --                (w x (w y b) x₁)
-- -- -- -- -- -- -- -- -- -- --                (w y (w x b) x₁)
-- -- -- -- -- -- -- -- -- -- --      wP x y b x₁ = {!!}

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

