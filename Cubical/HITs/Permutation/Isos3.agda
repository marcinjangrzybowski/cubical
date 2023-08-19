{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.Isos3 where

open import Cubical.Data.Nat.Base as ℕ hiding (_·_)
open import Cubical.Data.Nat.Properties


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Path
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Nat.Order.Permutation
-- open import Cubical.Data.Nat.Order.RecursiveMoreEquiv

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group

open import Cubical.Algebra.SymmetricGroup

import Cubical.Functions.Logic as L

open import Cubical.Functions.Embedding

open import Cubical.Data.List as Li

import Cubical.Data.Nat.FinGenAut2 as A

open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import Cubical.Data.FinSet.Cardinality

import Cubical.HITs.PropositionalTruncation as PropTrunc



open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SequentialColimit as SC


-- open import Cubical.Data.FinData.GTrun

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)

open import Cubical.Relation.Binary

import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.Permutation.Base
open import Cubical.HITs.Interval
open import Cubical.Data.Nat.Order.Permutation


-- isPermutation : ∀ n →  (Iso (Bool ×^ n) (Bool ×^ n)) →
--                 hProp ℓ-zero
-- isPermutation = ?


private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ



tabulate× : ∀ {n} → (Fin× n → A) → A ×^ n
tabulate× {n = zero} f = tt*
tabulate× {n = suc n} f = f Fin×0 , tabulate× (f ∘ sucFin×)

lookup× : ∀ n → A ×^ n → Fin× n → A
lookup× (suc n) x ((false , bs) , p) = lookup× n (snd x) (bs , p)
lookup× (suc n) x ((true , bs) , p) = fst x

tabulate×lookup× : ∀ n → section (tabulate× {A = A}) (lookup× n)
tabulate×lookup× zero b = refl
tabulate×lookup× (suc n) b = ΣPathP (refl , tabulate×lookup× n (snd b))

lookup×tabulate× : ∀ n → retract (tabulate× {A = A}) (lookup× n)
lookup×tabulate× zero a i ()
lookup×tabulate× (suc n) a i ((true , snd₂) , snd₁) =
  a (Fin×0= n {repeat n false} {snd₂}
    {allFalse-repeat-false n}
    {snd₁} i)
lookup×tabulate× (suc (suc n)) a i ((false , snd₂) , snd₁) =
  lookup×tabulate× (suc n) (a ∘ sucFin×) i (snd₂ , snd₁)

tabulate×lookup×Iso : ∀ n → Iso (Fin× n → A) (A ×^ n)
Iso.fun (tabulate×lookup×Iso n) = tabulate×
Iso.inv (tabulate×lookup×Iso n) = lookup× n
Iso.rightInv (tabulate×lookup×Iso n) = tabulate×lookup× n
Iso.leftInv (tabulate×lookup×Iso n) = lookup×tabulate× n

tabulate×lookup×≃ : ∀ n → (Fin× n → A) ≃ (A ×^ n)
tabulate×lookup×≃ = isoToEquiv ∘ tabulate×lookup×Iso

module _ {A : Type ℓ} {B B' : Type ℓ} (a₀ : A) where

 IsoSnd : (x : Iso (A × B) (A × B'))
          → (∀ a b → fst (Iso.fun x (a , b)) ≡ a)
          → Iso B B'
 Iso.fun (IsoSnd x p) = snd ∘ Iso.fun x ∘ (a₀ ,_)
 Iso.inv (IsoSnd x p) = snd ∘ Iso.inv x ∘ (a₀ ,_)
 Iso.rightInv (IsoSnd x p) b' = 
     cong (snd ∘ Iso.fun x)
       (cong₂ _,_
         (cong fst (isoInvInjective x _ _
           (sym (Iso.leftInv x (Iso.inv x (a₀ , b')))))
           ∙ p _ _)
         refl)
      ∙ cong snd (Iso.rightInv x (a₀ , b'))
 Iso.leftInv (IsoSnd x p) b =
   cong (snd ∘ Iso.inv x)
     (cong₂ _,_ (sym (p _ _)) refl)
    ∙ cong snd (Iso.leftInv x (a₀ , b))

 fE = fiberProjEquiv A (λ _ → B) a₀

 ≃Snd : (x : (A × B) ≃ (A × B'))
          → (∀ a b → fst (fst x (a , b)) ≡ a)
          → B ≃ B'
 ≃Snd e p = snd ∘ (fst e) ∘ (a₀ ,_) ,
       subst isEquiv
         (funExt λ x → transportRefl _)         
         (snd (fE ∙ₑ Σ-cong-equiv e
             (λ (a , b) → compPathlEquiv (p _ _)) ∙ₑ
           invEquiv (fiberProjEquiv A (λ _ → B') a₀)))



-- ΣPerm×Snd : ∀ n → Iso (Bool ×^ n) (Bool ×^ n) → hProp ℓ-zero
-- ΣPerm×Snd n e =
--   Σ (∀ x → ⟨ Fin×Snd n x ⟩ → ⟨ Fin×Snd n (Iso.fun e x) ⟩)
--     (λ f → (v : Bool ×^ n) → (lookup× n (Iso.fun e v)) ≡
--                              lookup× n v ∘
--                                λ (a , b) → Iso.fun e a , f a b)
--   , isPropΣ (isPropΠ2 λ x _ → snd (Fin×Snd n (Iso.fun e x)))
--            λ _ → isPropΠ λ _ → isSet→ isSetBool _ _ 


ΣPerm×Snd : ∀ n → ((Bool ×^ n) → (Bool ×^ n)) → hProp ℓ-zero
ΣPerm×Snd n f =
   isEquiv f × Σ (∀ x → ⟨ Fin×Snd n x ⟩ → ⟨ Fin×Snd n (f x) ⟩)
    (λ p →  f ≡ λ v → tabulate× (lookup× n v ∘
                               λ (a , b) → f a , p a b))
  , isProp× (isPropIsEquiv f)
    (isPropΣ (isPropΠ2 λ x _ → snd (Fin×Snd n (f x)))
           λ _ → isSet→ (isOfHLevel×^ n 2 isSetBool) _ _ ) 




ΣPerm× : ℕ → Type
ΣPerm× n = Σ _ (fst ∘ ΣPerm×Snd n)

idΣPerm× : ∀ {n} → ΣPerm× n
fst idΣPerm× = idfun _
snd idΣPerm× = (idIsEquiv _) , (λ x y → y) , (sym (funExt (tabulate×lookup× _)))

-- true,rep-false : ∀ n → Bool ×^ n
-- true,rep-false zero = tt*
-- true,rep-false (suc n) = true , repeat n false


ΣPerm×-suc : ∀ n → ΣPerm× n                  
                  → ΣPerm× (suc n)
ΣPerm×-suc n (f , isEqf , p , q) =
  (λ (x , y) → x , f y) , {!!}

ΣPerm×-pred : ∀ n → (f : ΣPerm× (suc n))
                  → (fst (fst f (true , repeat n false)) ≡ true)
                  → ΣPerm× n
ΣPerm×-pred zero f x = idΣPerm×
ΣPerm×-pred (suc n) (f , isEqf , p , q) x = 
   fst  e' , (snd e') , w , w'
  where
   e'' = λ a b → cong fst (funExt⁻ q (a , b)) ∙
          cong {y = Fin×0}
            (lookup× (suc (suc n)) (a , b))
            (Fin×0=' (suc n) (sym x))
   e' = ≃Snd false (f , isEqf)
          e'' 
   w : ∀ x → _ → _
   w v vS = subst
             {x = f (false , v)}
             {y = false , (snd (f (false , v)))} (fst ∘ Fin×Snd (suc (suc n)))
     (cong (_, ((snd (f (false , v))))) (e'' false v))
     (p (false , v) vS) 

   w' : _ ≡ _
   w' = {!!}

ΣPerm×-pred-id : ∀ n p q  →
                 fst (ΣPerm×-pred n (idfun _ , q) p) ≡
                  idfun _
ΣPerm×-pred-id zero p q = refl
ΣPerm×-pred-id (suc n) p q = refl

ΣPerm×Snd→≃-lem : ∀ n → (f : ΣPerm× n)
                   → ∀ x
                   → ⟨ Fin×Snd n (fst f x) ⟩
                   → ⟨ Fin×Snd n x ⟩
                  
ΣPerm×Snd→≃-lem (suc n) (f , isEqf , p , q) x xS =
  {!? , ?!}
 where
 e' = ≃Snd false (f , isEqf) {!!}
 z = ΣPerm×Snd→≃-lem n
      {!!} {!!} {!!}
  
ΣPerm×Snd→≃ : ∀ n → ΣPerm× n → Fin× n ≃ Fin× n
ΣPerm×Snd→≃ n e@(f , isEqf , p , q) =  
  (λ (bs , sndF×) → f bs , p bs sndF×) ,
  isoToIsEquiv w
 where
  
  w : Iso (Fin× n) (Fin× n)
  Iso.fun w = (λ (bs , sndF×) → f bs , p bs sndF×)
  Iso.inv w = (λ (bs , sndF×) → invEq (f , isEqf) bs ,
    ΣPerm×Snd→≃-lem n e (invEq (f , isEqf) bs)
      (subst (fst ∘ Fin×Snd n) (sym (secEq (f , isEqf) bs)) sndF×))
  Iso.rightInv w (b , _) = Σ≡Prop (snd ∘ Fin×Snd n) (secEq (f , isEqf) b)
  Iso.leftInv w (a , _) = Σ≡Prop (snd ∘ Fin×Snd n) (retEq (f , isEqf) a)

≃→ΣPerm×Snd : ∀ n → Fin× n ≃ Fin× n → ΣPerm× n
≃→ΣPerm×Snd n e@(f , isEqF) =
  tabulate× ∘ (_∘ f) ∘ lookup× n ,
    snd (invEquiv (tabulate×lookup×≃ n)
      ∙ₑ preCompEquiv e  ∙ₑ tabulate×lookup×≃ n) ,
       ({!!} , {!!})

compΣPerm× : ∀ {n} → ΣPerm× n → ΣPerm× n → ΣPerm× n
fst (compΣPerm× (f , _) (g , _)) = g ∘ f
snd (compΣPerm× (fst₁ , snd₁) x₁) = {!!}


rotℙrmΩ : ∀ n → Bool ×^ (suc n) → Path (ℙrm {true} (suc n)) 𝕡base 𝕡base
rotℙrmΩ n (true , _) = refl
rotℙrmΩ zero (false , _) = refl
rotℙrmΩ (suc n) (false , bs) =
  𝕡loop (zero , _) ∙ cong (sucℙrm _) (rotℙrmΩ n bs) 

rotℙrmΩpop : ∀ n k k< →
   rotℙrmΩ n (ℕ→Fin× (suc n) (suc k))
     ≡ rotℙrmΩ n (ℕ→Fin× (suc n) k) ∙ 𝕡loop (k , k<)
rotℙrmΩpop (suc n) zero k<  = sym (compPath≡compPath' _ _)
rotℙrmΩpop (suc n) (suc k) k<  =
 cong (𝕡loop (zero , _) ∙_)
  (cong (cong (sucℙrm _)) (rotℙrmΩpop n k k<) ∙
     cong-∙ (sucℙrm _) (rotℙrmΩ n (ℕ→Fin× (suc n) k)) (𝕡loop (k , k<)))
     ∙ assoc _ _ _



ΣPermloop : ∀ {n} → (Σ _ λ k → suc k < n) → ΣPerm× n
ΣPermloop {n} (k , k<) = adjT×^ k ,
  (isEquivAdjT×^ n k) ,
    (Fin×Snd∘adjT× n k) ,
    {!!}

rotΣPerm× : ∀ n → Bool ×^ (suc n) → ΣPerm× (suc n)
rotΣPerm× n (true , _) = idΣPerm×
rotΣPerm× zero (false , _) = idΣPerm×
rotΣPerm× (suc n) (false , bs) =
  compΣPerm× (ΣPerm×-suc _ (rotΣPerm× n bs))
            (ΣPermloop (zero , _))
  -- 𝕡loop (zero , _) ∙ cong (sucℙrm _) (rotℙrmΩ n bs) 


compΣPerm×rotΣPerm× : ∀ n (e : ΣPerm× (suc n)) →
       fst
      (fst (rotΣPerm× n (fst e (fst Fin×0)))
       (fst e (true , repeat n false)))
      ≡ true
compΣPerm×rotΣPerm× = {!!}

toℙrmΩ : ∀ {n} → ΣPerm× n → Path (ℙrm {true} n) 𝕡base 𝕡base
toℙrmΩ {zero} x = refl
toℙrmΩ {suc n} x =
  cong (sucℙrm n) (toℙrmΩ (ΣPerm×-pred _
     (compΣPerm× x (rotΣPerm× n ((fst x) (fst (Fin×0)))))
       (compΣPerm×rotΣPerm× n x)))
    ∙ rotℙrmΩ n ((fst x) (fst (Fin×0)))


toℙrmΩId : ∀ n → toℙrmΩ (idΣPerm× {n = n}) ≡ refl
toℙrmΩId zero = refl
toℙrmΩId (suc n) = sym (rUnit _) ∙
  cong′ (cong′ (sucℙrm n) {x = 𝕡base} {y = 𝕡base})
     
       (cong toℙrmΩ (Σ≡Prop (snd ∘ ΣPerm×Snd n)
          (ΣPerm×-pred-id _ _ _)) ∙ toℙrmΩId n)

toℙrmΩ-≡-refl : ∀ n → (x : ΣPerm× n) (y : toℙrmΩ x ≡ refl) →
                 idΣPerm× ≡ x
toℙrmΩ-≡-refl zero x y =
 Σ≡Prop (snd ∘ (ΣPerm×Snd zero)) refl
toℙrmΩ-≡-refl (suc n) x y = {!!}



module toℙrmΩ∙𝕡loop where
 data Cases {n} k (f0 : Bool ×^ n) : Type where
  f0<k : Fin×→ℕ n f0 < k → Cases k f0
  f0=k : Fin×→ℕ n f0 ≡ k →  Cases k f0
  f0=k+1 : Fin×→ℕ n f0 ≡ suc k → Cases k f0
  k+1<f0 : suc k < Fin×→ℕ n f0 → Cases k f0


 Fin0×' : ∀ {n}  → Bool ×^ n
 Fin0×' {zero} = tt*
 Fin0×' {suc n} = fst Fin×0

 comm-rot-loop : ∀ {n} → ∀ k k< (f0 : Bool ×^ (suc n)) →
          Fin×→ℕ (suc n) f0 < (suc k) →
           𝕡loop (suc k , k<) ∙ rotℙrmΩ n f0 ≡
          rotℙrmΩ n f0 ∙ 𝕡loop (suc k , k<)

 comm-rot-loop k k< (true , bs) x = sym (compPath≡compPath' _ _)
 comm-rot-loop {suc n} (suc k) k< (false , bs) x =
   assoc _ _ _
    ∙∙ cong (_∙ cong (sucℙrm (suc n)) (rotℙrmΩ n bs))
        (sym (𝕡loopComm (zero , tt) (suc (suc k) , k<)  tt))
     ∙∙ sym (assoc _ _ _)
     ∙∙ cong (𝕡loop (zero , tt) ∙_)
       (sym (cong-∙ (sucℙrm (suc n))
          (𝕡loop (suc k , k<))
          (rotℙrmΩ n bs))
           ∙ cong (cong (sucℙrm (suc n)))
           (comm-rot-loop k k< bs x) ∙
           cong-∙ (sucℙrm (suc n))
          (rotℙrmΩ n bs)
          (𝕡loop (suc k , k<))
          )
    ∙∙ assoc _ _ _

 comm-rot-loop' : ∀ {n} → ∀ k k< k<' (f0 : Bool ×^ (suc n)) →
           (suc k) < Fin×→ℕ (suc n) f0 →
           𝕡loop (suc k , k<) ∙ rotℙrmΩ n f0 ≡
          rotℙrmΩ n f0 ∙ 𝕡loop (k , k<')

 comm-rot-loop' {suc n} (suc k) k< k<' (false , bs) x =
   (assoc _ _ _ ∙∙
     cong (_∙ (cong (sucℙrm (suc n)) (rotℙrmΩ n bs)))
      ((sym (𝕡loopComm (zero , tt) (suc (suc k) , k<)  tt))) ∙∙
     (sym (assoc _ _ _) ∙
       cong (𝕡loop (zero , _) ∙_)
         (sym (cong-∙ (sucℙrm (suc n)) (𝕡loop (suc k , k<))
            (rotℙrmΩ n bs)))))   
     ∙∙
       cong (𝕡loop (zero , _) ∙_
     ∘' (cong (sucℙrm (suc n)))) (comm-rot-loop' {n} k k< k<' (bs) x)
     ∙∙ (cong (𝕡loop (zero , _) ∙_)
          (cong-∙ (sucℙrm (suc n)) (rotℙrmΩ n bs) (𝕡loop (k , k<')))
            ∙ assoc _ _ _)
 comm-rot-loop' {suc (suc n)} zero k< k<' (false , false , fst₁ , snd₁) x =
   {!!} ∙ assoc _ _ _
   
 ΣPermloop< : ∀ {n} v → ⟨ Fin×Snd n v ⟩ → ∀ k k< → Fin×→ℕ n v < k →
    fst (ΣPermloop (k , k<)) v ≡ v
 ΣPermloop< {suc (suc n)} (false , bs) x (suc k) k< x₁ =
    cong (false ,_) (ΣPermloop< bs x k k< x₁)
 ΣPermloop< {suc (suc n)} v@(true , bs) x (suc k) k< x₁ =
   cong fst (Fin×0= _ {_} {_} {fst (snd (snd (ΣPermloop (suc k , k<)))) v x }
     {x}) 
 
 toℙrmΩ∙𝕡loop' : ∀ {n} e k k< →
                 Cases k (fst e Fin0×')
                 → toℙrmΩ {n} (compΣPerm× e (ΣPermloop (k , k<)))
                               ≡ toℙrmΩ e ∙ 𝕡loop (k , k<)
 toℙrmΩ∙𝕡loop' {suc n} e (suc k) k< (f0<k x) =
   ((cong₂ _∙_
       {!!}
       (cong (rotℙrmΩ n) (ΣPermloop< (fst e Fin0×')
         (uncurry (e .snd .snd .fst) Fin×0)
         (suc k) k< x))
          )
     ∙∙ cong (_∙ p₁) (
         cong (cong (sucℙrm n)) (toℙrmΩ∙𝕡loop' {n}
             e' k k< {!!})
             ∙ cong-∙ (sucℙrm n)
          p₀' (𝕡loop (k , k<)))
     ∙∙ sym (assoc _ _ _))
    ∙∙ cong (p₀ ∙_) (comm-rot-loop k k< (fst e (fst Fin×0)) x)
        
    ∙∙ assoc p₀ p₁ _
  where
  e' = (ΣPerm×-pred _
     (compΣPerm× e (rotΣPerm× n ((fst e (fst Fin×0)))))
       (compΣPerm×rotΣPerm× n e))
  p₀' = toℙrmΩ {n} e'
  p₀ = cong (sucℙrm n) p₀' 
  p₁ = _
  
 toℙrmΩ∙𝕡loop' {suc n} e k k< (f0=k x) = {!!}
 toℙrmΩ∙𝕡loop' {suc n} e k k< (f0=k+1 x) = {!!}
 
 toℙrmΩ∙𝕡loop' {suc n} e k k< (k+1<f0 x) = {!!}


toℙrmΩ∙𝕡loop : ∀ {n} e k → toℙrmΩ {n} (compΣPerm× e (ΣPermloop k))
                              ≡ toℙrmΩ e ∙ 𝕡loop k
toℙrmΩ∙𝕡loop = {!!}

-- lemΣℙerm×Snd : ∀ n k → ∀ i → 
--      (Bool ×^ n → ⟨ 𝕍₂ Bool isSetBool n (𝕡loop k i) ⟩)
--       ≡ ua (postCompEquiv {A = Bool ×^ n}
--                            {!!}) i
-- lemΣℙerm×Snd = {!!}

-- adjT×^≡-≡-adjTF× : ∀ n k (x : Bool ×^ suc (suc n)) →
--     transp (λ i → adjT×^≡ {A = Bool}
--         {n = (suc (suc n))} (Fin×→ℕ n (fst k)) i) i0 x
--       ≡ Iso.fun (fst (adjTF× {n} k)) x
-- adjT×^≡-≡-adjTF× (suc n) ((false , snd₃) , snd₂) (b , bs) =
--   cong (b ,_) (adjT×^≡-≡-adjTF× n (snd₃ , snd₂) bs)
-- adjT×^≡-≡-adjTF× (suc n) ((true , snd₃) , snd₂) (b , bs) =
--   transportRefl _


adjT×^≡-≡-adjTF× : ∀ n k k<  x →
    transp (λ i → adjT×^≡ {A = Bool}
        {n = n} k (~ i)) i0 x
      ≡ fst (ΣPermloop (k , k<)) x
adjT×^≡-≡-adjTF× = {!!}

Σℙerm×Snd : ∀ n → (𝕡 : ℙrm {true} n)
     → ((Bool ×^ n) → ⟨ 𝕍₂ Bool isSetBool n 𝕡 ⟩) → hProp ℓ-zero
Σℙerm×Snd n = R𝕡elimSet'.f w
 where
 w : R𝕡elimSet' _
 R𝕡elimSet'.isSetA w _ = isSetΠ λ _ → isSetHProp
 R𝕡elimSet'.abase w = ΣPerm×Snd n
 R𝕡elimSet'.aloop w k =
   funTypeTransp' (λ x → (Bool ×^ n) → ⟨ 𝕍₂ Bool isSetBool n x ⟩) _
            {x = 𝕡base}
            {y = 𝕡base}
            (𝕡loop k) _
    ▷ (cong (ΣPerm×Snd n ∘_)
        (funExt₂ λ x y i → adjT×^≡-≡-adjTF× _ _ (snd k)
                    (x (transportRefl y i)) i)
      ∙ funExt λ v →
         L.⇔toPath
           (λ p → subst {x = (fst (ΣPermloop k)) ∘ (fst (ΣPermloop k))}
                        {y = idfun _} (fst ∘ (ΣPerm×Snd _) ∘ (_∘ v))
                      {!!}
                   (snd (compΣPerm× (_ , p) (ΣPermloop k))))
           λ p → snd (compΣPerm× (v , p) (ΣPermloop k)) )
  
  -- toPathP (funExt λ x → Σ≡Prop (λ _ → isPropIsProp)
  --   {!!})


Σℙerm× : ∀ n → ℙrm {true} n → Type
Σℙerm× n 𝕡 = Σ _ (fst ∘ Σℙerm×Snd n 𝕡)

toℙrm≡ : ∀ {n} → ∀ 𝕡 → Σℙerm× n 𝕡 → 𝕡base ≡ 𝕡
toℙrm≡ {n} = R𝕡elimSet'.f w
 where
 w : R𝕡elimSet' _
 R𝕡elimSet'.isSetA w _ = isSet→ (𝕡squash _ _ _)
 R𝕡elimSet'.abase w = toℙrmΩ
 R𝕡elimSet'.aloop w k =
   funTypePathP _ _ _ _
    (funExt λ x → substInPathsL _
           (toℙrmΩ (transport (λ i → Σℙerm× n (𝕡loop k (~ i))) x)) ∙
         cong (_∙ 𝕡loop k) (cong toℙrmΩ
           (Σ≡Prop (snd ∘ ΣPerm×Snd n )
              (funExt λ y i →
                adjT×^≡-≡-adjTF× _ (fst k) (snd k)
                  ((fst x (transp (λ j → Bool ×^ n) i y))) i ))
                   ∙ toℙrmΩ∙𝕡loop x k) ∙∙
           ( sym (assoc _ (𝕡loop k) _) ∙ cong (toℙrmΩ x ∙_)
            {!!}) ∙∙ sym (rUnit _))

IsEquiv : ∀ n 𝕡 → isEquiv' (toℙrm≡ {n} 𝕡)
IsEquiv n 𝕡 = J ((isContr ∘_) ∘ fiber ∘ toℙrm≡)
    ((idΣPerm× , toℙrmΩId n) ,
    (Σ≡Prop (λ _ → 𝕡squash _ _ _ _ _) ∘
      uncurry (toℙrmΩ-≡-refl n)))

-- IsoℙrmΩΣPerm× : ∀ n → Iso (ΣPerm× n) (Path (ℙrm {true} n) 𝕡base 𝕡base)
-- Iso.fun (IsoℙrmΩΣPerm× n) = toℙrmΩ 
-- Iso.inv (IsoℙrmΩΣPerm× n) = {!!}
-- Iso.rightInv (IsoℙrmΩΣPerm× n) = {!!}
-- Iso.leftInv (IsoℙrmΩΣPerm× n) = {!!}



-- invΣPerm× : ∀ {n} → ΣPerm× n → ΣPerm× n 
-- invΣPerm× {n} (f , isEqf , (p , q)) =
--  let (f' , isEqf') = invEquiv (f , isEqf)
--      -- q' : _ ≡
--      --        (λ v →
--      --           tabulate×
--      --           (λ x →
--      --              lookup× n v
--      --              (fst (invEquiv (f , isEqf)) (fst x) , p' (fst x) (snd x))))
--      -- q' = cong fst (cong invEquiv (equivEq q)) ∙
--      --       {!!}
--  in f' , isEqf' , {!!} , {!!}
--  -- where
--  -- p' : (x : Bool ×^ n) →
--  --        ⟨ Fin×Snd n x ⟩ → ⟨ Fin×Snd n (fst (invEquiv (f , isEqf)) x) ⟩
--  -- p' = {!!}


-- --  -- w : (x : Bool ×^ n) → Dec ⟨ Fin×Snd n (fst (invEquiv (f , isEqf)) x) ⟩
-- --  --       → ⟨ Fin×Snd n x ⟩ → ⟨ Fin×Snd n (fst (invEquiv (f , isEqf)) x) ⟩
-- --  -- w x (yes p) _ = p
-- --  -- w x (no ¬p) z = ⊥.elim (¬p
-- --  --   let qq = (p (fst (invEquiv (f , isEqf)) x) {!!})
-- --  --    in {!qq!})

-- ΣPerm×Snd→≃ : ∀ n → ΣPerm× n → Fin× n ≃ Fin× n
-- ΣPerm×Snd→≃ n (f , isEqf , (p , q)) =
--   (λ (bs , sndF×) → f bs , p bs sndF×) ,
--   isoToIsEquiv w
--  where
  
--   w : Iso (Fin× n) (Fin× n)
--   Iso.fun w = (λ (bs , sndF×) → f bs , p bs sndF×)
--   Iso.inv w = (λ (bs , sndF×) → invEq (f , isEqf) bs ,
--     {!!})
--   Iso.rightInv w = {!!}
--   Iso.leftInv w = {!!}

-- ≃→ΣPerm×Snd : ∀ n → Fin× n ≃ Fin× n → ΣPerm× n
-- ≃→ΣPerm×Snd n (f , isEqF) =
--    (λ v → tabulate× (lookup× n v ∘ f)) ,
--     snd (invEquiv (tabulate×lookup×≃ n)
--        ∙ₑ preCompEquiv (f , isEqF) ∙ₑ tabulate×lookup×≃ n) ,
--         ( {!!}
--          -- (λ x y → subst (fst ∘ (Fin×Snd n))
--          --    {!!} (snd (f {!!})))
--             , {!refl!})

-- Iso-ΣPerm×Snd-≃ : ∀ n →
--   Iso
--     (ΣPerm× n)
--     (Fin× n ≃ Fin× n)
-- Iso.fun (Iso-ΣPerm×Snd-≃ n) = ΣPerm×Snd→≃ n
-- Iso.inv (Iso-ΣPerm×Snd-≃ n) = {!!}
-- Iso.rightInv (Iso-ΣPerm×Snd-≃ n) = {!!}
-- Iso.leftInv (Iso-ΣPerm×Snd-≃ n) = {!!}

-- -- -- --  -- IsoSnd' : (x : Iso (A × B) (A × B'))
-- -- -- --  --          → (∀ a a' b → snd (Iso.fun x (a , b))
-- -- -- --  --                      ≡ snd (Iso.fun x (a' , b)))
-- -- -- --  --          → Iso B B'
-- -- -- --  -- Iso.fun (IsoSnd' x x₁) = snd ∘ Iso.fun x ∘ (a₀ ,_)
-- -- -- --  -- Iso.inv (IsoSnd' x x₁) = snd ∘ Iso.inv x ∘ (a₀ ,_)
-- -- -- --  -- Iso.rightInv (IsoSnd' x x₁) b' =
-- -- -- --  --  cong (snd ∘ (Iso.fun x))
-- -- -- --  --    {!!} 
-- -- -- --  --   ∙ cong snd (Iso.rightInv x (a₀ , b'))
-- -- -- --  -- Iso.leftInv (IsoSnd' x x₁) = {!!}

-- -- -- --  -- IsoSndIso : Iso
-- -- -- --  --     (Σ (Iso (A × B) (A × B'))
-- -- -- --  --       λ x → (∀ a a' b → snd (Iso.fun x (a , b))
-- -- -- --  --                      ≡ snd (Iso.fun x (a' , b))))
-- -- -- --  --     (Iso B B')
-- -- -- --  -- Iso.fun IsoSndIso = uncurry IsoSnd'
-- -- -- --  -- Iso.inv IsoSndIso x = (Σ-cong-iso-snd (λ _ → x)) , λ _ _ _ → refl
-- -- -- --  -- Iso.fun (Iso.rightInv IsoSndIso b i) = Iso.fun b
-- -- -- --  -- Iso.inv (Iso.rightInv IsoSndIso b i) = Iso.inv b
-- -- -- --  -- Iso.rightInv (Iso.rightInv IsoSndIso b i) = {!!}
-- -- -- --  -- Iso.leftInv (Iso.rightInv IsoSndIso b i) = {!!}
-- -- -- --  -- Iso.fun (fst (Iso.leftInv IsoSndIso a i)) =
-- -- -- --  --   {!!}
-- -- -- --  -- Iso.inv (fst (Iso.leftInv IsoSndIso a i)) =
-- -- -- --  --   {!!}
-- -- -- --  -- Iso.rightInv (fst (Iso.leftInv IsoSndIso a i)) = {!!}
-- -- -- --  -- Iso.leftInv (fst (Iso.leftInv IsoSndIso a i)) = {!!}
-- -- -- --  -- snd (Iso.leftInv IsoSndIso a i) = {!!}

-- -- -- -- -- module _ {A : Type ℓ} {B B' : Type ℓ} {a₀} where

-- -- -- -- --  IsoSndIso : Iso
-- -- -- -- --      (Σ (Iso (A × B) (A × B')) λ x → ∀ a b → fst (Iso.fun x (a , b)) ≡ a)
-- -- -- -- --      (Iso B B')
-- -- -- -- --  Iso.fun IsoSndIso = uncurry (IsoSnd a₀)
-- -- -- -- --  Iso.inv IsoSndIso x = (Σ-cong-iso-snd (λ _ → x)) , λ _ _ → refl
-- -- -- -- --  Iso.fun (Iso.rightInv IsoSndIso b i) = Iso.fun b
-- -- -- -- --  Iso.inv (Iso.rightInv IsoSndIso b i) = Iso.inv b
-- -- -- -- --  Iso.rightInv (Iso.rightInv IsoSndIso b i) b₁ i₁ = {!!}
-- -- -- -- --  Iso.leftInv (Iso.rightInv IsoSndIso b i) a i₁ = {!!}
-- -- -- -- --  Iso.fun (fst (Iso.leftInv IsoSndIso a i)) (a' , b') = {!!}
-- -- -- -- --  Iso.inv (fst (Iso.leftInv IsoSndIso a i)) = {!!}
-- -- -- -- --  Iso.rightInv (fst (Iso.leftInv IsoSndIso a i)) = {!!}
-- -- -- -- --  Iso.leftInv (fst (Iso.leftInv IsoSndIso a i)) = {!!}
-- -- -- -- --  snd (Iso.leftInv IsoSndIso a i) a₁ b i₁ = {!!}


-- -- -- -- -- -- ΣFin×≃ : ∀ n → Σ ((Bool ×^ n) → (Bool ×^ n))
-- -- -- -- -- --                  λ e → Σ (isEquiv e)
-- -- -- -- -- --                  λ isEquivE →
-- -- -- -- -- --                     {!!}
-- -- -- -- -- -- ΣFin×≃ = {!!}








-- -- -- -- -- -- -- 𝔽in≡-snd : ∀ n → (x : ℙrm {true} n)
-- -- -- -- -- -- --                  → (y : ℙrm {true} n)
-- -- -- -- -- -- --                  → ⟨ 𝕍₂ Bool isSetBool n x ⟩ ≡  ⟨ 𝕍₂ Bool isSetBool n y ⟩ 
-- -- -- -- -- -- --                  → hProp ℓ-zero
-- -- -- -- -- -- -- 𝔽in≡-snd n x y x₁ =
-- -- -- -- -- -- --   L.∃[ f ∶ {!!} ] {!Bool ≡  Bool!}




-- -- -- -- -- -- -- 𝔽in≡-snd : ∀ n → (x : ℙrm {true} n)
-- -- -- -- -- -- --                  → (y : ℙrm {true} n)
-- -- -- -- -- -- --                  → (⟨ 𝕍₂ Bool isSetBool n x ⟩  ≡ ⟨ 𝕍₂ Bool isSetBool n y ⟩)
-- -- -- -- -- -- --                  → hProp (ℓ-suc ℓ-zero)
-- -- -- -- -- -- -- 𝔽in≡-snd n x y p =
-- -- -- -- -- -- --   Σ (PathP (λ i → p i → hProp ℓ-zero) ((𝔽inSnd n x))
-- -- -- -- -- -- --      ((𝔽inSnd n y))) {!!} ,
-- -- -- -- -- -- --   {!!}
-- -- -- -- -- -- --   -- L.∃[ v≡ ∶ ⟨ 𝕍₂ Bool isSetBool n x ⟩  ≡ ⟨ 𝕍₂ Bool isSetBool n y ⟩  ]
-- -- -- -- -- -- --   --   Σ (PathP (λ i → v≡ i → hProp ℓ-zero) ((𝔽inSnd n x))
-- -- -- -- -- -- --   --                 ((𝔽inSnd n y)))
-- -- -- -- -- -- --   --     (λ p≡ → p ≡ λ i → Σ (v≡ i) (fst ∘ p≡ i) ) ,
-- -- -- -- -- -- --   --    isPropΣ (isOfHLevelPathP' 1 (isSet→ isSetHProp) _ _)
-- -- -- -- -- -- --   --    {!!}
-- -- -- -- -- -- --   --  -- L.∃[ p≡ ∶  PathP (λ i → v≡ i → Type) (λ z → fst (𝔽inSnd n x z))
-- -- -- -- -- -- --   --  --                (λ z → fst (𝔽inSnd n y z)) ]
-- -- -- -- -- -- --   --  --   (p ≡ cong₂ Σ v≡ {!p≡!}) , isOfHLevel≡ 2 (snd (h𝔽in n x)) (snd (h𝔽in n y)) p
-- -- -- -- -- -- --   --  --      {!!}


-- -- -- -- -- -- -- -- -- ΩFin[_] : ∀ n → Type
-- -- -- -- -- -- -- -- -- ΩFin[ n ] = Σ (Bool ×^ n) {!!}

-- -- -- -- -- -- -- -- 𝔽in≡ : ∀ n → Type₁
-- -- -- -- -- -- -- -- 𝔽in≡ n = Σ _ (fst ∘ 𝔽in≡-snd n (𝕡base {n = n}) (𝕡base {n = n}))

-- -- -- -- -- -- -- -- sucFin×≡ : ∀ n  → 𝔽in≡ n
-- -- -- -- -- -- -- --                 → 𝔽in≡ (suc n)
-- -- -- -- -- -- -- -- sucFin×≡ zero _ _ = {!!}
-- -- -- -- -- -- -- -- sucFin×≡ (suc n) x = {!!}




-- -- -- -- -- -- -- -- -- predFin×≡ : ∀ n → (p : Fin× (suc n) ≡ Fin× (suc n))
-- -- -- -- -- -- -- -- --                 → transport p Fin×0 ≡ Fin×0
-- -- -- -- -- -- -- -- --                 → Fin× n ≡ Fin× n
-- -- -- -- -- -- -- -- -- predFin×≡ zero _ _ = refl
-- -- -- -- -- -- -- -- -- predFin×≡ (suc n) p x = {!!}

-- -- -- -- -- -- -- -- -- -- unwindFin×≡ : ∀ n → (Fin× (suc n) ≡ Fin× (suc n)) →
-- -- -- -- -- -- -- -- -- --                      Fin n × (Fin× n ≡ Fin× n)
-- -- -- -- -- -- -- -- -- -- unwindFin×≡ = {!!}
