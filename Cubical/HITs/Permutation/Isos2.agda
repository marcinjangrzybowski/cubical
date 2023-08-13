{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.Isos2 where

open import Cubical.Data.Nat.Base as ℕ hiding (_·_)
open import Cubical.Data.Nat.Properties


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.Everything
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


-- lookup×' : ∀ n → A ×^ (suc n) → (Bool ×^ (suc n)) → A
-- lookup×' n (a , _) (true , _) = a
-- lookup×' n (_ , a) (false , bs) = {!a!}
-- -- lookup×' (suc n) x (false , bs) = lookup×' n (snd x) bs
-- -- lookup×' (suc n) x (true , bs) = fst x


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
  
isRemap : ∀ n m → (A ×^ n → A ×^ m) → hProp _
isRemap n m f = L.∃[ fF ∶ (Fin× m → Fin× n ) ] 
   (f L.≡ₚ (tabulate× ∘ (_∘ fF) ∘ lookup× n))

Remaping : ∀ (A : Type ℓ) → ℕ → ℕ → Type _
Remaping A = λ n m → Σ _ (fst ∘ isRemap {A = A} n m)

module _ {ℓa ℓb}{ℓa' ℓb'}{ℓa'' ℓb''}
            {A : Type ℓa} {B : A → Type ℓb}
            {A' : Type ℓa'} {B' : A' → Type ℓb'}
            {A'' : Type ℓa''} {B'' : A'' → Type ℓb''} where

 uncurry-transposed :
     (f : A → A' → A'')
   → (∀ {a a'} → B a → B' a' → B'' (f a a'))
   → Σ A B → Σ A' B' → Σ A'' B''
 uncurry-transposed f g (a , b) (a' , b') = f a a' , g b b'
 

CompRemaping : ∀ (A : Type ℓ) →
                 ∀ n m o →
                  Remaping A m o →
                  Remaping A n m →
                  Remaping A n o
CompRemaping A n m o =
  uncurry-transposed
    _∘'_
    (PropTrunc.map2
     (uncurry-transposed
       (flip _∘'_)
       (λ {a} {a'} → PropTrunc.map2 λ p q → cong₂ _∘'_ p q ∙
         funExt λ x →
          cong tabulate× (cong (_∘ a) (lookup×tabulate× _ _)) )))
  
isPermuatationA : ∀ n → Iso (A ×^ n) (A ×^ n) → hProp _
isPermuatationA n x = isRemap n n (Iso.fun x)

ΣPerm× : ℕ → Type
ΣPerm× n = Σ _ (fst ∘ isPermuatationA {A = Bool} n)

ΣPerm×→Perm× : ∀ n → ΣPerm× n → Perm× n
ΣPerm×→Perm× n (e' , x) = w
 where
 module e = Iso e'
 w : Perm× n
 Iso.fun w (x , y) = (e.fun x) , {!y!}
 Iso.inv w (x , y) = (e.inv x) , {!!}
 Iso.rightInv w (x , y) =
   Σ≡Prop (snd ∘ Fin×Snd n) (e.rightInv x)
 Iso.leftInv w (x , y) =
   Σ≡Prop (snd ∘ Fin×Snd n) (e.leftInv x)
   
Perm×→ΣPerm× : ∀ n → Perm× n → ΣPerm× n
Perm×→ΣPerm× n e = {!!}

sucΣPerm× : ∀ n → ΣPerm× n → ΣPerm× (suc n)
sucΣPerm× n (x , y) =
  Σ-cong-iso-snd (λ _ → x) ,
   PropTrunc.map
     {!!}
     y

invΣPerm× : ∀ {n} → ΣPerm× n → ΣPerm× n
invΣPerm× x = invIso (fst x) , {!!}
  -- PropTrunc.map
  --   {!!}
  --   (snd x)
  
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

swap01F× : ∀ {n} → ΣPerm× (2 + n)
fst swap01F× = Σ-swap-01-Iso
snd swap01F× = ∣ F×adjT zero ,
  ∣ funExt (λ x → cong′ (_ ,_) (cong′ (_ ,_) (sym (tabulate×lookup× _ _) ))) ∣₁ ∣₁

-- adjTF× : ∀ {n} → ΣPerm× n
-- adjTF× = ?


constAtFst : ∀ n → (f :  (Bool ×^ (suc n)) → (Bool ×^ (suc n))) →
                 Type
constAtFst n f = ∀ b bs → fst (f (b , bs)) ≡ b

predΣPerm× : ∀ n → (f : ΣPerm× (suc n)) →
                  (∀  b bs → fst (Iso.fun (fst f) (b , bs)) ≡ b) → ΣPerm× n
predΣPerm× n (f , p) q =
   IsoSnd false f q ,
     {!!}

compΣPerm× : ∀ {n} → ΣPerm× n → ΣPerm× n → ΣPerm× n
compΣPerm× = uncurry-transposed
  compIso λ x y → snd (CompRemaping _ _ _ _ (_ , y) (_ , x))

rotF× : ∀ {n} → Fin× n → ΣPerm× n
rotF× {suc n} ((true , snd₁) , bs) =
 idIso , {!!}
rotF× {suc (suc n)} ((false , x) , y) =
 compΣPerm× swap01F× (sucΣPerm× (suc n) (rotF× (x , y)))


elimF× : ∀ {ℓ} (A : ∀ n (k : Fin× (suc n)) → Type ℓ)
         → (∀ {n bs q} → A n ((true , bs) , q))
         → (∀ {n bs q}
              → A n (bs , q)
              → A (suc n) ((false , bs) , q))
         → ∀ {n} k
         → A n k
elimF× _ x x₁ {n} ((true , snd₂) , snd₁) = x
elimF× A x x₁ {suc n} ((false , snd₂) , snd₁) =
  x₁ (elimF× A x x₁ {n} (snd₂ , snd₁))

rotF×[zero]≡k : ∀ {n} k → ∀ v →
     lookup× _ ((Iso.fun (fst (rotF× {suc n} k))) v) k
      ≡ fst v  
rotF×[zero]≡k ((true , bs) , _) v = refl
rotF×[zero]≡k {suc n} ((false , bs) , p) (v , _ , vs) =
 rotF×[zero]≡k (bs , p) (v , vs)
 

rotF×[k]≡zero : ∀ {n} k → ∀ v →
     fst ((Iso.inv (fst (rotF× {suc n} k))) v)
      ≡ lookup× _ v k  
rotF×[k]≡zero {n} ((true , snd₂) , snd₁) v = refl
rotF×[k]≡zero {suc n} ((false , snd₂) , snd₁) (_ , v , vs) =
 rotF×[k]≡zero (snd₂ , snd₁) (v , vs)


unwinndF×Iso-lem : ∀ {n} (e : ΣPerm× (suc n)) p (v : Bool ×^ (suc n)) →
      lookup× (suc n) (Iso.fun (fst e) v)
      (Iso.fun (fst e) (true , repeat n false) , p)
      ≡ fst v
unwinndF×Iso-lem {n} = uncurry
 λ e → PropTrunc.elim
   (λ _ → isPropΠ2 λ _ _ → isSetBool _ _)
    (uncurry λ f →
     PropTrunc.elim (λ _ → isPropΠ2 λ _ _ → isSetBool _ _)
      λ q p v →
        subst {A = Σ ((Bool ×^ suc n) → (Bool ×^ suc n))
                     λ f' → ⟨ Fin×Snd (suc n)
                               (f' (true , repeat n false)) ⟩ }
         (λ z →
           lookup× (suc n) (fst z v)
               (fst z (true , repeat n false) , snd z)
               ≡ fst v)
                 (Σ≡Prop 
                   (λ f' → snd ( Fin×Snd (suc n)
                               (f' (true , repeat n false))))
                   {u = _ , {!!}}
                   (sym q))
               {!!}
        )


unwinndF×Iso : ∀ {n} → ΣPerm× (suc n) → ΣPerm× n 
unwinndF×Iso {n} e =
 let k = (Iso.fun (ΣPerm×→Perm× _ e) Fin×0)
 in predΣPerm× n
    (compΣPerm× e (invΣPerm× (rotF× k
      )))
        λ b bs →
           (rotF×[k]≡zero k
             (Iso.fun (fst e) (b , bs)) ∙
             unwinndF×Iso-lem e (snd k) (b , bs))


IsoUnwindF× : ∀ n →
     Iso
       (ΣPerm× (suc n))
       (Fin× (suc n) × ΣPerm× n)
Iso.fun (IsoUnwindF× n) e =
   Iso.fun (ΣPerm×→Perm× _ e) Fin×0 , unwinndF×Iso e
Iso.inv (IsoUnwindF× n) (k , e) =
   compΣPerm× (sucΣPerm× n e) (rotF× k)
Iso.rightInv (IsoUnwindF× n) (k , e) =
 ΣPathP (Σ≡Prop {!!} {!!} ,
  Σ≡Prop (snd ∘ isPermuatationA n)
   {!!})
Iso.leftInv (IsoUnwindF× n) (e , _) =
  Σ≡Prop (snd ∘ (isPermuatationA (suc n)))
   {!!}

-- UnwindF×Law : ∀ n e k →
--    Perm n → {!!}
-- UnwindF×Law = {!!}

ΣPerm×→Perm : ∀ n → ΣPerm× n → Perm n
ΣPerm×→Perm = {!!}


Perm→ΣPerm× : ∀ n → Perm n → ΣPerm× n
Perm→ΣPerm× n = Rrec.f (w n)
 where
 w : ∀ n → Rrec {n = n} (ΣPerm× n)
 Rrec.isSetA (w n) = {!!}
 Rrec.εA (w n) = idIso , {!!}
 Rrec.∷A (w (suc (suc n))) (k , _) e =
   compΣPerm×  {!!} e
 Rrec.invoA (w (suc (suc n))) (k , _) xs = {!!}
 Rrec.braidA (w n) = {!!}
 Rrec.commA (w n) = {!!}

PermIso : ∀ n → Iso (Perm n) (ΣPerm× n)
Iso.fun (PermIso n) = Perm→ΣPerm× n
Iso.inv (PermIso n) = ΣPerm×→Perm n
Iso.rightInv (PermIso n) = {!!}
Iso.leftInv (PermIso n) = {!!}

-- --   -- (compIso (Iso-×^-F→ n)
-- --   --   (compIso (domIso (
-- --   --     compIso (IsoFinFin× n)
-- --   --      (compIso e (invIso (IsoFinFin× n))))) (invIso (Iso-×^-F→ n)))) ,
-- --   --       PropTrunc.∣
-- --   --        (Iso.inv (IsoFinFin× n) ∘ Iso.inv e
-- --   --          ∘ Iso.fun (IsoFinFin× n)) ,
-- --   --         PropTrunc.∣ refl ∣₁ ∣₁

-- -- -- SetsIso≡-ext-fun : (isSetA : isSet A) → {e f : Iso A A} →
-- -- --     Iso.fun e ≡ Iso.fun f → e ≡ f
-- -- -- SetsIso≡-ext-fun isSetA p = 
-- -- --   invEq (congEquiv (isoToEquiv (isSet→Iso-Iso-≃ isSetA isSetA)))
-- -- --    (equivEq p) 

-- -- -- IsoΣPerm×Perm× : ∀ n → Iso (ΣPerm× n) (Perm× n)
-- -- -- Iso.fun (IsoΣPerm×Perm× n) = ΣPerm×→Perm× n
-- -- -- Iso.inv (IsoΣPerm×Perm× n) = Perm×→ΣPerm× n
-- -- -- Iso.rightInv (IsoΣPerm×Perm× n) e =
-- -- --   SetsIso≡-ext-fun (isSetFin× _)
-- -- --     {!!}
-- -- -- Iso.leftInv (IsoΣPerm×Perm× n) = uncurry
-- -- --   λ e →
-- -- --     PropTrunc.elim (λ _ →
-- -- --      isSetΣ (isSet-SetsIso
-- -- --        (isOfHLevel×^ n 2 isSetBool)
-- -- --        (isOfHLevel×^ n 2 isSetBool))
-- -- --          (isProp→isSet ∘ snd ∘ isPermuatationA n) _ _)
-- -- --            (uncurry λ x →
-- -- --             PropTrunc.elim {!!}
-- -- --               λ p →
-- -- --                 Σ≡Prop {!!}
-- -- --                   (SetsIso≡-ext-fun (isOfHLevel×^ n 2 isSetBool)
-- -- --                    ({!!} ∙ sym p)) )
-- -- --          -- λ (x , p) →
-- -- --          --  Σ≡Prop
-- -- --          --    (snd ∘ isPermuatationA n)
-- -- --          --    (SetsIso≡-ext-fun (isOfHLevel×^ n 2 isSetBool)
-- -- --          --      {!p!}
-- -- --          --      ) 
-- -- --   -- Σ≡Prop (snd ∘ isPermuatationA n)
-- -- --   --   (SetsIso≡-ext-fun (isOfHLevel×^ n 2 isSetBool)
-- -- --   --   {!!})
