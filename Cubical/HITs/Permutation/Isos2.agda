{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.Isos2 where

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

idΣPerm× : ∀ n → ΣPerm× n
idΣPerm× n =
 idIso , ∣ (idfun _) ,
   ∣ (funExt (sym ∘ (tabulate×lookup× n))) ∣₁ ∣₁

record R𝕡elimSet'₂ {n} {true}
           (A : ℙrm {true} n → ℙrm {true} n → Type ℓ) : Type ℓ where
 no-eta-equality
 field
   isSetA' : ∀ x y → isSet (A x y)
   abase' : A 𝕡base 𝕡base
   aloopR : (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
      PathP (λ i → A 𝕡base (𝕡loop k i)) abase' abase'
   aloopL : (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
      PathP (λ i → A (𝕡loop k i) 𝕡base) abase' abase'
 -- fR : R𝕡elimSet (λ z → A z)
 -- R𝕡elimSet.isSetA fR = isSetA
 -- R𝕡elimSet.abase fR = abase
 -- R𝕡elimSet.aloop fR = aloop
 -- R𝕡elimSet.alooop fR  = w
 --  where
 --   abstract
 --    w : (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
 --     PathP (λ i → A (𝕡looop k l i)) (R𝕡elimSet.abase fR)
 --     (R𝕡elimSet.abase fR)
 --    w = λ k l i → comp (λ j → A (𝕡comp k l i (~ j)))
 --      (λ j → λ { (i = i0) → aloop k (~ j) ; (i = i1) → aloop l (~ j) })
 --      abase

 open R𝕡elimSet' hiding (f)

 f' : R𝕡elimSet' {n = n} {true}
        λ 𝕡₀ → R𝕡elimSet' {n = n} {true}
          λ 𝕡₁ → A 𝕡₀ 𝕡₁
 isSetA f' _ = {!!}
 isSetA (abase f') x = isSetA' 𝕡base x
 abase (abase f') = abase'
 aloop (abase f') = aloopR
 isSetA (aloop f' k i) = {!!}
 abase (aloop f' k i) = aloopL k i
 aloop (aloop f' k i) k₁ i₁ =
  isSet→SquareP
    (λ i j → isSetA' (𝕡loop k i) (𝕡loop k₁ j))
    (aloopR k₁) (aloopR k₁) (aloopL k) (aloopL k) i i₁

 -- f : ∀ x y → A x y
 -- f = R𝕡elimSet'.f {n = n} {true} ∘ R𝕡elimSet'.f {n = n} {true} f'


ℙerm×Snd : ∀ n → (𝕡₀ 𝕡₁ : ℙrm {true} n)
               → Iso
                  ⟨ 𝕍₂ Bool isSetBool n 𝕡₀ ⟩
                  ⟨ 𝕍₂ Bool isSetBool n 𝕡₁ ⟩
               → hProp ℓ-zero 
ℙerm×Snd n = R𝕡elimSet'.f ∘ R𝕡elimSet'.f (R𝕡elimSet'₂.f' (w n))
 where
 open R𝕡elimSet'₂
 w : ∀ n → R𝕡elimSet'₂ {n = n}
          λ (𝕡₀ 𝕡₁ : ℙrm {true} n)
               → (Iso
                  ⟨ 𝕍₂ Bool isSetBool n 𝕡₀ ⟩
                  ⟨ 𝕍₂ Bool isSetBool n 𝕡₁ ⟩) → hProp ℓ-zero 
 isSetA' (w n) _ _ = isSet→ isSetHProp
 abase' (w n) = isPermuatationA {A = Bool} n
 aloopR (w n) k = 
   funTypeTransp'
          (λ x → Iso (Bool ×^ n) ⟨ 𝕍₂ Bool isSetBool n x ⟩) _
            {x = 𝕡base}
            {y = 𝕡base}
            (𝕡loop k) _ ▷
          funExt λ x →
            {!!}
  
 aloopL (w n) = {!!}

ℙerm× : ∀ n → (𝕡₀ 𝕡₁ : ℙrm {true} n)
               → Type
ℙerm× n 𝕡₀ 𝕡₁ = Σ _ (fst ∘ ℙerm×Snd n 𝕡₀ 𝕡₁)


ΣPerm×≡ : ∀ n → {e₀ e₁ : ΣPerm× n} →
        Iso.fun (fst e₀) ≡ Iso.fun (fst e₁) 
        → e₀ ≡ e₁
ΣPerm×≡ n p =
  Σ≡Prop (snd ∘ (ℙerm×Snd n 𝕡base 𝕡base))
    (invEq
      (congEquiv
        (_ , isSet→isEquiv-isoToPath
          (isOfHLevel×^ n 2 isSetBool)
          (isOfHLevel×^ n 2 isSetBool) ))
      (equivEq p)) 


-- fromℙrm≡-refl : ∀ n 𝕡 → ℙerm× n 𝕡 𝕡
-- fromℙrm≡-refl n 𝕡 =
--   idIso , R𝕡elimProp.f (w n) 𝕡
--  where
--  w : ∀ n →
--        R𝕡elimProp {n = n} {trunc = true}
--          (λ 𝕡 → fst (ℙerm×Snd n 𝕡 𝕡 idIso))
--  R𝕡elimProp.isPropA (w n) 𝕡 =
--    snd (ℙerm×Snd n 𝕡 𝕡 idIso)
--  R𝕡elimProp.abase (w n) = snd (idΣPerm× n)
   
 
 -- R𝕡elimSet'.f (w n)
 --  where
 --  w : ∀ n → R𝕡elimSet'
 --         λ 𝕡 → ℙerm× n 𝕡 𝕡
 --  R𝕡elimSet'.isSetA (w n) = {!!}
 --  R𝕡elimSet'.abase (w n) = idIso , {!!}
 --  R𝕡elimSet'.aloop (w n) k = {!!}
 
-- fromℙrm≡ : ∀ n → (𝕡₀ 𝕡₁ : ℙrm {true} n)
--               → 𝕡₀ ≡ 𝕡₁
--               → ℙerm× n 𝕡₀ 𝕡₁
-- fromℙrm≡ n 𝕡₀ 𝕡₁ =
--  J (λ 𝕡₁ _ → ℙerm× n 𝕡₀ 𝕡₁)
--  (fromℙrm≡-refl n 𝕡₀)

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

push×^ : ∀ n → A → A ×^ n → A ×^ (suc n)
push×^ zero x _ = x , _
push×^ (suc n) x (v , vs) = v , push×^ n x vs

pop×^ : ∀ n → A ×^ (suc n) → A ×^ n
pop×^ zero = _
pop×^ (suc n) (v , vs) = v , pop×^ n vs

-- congIsoLast×^ : ∀ n → Iso (A ×^ n) (A ×^ n)
--                         → Iso (A ×^ (suc n)) (A ×^ (suc n))   
-- Iso.fun (congIsoLast×^ n x) =
--    (λ {a} → push×^ n (fst a))
--         ∘ (Iso.fun x ∘ pop×^ n)
-- Iso.inv (congIsoLast×^ n x) =
--   (λ {a} → push×^ n (fst a))
--         ∘ (Iso.inv x ∘ pop×^ n)
-- Iso.rightInv (congIsoLast×^ zero x) _ = refl
-- Iso.rightInv (congIsoLast×^ (suc n) x) (vs) =
--   {!!} ∙ {!cong (push×^ n) ? (Iso.rightInv x (pop×^ (suc n) vs))!} ∙ {!!}
--   -- ΣPathP
--   --   ({!!} ,
--   --    ({!!} ∙ Iso.rightInv (congIsoLast×^ n {!!}) vs))
-- Iso.leftInv (congIsoLast×^ n x) = {!!}

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


IsoSndIdIso : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (a₀ : A) p → (isSet A)
  → IsoSnd a₀ (idIso {A = A × B}) (p) ≡ idIso
IsoSndIdIso a₀ p x =
  cong (IsoSnd a₀ idIso)
    (isPropΠ2 (λ _ _ → x _ _) p (λ _ _ → refl)) ∙
     w
 where
 w : IsoSnd a₀ idIso (λ z z₁ _ → fst (Iso.fun idIso (z , z₁))) ≡
     idIso
 Iso.fun (w i) = idfun _
 Iso.inv (w i) = idfun _
 Iso.rightInv (w i) b j = lUnit (λ _ → b) (~ i) j
 Iso.leftInv (w i) a j = lUnit (λ _ → a) (~ i) j

swap01F× : ∀ {n} → ΣPerm× (2 + n)
fst swap01F× = Σ-swap-01-Iso
snd swap01F× = ∣ F×adjT zero ,
  ∣ funExt (λ x → cong′ (_ ,_) (cong′ (_ ,_) (sym (tabulate×lookup× _ _) ))) ∣₁ ∣₁

adjTF× : ∀ {n} → (Fin× n) → ΣPerm× (suc (suc n))
adjTF× {suc n} ((false , bs) , p) = sucΣPerm× (suc (suc n)) (adjTF× (bs , p))
adjTF× {suc n} ((true , _) , _) = swap01F×


adjTF×' : ∀ {n} → (Σ _ λ k → suc k < n) → ΣPerm× n
adjTF×' {suc n} (suc fst₁ , snd₁) = sucΣPerm× n (adjTF×' {n} (fst₁ , snd₁))
adjTF×' {suc (suc n)} (zero , snd₁) = swap01F×


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
 idΣPerm× _
rotF× {suc (suc n)} ((false , x) , y) =
 compΣPerm× swap01F× (sucΣPerm× (suc n) (rotF× (x , y)))


rotF×< : ∀ {n} → ∀ k → (k < n) → ΣPerm× n
rotF×< zero  k< = idΣPerm× _
rotF×< {n} (suc k)  k< =
  compΣPerm× (rotF×< {n} k (<-weaken {n = n} k<))
  (adjTF×' {n} (k , k<))


adjFin< : ∀ {n} → ∀ k → (suc k < n) → Fin n → Fin n 
adjFin< {n} (suc k) x (zero , snd₁) = zero , snd₁
adjFin< {suc n} (suc k) x (suc fst₁ , snd₁) =
 let (q , qq) = adjFin< {n} k x (fst₁ , snd₁)
 in suc q , qq
adjFin< {suc (suc n)} zero x (zero , snd₁) = suc zero , _
adjFin< {suc (suc n)} zero x (suc zero , snd₁) = zero , _
adjFin< {suc (suc n)} zero x k@(suc (suc fst₁) , snd₁) = k

rotFin< : ∀ {n} → ∀ k → (k < n) → Fin n → Fin n 
rotFin< zero _ x₁ = x₁
rotFin< {n} (suc k) k< =
  adjFin< {n} k  k<
  ∘ rotFin< {n} k (<-weaken {n = n} k<)
    

-- rotF× : ∀ {n} → Fin× n → ΣPerm× n
-- rotF× {suc n} ((true , snd₁) , bs) =
--  idΣPerm× _
-- rotF× {suc (suc n)} ((false , x) , y) =
--   compΣPerm× {!rotF× {suc n}!} {!!}
--  -- compΣPerm× swap01F× (sucΣPerm× (suc n) (rotF× (x , y)))



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

rotℙrm≡< : ∀ n → ∀ k →  k < n →
                  Path
                   (ℙrm {true} (n))
                   𝕡base
                   𝕡base
rotℙrm≡< n zero x = refl
rotℙrm≡< n (suc k) x =
  rotℙrm≡< n k (<-weaken {n = n} x) ∙
    𝕡loop (k , x)

rotℙrm≡ : ∀ n → Fin× (suc n) →
                  Path
                   (ℙrm {true} (suc n))
                   𝕡base
                   𝕡base
rotℙrm≡ n ((true , snd₁) , y) = refl
rotℙrm≡ (suc n) ((false , x) , y) =
   𝕡loop (zero , _) ∙ cong (sucℙrm (suc n)) (rotℙrm≡ n (x , y))

toℙrm≡base : ∀ n → ΣPerm× n
                 → Path
                   (ℙrm {true} n)
                   𝕡base
                   𝕡base
toℙrm≡base zero x = refl
toℙrm≡base (suc n) x =
 let (k , z) = Iso.fun (IsoUnwindF× n) x
 in cong (sucℙrm n) (toℙrm≡base n z) ∙ rotℙrm≡ n k
     

idΣPerm×-lem : ∀ n k p →
   Path (Path (ℙrm {true} (suc n)) 𝕡base 𝕡base)
     (cong {x = 𝕡base} {𝕡base} (sucℙrm n) p ∙ rotℙrm≡ n k) (λ _ → 𝕡base) 
     → (fst (fst k) ≡ true) × (p ≡ refl) 
idΣPerm×-lem = {!!}

idΣPerm×-refl : ∀ n e p
   → toℙrm≡base n (e , p) ≡ refl → idfun _ ≡ (Iso.fun e)
idΣPerm×-refl zero _ _ _ _ _ = tt*
idΣPerm×-refl (suc n) e p x =
  let (k , z) = Iso.fun (IsoUnwindF× n) (e , p)
      (k= , p=) =
         idΣPerm×-lem _ ((Iso.fun (ΣPerm×→Perm× (suc n) (e , p)) Fin×0))
                    (toℙrm≡base n (unwinndF×Iso (e , p))) x
      
      z = idΣPerm×-refl n (fst z) (snd z) p=
      
  in {!!}


-- toℙrmLem' : ∀ n k → (x : ΣPerm× n) →
--       toℙrm≡base n (compΣPerm× x {!!}) 
--       ≡ toℙrm≡base n x ∙ 𝕡loop k
-- toℙrmLem' n k = {!!} 

Fin'fromFin×Snd : ∀ n → (k : Fin× n) → suc (Fin×→ℕ n (fst k)) < (suc (suc n))
Fin'fromFin×Snd = {!!}

Fin'fromFin× : ∀ n → Fin× (n) → Σ _ λ k → suc k < (suc (suc n))
Fin'fromFin× n x = Fin×→ℕ n (fst x) , Fin'fromFin×Snd n x

adjT×^≡-≡-adjTF× : ∀ n k (x : Bool ×^ suc (suc n)) →
    transp (λ i → adjT×^≡ {A = Bool}
        {n = (suc (suc n))} (Fin×→ℕ n (fst k)) i) i0 x
      ≡ Iso.fun (fst (adjTF× {n} k)) x
adjT×^≡-≡-adjTF× (suc n) ((false , snd₃) , snd₂) (b , bs) =
  cong (b ,_) (adjT×^≡-≡-adjTF× n (snd₃ , snd₂) bs)
adjT×^≡-≡-adjTF× (suc n) ((true , snd₃) , snd₂) (b , bs) =
  transportRefl _

substℙrm𝕡loop : ∀ n k x →
    subst (ℙerm× (suc (suc n)) 𝕡base) (𝕡loop (Fin'fromFin× n k)) x
     ≡ compΣPerm× x (adjTF× k)
substℙrm𝕡loop n k x = ΣPerm×≡ (suc (suc n))
  (funExt λ y i →
      (adjT×^≡-≡-adjTF× n k (Iso.fun (fst x)
        (transp (λ _ → Bool ×^ suc (suc n)) i y))) i)

-- substℙrm𝕡loop' : ∀ n k x v →
--     Iso.fun (fst (subst (ℙerm× n 𝕡base) (𝕡loop k) x)) v
--      ≡ Iso.fun (fst (compΣPerm× x (adjTF×' k))) v
-- substℙrm𝕡loop' (suc n) (suc k , k<) x (b , v) =
--   ΣPathP (cong (fst ∘ (Iso.fun (fst x))) (transportRefl (b , v)) ,
--     {!substℙrm𝕡loop' n (k , k<) !})
-- substℙrm𝕡loop' (suc (suc n)) (zero , k<) x v =
--    transportRefl _ ∙ cong (swap-01 ∘ Iso.fun (fst x)) (transportRefl v)

-- adjT×^≡-≡-adjTF× : ∀ n k (x : Bool ×^ suc (suc n)) →
--     transp (λ i → adjT×^≡ {A = Bool}
--         {n = (suc (suc n))} (Fin×→ℕ n (fst k)) i) i0 x
--       ≡ Iso.fun (fst (adjTF× {n} k)) x
-- adjT×^≡-≡-adjTF× (suc n) ((false , snd₃) , snd₂) (b , bs) =
--   cong (b ,_) (adjT×^≡-≡-adjTF× n (snd₃ , snd₂) bs)
-- adjT×^≡-≡-adjTF× (suc n) ((true , snd₃) , snd₂) (b , bs) =
--   transportRefl _

adjT×^≡-≡-adjTF×' : ∀ n k (f : Bool ×^ n → Bool ×^ n) v →
        (transp (λ i → adjT×^≡ {A = Bool} {n = n} (fst k) i) i0
      (f v))
      ≡ Iso.fun (fst (adjTF×' k)) (f v)
adjT×^≡-≡-adjTF×' (suc n) (suc fst₁ , snd₁) f v =
  cong (fst (f v) ,_) (adjT×^≡-≡-adjTF×' n (fst₁ , snd₁)
     (snd ∘ f ∘ ((fst v) ,_) ) (snd v))
adjT×^≡-≡-adjTF×' (suc (suc n)) (zero , snd₁) f v = transportRefl _

substℙrm𝕡loop'' :  ∀ n k x →
  subst (ℙerm× n 𝕡base) (𝕡loop k) x ≡ compΣPerm× x (adjTF×' k)
substℙrm𝕡loop'' n k x =
  ΣPerm×≡ n (funExt λ v i →
    adjT×^≡-≡-adjTF×' n k (Iso.fun (fst x))
      (transp (λ _ → Bool ×^ n) i v) i)



-- -- toℙrmLem' : ∀ n 1<n → (x : ΣPerm× (suc n)) →
-- --          ∀ f0 → ⟨ Fin×Snd (suc n) f0 ⟩ →  f0 ≡ Iso.fun (fst x) (fst (Fin×0)) → 
-- --          toℙrm≡base (suc n) (compΣPerm× x (adjTF×' (zero , 1<n))) 
-- --       ≡ toℙrm≡base (suc n) x ∙ 𝕡loop (zero , 1<n)
-- -- toℙrmLem' (suc n) 1<n x (false , false , bs) f0S x₁ =
-- --   {!!}
-- -- toℙrmLem' (suc n) 1<n x (false , true , bs) f0S x₁ = {!!}
-- -- toℙrmLem' (suc n) 1<n x (true , bs) f0S x₁ = {!!}

-- T×repF : ∀ n → Bool ×^ n
-- T×repF zero = tt*
-- T×repF (suc n) = true , repeat n false

-- -- toℙrmLem' : ∀ n k → (x : ΣPerm× n) →
-- --             ∀ f0 → ⟨ Fin×Snd n f0 ⟩
-- --            →  f0 ≡ Iso.fun (fst x) (T×repF n)  →       
-- --          toℙrm≡base n (compΣPerm× x (adjTF×' k)) 
-- --       ≡ toℙrm≡base n x ∙ 𝕡loop k
-- -- toℙrmLem' (suc n) k x (false , snd₁) f0S f0≡ = {!!}
-- -- toℙrmLem' (suc n) (zero , snd₂) x (true , snd₁) f0S f0≡ = {!!}
-- -- toℙrmLem' (suc n) k@(suc k* , snd₂) x (true , snd₁) f0S f0≡ =
-- --   {!!}
-- --   ≡⟨ cong₂ 
-- --            {y = idΣPerm× _}
-- --           (λ u v → cong (sucℙrm _)
-- --           (toℙrm≡base n (predΣPerm× n
-- --              (compΣPerm× (compΣPerm× x (adjTF×' k)) u)
-- --               {!!})) ∙ v)
-- --           (ΣPerm×≡ (suc n)
-- --             ( {!!} ∙ {!!}))
-- --           {u = rotℙrm≡ n (Iso.fun (fst x)
-- --              (fst ((Iso.fun (ΣPerm×→Perm× _ x) Fin×0))) , {!!})}
-- --           {v = refl} {!!} ⟩
-- --   {!!}
-- --   ≡⟨ {!!} ⟩
-- --   _
-- --   ≡⟨ cong₂ {x = refl} (λ u v →
-- --           (cong (sucℙrm _)
-- --          ( toℙrm≡base n (predΣPerm× n
-- --              (compΣPerm× x v) {!!}))
-- --          ∙ u) ∙ 𝕡loop k)  {!!} {u = idΣPerm× _} {!!} ⟩
-- --   {!!} ∎
-- --   -- {!!} ∙
-- --   -- cong-∙ {!cong (sucℙrm n)!} {!!} {!!}
-- --  -- let (k0' , x'') = Iso.fun (IsoUnwindF× n)
-- --  --                       (compΣPerm× x (adjTF×' k))
-- --  --     (k0 , x') = Iso.fun (IsoUnwindF× n) x
-- --  -- in
-- --  --       cong (sucℙrm _)
-- --  --          (toℙrm≡base n (predΣPerm× n
-- --  --             (compΣPerm× (compΣPerm× x (adjTF×' k)) (invΣPerm× (rotF× k0'
-- --  --               ))) {!!})) ∙ rotℙrm≡ n k0'
-- --  --      ≡⟨ {!!} ⟩
-- --  --       (cong (sucℙrm _)
-- --  --         ( toℙrm≡base n (predΣPerm× n
-- --  --             (compΣPerm× x (invΣPerm× (rotF× k0
-- --  --               ))) {!!}))
-- --  --         ∙ rotℙrm≡ n k0) ∙ 𝕡loop k ∎ 


-- toℙrmLem'C : ∀ n k f0 f0< (x : ΣPerm× (suc n)) pL pR  →
      
--        cong (sucℙrm _)
--     (toℙrm≡base
--        n
--        (predΣPerm× n
--          (compΣPerm×
--            (compΣPerm× x (adjTF×' k))
--            (invΣPerm×
--              (uncurry rotF×< (adjFin< {suc n} (fst k) (snd k) (f0 , f0<)))
--               -- (rotF×< {n = suc n}
--               --   {!!} {!!})
--                 ))
--          pL) )
--     ∙ uncurry (rotℙrm≡< (suc n))
--        (adjFin< {suc n} (fst k) (snd k) (f0 , f0<))
--       -- rotℙrm≡< (suc n)
--       --   (fst (rotFin< {n = suc n} (fst k)
--       --     (<-weaken {n = n} (snd k)) (f0 , f0<)))
--       --   (snd (rotFin< {n = suc n} (fst k)
--       --     (<-weaken {n = n} (snd k)) (f0 , f0<)))
--         ≡
--      (cong (sucℙrm _)
--        (toℙrm≡base
--           n
--           (predΣPerm× n
--              (compΣPerm× x
--                (invΣPerm× (rotF×< f0 f0<)))
--              pR))
--       ∙ rotℙrm≡< (suc n) f0 f0<) ∙ 𝕡loop k
-- toℙrmLem'C n (zero , snd₁) zero x x₁ pL pR = {!!}
-- toℙrmLem'C n (suc k , snd₁) zero x x₁ pL pR =
--   sym (rUnit _) ∙ {!!}
--    ∙ cong-∙ (sucℙrm n)
--      (toℙrm≡base n
--         (predΣPerm× n (compΣPerm× x₁ (invΣPerm× (idΣPerm× (suc n)))) pR))
--      (𝕡loop (k , snd₁))
--    ∙ cong (_∙ 𝕡loop (suc k , snd₁))
--      (rUnit _)

-- -- (cong (sucℙrm n)
-- --        (toℙrm≡base n
-- --         (predΣPerm× n (compΣPerm× x₁ (invΣPerm× (idΣPerm× (suc n)))) pR))
-- --        ∙ (λ _ → 𝕡base))
-- --       ∙ 𝕡loop (suc k , snd₁)

--      -- cong-∙ (sucℙrm n)
--      -- {!!} (𝕡loop (k , snd₁))
-- toℙrmLem'C n k (suc f0) x = {!!}



-- toℙrmLem' : ∀ n k → (x : ΣPerm× n) →
      
--          toℙrm≡base n (compΣPerm× x (adjTF×' k)) 
--       ≡ toℙrm≡base n x ∙ 𝕡loop k
-- toℙrmLem' (suc n) k x =
--   cong (sucℙrm _)
--     (toℙrm≡base
--        n
--        (predΣPerm× n
--          (compΣPerm×
--            (compΣPerm× x (adjTF×' k))
--            {!!})
--          {!!}) )
--     ∙ {!!}
--    ≡⟨ {!!} ⟩
--    (cong (sucℙrm _)
--        (toℙrm≡base
--           n
--           (predΣPerm× n
--              (compΣPerm× x
--                (invΣPerm× {!!}))
--              {!!} ))
--       ∙ {!!}) ∙ 𝕡loop k ∎

-- -- -- -- toℙrmLem' (suc n) k@((false , bs) , p) x =
-- -- -- --   let (k0' , x'') = Iso.fun (IsoUnwindF× (suc (suc n)))
-- -- -- --                        (compΣPerm× x (adjTF× k))
-- -- -- --       (k0 , x') = Iso.fun (IsoUnwindF× (suc (suc n))) x
-- -- -- --       z = toℙrmLem' n (bs , p) x'
-- -- -- --   in cong (sucℙrm (2 + n)) (toℙrm≡base (2 + n)
-- -- -- --           ?) ∙
-- -- -- --         (rotℙrm≡ (suc (suc n)) k0')
-- -- -- --      --  ≡⟨ {!!} ⟩
-- -- -- --      -- {!!}
-- -- -- --      --  ≡⟨ {!!} ⟩
-- -- -- --      -- {!!}
-- -- -- --      --  ≡⟨ {!!} ⟩
-- -- -- --      -- {!!}
-- -- -- --       ≡⟨ {!!} ⟩
-- -- -- --      -- cong (sucℙrm (2 + n)) (toℙrm≡base (2 + n)
-- -- -- --      --        {!!}) ∙
-- -- -- --      --    (rotℙrm≡ (2 + n) k0 ∙
-- -- -- --      --        𝕡loop (Fin'fromFin× (1 + n) k))
-- -- -- --      --  ≡⟨ assoc _ _ _ ⟩
-- -- -- --        (cong (sucℙrm (2 + n))
-- -- -- --           (toℙrm≡base (2 + n) x')
-- -- -- --          ∙ rotℙrm≡ (2 + n) k0)
-- -- -- --          ∙ 𝕡loop (Fin'fromFin× (1 + n) k) ∎
-- -- -- -- -- cong (sucℙrm n) (toℙrm≡base n z) ∙ rotℙrm≡ n k

-- -- -- -- toℙrmLem : ∀ n k → (x : ΣPerm× n) →
      
-- -- -- --          toℙrm≡base n (subst (ℙerm× n 𝕡base) (λ i → 𝕡loop k (~ i)) x) 
-- -- -- --       ≡ toℙrm≡base n x ∙ 𝕡loop k
-- -- -- -- toℙrmLem (suc (suc n)) k x =
-- -- -- --    {!substℙrm𝕡loop k x !}

-- -- -- -- -- toℙrm≡ : ∀ n → (𝕡 : ℙrm {true} n)
-- -- -- -- --              → ℙerm× n 𝕡base 𝕡
-- -- -- -- --              → 𝕡base ≡ 𝕡
-- -- -- -- -- toℙrm≡ n = R𝕡elimSet'.f w
-- -- -- -- --  where
-- -- -- -- --  w : R𝕡elimSet' (λ z → ℙerm× n 𝕡base z → 𝕡base ≡ z)
-- -- -- -- --  R𝕡elimSet'.isSetA w _ = isSet→ (𝕡squash _ _ _)
-- -- -- -- --  R𝕡elimSet'.abase w = toℙrm≡base n 
-- -- -- -- --  R𝕡elimSet'.aloop w k = 
-- -- -- -- --    funTypeTransp {A = ℙrm {true} n}
-- -- -- -- --       (ℙerm× n 𝕡base) (𝕡base ≡_) _ _
-- -- -- -- --      ▷  
-- -- -- -- --       (cong (_∘ (toℙrm≡base n
-- -- -- -- --        ∘ subst (ℙerm× n 𝕡base)
-- -- -- -- --          (sym (𝕡loop k))))
-- -- -- -- --          (funExt (substInPathsL (𝕡loop k))) ∙
-- -- -- -- --                 {!!})

-- -- -- -- -- -- Goal: PathP (λ i → ℙerm× n 𝕡base (𝕡loop k i) → 𝕡base ≡ 𝕡loop k i)
-- -- -- -- -- --       (toℙrm≡base n) (toℙrm≡base n)




-- -- -- -- -- toℙrm≡-refl : ∀ n → toℙrm≡ n 𝕡base (idΣPerm× n) ≡ refl
-- -- -- -- -- toℙrm≡-refl zero = refl
-- -- -- -- -- toℙrm≡-refl (suc n) =
-- -- -- -- --   w ∙ cong (cong (sucℙrm n)) (toℙrm≡-refl n)
-- -- -- -- --  where
-- -- -- -- --  w : (cong (sucℙrm n) (toℙrm≡ n 𝕡base
-- -- -- -- --             (snd (Iso.fun (IsoUnwindF× n) (idΣPerm× (suc n))))))
-- -- -- -- --        ∙ (rotℙrm≡ n (fst (Iso.fun (IsoUnwindF× n) (idΣPerm× (suc n))))) ≡
-- -- -- -- --        (cong (sucℙrm n) (toℙrm≡ n 𝕡base (idΣPerm× n)))
-- -- -- -- --  w =
-- -- -- -- --       cong (_∙ refl)
-- -- -- -- --         (cong (cong (sucℙrm n) ∘ toℙrm≡ n 𝕡base)
-- -- -- -- --           (ΣPerm×≡ n
-- -- -- -- --             (cong Iso.fun
-- -- -- -- --               (IsoSndIdIso false (λ _ _ → refl) isSetBool)))) ∙
-- -- -- -- --        sym
-- -- -- -- --         (rUnit
-- -- -- -- --           (cong (sucℙrm n) (toℙrm≡ n 𝕡base (idΣPerm× n))))


-- -- -- -- -- -- Goal: idΣPerm× n .fst ≡ x .fst
-- -- -- -- -- -- ————————————————————————————————————————————————————————————
-- -- -- -- -- -- y : toℙrm≡ n 𝕡base x ≡ refl
-- -- -- -- -- -- x : ℙerm× n 𝕡base 𝕡base

-- -- -- -- -- isEquivFromℙrm≡ : ∀ n 𝕡 → isEquiv' (toℙrm≡ n 𝕡)
-- -- -- -- -- isEquivFromℙrm≡ n 𝕡 =
-- -- -- -- --   J (λ 𝕡 p → isContr (fiber (toℙrm≡ n 𝕡) p))
-- -- -- -- --     (((idΣPerm× n) ,
-- -- -- -- --       toℙrm≡-refl n) ,
-- -- -- -- --        uncurry λ x y →
-- -- -- -- --          Σ≡Prop (λ _ → 𝕡squash _ _ _ _ _)
-- -- -- -- --          (ΣPerm×≡ n (idΣPerm×-refl n (fst x) (snd x) y)))

-- -- -- -- -- -- Iso𝔽in≡ : ∀ n → Iso (𝕡base {true} {n = n} ≡ 𝕡base {n = n})
-- -- -- -- -- --                    (ΣPerm× n)
-- -- -- -- -- -- Iso.fun (Iso𝔽in≡ n) = fromℙrm≡ n _ _
-- -- -- -- -- -- Iso.inv (Iso𝔽in≡ n) = {!!}
-- -- -- -- -- -- Iso.rightInv (Iso𝔽in≡ n) = {!!}
-- -- -- -- -- -- Iso.leftInv (Iso𝔽in≡ n) = {!!}

-- -- -- -- -- -- Iso.fun (Iso𝔽in≡ n x y) = to𝔽Iso n x y
-- -- -- -- -- -- Iso.inv (Iso𝔽in≡ n x y) = toℙ≡ n x y 
-- -- -- -- -- -- Iso.rightInv (Iso𝔽in≡ n x y) = {!!}
-- -- -- -- -- -- Iso.leftInv (Iso𝔽in≡ n x y) = {!!}



-- -- -- -- -- -- toℙ≡bb : ∀ n → Iso (𝔽in n 𝕡base) (𝔽in n 𝕡base)
-- -- -- -- -- --                → Path (ℙrm {true} n) 𝕡base 𝕡base
-- -- -- -- -- -- toℙ≡bb zero _ = refl
-- -- -- -- -- -- toℙ≡bb (suc n) x = {!!}
-- -- -- -- -- --   -- let (k , x') = Iso.fun (unwindIsoFin× n) x
-- -- -- -- -- --   -- in cong (sucℙrm n) (toℙ≡bb n x') ∙ rotℙ _ k




-- -- -- -- -- -- UnwindF×Law : ∀ n e k →
-- -- -- -- -- --    Perm n → {!!}
-- -- -- -- -- -- UnwindF×Law = {!!}



-- -- -- -- -- -- toℙ≡bb : ∀ n → Iso (𝔽in n 𝕡base) (𝔽in n 𝕡base)
-- -- -- -- -- --                → Path (ℙrm {true} n) 𝕡base 𝕡base
-- -- -- -- -- -- toℙ≡bb zero _ = refl
-- -- -- -- -- -- toℙ≡bb (suc n) x =
-- -- -- -- -- --   let (k , x') = Iso.fun (unwindIsoFin× n) x
-- -- -- -- -- --   in cong (sucℙrm n) (toℙ≡bb n x') ∙ rotℙ _ k


-- -- -- -- -- -- toℙ≡ : ∀ n x → (Iso (𝔽in n 𝕡base) (𝔽in n x)) → (𝕡base ≡ x)
-- -- -- -- -- -- toℙ≡ n = R𝕡elimSet'.f {n = n} {true} (w {n}) 
-- -- -- -- -- --  where
-- -- -- -- -- --  open R𝕡elimSet'
-- -- -- -- -- --  w : ∀ {n} → R𝕡elimSet' λ x → (Iso (𝔽in n 𝕡base) (𝔽in n x)) → (𝕡base ≡ x)
-- -- -- -- -- --  isSetA w _ = isSetΠ λ _ → 𝕡squash _ _ _
-- -- -- -- -- --  abase w = toℙ≡bb _
-- -- -- -- -- --  aloop (w {n}) k = funTypePathP
-- -- -- -- -- --   _ _ _ _ (funExt
-- -- -- -- -- --     λ e → substInPathsL _ _ ∙ 
-- -- -- -- -- --       cong (λ x → toℙ≡bb n x ∙ 𝕡loop k)
-- -- -- -- -- --        (transportIsoR (λ i → (𝔽in n (𝕡loop k (~ i)))) e)
-- -- -- -- -- --         ∙ sym (p∙ploop≡q→p≡q∙ploop _ _ (toℙ≡bb n e) _
-- -- -- -- -- --          (sym (toℙ≡sq n k e) ∙
-- -- -- -- -- --           cong (toℙ≡bb n ∘ (compIso e)) (sym (pathToIso𝕡loop n k)))))



-- -- -- -- -- -- Iso𝔽in≡ : ∀ n x → Iso (𝕡base ≡ x) (Iso (𝔽in n 𝕡base) (𝔽in n x))
-- -- -- -- -- -- Iso.fun (Iso𝔽in≡ n x) = pathToIso ∘ cong (𝔽in n)
-- -- -- -- -- -- Iso.inv (Iso𝔽in≡ n x) = {!!} --toℙ≡ n x
-- -- -- -- -- -- Iso.rightInv (Iso𝔽in≡ n x) = {!!} --secIsoFin≡ n x
-- -- -- -- -- -- Iso.leftInv (Iso𝔽in≡ n x) = {!!} --retIsoFin≡ n x 




-- -- -- -- -- -- -- ΣPerm×→Perm : ∀ n → ΣPerm× n → Perm n
-- -- -- -- -- -- -- ΣPerm×→Perm = {!!}


-- -- -- -- -- -- -- Perm→ΣPerm× : ∀ n → Perm n → ΣPerm× n
-- -- -- -- -- -- -- Perm→ΣPerm× n = Rrec.f (w n)
-- -- -- -- -- -- --  where
-- -- -- -- -- -- --  w : ∀ n → Rrec {n = n} (ΣPerm× n)
-- -- -- -- -- -- --  Rrec.isSetA (w n) = {!!}
-- -- -- -- -- -- --  Rrec.εA (w n) = idIso , {!!}
-- -- -- -- -- -- --  Rrec.∷A (w (suc (suc n))) (k , _) e =
-- -- -- -- -- -- --    compΣPerm×  {!!} e
-- -- -- -- -- -- --  Rrec.invoA (w (suc (suc n))) (k , _) xs = {!!}
-- -- -- -- -- -- --  Rrec.braidA (w n) = {!!}
-- -- -- -- -- -- --  Rrec.commA (w n) = {!!}

-- -- -- -- -- -- -- PermIso : ∀ n → Iso (Perm n) (ΣPerm× n)
-- -- -- -- -- -- -- Iso.fun (PermIso n) = Perm→ΣPerm× n
-- -- -- -- -- -- -- Iso.inv (PermIso n) = ΣPerm×→Perm n
-- -- -- -- -- -- -- Iso.rightInv (PermIso n) = {!!}
-- -- -- -- -- -- -- Iso.leftInv (PermIso n) = {!!}

-- -- -- -- -- -- -- -- --   -- (compIso (Iso-×^-F→ n)
-- -- -- -- -- -- -- -- --   --   (compIso (domIso (
-- -- -- -- -- -- -- -- --   --     compIso (IsoFinFin× n)
-- -- -- -- -- -- -- -- --   --      (compIso e (invIso (IsoFinFin× n))))) (invIso (Iso-×^-F→ n)))) ,
-- -- -- -- -- -- -- -- --   --       PropTrunc.∣
-- -- -- -- -- -- -- -- --   --        (Iso.inv (IsoFinFin× n) ∘ Iso.inv e
-- -- -- -- -- -- -- -- --   --          ∘ Iso.fun (IsoFinFin× n)) ,
-- -- -- -- -- -- -- -- --   --         PropTrunc.∣ refl ∣₁ ∣₁

-- -- -- -- -- -- -- -- -- -- SetsIso≡-ext-fun : (isSetA : isSet A) → {e f : Iso A A} →
-- -- -- -- -- -- -- -- -- --     Iso.fun e ≡ Iso.fun f → e ≡ f
-- -- -- -- -- -- -- -- -- -- SetsIso≡-ext-fun isSetA p = 
-- -- -- -- -- -- -- -- -- --   invEq (congEquiv (isoToEquiv (isSet→Iso-Iso-≃ isSetA isSetA)))
-- -- -- -- -- -- -- -- -- --    (equivEq p) 

-- -- -- -- -- -- -- -- -- -- IsoΣPerm×Perm× : ∀ n → Iso (ΣPerm× n) (Perm× n)
-- -- -- -- -- -- -- -- -- -- Iso.fun (IsoΣPerm×Perm× n) = ΣPerm×→Perm× n
-- -- -- -- -- -- -- -- -- -- Iso.inv (IsoΣPerm×Perm× n) = Perm×→ΣPerm× n
-- -- -- -- -- -- -- -- -- -- Iso.rightInv (IsoΣPerm×Perm× n) e =
-- -- -- -- -- -- -- -- -- --   SetsIso≡-ext-fun (isSetFin× _)
-- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- Iso.leftInv (IsoΣPerm×Perm× n) = uncurry
-- -- -- -- -- -- -- -- -- --   λ e →
-- -- -- -- -- -- -- -- -- --     PropTrunc.elim (λ _ →
-- -- -- -- -- -- -- -- -- --      isSetΣ (isSet-SetsIso
-- -- -- -- -- -- -- -- -- --        (isOfHLevel×^ n 2 isSetBool)
-- -- -- -- -- -- -- -- -- --        (isOfHLevel×^ n 2 isSetBool))
-- -- -- -- -- -- -- -- -- --          (isProp→isSet ∘ snd ∘ isPermuatationA n) _ _)
-- -- -- -- -- -- -- -- -- --            (uncurry λ x →
-- -- -- -- -- -- -- -- -- --             PropTrunc.elim {!!}
-- -- -- -- -- -- -- -- -- --               λ p →
-- -- -- -- -- -- -- -- -- --                 Σ≡Prop {!!}
-- -- -- -- -- -- -- -- -- --                   (SetsIso≡-ext-fun (isOfHLevel×^ n 2 isSetBool)
-- -- -- -- -- -- -- -- -- --                    ({!!} ∙ sym p)) )
-- -- -- -- -- -- -- -- -- --          -- λ (x , p) →
-- -- -- -- -- -- -- -- -- --          --  Σ≡Prop
-- -- -- -- -- -- -- -- -- --          --    (snd ∘ isPermuatationA n)
-- -- -- -- -- -- -- -- -- --          --    (SetsIso≡-ext-fun (isOfHLevel×^ n 2 isSetBool)
-- -- -- -- -- -- -- -- -- --          --      {!p!}
-- -- -- -- -- -- -- -- -- --          --      ) 
-- -- -- -- -- -- -- -- -- --   -- Σ≡Prop (snd ∘ isPermuatationA n)
-- -- -- -- -- -- -- -- -- --   --   (SetsIso≡-ext-fun (isOfHLevel×^ n 2 isSetBool)
-- -- -- -- -- -- -- -- -- --   --   {!!})
