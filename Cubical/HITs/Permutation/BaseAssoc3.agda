{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.BaseAssoc3 where

import Cubical.Data.Nat.Base as ℕ
import Cubical.Data.Nat.Properties as ℕprops


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution

open import Cubical.Foundations.Everything
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive
-- open import Cubical.Data.Nat.Order.RecursiveMoreEquiv

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

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)


open import Cubical.Relation.Binary

-- import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint

import Cubical.HITs.Permutation.Base as B

private
  variable
    ℓ : Level
    A : Type ℓ

infixl 6 _+_

data ℕₐ⁺¹' {trunc : Type}  : Type where
 one : ℕₐ⁺¹' 
 _+_ : ℕₐ⁺¹' {trunc} → ℕₐ⁺¹' {trunc} → ℕₐ⁺¹' {trunc}
 +-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
 +-sym : ∀ m n → m + n ≡ n + m
 isSetℕₐ⁺¹' : trunc → isSet ℕₐ⁺¹' 

-- record ℕₐ⁺¹rec (h : HLevel) (A : Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--    aOne : {0 < h} → A
--    _a+_ : {0 < h} → A → A → A
--    a-assoc : ∀ x y z → x a+ (y a+ z) ≡ (x a+ y) a+ z
--    -- asquash : if trunc then (isSet A) else Unit*

--  -- f : ∀ {trunc} → {_ : if trunc then (isSet A) else Unit*} →
--  --       ℕₐ⁺¹' {if trunc then Unit else ⊥} → A
--  -- f one = aOne
--  -- f {trunc} {squashA} (x + x₁) = f {trunc} {squashA} x a+ f {trunc} {squashA}x₁
--  -- f {trunc} {squashA} (+-assoc x x₁ x₂ i) =
--  --   a-assoc
--  --    (f {trunc} {squashA} x)
--  --    (f {trunc} {squashA} x₁)
--  --    (f {trunc} {squashA} x₂) i
--  -- f {true} {squashA} (isSetℕₐ⁺¹' x x₁ x₂ x₃ y i i₁) =
--  --   squashA _ _ (cong (f {true} {squashA}) x₃) (cong f y) i i₁


record ℕₐ⁺¹rec (A : Type ℓ) : Type ℓ where
 no-eta-equality
 field
   aOne : A
   _a+_ : A → A → A
   a-assoc : ∀ x y z → x a+ (y a+ z) ≡ (x a+ y) a+ z
   a-sym : ∀ x y → x a+ y ≡ (y a+ x)
   -- asquash : if trunc then (isSet A) else Unit*

 f : ∀ {trunc} → {_ : if trunc then (isSet A) else Unit*} →
       ℕₐ⁺¹' {if trunc then Unit else ⊥} → A
 f one = aOne
 f {trunc} {squashA} (x + x₁) = f {trunc} {squashA} x a+ f {trunc} {squashA}x₁
 f {trunc} {squashA} (+-assoc x x₁ x₂ i) =
   a-assoc
    (f {trunc} {squashA} x)
    (f {trunc} {squashA} x₁)
    (f {trunc} {squashA} x₂) i
 f {trunc} {squashA} (+-sym x x₁ i) =
   a-sym
    (f {trunc} {squashA} x)
    (f {trunc} {squashA} x₁) i
 f {true} {squashA} (isSetℕₐ⁺¹' x x₁ x₂ x₃ y i i₁) =
   squashA _ _ (cong (f {true} {squashA}) x₃) (cong f y) i i₁

ℕₐ⁺¹ = ℕₐ⁺¹' {Unit}


ℕₐ : Type 
ℕₐ = Maybe ℕₐ⁺¹

infix 7 _++_++_

_++_++_ : ℕₐ⁺¹ → ℕₐ⁺¹ → ℕₐ⁺¹ → ℕₐ⁺¹
_++_++_ x y z = x + y + z

isSetℕₐ⁺¹ = isSetℕₐ⁺¹' tt


isSetℕₐ : isSet ℕₐ
isSetℕₐ = isOfHLevelMaybe 0 isSetℕₐ⁺¹


record ℕₐ⁺¹elim (A : ℕₐ⁺¹ → Type ℓ) : Type ℓ where
 no-eta-equality
 field
   aOne : A one
   _a+_ : ∀ {n m} → A n → A m → A (n + m)
   a-assoc : ∀ {n m o} (x : A n) (y : A m) (z : A o)
                 → PathP (λ i → A (+-assoc n m o i))
                   (x a+ (y a+ z))
                   ((x a+ y) a+ z)
   a-sym : ∀ {n m} (x : A n) (y : A m)
                 → PathP (λ i → A (+-sym n m i))
                   (x a+ y)
                   (y a+ x)                   
   asquash : ∀ x → (isSet (A x))

 f : ∀ x → A x
 f one = aOne
 f (x + x₁) = f x a+ f x₁
 f (+-assoc x x₁ x₂ i) = a-assoc (f x) (f x₁) (f x₂) i
 f (+-sym x x₁  i) = a-sym (f x) (f x₁) i
 f (isSetℕₐ⁺¹' x x₁ x₂ x₃ y i i₁) =
    isOfHLevel→isOfHLevelDep 2 (asquash)
      _ _
     (cong f x₃) (cong f y)
     (isSetℕₐ⁺¹' x x₁ x₂ x₃ y) i i₁

record ℕₐ⁺¹elimProp (A : ℕₐ⁺¹ → Type ℓ) : Type ℓ where
 no-eta-equality
 field
   aOne : A one
   _a+_ : ∀ {n m} → A n → A m → A (n + m)

   asquash : ∀ x → (isProp (A x))

 w : ℕₐ⁺¹elim A
 ℕₐ⁺¹elim.aOne w = aOne
 ℕₐ⁺¹elim._a+_ w = _a+_
 ℕₐ⁺¹elim.a-assoc w x y z = isProp→PathP (λ i → asquash (+-assoc _ _ _ i)) _ _
 ℕₐ⁺¹elim.a-sym w x y = isProp→PathP (λ i → asquash (+-sym _ _ i)) _ _
 ℕₐ⁺¹elim.asquash w = isProp→isSet ∘ asquash 

 f : ∀ x → A x
 f = ℕₐ⁺¹elim.f w

+-sym-one : (m : ℕₐ⁺¹') → one + m ≡ m + one
+-sym-one = ℕₐ⁺¹elimProp.f w
 where
 w : ℕₐ⁺¹elimProp (λ z → one + z ≡ z + one)
 ℕₐ⁺¹elimProp.aOne w = refl
 ℕₐ⁺¹elimProp._a+_ w {n = n} {m = m} q p = +-assoc _ _ _ ∙
  cong (_+ m) q ∙
   sym (+-assoc _ _ _)
    ∙ cong (n +_) p ∙ +-assoc _ _ _
 ℕₐ⁺¹elimProp.asquash w _ = isSetℕₐ⁺¹ _ _
 
+-sym' : ∀ (n : ℕₐ⁺¹) m → n + m ≡ m + n
+-sym' = ℕₐ⁺¹elimProp.f w
 where
 w : ℕₐ⁺¹elimProp (λ z → (m : ℕₐ⁺¹') → z + m ≡ m + z)
 ℕₐ⁺¹elimProp.aOne w = +-sym-one
 ℕₐ⁺¹elimProp._a+_ w {n} {m} p' q' o =
    sym (+-assoc _ _ _)
   ∙ (p' (m + o)
   ∙ sym (+-assoc _ _ _))
   ∙ q' ( o + n) ∙ sym (+-assoc _ _ _)
 ℕₐ⁺¹elimProp.asquash w _ = isPropΠ (λ _ → isSetℕₐ⁺¹ _ _)

isOne : ℕₐ⁺¹ → hProp ℓ-zero
isOne = ℕₐ⁺¹rec.f w {true} {isSetHProp}
 where
 w : ℕₐ⁺¹rec (hProp ℓ-zero)
 ℕₐ⁺¹rec.aOne w = L.⊤
 ℕₐ⁺¹rec._a+_ w _ _ = L.⊥
 ℕₐ⁺¹rec.a-assoc w _ _ _ = refl
 ℕₐ⁺¹rec.a-sym w _ _ = refl

-- isOne⇔one≡ : ∀ n → ⟨ isOne n L.⇔ (one ≡ n) , isSetℕₐ⁺¹ _ _ ⟩
-- isOne⇔one≡ = ℕₐ⁺¹elimProp.f w
--  where
--  w : ℕₐ⁺¹elimProp (λ z → ⟨ isOne z L.⇔ (one ≡ z) , isSetℕₐ⁺¹ one z ⟩)
--  ℕₐ⁺¹elimProp.aOne w = (λ _ → refl) , (λ _ → tt*)
--  fst (ℕₐ⁺¹elimProp._a+_ w {n} {m} x x₁) ()
--  snd (ℕₐ⁺¹elimProp._a+_ w {n} {m} x x₁) = {!!}
--  ℕₐ⁺¹elimProp.asquash w n = snd (isOne n L.⇔ (one ≡ n) , isSetℕₐ⁺¹ _ _)

one< : ℕₐ⁺¹ → hProp ℓ-zero
one< = ℕₐ⁺¹rec.f w {true} {isSetHProp}
 where
 w : ℕₐ⁺¹rec (hProp ℓ-zero)
 ℕₐ⁺¹rec.aOne w = L.⊥
 ℕₐ⁺¹rec._a+_ w _ _ = L.⊤
 ℕₐ⁺¹rec.a-assoc w _ _ _ = refl
 ℕₐ⁺¹rec.a-sym w _ _ = refl



+≢one : ∀ n m → n + m ≡ one → ⊥
+≢one n m p = subst⁻ (fst ∘ isOne) p _

ℕ→ℕₐ⁺¹ :  ℕ.ℕ → ℕₐ⁺¹
ℕ→ℕₐ⁺¹ ℕ.zero = one
ℕ→ℕₐ⁺¹ (ℕ.suc x) = one + (ℕ→ℕₐ⁺¹ x)


ℕ→ℕₐ :  ℕ.ℕ → ℕₐ
ℕ→ℕₐ ℕ.zero = nothing
ℕ→ℕₐ (ℕ.suc x) = just (ℕ→ℕₐ⁺¹ x)

ℕₐ⁺¹→ℕ : ℕₐ⁺¹ → ℕ.ℕ
ℕₐ⁺¹→ℕ = ℕₐ⁺¹rec.f w {true} {ℕprops.isSetℕ}
 where
 w : ℕₐ⁺¹rec ℕ.ℕ
 ℕₐ⁺¹rec.aOne w = 1
 ℕₐ⁺¹rec._a+_ w = ℕ._+_
 ℕₐ⁺¹rec.a-assoc w = ℕprops.+-assoc
 ℕₐ⁺¹rec.a-sym w = ℕprops.+-comm

ℕₐ⁺¹→ℕ-elimProp : ∀ {ℓ} {A : ℕ.ℕ → Type ℓ} → (∀ n → isProp (A n)) →
    (∀ n → A (ℕ.suc n)) → ∀ n → A (ℕₐ⁺¹→ℕ n) 
ℕₐ⁺¹→ℕ-elimProp {A = A} isPropA Asuc = ℕₐ⁺¹elimProp.f w
  where
   w : ℕₐ⁺¹elimProp λ z → A (ℕₐ⁺¹→ℕ z)
   ℕₐ⁺¹elimProp.aOne w = Asuc _
   ℕₐ⁺¹elimProp._a+_ w _ _ = {!!}
   ℕₐ⁺¹elimProp.asquash w = {!!}

ℕₐ→ℕ :  ℕₐ → ℕ.ℕ
ℕₐ→ℕ nothing = ℕ.zero
ℕₐ→ℕ (just x) = ℕₐ⁺¹→ℕ x


-- Isoℕℕₐ⁺¹ : Iso ℕ.ℕ ℕₐ
-- Isoℕℕₐ⁺¹ = w
--  where
--  w : Iso ℕ.ℕ ℕₐ
--  Iso.fun w = ℕ→ℕₐ
--  Iso.inv w = ℕₐ→ℕ
--  Iso.rightInv w =
--   Mb.elim _ refl
--    (ℕₐ⁺¹elimProp.f w')
--    where
--    w' : ℕₐ⁺¹elimProp _
--    ℕₐ⁺¹elimProp.aOne w' = refl
--    ℕₐ⁺¹elimProp._a+_ w' p q =
--      {!cong₂ _+_ p q!}
--    ℕₐ⁺¹elimProp.asquash w' = {!!}
--  Iso.leftInv w = {!!}

+ₐ≡+ : ∀ n m → ℕₐ⁺¹→ℕ (n + m) ≡ (ℕₐ⁺¹→ℕ n) ℕ.+ (ℕₐ⁺¹→ℕ m) 
+ₐ≡+ = ℕₐ⁺¹elimProp.f w
 where
 w : ℕₐ⁺¹elimProp (λ z → (m : ℕₐ⁺¹') → ℕₐ⁺¹→ℕ (z + m) ≡ ℕₐ⁺¹→ℕ z ℕ.+ ℕₐ⁺¹→ℕ m)
 ℕₐ⁺¹elimProp.aOne w m = refl
 ℕₐ⁺¹elimProp._a+_ w {n} {m} q p m' =
    (cong ℕₐ⁺¹→ℕ (sym (+-assoc n m m')) ∙∙ q (m + m')
      ∙∙ cong ((ℕₐ⁺¹→ℕ n) ℕ.+_) (p m'))
     ∙∙ ℕprops.+-assoc (ℕₐ⁺¹→ℕ n) (ℕₐ⁺¹→ℕ m) (ℕₐ⁺¹→ℕ m') ∙∙
     (cong (ℕ._+ (ℕₐ⁺¹→ℕ m') ) (sym (q m)) ∙ cong (ℕ._+ (ℕₐ⁺¹→ℕ m')) (q m))

 ℕₐ⁺¹elimProp.asquash w _ = isPropΠ λ _ → ℕprops.isSetℕ _ _

-- record : ?

-- Finₐ : ℕₐ⁺¹' {⊥} → Type
-- Finₐ one = Unit 
-- Finₐ (x + x₁) = Finₐ x ⊎ Finₐ x₁
-- Finₐ (+-assoc x x₁ x₂ i) =
--  ua (⊎-assoc-≃ {A = Finₐ x} {B = Finₐ x₁} {C = Finₐ x₂}) (~ i) 

-- toTrunc : {!!}
-- toTrunc = {!!}

FinSucUnit⊎ : ∀ n → Iso (Fin (ℕ.suc n)) (Unit ⊎ Fin n)
FinSucUnit⊎ n = w
 where
 w : Iso (Fin (ℕ.suc n)) (Unit ⊎ Fin n)
 Iso.fun w (ℕ.zero , snd₁) = inl _
 Iso.fun w (ℕ.suc fst₁ , snd₁) = inr (fst₁ , snd₁)
 Iso.inv w (inl x) = ℕ.zero , _
 Iso.inv w (inr x) = ℕ.suc (fst x) , (snd x)
 Iso.rightInv w (inl x) = refl
 Iso.rightInv w (inr (fst₁ , snd₁)) = refl
 Iso.leftInv w (ℕ.zero , snd₁) = refl
 Iso.leftInv w (ℕ.suc fst₁ , snd₁) = refl

Fin⊎ : ∀ n m → Iso (Fin (n ℕ.+ m)) (Fin n ⊎ Fin m)
Fin⊎ ℕ.zero m =
 compIso (invIso ⊎-⊥-Iso)
   (compIso ⊎-swap-Iso (⊎Iso (compIso (invIso (ΣEmptyIso _)) Σ-swap-Iso) idIso))
Fin⊎ (ℕ.suc n) m =
  compIso (FinSucUnit⊎ _)
   (compIso (compIso (⊎Iso idIso (Fin⊎ n m))
    (invIso ⊎-assoc-Iso)) (⊎Iso (invIso (FinSucUnit⊎ _)) idIso)) 

Fin⊎≡ : ∀ n m →  (Fin (n ℕ.+ m)) ≡ (Fin n ⊎ Fin m)
Fin⊎≡ n m = ua (isoToEquiv (Fin⊎ n m))


+-hlp-sing-Fin : (n m : ℕₐ⁺¹) →
     Fin (ℕₐ⁺¹→ℕ (n + m)) ≡ (Fin (ℕₐ⁺¹→ℕ n) ⊎ Fin (ℕₐ⁺¹→ℕ m))
+-hlp-sing-Fin n m  =
  cong Fin (+ₐ≡+ n m)
   ∙ Fin⊎≡ (ℕₐ⁺¹→ℕ n) (ℕₐ⁺¹→ℕ m)  

module _ {ℓ} {A : Type ℓ} where

 ×^-+-≃ : ∀ n m →  (A ×^ n × A ×^ m) ≃ (A ×^ (n ℕ.+ m))  
 ×^-+-≃ (ℕ.zero) m = isoToEquiv (iso snd (_ ,_) (λ _ → refl) λ _ → refl)
 ×^-+-≃ (ℕ.suc n) m = Σ-assoc-≃ ∙ₑ ≃-× (idEquiv _) (×^-+-≃ n m)

 ×^-+-≡ : ∀ n m →  (A ×^ n × A ×^ m) ≡ (A ×^ (n ℕ.+ m))  
 ×^-+-≡ n m = ua (×^-+-≃ n m)


module _ {ℓ} (A : Type ℓ) where

 -- 𝑽' : ℕₐ⁺¹rec (Type ℓ)
 -- 𝑽' = {!!}
 -- -- ℕₐ⁺¹rec.aOne 𝑽' = A
 -- -- ℕₐ⁺¹rec._a+_ 𝑽' = _×_
 -- -- ℕₐ⁺¹rec.a-assoc 𝑽' _ _ _ = sym (ua Σ-assoc-≃)
 -- -- ℕₐ⁺¹rec.a-sym 𝑽' _ _ _ = {!!}

 -- -- module _ (isSetA : isSet A) where

 -- singl𝑽 : (x : ℕₐ⁺¹) → singl (A ×^ (ℕₐ⁺¹→ℕ x))
 -- singl𝑽 = ℕₐ⁺¹elim.f w
 --  where
 --   w : ℕₐ⁺¹elim (λ z → singl (A ×^ ℕₐ⁺¹→ℕ z))
 --   ℕₐ⁺¹elim.aOne w = _ , isoToPath (iso fst (_, _) (λ _ → refl) λ _ → refl)
 --   fst ((w ℕₐ⁺¹elim.a+ (x , x=)) (y , y=)) = x × y
 --   snd (((ℕₐ⁺¹elim._a+_ w {n} {m}) (x , x=)) (y , y=)) =
 --      (sym (ua (×^-+-≃ (ℕₐ⁺¹→ℕ n) (ℕₐ⁺¹→ℕ m)))) ∙  cong₂ _×_ x= y=
 --   ℕₐ⁺¹elim.a-assoc w {n} {m} {o} (x , x=) (y , y=) (z , z=) =
 --     ΣPathP (sym (ua Σ-assoc-≃)
 --           , {!!})
 --   ℕₐ⁺¹elim.a-sym  w {n} {m} (x , x=) (y , y=) =
 --      ΣPathP ((sym (cong₂ _×_ x= y=) ∙ ×^-+-≡ (ℕₐ⁺¹→ℕ n) (ℕₐ⁺¹→ℕ m)) ∙∙
 --               cong (A ×^_) (ℕprops.+-comm (ℕₐ⁺¹→ℕ n) (ℕₐ⁺¹→ℕ m))
 --              ∙∙ (sym (×^-+-≡ (ℕₐ⁺¹→ℕ m) (ℕₐ⁺¹→ℕ n)) ∙ cong₂ _×_ y= x=)
 --        , {!!}) 
 --   ℕₐ⁺¹elim.asquash w = {!!}
 --  -- w : ℕₐ⁺¹elim (λ z → singl (A ×^ ℕₐ→ℕ z))
 --  -- ℕₐ⁺¹elim.aOne w = _ , isoToPath (iso fst (_, _) (λ _ → refl) λ _ → refl) 
 --  -- fst ((w ℕₐ⁺¹elim.a+ (x , x=)) (y , y=)) = x × y
 --  -- snd (((ℕₐ⁺¹elim._a+_ w {n} {m}) (x , x=)) (y , y=)) =
 --  --   (sym (ua (×^-+-≃ (ℕₐ→ℕ n) (ℕₐ→ℕ m)))) ∙  cong₂ _×_ x= y=
 --  -- ℕₐ⁺¹elim.a-assoc w {n} {m} {o} x y z =
 --  --  ΣPathP (sym (ua Σ-assoc-≃) ,
 --  --    {!!})
 --  -- -- fst (ℕₐelim.a-assoc w {n} {m} {o} x y z i) =
 --  -- --   sym (ua (Σ-assoc-≃ {A = fst x} {B = λ _ → fst y} {C = λ _ _ → fst z})) i
 --  -- -- snd (ℕₐelim.a-assoc w {n} {m} {o} x y z i) =
 --  -- --   {!!}
 --  -- ℕₐelim.asquash w _ = isOfHLevelPlus {n = 0} 2 (isContrSingl _)

--  𝑽 : ℕₐ → Type ℓ
--  𝑽 = fst ∘ singl𝑽

-- allFalse𝑩 : ∀ n → 𝑽 Bool n → hProp ℓ-zero
-- allFalse𝑩 = ℕₐelim.f w
--  where
--  w : ℕₐelim (λ z → 𝑽 Bool z → hProp ℓ-zero)
--  ℕₐelim.aOne w false = L.⊤
--  ℕₐelim.aOne w true = L.⊥
--  ℕₐelim._a+_ w {n} {m} Fn Fm = λ (x , y) → Fn x L.⊓ Fm y
--  ℕₐelim.a-assoc w {n} {m} {o} Fn Fm Fo i q =
--    let q' = unglue (i ∨ ~ i) q
--    in L.⊓-assoc (Fn (fst q')) (Fm (fst (snd q'))) ((Fo (snd (snd q')))) i

--  ℕₐelim.asquash w _ = isSet→ isSetHProp

-- onlyOneTrue𝑩 : ∀ n → 𝑽 Bool n → hProp ℓ-zero
-- onlyOneTrue𝑩 = ℕₐelim.f w
--  where
--  w : ℕₐelim (λ z → 𝑽 Bool z → hProp ℓ-zero)
--  ℕₐelim.aOne w false = L.⊥
--  ℕₐelim.aOne w true = L.⊤
--  ℕₐelim._a+_ w {n} {m} Fn Fm =
--    λ (x , y) → (Fn x L.⊓ allFalse𝑩 n x) L.⊔ (Fm y L.⊓ allFalse𝑩 m y)
--  ℕₐelim.a-assoc w {n} {m} {o} Fn Fm Fo i q =
--    let q' = unglue (i ∨ ~ i) q
--    in {!!}
--       -- funExtDep λ {x₀} {x₁} p →
--       --   λ i →
--       --     let q = sym (ua-ungluePath _ (symP p)) i
--       --     in L.⊓-assoc (Fn (fst q)) (Fm (fst (snd q))) ((Fo (snd (snd q)))) i

--  ℕₐelim.asquash w _ = isSet→ isSetHProp



pattern suc k = one + k

infixl 6 _+ₐ_ _ₐ+_ _⊹_

_+ₐ_ : ℕₐ → ℕₐ⁺¹ → ℕₐ⁺¹
nothing +ₐ x₁ = x₁
just x +ₐ x₁ = x + x₁

_ₐ+_ : ℕₐ⁺¹ → ℕₐ →  ℕₐ⁺¹
x ₐ+ nothing = x
x ₐ+ just x₁ = x + x₁

_⊹ₐ_ : ℕₐ → ℕₐ⁺¹ → ℕₐ
x ⊹ₐ y = just (x +ₐ y)

_ₐ⊹_ : ℕₐ⁺¹ → ℕₐ → ℕₐ
x ₐ⊹ y = just (x ₐ+ y)

_⊹_ : ℕₐ → ℕₐ → ℕₐ
nothing ⊹ x₁ = x₁
just x ⊹ x₁ = x ₐ⊹ x₁

infix 7 _++ₐ_ₐ++_

_++ₐ_ₐ++_ : ℕₐ → ℕₐ⁺¹ → ℕₐ → ℕₐ⁺¹
_++ₐ_ₐ++_ x y z = x +ₐ y ₐ+ z


ₐ+ₐ-assoc : ∀ l c r →
   l +ₐ (c ₐ+ r) ≡ l +ₐ c ₐ+ r 
ₐ+ₐ-assoc nothing c r = refl
ₐ+ₐ-assoc (just x) c nothing = refl
ₐ+ₐ-assoc (just x) c (just x₁) = +-assoc _ _ _



record AdjacentBundles' (n : ℕₐ⁺¹) : Type₀ where
 constructor 𝕒𝕓'
 field
  l r  : ℕₐ⁺¹
  <n : (l + r) ≡ n


record AdjacentBundles (n : ℕₐ⁺¹) : Type₀ where
 constructor 𝕒𝕓
 field
  lPad : ℕₐ
  l r  : ℕₐ⁺¹
  rPad : ℕₐ
  <n : lPad +ₐ (l + r) ₐ+ rPad ≡ n


swapAB : ∀ {n} → AdjacentBundles n → AdjacentBundles n
swapAB (𝕒𝕓 lPad l r rPad <n) =
  𝕒𝕓 lPad r l rPad (cong (λ x → (lPad +ₐ x ₐ+ rPad)) (+-sym r l) ∙ <n)


swapAB' : ∀ {n} → (x : AdjacentBundles n) → _ → AdjacentBundles n
swapAB' (𝕒𝕓 lPad l r rPad <n) p =
  𝕒𝕓 lPad r l rPad p


-- -- +-suc : ∀ trunc → (m n : ℕₐ⁺¹ {trunc}) → m + (suc n) ≡ suc (m + n)
-- -- +-suc = {!!}

suc' : ℕₐ → ℕₐ
suc' = just ∘ Mb.rec one suc

-- sucAB : ∀ {n} → AdjacentBundles n → AdjacentBundles (suc n)
-- AdjacentBundles.lPad (sucAB x) = suc' (AdjacentBundles.lPad x)
-- AdjacentBundles.l (sucAB x) = AdjacentBundles.l x
-- AdjacentBundles.r (sucAB x) = AdjacentBundles.r x
-- AdjacentBundles.rPad (sucAB x) = AdjacentBundles.rPad x
-- AdjacentBundles.<n (sucAB {n} (𝕒𝕓 lPad l r rPad <n)) = w lPad rPad <n
--  where
--  w : ∀ lPad rPad → lPad +ₐ (l + r) ₐ+ rPad ≡ n
--      →  Mb.rec one (_+_ one) lPad + (l + r) ₐ+ rPad ≡ suc n
--  w nothing nothing p = cong suc p
--  w nothing (just x) p = sym (+-assoc _ _ _) ∙ cong suc p
--  w (just x) nothing p = sym (+-assoc _ _ _) ∙ cong suc p
--  w (just x) (just x₁) p = ( sym (+-assoc _ _ _) ∙ sym (+-assoc _ _ _) ∙ cong suc (+-assoc _ _ _)) ∙ cong suc p


m+AB : ∀ m {n} → AdjacentBundles n → AdjacentBundles (m + n)
AdjacentBundles.lPad (m+AB m x) = (m ₐ⊹ AdjacentBundles.lPad x)
AdjacentBundles.l (m+AB m x) = AdjacentBundles.l x
AdjacentBundles.r (m+AB m x) = AdjacentBundles.r x
AdjacentBundles.rPad (m+AB m x) = AdjacentBundles.rPad x
AdjacentBundles.<n (m+AB m {n} (𝕒𝕓 lPad l r rPad <n)) = w lPad rPad <n
 where
 w : ∀ lPad rPad → lPad +ₐ (l + r) ₐ+ rPad ≡ n
     →  m ₐ+  lPad + (l + r) ₐ+ rPad ≡ m + n
 w nothing nothing p = cong (m +_) p
 w nothing (just x) p = sym (+-assoc _ _ _) ∙ cong (m +_) p
 w (just x) nothing p = sym (+-assoc _ _ _) ∙ cong (m +_) p
 w (just x) (just x₁) p = ( sym (+-assoc _ _ _) ∙ sym (+-assoc _ _ _) ∙ cong (m +_) (+-assoc _ _ _)) ∙ cong (m +_) p


AB+m : ∀ m {n} → AdjacentBundles n → AdjacentBundles (n + m)
AdjacentBundles.lPad (AB+m m x) = AdjacentBundles.lPad x
AdjacentBundles.l (AB+m m x) = AdjacentBundles.l x
AdjacentBundles.r (AB+m m x) = AdjacentBundles.r x
AdjacentBundles.rPad (AB+m m x) = AdjacentBundles.rPad x ⊹ₐ m
AdjacentBundles.<n (AB+m m {n} (𝕒𝕓 lPad l r rPad <n)) = w lPad rPad <n
 where
 w : ∀ lPad rPad → lPad +ₐ (l + r) ₐ+ rPad ≡ n
     →  lPad +ₐ (l + r) + (rPad +ₐ m) ≡ n + m
 w _ nothing p = cong (_+ m) p
 w _ (just x) p = +-assoc _ _ _ ∙ cong (_+ m) p
    


        



data ℙrmₐ {trunc : Bool} (n : ℕₐ⁺¹) : Type₀ where 
  𝕡base : ℙrmₐ n
  
  𝕡loop' : AdjacentBundles n → 𝕡base ≡ 𝕡base

  𝕡invol' : ∀ ab p → 𝕡loop' (swapAB' ab p) ≡ sym (𝕡loop' ab)
  𝕡hex' : ∀ lPad rPad l c r → ∀ p p' p'' →
     Square {A = ℙrmₐ {trunc} n}
       (𝕡loop' (𝕒𝕓 lPad l c (r ₐ⊹ rPad) p''))
       (𝕡loop' (𝕒𝕓 lPad l (c + r) rPad p))
       refl
       (𝕡loop' (𝕒𝕓 (lPad ⊹ₐ c) l r rPad p'))
       

  𝕡comm :
      ∀ lPad cPad rPad l r l' r' → ∀ p p' →
     Square {A = ℙrmₐ {trunc} n}
       (𝕡loop' (𝕒𝕓 lPad l r ((cPad +ₐ (l' + r')) ₐ⊹ rPad) p'))       
       (𝕡loop' (𝕒𝕓 lPad l r ((cPad +ₐ (l' + r')) ₐ⊹ rPad) p'))
       (𝕡loop' (𝕒𝕓 (lPad ⊹ₐ ((l + r) ₐ+ cPad)) l' r' rPad p))
       (𝕡loop' (𝕒𝕓 (lPad ⊹ₐ ((l + r) ₐ+ cPad)) l' r' rPad p))

  𝕡over : ∀ lPad rPad l x x' → ∀ p p' p'' →
     Square {A = ℙrmₐ {trunc} n}
       (𝕡loop' (𝕒𝕓 (lPad ⊹ₐ l) x x' rPad p'))       
       (𝕡loop' (𝕒𝕓 lPad x' x (l  ₐ⊹ rPad) p''))
       (𝕡loop' (𝕒𝕓 lPad l (x' + x) rPad p))
       (𝕡loop' (𝕒𝕓 lPad l (x' + x) rPad p))

  𝕡squash : Bool→Type trunc → isGroupoid (ℙrmₐ n)

-- 𝕡loopGap : {!!}
-- 𝕡loopGap = {!!}

-- 𝕡overGap : ∀ n lPad cPad rPad l x x' → ∀ p p' p'' →
--    Square {A = ℙrmₐ {true} n}
--      (𝕡loop' (𝕒𝕓 (lPad ⊹ₐ (l ₐ+ cPad)) x x' rPad p'))       
--      (𝕡loop' (𝕒𝕓 lPad x' x ((cPad +ₐ l)  ₐ⊹ rPad) p''))
--      (𝕡loop' (𝕒𝕓 lPad l (x' + x) rPad p))
--      (𝕡loop' (𝕒𝕓 lPad l (x' + x) rPad p))
-- 𝕡overGap = {!!}

record ℙrmRec (A : Type ℓ) : Type ℓ where
 field
  abase : ℕₐ⁺¹ → A
  aloop : ∀ n → AdjacentBundles n → abase n ≡ abase n
  ainvol : ∀ n ab p → aloop n  (swapAB' ab p) ≡ sym (aloop n ab)
  ahex : ∀ n lPad rPad l c r → ∀ p p' p'' →
     Square {A = A}
       (aloop n (𝕒𝕓 lPad l c (r ₐ⊹ rPad) p''))
       (aloop n (𝕒𝕓 lPad l (c + r) rPad p))
       refl
       (aloop n (𝕒𝕓 (lPad ⊹ₐ c) l r rPad p'))       
  acomm :
      ∀ n lPad cPad rPad l r l' r' → ∀ p p' →
     Square {A = A}
       (aloop n (𝕒𝕓 lPad l r ((cPad +ₐ (l' + r')) ₐ⊹ rPad) p'))       
       (aloop n (𝕒𝕓 lPad l r ((cPad +ₐ (l' + r')) ₐ⊹ rPad) p'))
       (aloop n (𝕒𝕓 (lPad ⊹ₐ ((l + r) ₐ+ cPad)) l' r' rPad p))
       (aloop n (𝕒𝕓 (lPad ⊹ₐ ((l + r) ₐ+ cPad)) l' r' rPad p))
  aover : ∀ n lPad rPad l x x' → ∀ p p' p'' →
     Square {A = A}
       (aloop n (𝕒𝕓 (lPad ⊹ₐ l) x x' rPad p'))       
       (aloop n (𝕒𝕓 lPad x' x (l ₐ⊹ rPad) p''))
       (aloop n (𝕒𝕓 lPad l (x' + x) rPad p))
       (aloop n (𝕒𝕓 lPad l (x' + x) rPad p))

  asquash : isGroupoid A
  
 f : ∀ {n} → ℙrmₐ {true} n → A
 f {n} 𝕡base = abase n
 f {n} (𝕡loop' x i) = aloop n x i
 f {n} (𝕡invol' ab p i i₁) = ainvol n ab p i i₁
 f {n} (𝕡hex' lPad rPad l c r p p' p'' i i₁) =
   ahex n lPad rPad l c r p p' p'' i i₁
 f {n} (𝕡comm lPad cPad rPad l r l' r' p p' i i₁) =
   acomm n lPad cPad rPad l r l' r' p p' i i₁
 f {n} (𝕡over lPad rPad l x x' p p' p'' i i₁) =
   aover n lPad rPad l x x' p p' p'' i i₁
 f (𝕡squash x x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) =
  asquash _ _ _ _
    (λ i₂ x₆ → f (x₄ i₂ x₆))
    (λ i₂ x₆ → f (y₁ i₂ x₆))
      i i₁ x₅

record ℙrmRecElimN (A : ℕₐ⁺¹ → Type ℓ) : Type ℓ where
 field
  abase : ∀ n → A n
  aloop : ∀ n → AdjacentBundles n → abase n ≡ abase n
  ainvol : ∀ n ab p → aloop n  (swapAB' ab p) ≡ sym (aloop n ab)
  ahex : ∀ n lPad rPad l c r → ∀ p p' p'' →
     Square {A = A n}
       (aloop n (𝕒𝕓 lPad l c (r ₐ⊹ rPad) p''))
       (aloop n (𝕒𝕓 lPad l (c + r) rPad p))
       refl
       (aloop n (𝕒𝕓 (lPad ⊹ₐ c) l r rPad p'))       
  acomm :
      ∀ n lPad cPad rPad l r l' r' → ∀ p p' →
     Square {A = A n}
       (aloop n (𝕒𝕓 lPad l r ((cPad +ₐ (l' + r')) ₐ⊹ rPad) p'))       
       (aloop n (𝕒𝕓 lPad l r ((cPad +ₐ (l' + r')) ₐ⊹ rPad) p'))
       (aloop n (𝕒𝕓 (lPad ⊹ₐ ((l + r) ₐ+ cPad)) l' r' rPad p))
       (aloop n (𝕒𝕓 (lPad ⊹ₐ ((l + r) ₐ+ cPad)) l' r' rPad p))
  aover : ∀ n lPad rPad l x x' → ∀ p p' p'' →
     Square {A = A n}
       (aloop n (𝕒𝕓 (lPad ⊹ₐ l) x x' rPad p'))       
       (aloop n (𝕒𝕓 lPad x' x (l ₐ⊹ rPad) p''))
       (aloop n (𝕒𝕓 lPad l (x' + x) rPad p))
       (aloop n (𝕒𝕓 lPad l (x' + x) rPad p))

  asquash : ∀ n → isGroupoid (A n)
  
 f : ∀ {n} → ℙrmₐ {true} n → A n
 f {n} 𝕡base = abase n
 f {n} (𝕡loop' x i) = aloop n x i
 f {n} (𝕡invol' ab p i i₁) = ainvol n ab p i i₁
 f {n} (𝕡hex' lPad rPad l c r p p' p'' i i₁) =
   ahex n lPad rPad l c r p p' p'' i i₁
 f {n} (𝕡comm lPad cPad rPad l r l' r' p p' i i₁) =
   acomm n lPad cPad rPad l r l' r' p p' i i₁
 f {n} (𝕡over lPad rPad l x x' p p' p'' i i₁) =
   aover n lPad rPad l x x' p p' p'' i i₁
 f {n} (𝕡squash x x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) =
   asquash n _ _ _ _
     (λ i₂ x₆ → f {n} (x₄ i₂ x₆))
     (λ i₂ x₆ → f {n} (y₁ i₂ x₆))
       i i₁ x₅

record ℙrmElimSet (n : ℕₐ⁺¹) (A : ℙrmₐ {true} n → Type ℓ) : Type ℓ where
 field
  abase : A 𝕡base
  aloop : (ab : AdjacentBundles n)
    → PathP (λ i → A (𝕡loop' ab i)) abase abase

  asquash : ∀ p → isSet (A p)

 f : (p : ℙrmₐ {true} n) → A p
 f 𝕡base = abase
 f (𝕡loop' x i) = aloop x i
 f (𝕡invol' ab p i i₁) =
   isSet→SquareP
     (λ i i₁ → asquash (𝕡invol' ab p i i₁))
     (aloop (swapAB' ab p)) (symP (aloop ab))
     refl refl
     i i₁

 f (𝕡hex' lPad rPad l c r p p' p'' i i₁) =
   isSet→SquareP
     (λ i i₁ → asquash (𝕡hex' lPad rPad l c r p p' p'' i i₁))
     (aloop (𝕒𝕓 lPad l c (r ₐ⊹ rPad) p''))
     (aloop (𝕒𝕓 lPad l (c + r) rPad p))
     refl (aloop (𝕒𝕓 (lPad ⊹ₐ c) l r rPad p'))
     i i₁

 f (𝕡comm lPad cPad rPad l r l' r' p p' i i₁) =
   isSet→SquareP
     (λ i i₁ → asquash (𝕡comm lPad cPad rPad l r l' r' p p' i i₁))
     (aloop (𝕒𝕓 lPad l r ((cPad +ₐ (l' + r')) ₐ⊹ rPad) p'))
     (aloop (𝕒𝕓 lPad l r ((cPad +ₐ (l' + r')) ₐ⊹ rPad) p'))
     (aloop (𝕒𝕓 (lPad ⊹ₐ ((l + r) ₐ+ cPad)) l' r' rPad p))
     (aloop (𝕒𝕓 (lPad ⊹ₐ ((l + r) ₐ+ cPad)) l' r' rPad p))
     i i₁

 f (𝕡over lPad rPad l x x' p p' p'' i i₁) =
   isSet→SquareP
     (λ i i₁ → asquash (𝕡over lPad rPad l x x' p p' p'' i i₁))
     (aloop (𝕒𝕓 (lPad ⊹ₐ l) x x' rPad p'))
     (aloop (𝕒𝕓 lPad x' x (l ₐ⊹ rPad) p''))
     (aloop (𝕒𝕓 lPad l (x' + x) rPad p))
     (aloop (𝕒𝕓 lPad l (x' + x) rPad p))
     i i₁

 f (𝕡squash x x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) =

     isOfHLevel→isOfHLevelDep 3
      (isSet→isGroupoid ∘ asquash ) _ _ _ _
     (λ i₂ x₆ → f (x₄ i₂ x₆))
     (λ i₂ x₆ → f (y₁ i₂ x₆))
     (𝕡squash x x₁ x₂ x₃ y x₄ y₁)
       i i₁ x₅

record ℙrmElimProp (n : ℕₐ⁺¹) (A : ℙrmₐ {true} n → Type ℓ) : Type ℓ where
 field
  abase : A 𝕡base
  asquash : ∀ p → isProp (A p)

 fR : ℙrmElimSet n A
 ℙrmElimSet.abase fR = abase
 ℙrmElimSet.aloop fR ab = isProp→PathP (λ i → asquash (𝕡loop' ab i)) _ _
 ℙrmElimSet.asquash fR = isProp→isSet ∘ asquash

 f : (p : ℙrmₐ {true} n) → A p
 f =  ℙrmElimSet.f fR



+𝕡 : ∀ n {m} → ℙrmₐ {true} m → ℙrmₐ {true} (n + m) 
+𝕡 n = ℙrmRecElimN.f w
 where
 open ℙrmRecElimN
 w : ℙrmRecElimN (λ m → ℙrmₐ (n + m))
 abase w _ = 𝕡base
 aloop w m x = 𝕡loop' (m+AB n x)
 ainvol w m ab p = 𝕡invol' _ _
 ahex w m lPad rPad l c r p p' p'' =
  let z = AdjacentBundles.<n (m+AB n (𝕒𝕓 (lPad ⊹ₐ c) l r rPad p'))
  in flipSquare
      (flipSquare (𝕡hex' _ _ _ _ _ _
        ({!!} ∙ z) _)
        ▷ λ j →
         𝕡loop' (𝕒𝕓 {!!} l r rPad {!!}))

 acomm w = {!!}
 aover w = {!!}
 asquash w = {!!}

𝕡+ : ∀ n {m} → ℙrmₐ {true} m → ℙrmₐ {true} (m + n) 
𝕡+ n = ℙrmRecElimN.f w
 where
 open ℙrmRecElimN
 w : ℙrmRecElimN (λ m → ℙrmₐ (m + n))
 abase w _ = 𝕡base
 aloop w m x = 𝕡loop' (AB+m n x)
 ainvol w m ab p = 𝕡invol' _ _
 ahex w m lPad rPad l c r p p' p'' = {!!}
  -- let z = AdjacentBundles.<n (m+AB n (𝕒𝕓 (lPad ⊹ₐ c) l r rPad p'))
  -- in flipSquare
  --     (flipSquare (𝕡hex' _ _ _ _ _ _
  --       ({!!} ∙ z) _)
  --       ▷ λ j →
  --        𝕡loop' (𝕒𝕓 {!!} l r rPad {!!}))

 acomm w = {!!}
 aover w = {!!}
 asquash w = {!!}


𝕡· : ∀ {n} → ℙrmₐ {true} n → ∀ {m} →  ℙrmₐ {true} m → ℙrmₐ {true} (n + m) 
𝕡· = ℙrmRecElimN.f
   {A = λ n → ∀ {m} →  ℙrmₐ {true} m → ℙrmₐ {true} (n + m)} w
 where
 open ℙrmRecElimN
 w : ℙrmRecElimN _
 abase w = +𝕡
 aloop w n abₙ = implicitFunExt
   λ {m} → funExt (ℙrmElimSet.f {n = m} (w' m) )
  where
  open ℙrmElimSet
  w' : ∀ m → ℙrmElimSet m _
  abase (w' m) = cong (𝕡+ m {n}) (𝕡loop' abₙ) 
  aloop (w' m) abₘ =
    whiskSq.sq' _
      (𝕡comm
        (lPad abₙ)
        (rPad abₙ ⊹ lPad abₘ)
        (rPad abₘ)
        (l abₙ) (r abₙ)
        (l abₘ) (r abₘ)
        {!!} {!!})
      {!!} {!!} {!!} {!!}
    where
    open AdjacentBundles
  asquash (w' m) = {!!}
 ainvol w = {!!}
 ahex w = {!!}
 acomm w = {!!}
 aover w = {!!}
 asquash w = {!!}


-- Goal: ℙrmₐ (+-sym (lenFCSG⊥ x) (lenFCSG⊥ x₁) i)
-- ———— Boundary (wanted) —————————————————————————————————————
-- i = i0 ⊢ 𝕡· (fromFCSG⊥' x) (fromFCSG⊥' x₁)
-- i = i1 ⊢ 𝕡· (fromFCSG⊥' x₁) (fromFCSG⊥' x)

𝕡loop : ∀ lPad l r rPad →
     PathP (λ i → ℙrmₐ {true} (lPad +ₐ +-sym l r i ₐ+ rPad))
       𝕡base
       𝕡base
𝕡loop lPad l r rPad i =
 𝕡loop' (𝕒𝕓 lPad l r rPad λ j → lPad +ₐ +-sym l r (j ∧ i) ₐ+ rPad) i


𝕡·-comm : ∀ {n m} → (x : ℙrmₐ {true} n)
         (y : ℙrmₐ {true} m) → 
     PathP (λ i → ℙrmₐ {true} (+-sym n m i))
       (𝕡· x y)
       (𝕡· y x)
𝕡·-comm {n} {m} =  ℙrmElimSet.f w
 where
 open AdjacentBundles
 open ℙrmElimSet
 w : ℙrmElimSet _ _
 abase w = ℙrmElimSet.f w'
  where
  open ℙrmElimSet
  w' : ℙrmElimSet _ _
  abase w' = 𝕡loop {!!} n m {!!}
  aloop w' = {!!}
  asquash w' = {!!}
 aloop w = {!!}
 asquash w = {!!}
 
-- 𝕡·-assoc : ∀ {n m o} → (x : ℙrmₐ {true} n)
--          (y : ℙrmₐ {true} m)
--          (z : ℙrmₐ {true} o) → 
--      PathP (λ i → ℙrmₐ {true} (+-assoc n m o i))
--        (𝕡· x (𝕡· y z))
--        (𝕡· (𝕡· x y) z)
-- 𝕡·-assoc {n} {m} {o} = ℙrmElimSet.f w
--  where
--  open ℙrmElimSet
--  w : ℙrmElimSet _ _
--  abase w = ℙrmElimSet.f w'
--   where
--   w' : ℙrmElimSet _ _
--   abase w' = ℙrmElimSet.f w''
--    where
--    w'' : ℙrmElimSet _ _
--    abase w'' = λ _ → 𝕡base
--    aloop w'' ab = flipSquareP {!!}
--    asquash w'' = {!!}
--   aloop w' abₘ = funExt (ℙrmElimProp.f w'')
--    where
--    open ℙrmElimProp
--    w'' : ℙrmElimProp _ _
--    abase w'' = {!!}
--    asquash w'' = {!!}
  
--   asquash w' = {!!}
--  aloop w = {!!}
--  asquash w _ = isSetΠ2 λ _ _ → {!!}


-- 𝕡invol : ∀ lPad l r rPad →
--      SquareP (λ i j → ℙrmₐ {true} (lPad +ₐ
--                 isSetℕₐ⁺¹ (l + r) (r + l)
--                   (+-sym _ _) (sym (+-sym _ _)) i j ₐ+ rPad))
--        (𝕡loop lPad l r rPad )
--        (symP (𝕡loop lPad r l rPad))
--        refl
--        refl

-- 𝕡invol lPad l r rPad i j = 
--  𝕡invol' (𝕒𝕓 lPad r l rPad
--     (cong (lPad ++ₐ_ₐ++ rPad) (
--       isSet→isSet' isSetℕₐ⁺¹
--          (λ i₁ → +-sym l r (j ∨ ~ i₁))
--          (λ i₁ → +-sym r l (i₁ ∧ ~ j))
--          refl
--          (λ i → isSetℕₐ⁺¹ (l + r) (r + l) (+-sym l r) (sym (+-sym r l)) i j)
--          i))
--          )
--   (cong (lPad ++ₐ_ₐ++ rPad) (isSet→isSet' isSetℕₐ⁺¹
--         (λ i₁ → +-sym l r (i₁ ∧ j))
--         (λ i₁ → +-sym r l (~ (i₁ ∧ j)))
--         refl
--         (λ i → isSetℕₐ⁺¹ (l + r) (r + l) (+-sym l r) (sym (+-sym r l)) i j) i)
--         ) i j

-- infixr 5 _·_


-- data FCSG⊤ : Type where
--  ● : FCSG⊤
--  _·_ : FCSG⊤ → FCSG⊤ → FCSG⊤
--  ·-assoc :  ∀ m n o → m · (n · o) ≡ (m · n) · o
--  ·-comm :  ∀ m n → m · n ≡ n · m
--  ·-hex-diag : ∀ l c r →
--       ((l · c) · r) ≡ (c · (r · l))
--  ·-hex-up : ∀ l c r →
--       Square 
--         (·-comm l (c · r))
--         (·-hex-diag l c r)
--         (·-assoc l c r)
--         (sym (·-assoc c r l))
--  ·-hex-down :  ∀ l c r →
--       Square 
--         (·-hex-diag l c r)
--         (sym (·-assoc c l r))
--         (cong (_· r) (·-comm l c))
--         (cong (c ·_) (·-comm r l))

--  ·-pentagon-diag : ∀ xs ys zs ws
--       → ((xs · ys) · zs) · ws ≡ xs · ys · zs · ws
--  ·-pentagon-△ : ∀ xs ys zs ws  →
--        Square refl (·-pentagon-diag xs ys zs ws)
--          (·-assoc _ _ _) (sym (·-assoc _ _ _))
--  ·-pentagon-□ : ∀ xs ys zs ws →
--        Square (·-pentagon-diag xs ys zs ws)
--           (sym (·-assoc _ _ _))
--           (sym (cong (_· ws) (·-assoc _ _ _)))           
--           ((cong (xs ·_) (·-assoc _ _ _)))


-- repFCSG⊥ℕ : ℕ.ℕ → FCSG⊤
-- repFCSG⊥ℕ ℕ.zero = ●
-- repFCSG⊥ℕ (ℕ.suc x) = ● · repFCSG⊥ℕ x 

-- rep+ : ∀ n m → repFCSG⊥ℕ (ℕ.predℕ (ℕ.suc n))
--                 · repFCSG⊥ℕ (ℕ.predℕ (ℕ.suc m)) ≡
--                repFCSG⊥ℕ (ℕ.predℕ  ((ℕ.suc n) ℕ.+ (ℕ.suc m))) 
-- rep+ ℕ.zero m = refl
-- rep+ (ℕ.suc n) m = sym (·-assoc _ _ _) ∙ cong (● ·_) (rep+ n m)

-- repFCSG⊥ℕsingl : (n : ℕₐ⁺¹) → singl (repFCSG⊥ℕ (ℕ.predℕ (ℕₐ⁺¹→ℕ n)))
-- repFCSG⊥ℕsingl = ℕₐ⁺¹elim.f w
--  where
--  h : ∀ n m → (ℕ.predℕ (((ℕₐ⁺¹→ℕ n) ℕ.+ ℕₐ⁺¹→ℕ m))) ≡
      
--       (ℕ.predℕ (ℕₐ⁺¹→ℕ n) ℕ.+
--        ℕ.suc
--        (ℕ.predℕ (ℕₐ⁺¹→ℕ m)))
--  h = ℕₐ⁺¹→ℕ-elimProp
--       {A = λ n → ∀ m →
--         (ℕ.predℕ ((n ℕ.+ ℕₐ⁺¹→ℕ m))) ≡
      
--       (ℕ.predℕ n ℕ.+
--        ℕ.suc
--        (ℕ.predℕ (ℕₐ⁺¹→ℕ m)))}
--     (λ n → isPropΠ λ _ → ℕprops.isSetℕ _ _)
--      λ n → ℕₐ⁺¹→ℕ-elimProp
--            {A = λ m → ( ((n ℕ.+ m))) ≡ ( n ℕ.+ ℕ.suc (ℕ.predℕ m))}
--              (λ _ → ℕprops.isSetℕ _ _)
--               λ _ → refl
 
--  w : ℕₐ⁺¹elim (λ z → singl (repFCSG⊥ℕ (ℕ.predℕ (ℕₐ⁺¹→ℕ z))))
--  ℕₐ⁺¹elim.aOne w = _ , refl
--  fst ((w ℕₐ⁺¹elim.a+ (x , _)) (y , _)) = x · y
--  snd (ℕₐ⁺¹elim._a+_ w {n} {m} (x , x=) (y , y=)) =
--     -- cong′ (repFCSG⊥ℕ ∘' ℕ.predℕ) {!!}
--      (cong (repFCSG⊥ℕ) (cong ℕ.predℕ (+ₐ≡+ n m) ∙ h n m))
--     ∙∙ sym (rep+ _ _)
--          ∙∙ cong₂ _·_ x= y=
  

--  ℕₐ⁺¹elim.a-assoc w {n} {m} {o} x y z =
--    ΣPathP (·-assoc _ _ _
--         , {!!}) 
--  ℕₐ⁺¹elim.a-sym w = {!!}
--  ℕₐ⁺¹elim.asquash w = {!!}



-- repFCSG⊥ℕₐ⁺¹ : ℕₐ⁺¹ → FCSG⊤
-- repFCSG⊥ℕₐ⁺¹ = fst ∘ repFCSG⊥ℕsingl

-- lenFCSG⊥ : FCSG⊤ → ℕₐ⁺¹
-- lenFCSG⊥ ● = one
-- lenFCSG⊥ (n · n₁) = lenFCSG⊥ n + lenFCSG⊥ n₁ 
-- lenFCSG⊥ (·-assoc n n₁ n₂ i) =
--    +-assoc (lenFCSG⊥ n) (lenFCSG⊥ n₁) (lenFCSG⊥ n₂) i
-- lenFCSG⊥ (·-comm n n₁ i) =
--   +-sym (lenFCSG⊥ n) (lenFCSG⊥ n₁) i
-- lenFCSG⊥ (·-hex-diag n n₁ n₂ i) = {!!}
-- lenFCSG⊥ (·-hex-up n n₁ n₂ i i₁) = {!!}
-- lenFCSG⊥ (·-hex-down n n₁ n₂ i i₁) = {!!}
-- lenFCSG⊥ (·-pentagon-diag n n₁ n₂ n₃ i) = {!!}
-- lenFCSG⊥ (·-pentagon-△ n n₁ n₂ n₃ i i₁) = {!!}
-- lenFCSG⊥ (·-pentagon-□ n n₁ n₂ n₃ i i₁) = {!!}


-- toFCSG⊥'loop : ∀ n → AdjacentBundles n →      
--         repFCSG⊥ℕₐ⁺¹ n ≡ repFCSG⊥ℕₐ⁺¹ n
-- toFCSG⊥'loop n (𝕒𝕓 nothing l r nothing <n) =
--    cong repFCSG⊥ℕₐ⁺¹ (sym <n ∙ +-sym _ _) ∙∙ ·-comm _ _ ∙∙ cong repFCSG⊥ℕₐ⁺¹ <n
-- toFCSG⊥'loop n (𝕒𝕓 nothing l r (just x) <n) = {!!}
-- toFCSG⊥'loop n (𝕒𝕓 (just x) l r nothing <n) = {!!}
-- toFCSG⊥'loop n (𝕒𝕓 (just x) l r (just x₁) <n) = {!!}

-- -- ℕₐ⁺¹elim.f w
-- --  where
-- --  w : ℕₐ⁺¹elim λ z → AdjacentBundles z → repFCSG⊥ℕₐ⁺¹ z ≡ repFCSG⊥ℕₐ⁺¹ z
-- --  ℕₐ⁺¹elim.aOne w _ = refl
-- --  ℕₐ⁺¹elim._a+_ w = {!!}
-- --  ℕₐ⁺¹elim.a-assoc w = {!!}
-- --  ℕₐ⁺¹elim.a-sym w = {!!}
-- --  ℕₐ⁺¹elim.asquash w = {!!}

-- toFCSG⊥' : ∀ n → ℙrmₐ {true} n → FCSG⊤
-- toFCSG⊥' n 𝕡base = repFCSG⊥ℕₐ⁺¹ n
-- toFCSG⊥' n (𝕡loop' x i) = toFCSG⊥'loop n x i
-- toFCSG⊥' n (𝕡invol' (𝕒𝕓 lPad l r rPad <n) p i i₁) = {!lPad rPad!}
-- toFCSG⊥' n (𝕡hex' lPad rPad l c r p p' p'' i i₁) = {!!}
-- toFCSG⊥' n (𝕡comm lPad cPad rPad l r l' r' p p' i i₁) = {!!}
-- toFCSG⊥' n (𝕡over lPad rPad l x x' p p' p'' i i₁) = {!!}
-- toFCSG⊥' n (𝕡squash x x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) = {!!}

-- fromFCSG⊥' : (x : FCSG⊤) → ℙrmₐ {true} (lenFCSG⊥ x)
-- fromFCSG⊥' ● = 𝕡base
-- fromFCSG⊥' (x · x₁) = 𝕡· (fromFCSG⊥' x) (fromFCSG⊥' x₁)
-- fromFCSG⊥' (·-assoc x x₁ x₂ i) =
--  𝕡·-assoc (fromFCSG⊥' x) (fromFCSG⊥' x₁) (fromFCSG⊥' x₂) i
-- fromFCSG⊥' (·-comm x x₁ i) = {!!}
-- fromFCSG⊥' (·-hex-diag x x₁ x₂ i) = {!!}
-- fromFCSG⊥' (·-hex-up x x₁ x₂ i i₁) = {!!}
-- fromFCSG⊥' (·-hex-down x x₁ x₂ i i₁) = {!!}
-- fromFCSG⊥' (·-pentagon-diag x x₁ x₂ x₃ i) = {!!}
-- fromFCSG⊥' (·-pentagon-△ x x₁ x₂ x₃ i i₁) = {!!}
-- fromFCSG⊥' (·-pentagon-□ x x₁ x₂ x₃ i i₁) = {!!}


-- -- -- -- 𝕡hex : ∀ lPad rPad l c r → ∀ p p' p'' →
-- -- -- --          SquareP (λ i j → ℙrmₐ {true}
-- -- -- --              (isSet→isSet' isSetℕₐ⁺¹
-- -- -- --              (λ j → lPad + +-sym l c j + (r + rPad))
-- -- -- --              (λ j → lPad + +-sym l (c + r) j + rPad)
-- -- -- --              -- (λ j → lPad + +-sym l c j + (r + rPad))
-- -- -- --              -- (λ j → c + lPad + +-sym l r j + rPad)
-- -- -- --              {!!}
-- -- -- --              ({!!} ∙∙ (λ i → (lPad + c) + +-sym l r i + rPad) ∙∙ {!!})
-- -- -- --              -- (+-assoc _ _ _ ∙ cong (_+ _) {!!})
-- -- -- --              --(λ i → (lPad + +-sym l (c + r) i + rPad))
-- -- -- --              i j)
-- -- -- --              )
-- -- -- --        -- {𝕡base {n = {!!}}}
-- -- -- --        -- {𝕡base {n = lPad + (l + (c + r)) + rPad}}
-- -- -- --        -- (𝕡loop lPad l c (r + rPad))
-- -- -- --        -- {𝕡base {n = {!!}}}
-- -- -- --        -- {𝕡base {n = {!!}}}
-- -- -- --        -- (𝕡loop (c + lPad) l r rPad)
-- -- -- --        -- {!!}
-- -- -- --        (𝕡loop lPad l c (r + rPad))
-- -- -- --        (𝕡loop lPad l (c + r) rPad)
-- -- -- --        {!!}
-- -- -- --        {!!}
-- -- -- --        -- (𝕡loop (lPad + c) l r rPad)
       
-- -- -- -- 𝕡hex = {!!}
