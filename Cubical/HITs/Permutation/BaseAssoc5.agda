{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.BaseAssoc5 where

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
open import Cubical.Functions.Implicit

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
   asquash : ∀ x → (isSet (A x))

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

isSetℕₐ⁺¹elim : ∀ {ℓ} {A : ℕₐ⁺¹ → Type ℓ} → isSet (ℕₐ⁺¹elim A)
isSetℕₐ⁺¹elim {A = A} =
  isSetRetract ff gg fg
    (isSetΣ (isProp→isSet (isPropΠ λ _ → isPropIsSet))
      λ sq → isSetΣ (sq _)
        λ _ → isSetΣ (isSetImplicitΠ λ _ → isSetImplicitΠ λ _  →
              isSetΠ2 λ _ _ → sq _)
               λ _ → isProp→isSet
                 (isProp×
                  (isPropImplicitΠ2 λ _ _ →
                   isPropImplicitΠ λ _ →
                     isPropΠ3 λ _ _ _ →
                      isOfHLevelPathP' 1 (sq _) _ _)
                  (isPropImplicitΠ2 λ _ _ →
                     isPropΠ2 λ _ _ →
                      isOfHLevelPathP' 1 (sq _) _ _)))

 where
 open ℕₐ⁺¹elim
 ff : ℕₐ⁺¹elim _ →
          (∀ x → (isSet (A x))) ×
          Σ (A one) (λ x' →
               Σ (∀ {n m} → A n → A m → A (n + m))
                λ xx' →  Σ
                 (∀ {n m o} (x : A n) (y : A m) (z : A o)
                 → PathP (λ i → A (+-assoc n m o i))
                   (xx' x (xx' y z))
                   (xx' (xx' x y) z))
                 λ _ → ∀ {n m} (x : A n) (y : A m)
                 → PathP (λ i → A (+-sym n m i))
                   (xx' x y)
                   (xx' y x)) 
 ff x = (asquash x) ,
        ((aOne x) ,
        ((_a+_ x) ,
        a-assoc x ,
         a-sym x))

 gg : _ → ℕₐ⁺¹elim A
 asquash (gg (fst₁ , x)) = fst₁
 aOne (gg (fst₁ , x)) = fst x
 _a+_ (gg (fst₁ , x)) = fst (snd x)
 a-assoc (gg (fst₁ , x)) = fst (snd (snd x))
 a-sym (gg (fst₁ , x)) = snd (snd (snd x))

 fg : (x : ℕₐ⁺¹elim (λ z → A z)) → gg (ff x) ≡ x
 asquash (fg x i) = asquash x
 aOne (fg x i) = aOne x
 _a+_ (fg x i) = x a+_
 a-assoc (fg x i) = a-assoc x
 a-sym (fg x i) = a-sym x

 
-- record ℕₐ⁺¹elim₂ (A : ℕₐ⁺¹ → ℕₐ⁺¹ → Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--    aOne' : A one one
--    a+ : ∀ {n m o} → A o n → A o m → A o (n + m)
--    +a : ∀ {n m o} → A n o  → A m o  → A (n + m) o
--    a-assoc+ : ∀ {n m o p} → (x : A p n) (y : A p m) (z : A p o) →
--       PathP (λ i → A p (+-assoc n m o i)) (a+ x (a+ y z))
--       (a+ (a+ x y) z)
--    a-+assoc : ∀ {n m o} → (x : A n one) (y : A m one) (z : A o one) →
--       PathP (λ i → A (+-assoc n m o i) one)
--       ((+a x (+a y z)))
--       (+a (+a x y) z)
--    a-sym+ : ∀ {n m o} → (x : A o n) (y : A o m) →
--       PathP (λ i → A o (+-sym n m i)) (a+ x y) (a+ y x)              
--    asquash₂ : ∀ x y → (isSet (A x y))

--  open ℕₐ⁺¹elim

--  f'one : ℕₐ⁺¹elim (λ z → A one z)
--  aOne f'one = aOne'
--  _a+_ f'one = a+
--  a-assoc f'one = a-assoc+
--  a-sym f'one = a-sym+
--  asquash f'one x = asquash₂ one x

--  f'+ : ∀ {n m}
--      → ℕₐ⁺¹elim (λ z → A n z)
--      → ℕₐ⁺¹elim (λ z → A m z)
--      → ℕₐ⁺¹elim (λ z → A (n + m) z)
--  aOne (f'+ n' m') = +a (aOne n') (aOne m')
--  _a+_ (f'+ {n = n} {m} n' m') =
--    a+ {o = n + m} 
--  a-assoc (f'+ n' m') = a-assoc+ 
--  a-sym (f'+ n' m') = a-sym+
--  asquash (f'+ n' m') x = asquash₂ _ _

--  f'assoc : ∀ {n m o} → (x : ℕₐ⁺¹elim (λ z → A n z)) (y : ℕₐ⁺¹elim (λ z → A m z))
--       (z : ℕₐ⁺¹elim (λ z₁ → A o z₁)) →
--       PathP (λ i → ℕₐ⁺¹elim (λ z₁ → A (+-assoc n m o i) z₁))
--       (f'+ x (f'+ y z)) (f'+ (f'+ x y) z)
--  asquash (f'assoc x y z i) x₁ = asquash₂ (+-assoc _ _ _ i) x₁
--  aOne (f'assoc {n = n} {m} {o} x y z i) = 
--    a-+assoc {n} {m} {o}
--     (aOne x) (aOne y) (aOne z) i 
--  _a+_ (f'assoc x y z i) x' y' =
--     a+ x' y'
--  a-assoc (f'assoc {n'} {m'} {o'} x y z i) =
--    {!!}
--    -- isSet→SquareP (λ i j → asquash₂ (+-assoc n' m' o' i) (+-assoc n m o j))
--    --    (λ i₁ → a-assoc+ {!!} {!!} {!!} i₁)
--    --    {!!}
--    --    {!!}
--    --    {!!} i j

-- -- Goal: A (+-assoc n' m' o' i) (+-assoc n m o j)
-- -- ———— Boundary (wanted) —————————————————————————————————————
-- -- j = i0 ⊢ a+ x' (a+ y' z')
-- -- j = i1 ⊢ a+ (a+ x' y') z'
-- -- i = i0 ⊢ a-assoc+ x' y' z' j
-- -- i = i1 ⊢ a-assoc+ x' y' z' j

--    -- isSet→SquareP (λ i j → asquash₂ (+-assoc _ _ _ i) (+-assoc _ _ _ j))
--    --   (λ j → {!a-assoc+ x' y' z' j!} )
--    --   (a-assoc+ _ _ _)
--    --   (λ i → {!!})
--    --   {!!} i j

-- -- j = i0 ⊢ a+ x' (a+ y' z')
-- -- j = i1 ⊢ a+ (a+ x' y') z'
-- -- i = i0 ⊢ a-assoc+ x' y' z' j
-- -- i = i1 ⊢ a-assoc+ x' y' z' j

--  a-sym (f'assoc x y z i) x' y' j =
--    {!!}

--  f' : ℕₐ⁺¹elim (λ x → ℕₐ⁺¹elim (λ z → A x z))
--  aOne f' = f'one
--  _a+_ f' = f'+
--  a-assoc f' = f'assoc
--   -- isProp→PathP (λ _ → {!isSetℕₐ⁺¹elim!})
--   --  _ _
--  a-sym f' = {!!}
--  asquash f' = {!!}
 
--  f₂ : ∀ x y → A x y
--  f₂ x = ℕₐ⁺¹elim.f (ℕₐ⁺¹elim.f f' x)



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

-- ℕₐ⁺¹→ℕ-elimProp : ∀ {ℓ} {A : ℕ.ℕ → Type ℓ} → (∀ n → isProp (A n)) →
--     (∀ n → A (ℕ.suc n)) → ∀ n → A (ℕₐ⁺¹→ℕ n) 
-- ℕₐ⁺¹→ℕ-elimProp {A = A} isPropA Asuc = w
--  where
--  w : (n : ℕₐ⁺¹) → A (ℕₐ⁺¹→ℕ n)
--  w one = Asuc 0
--  w (n + n₁) = {!!}
--  w (+-assoc n n₁ n₂ i) = {!!}
--  w (+-sym n n₁ i) = {!!}
--  w (isSetℕₐ⁺¹' x n n₁ x₁ y i i₁) = {!!}
-- -- ℕₐ⁺¹elimProp.f w
-- --   where
-- --    w : ℕₐ⁺¹elimProp λ z → A (ℕₐ⁺¹→ℕ z)
-- --    ℕₐ⁺¹elimProp.aOne w = Asuc _
-- --    ℕₐ⁺¹elimProp._a+_ w x x₁ = {!!}
-- --    ℕₐ⁺¹elimProp.asquash w = {!!}

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

⊹-0 : ∀ {x} → x ⊹ nothing ≡ x
⊹-0 {nothing} = refl
⊹-0 {just x} = refl

ₐ+ₐ-assoc : ∀ l c r →
   l +ₐ (c ₐ+ r) ≡ l +ₐ c ₐ+ r 
ₐ+ₐ-assoc nothing c r = refl
ₐ+ₐ-assoc (just x) c nothing = refl
ₐ+ₐ-assoc (just x) c (just x₁) = +-assoc _ _ _

-- n ₐ+ (p₋ᵢ .AB.lPad ⊹ fst a) ≡ n ₐ+ AB.lPad p₋ᵢ ₐ+ fst a

ₐ+ₐ-assoc' : ∀ n m o → n ₐ+ (m ⊹ o) ≡ n ₐ+ m ₐ+ o
ₐ+ₐ-assoc' n nothing o = refl
ₐ+ₐ-assoc' n (just x) nothing = refl
ₐ+ₐ-assoc' n (just x) (just x₁) = +-assoc _ _ _


ₐ+ₐ-assoc'' : ∀ n m o → ((n ⊹ m) ⊹ₐ o) ≡ n ⊹ (m ⊹ₐ o)
ₐ+ₐ-assoc'' nothing m o = refl
ₐ+ₐ-assoc'' (just x) nothing o = refl
ₐ+ₐ-assoc'' (just x) (just x₁) o = cong just (sym (+-assoc _ _ _))


+-+ₐ≡ₐ+-+ : ∀ {n m l} → n + (m +ₐ l) ≡ n ₐ+ m + l
+-+ₐ≡ₐ+-+ {m = nothing} = refl
+-+ₐ≡ₐ+-+ {m = just x} = +-assoc _ _ _

+-+ₐ≡ₐ+-+' : ∀ {n m l} → n +ₐ (m + l) ≡ n +ₐ m + l
+-+ₐ≡ₐ+-+' {nothing} = refl
+-+ₐ≡ₐ+-+' {just x} = +-assoc _ _ _

+-ₐ+≡ₐ+-+' : ∀ {n m l} → n + (m ₐ+ l) ≡ n + m ₐ+ l
+-ₐ+≡ₐ+-+' {l = nothing} = refl
+-ₐ+≡ₐ+-+' {l = just x} = +-assoc _ _ _


+ₐ-lem : ∀ {n m l o p} →
                    n +ₐ (m + l) ₐ+ o ₐ+ p ≡
                    n +ₐ (m + l ₐ+ (o ⊹ p))
+ₐ-lem {nothing} {o = nothing} {p} = refl
+ₐ-lem {nothing} {o = just x} {nothing} = refl
+ₐ-lem {nothing} {o = just x} {just x₁} = sym (+-assoc _ _ _)
+ₐ-lem {just x} {o = nothing} {nothing} = refl
+ₐ-lem {just x} {o = nothing} {just x₁} = sym (+-assoc _ _ _)
+ₐ-lem {just x} {o = just x₁} {nothing} = sym (+-assoc _ _ _)
+ₐ-lem {just x} {o = just x₁} {just x₂} =
  sym (+-assoc _ _ _) ∙ sym (+-assoc _ _ _)


record AB' (n : ℕₐ⁺¹) : Type₀ where
 constructor 𝕒𝕓'
 field
  l r  : ℕₐ⁺¹
  <n : (l + r) ≡ n


record AB (n : ℕₐ⁺¹) : Type₀ where
 constructor 𝕒𝕓
 field
  lPad : ℕₐ
  l r  : ℕₐ⁺¹
  rPad : ℕₐ
  <n : lPad +ₐ (l + r) ₐ+ rPad ≡ n

AB≡ : ∀ n → (p p' : AB n) 
       → AB.lPad p ≡ AB.lPad p'
       → AB.l p ≡ AB.l p'
       → AB.r p ≡ AB.r p'
       → AB.rPad p ≡ AB.rPad p'
       → p ≡ p'
       
AB.lPad (AB≡ n p p' x x₁ x₂ x₃ i) = x i
AB.l (AB≡ n p p' x x₁ x₂ x₃ i) = x₁ i
AB.r (AB≡ n p p' x x₁ x₂ x₃ i) = x₂ i
AB.rPad (AB≡ n p p' x x₁ x₂ x₃ i) = x₃ i
AB.<n (AB≡ n p p' x x₁ x₂ x₃ i) j =
 isSet→isSet' isSetℕₐ⁺¹
    (AB.<n p)
    (AB.<n p')
    (λ i → x i +ₐ (x₁ i + x₂ i) ₐ+ x₃ i)
    (λ _ → n) i j

≡AB : ∀ {n} → (p p' : AB n) → Type
≡AB p p' =
           (AB.lPad p ≡ AB.lPad p')
         × (AB.l p ≡ AB.l p')
         × (AB.r p ≡ AB.r p')
         × (AB.rPad p ≡ AB.rPad p')

isProp≡AB : ∀ {n} → (p p' : AB n) → isProp (≡AB p p')
isProp≡AB p p' =
  isProp× (isSetℕₐ _ _)
 (isProp× (isSetℕₐ⁺¹ _ _)
 (isProp× (isSetℕₐ⁺¹ _ _)
 (isSetℕₐ _ _)))

isSetAB : ∀ {n} → isSet (AB n)
isSetAB =
  isSetRetract
    _
    (uncurry (uncurry (uncurry (uncurry 𝕒𝕓))))
    (λ x → refl)
    (isSetΣ (isSet×
            (isSet×
            (isSet× isSetℕₐ isSetℕₐ⁺¹)
            isSetℕₐ⁺¹)
            isSetℕₐ)
      λ _ → isProp→isSet (isSetℕₐ⁺¹ _ _))


≡ABiso : ∀ {n} → (p p' : AB n) → Iso (≡AB p p') (p ≡ p')
≡ABiso p p' = w
 where
 open Iso
 w : Iso _ _
 fun w (x , x' , x'' , x''') = AB≡ _ _ _ x x' x'' x'''
 fst (inv w p) i = AB.lPad (p i)
 fst (snd (inv w p)) i = AB.l (p i)
 fst (snd (snd (inv w p))) i = AB.r (p i)
 snd (snd (snd (inv w p))) i = AB.rPad (p i)

 rightInv w _ = isSetAB _ _ _ _ 
 leftInv w _ = isProp≡AB p p' _ _

swapAB : ∀ {n} → AB n → AB n
swapAB (𝕒𝕓 lPad l r rPad <n) =
  𝕒𝕓 lPad r l rPad (cong (λ x → (lPad +ₐ x ₐ+ rPad)) (+-sym r l) ∙ <n)


swapAB' : ∀ {n} → (x : AB n) → _ → AB n
swapAB' (𝕒𝕓 lPad l r rPad <n) p =
  𝕒𝕓 lPad r l rPad p


-- -- +-suc : ∀ trunc → (m n : ℕₐ⁺¹ {trunc}) → m + (suc n) ≡ suc (m + n)
-- -- +-suc = {!!}

suc' : ℕₐ → ℕₐ
suc' = just ∘ Mb.rec one suc

-- sucAB : ∀ {n} → AB n → AB (suc n)
-- AB.lPad (sucAB x) = suc' (AB.lPad x)
-- AB.l (sucAB x) = AB.l x
-- AB.r (sucAB x) = AB.r x
-- AB.rPad (sucAB x) = AB.rPad x
-- AB.<n (sucAB {n} (𝕒𝕓 lPad l r rPad <n)) = w lPad rPad <n
--  where
--  w : ∀ lPad rPad → lPad +ₐ (l + r) ₐ+ rPad ≡ n
--      →  Mb.rec one (_+_ one) lPad + (l + r) ₐ+ rPad ≡ suc n
--  w nothing nothing p = cong suc p
--  w nothing (just x) p = sym (+-assoc _ _ _) ∙ cong suc p
--  w (just x) nothing p = sym (+-assoc _ _ _) ∙ cong suc p
--  w (just x) (just x₁) p = ( sym (+-assoc _ _ _) ∙ sym (+-assoc _ _ _) ∙ cong suc (+-assoc _ _ _)) ∙ cong suc p




m+AB* : ∀ m {n} m+n → (m + n ≡ m+n) → AB n → AB (m+n)
AB.lPad (m+AB* m m+n p x) = m ₐ⊹ AB.lPad x
AB.l (m+AB* m m+n p x) = AB.l x
AB.r (m+AB* m m+n p x) = AB.r x
AB.rPad (m+AB* m m+n p x) = AB.rPad x
AB.<n (m+AB* m {n} m+n p (𝕒𝕓 lPad l r rPad <n)) = w lPad rPad <n ∙ p
 where
 w : ∀ lPad rPad → lPad +ₐ (l + r) ₐ+ rPad ≡ n
     →  m ₐ+  lPad + (l + r) ₐ+ rPad ≡ m + n
 w nothing nothing p = cong (m +_) p
 w nothing (just x) p = sym (+-assoc _ _ _) ∙ cong (m +_) p
 w (just x) nothing p = sym (+-assoc _ _ _) ∙ cong (m +_) p
 w (just x) (just x₁) p = ( sym (+-assoc _ _ _) ∙ sym (+-assoc _ _ _) ∙ cong (m +_) (+-assoc _ _ _)) ∙ cong (m +_) p

m+AB : ∀ m {n} → AB n → AB (m + n)
m+AB m = m+AB* m _ refl

AB+m* : ∀ m {n} n+m → (n + m ≡ n+m) → AB n → AB (n+m)
AB.lPad (AB+m* m _ _ x) = AB.lPad x
AB.l (AB+m* m  _ _ x) = AB.l x
AB.r (AB+m* m  _ _ x) = AB.r x
AB.rPad (AB+m* m  _ _ x) = AB.rPad x ⊹ₐ m
AB.<n (AB+m* m {n} _ p (𝕒𝕓 lPad l r rPad <n)) = w lPad rPad <n ∙ p
 where
 w : ∀ lPad rPad → lPad +ₐ (l + r) ₐ+ rPad ≡ n
     →  lPad +ₐ (l + r) + (rPad +ₐ m) ≡ n + m
 w _ nothing p = cong (_+ m) p
 w _ (just x) p = +-assoc _ _ _ ∙ cong (_+ m) p


AB+m : ∀ m {n} → AB n → AB (n + m)
AB+m m = AB+m* m _ refl


MbAB : ℕₐ⁺¹ → Type
MbAB = Maybe ∘' AB


-- data ℙ□ (n : ℕₐ⁺¹) : Type₀ where
--  □invol □hex □comm □over : ℙ□ n


data ℙrmₐ {trunc : Bool} (n : ℕₐ⁺¹) : Type₀


𝕡base' : ∀ {trunc : Bool} {n : ℕₐ⁺¹} → ℙrmₐ {trunc} n

Ωℙ : {trunc : Bool} (n : ℕₐ⁺¹) → Type₀
Ωℙ {trunc} n = Path (ℙrmₐ {trunc} n) 𝕡base' 𝕡base'


involGuard : ∀ {n} (p₀₋ p₁₋ : AB n) → Type 
involGuard p₀₋ p₁₋ = ≡AB (swapAB p₀₋) p₁₋

hexGuard : ∀ {n} (p₀₋ p₁₋ p₋₁ : AB n) → Type
hexGuard p₀₋ p₁₋ p₋₁ =
     (p₀₋ .lPad ≡ p₁₋ .lPad)
   × (p₁₋ .rPad ≡ p₋₁ .rPad)
   × (p₋₁ .l ≡ p₁₋ .l) 
   × (p₀₋ .l ≡ p₁₋ .l)
   × (p₁₋ .r ≡ p₀₋ .r + p₋₁ .r) 
 where
 open AB
 
commGuard : ∀ {n} (pᵢ₋ p₋ᵢ : AB n) → Type
commGuard pᵢ₋ p₋ᵢ = Σ _ λ cPad → p₋ᵢ .lPad ≡
         ((pᵢ₋ .lPad ⊹ₐ ((pᵢ₋ .l + pᵢ₋ .r) ₐ+ cPad))) 
 where
 open AB


overGuard : ∀ {n} (p₀₋ p₁₋ p₋ᵢ : AB n) → Type
overGuard p₀₋ p₁₋ p₋ᵢ =
  Σ (_ × _) (λ (lPad' , rPad') →
     (p₁₋ .lPad ≡ p₋ᵢ .lPad ⊹ lPad')
   × (p₀₋ .rPad ≡ rPad' ⊹ p₋ᵢ .rPad)
   × (p₀₋ .l ≡ p₁₋ .l)
   × (p₀₋ .r ≡ p₁₋ .r)
   × (lPad' +ₐ (((p₀₋ .l) + (p₀₋ .r)) ₐ+ rPad') ≡ p₋ᵢ .r))

 where
 open AB

-- cPad
--   𝕡over : ∀ lPad rPad l x x' → ∀ p p' p'' →
--      Square {A = ℙrmₐ {trunc} n}
--        (𝕡loop' (𝕒𝕓 (lPad ⊹ₐ l + lPad') x x' (rPad' + rPad) p'))       
--        (𝕡loop' (𝕒𝕓 (lPad + lPad') x x' (rPad' + l ₐ⊹ rPad) p''))
--        (𝕡loop' (𝕒𝕓 lPad l (lPad' + x' + x + rPad') rPad p))
--        (𝕡loop' (𝕒𝕓 lPad l (lPad' + x' + x + rPad') rPad p))


data ℙrmₐ {trunc} n where 
  𝕡base : ℙrmₐ n
  𝕡loop : AB n → 𝕡base ≡ 𝕡base
  𝕡invol : (p₀₋ p₁₋ : AB n) → involGuard p₀₋ p₁₋
            → Square {A = ℙrmₐ {trunc} n}
                  (𝕡loop p₀₋)
                  (sym (𝕡loop p₁₋))
                  refl
                  refl
  𝕡hex : (p₀₋ p₁₋ p₋₁ : AB n) → hexGuard p₀₋ p₁₋ p₋₁
    → Square {A = ℙrmₐ {trunc} n}
       (𝕡loop p₀₋)
       (𝕡loop p₁₋)
       refl
       (𝕡loop p₋₁)
  𝕡comm : (pᵢ₋ p₋ᵢ : AB n) → commGuard pᵢ₋ p₋ᵢ
     → Square {A = ℙrmₐ {trunc} n}
       (𝕡loop pᵢ₋)
       (𝕡loop pᵢ₋)
       (𝕡loop p₋ᵢ)
       (𝕡loop p₋ᵢ)

  𝕡over : (p₀₋ p₁₋ p₋ᵢ : AB n) → overGuard p₀₋ p₁₋ p₋ᵢ
     → Square {A = ℙrmₐ {trunc} n}
       (𝕡loop p₀₋)
       (𝕡loop p₁₋)
       (𝕡loop p₋ᵢ)
       (𝕡loop p₋ᵢ)

  𝕡squash : Bool→Type trunc → isGroupoid (ℙrmₐ n)

𝕡base' = 𝕡base


-- record ℙrmRec (A : Type ℓ) : Type ℓ where
--  field
--   abase : ℕₐ⁺¹ → A
--   aloop : ∀ n → AB n → abase n ≡ abase n
--   ainvol : ∀ n ab p → aloop n  (swapAB' ab p) ≡ sym (aloop n ab)
--   ahex : ∀ n lPad rPad l c r → ∀ p p' p'' →
--      Square {A = A}
--        (aloop n (𝕒𝕓 lPad l c (r ₐ⊹ rPad) p''))
--        (aloop n (𝕒𝕓 lPad l (c + r) rPad p))
--        refl
--        (aloop n (𝕒𝕓 (lPad ⊹ₐ c) l r rPad p'))       
--   acomm :
--       ∀ n lPad cPad rPad l r l' r' → ∀ p p' →
--      Square {A = A}
--        (aloop n (𝕒𝕓 lPad l r ((cPad +ₐ (l' + r')) ₐ⊹ rPad) p'))       
--        (aloop n (𝕒𝕓 lPad l r ((cPad +ₐ (l' + r')) ₐ⊹ rPad) p'))
--        (aloop n (𝕒𝕓 (lPad ⊹ₐ ((l + r) ₐ+ cPad)) l' r' rPad p))
--        (aloop n (𝕒𝕓 (lPad ⊹ₐ ((l + r) ₐ+ cPad)) l' r' rPad p))
--   aover : ∀ n lPad rPad l x x' → ∀ p p' p'' →
--      Square {A = A}
--        (aloop n (𝕒𝕓 (lPad ⊹ₐ l) x x' rPad p'))       
--        (aloop n (𝕒𝕓 lPad x' x (l ₐ⊹ rPad) p''))
--        (aloop n (𝕒𝕓 lPad l (x' + x) rPad p))
--        (aloop n (𝕒𝕓 lPad l (x' + x) rPad p))

--   asquash : isGroupoid A
  
--  f : ∀ {n} → ℙrmₐ {true} n → A
--  f {n} 𝕡base = abase n
--  f {n} (𝕡loop' x i) = aloop n x i
--  f {n} (𝕡invol' ab p i i₁) = ainvol n ab p i i₁
--  f {n} (𝕡hex' lPad rPad l c r p p' p'' i i₁) =
--    ahex n lPad rPad l c r p p' p'' i i₁
--  f {n} (𝕡comm lPad cPad rPad l r l' r' p p' i i₁) =
--    acomm n lPad cPad rPad l r l' r' p p' i i₁
--  f {n} (𝕡over lPad rPad l x x' p p' p'' i i₁) =
--    aover n lPad rPad l x x' p p' p'' i i₁
--  f (𝕡squash x x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) =
--   asquash _ _ _ _
--     (λ i₂ x₆ → f (x₄ i₂ x₆))
--     (λ i₂ x₆ → f (y₁ i₂ x₆))
--       i i₁ x₅


record ℙrmElim (n : ℕₐ⁺¹) (A : ℙrmₐ {true} n → Type ℓ) : Type ℓ where
 no-eta-equality
 constructor 𝕡rmElim
 field
  asquash : ∀ p → isGroupoid (A p)

  abase : A 𝕡base
  aloop : (ab : AB n)
    → PathP (λ i → A (𝕡loop ab i)) abase abase
  ainvol : (p₀₋ p₁₋ : AB n) → ∀ g →
             SquareP (λ i j → A (𝕡invol p₀₋ p₁₋ g i j) )
               (aloop p₀₋) (symP (aloop p₁₋)) refl refl
  ahex :  (p₀₋ p₁₋ p₋₁ : AB n) → ∀ g →
      SquareP (λ i j → A (𝕡hex p₀₋ p₁₋ p₋₁ g i j))
        (aloop p₀₋)
        (aloop p₁₋)
        refl
        (aloop p₋₁)
  acomm : (pᵢ₋ p₋ᵢ : AB n) → ∀ g →
      SquareP (λ i j → A (𝕡comm pᵢ₋ p₋ᵢ g i j))
       (aloop pᵢ₋)
       (aloop pᵢ₋)
       (aloop p₋ᵢ)
       (aloop p₋ᵢ)

  aover : (p₀₋ p₁₋ p₋ᵢ : AB n) → ∀ g
     → SquareP (λ i j → A (𝕡over p₀₋ p₁₋ p₋ᵢ g i j))
       (aloop p₀₋)
       (aloop p₁₋)
       (aloop p₋ᵢ)
       (aloop p₋ᵢ)




 f : (p : ℙrmₐ {true} n) → A p 
 f 𝕡base = abase
 f (𝕡loop x i) = aloop x i
 f (𝕡invol p₀₋ p₁₋ x i i₁) = ainvol p₀₋ p₁₋ x i i₁

 f (𝕡hex p₀₋ p₁₋ p₋₁ x i i₁) = ahex p₀₋ p₁₋ p₋₁ x i i₁

 f (𝕡comm pᵢ₋ p₋ᵢ x i i₁) = acomm pᵢ₋ p₋ᵢ x i i₁

 f (𝕡over p₀₋ p₁₋ p₋ᵢ x i i₁) = aover p₀₋ p₁₋ p₋ᵢ x i i₁
 f (𝕡squash x x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) =   
     isOfHLevel→isOfHLevelDep 3
      (asquash) _ _ _ _
     (λ i₂ x₆ → f (x₄ i₂ x₆))
     (λ i₂ x₆ → f (y₁ i₂ x₆))
     (𝕡squash x x₁ x₂ x₃ y x₄ y₁)
       i i₁ x₅


record ℙrmRecElimN (A : ℕₐ⁺¹ → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  abase : ∀ n → A n
  aloop : ∀ n → AB n → abase n ≡ abase n
  ainvol : ∀ n p₀₋ p₁₋ → involGuard  p₀₋ p₁₋
    → aloop n p₀₋ ≡ sym (aloop n p₁₋)
  ahex : ∀ n p₀₋ p₁₋ p₋₁ → hexGuard p₀₋ p₁₋ p₋₁  
   →  Square {A = A n}
       (aloop n p₀₋)
       (aloop n p₁₋)
       refl
       (aloop n p₋₁)

  acomm : ∀ n pᵢ₋ p₋ᵢ → commGuard pᵢ₋ p₋ᵢ
     → Square {A = A n}
       (aloop n pᵢ₋)
       (aloop n pᵢ₋)
       (aloop n p₋ᵢ)
       (aloop n p₋ᵢ)

  aover : ∀ n p₀₋ p₁₋ p₋ᵢ → overGuard p₀₋ p₁₋ p₋ᵢ
     → Square {A = A n}
       (aloop n p₀₋)
       (aloop n p₁₋)
       (aloop n p₋ᵢ)
       (aloop n p₋ᵢ)


  asquash : ∀ n → isGroupoid (A n)
  
 f : ∀ {n} → ℙrmₐ {true} n → A n
 f {n} 𝕡base = abase n
 f {n} (𝕡loop x i) = aloop n x i
 f {n} (𝕡invol p₀₋ p₁₋ x i i₁) = ainvol n p₀₋ p₁₋ x i i₁
 f {n} (𝕡hex p₀₋ p₁₋ p₋₁ x i i₁) = ahex n p₀₋ p₁₋ p₋₁ x i i₁
 f {n} (𝕡comm pᵢ₋ p₋ᵢ x i i₁) = acomm n pᵢ₋ p₋ᵢ x i i₁
 f {n} (𝕡over p₀₋ p₁₋ p₋ᵢ x i i₁) =
   aover n p₀₋ p₁₋ p₋ᵢ x i i₁
 f {n} (𝕡squash x x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) =
   asquash n _ _ _ _
     (λ i₂ x₆ → f {n} (x₄ i₂ x₆))
     (λ i₂ x₆ → f {n} (y₁ i₂ x₆))
       i i₁ x₅

record ℙrmElimSet (n : ℕₐ⁺¹) (A : ℙrmₐ {true} n → Type ℓ) : Type ℓ where
 no-eta-equality
 constructor 𝕡rmElimSet
 field
  asquash : ∀ p → isSet (A p)

  abase : A 𝕡base
  aloop : (ab : AB n)
    → PathP (λ i → A (𝕡loop ab i)) abase abase


 f : (p : ℙrmₐ {true} n) → A p
 f 𝕡base = abase
 f (𝕡loop x i) = aloop x i
 f (𝕡invol p₀₋ p₁₋ x i i₁) =
   isSet→SquareP
     (λ i i₁ → asquash (𝕡invol p₀₋ p₁₋ x i i₁))
     (aloop p₀₋) (symP (aloop p₁₋))
     refl refl
     i i₁

 f (𝕡hex p₀₋ p₁₋ p₋₁ x i i₁) =
    isSet→SquareP
     (λ i i₁ → asquash (𝕡hex p₀₋ p₁₋ p₋₁ x i i₁))
     (aloop p₀₋) (aloop p₁₋)
     refl (aloop p₋₁)
     i i₁

 f (𝕡comm pᵢ₋ p₋ᵢ x i i₁) =
   isSet→SquareP
     (λ i i₁ → asquash (𝕡comm pᵢ₋ p₋ᵢ x i i₁))
     (aloop pᵢ₋) (aloop pᵢ₋)
     (aloop p₋ᵢ) (aloop p₋ᵢ)
     i i₁
 f (𝕡over p₀₋ p₁₋ p₋ᵢ x i i₁) =
   isSet→SquareP
     (λ i i₁ → asquash (𝕡over p₀₋ p₁₋ p₋ᵢ x i i₁))
     (aloop p₀₋) (aloop p₁₋)
     (aloop p₋ᵢ) (aloop p₋ᵢ)
     i i₁
 f (𝕡squash x x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) =   
     isOfHLevel→isOfHLevelDep 3
      (isSet→isGroupoid ∘ asquash ) _ _ _ _
     (λ i₂ x₆ → f (x₄ i₂ x₆))
     (λ i₂ x₆ → f (y₁ i₂ x₆))
     (𝕡squash x x₁ x₂ x₃ y x₄ y₁)
       i i₁ x₅

isSetℙrmElimSet : ∀ {ℓ} {n} {A} → isSet (ℙrmElimSet {ℓ} n A)
isSetℙrmElimSet = isSetRetract
 (λ x → ℙrmElimSet.asquash x , ℙrmElimSet.abase x , ℙrmElimSet.aloop x)
 (uncurry (uncurry 𝕡rmElimSet) ∘ invEq Σ-assoc-≃)
 w
 -- (λ x i → 𝕡rmElimSet (ℙrmElimSet.asquash x)
 --                      (ℙrmElimSet.abase x)
 --                      (ℙrmElimSet.aloop x))
 (isSetΣ 
   (isProp→isSet (isPropΠ (λ _ → isPropIsSet)))
   λ isSetA → isSetΣ (isSetA _) λ _ →
     isSetΠ λ _ → isOfHLevelPathP 2 (isSetA _) _ _)

 where
 w : (x : ℙrmElimSet _ _) →
       uncurry (uncurry 𝕡rmElimSet) (invEq Σ-assoc-≃ _) ≡ x
 
 ℙrmElimSet.asquash (w x i) = ℙrmElimSet.asquash x
 ℙrmElimSet.abase (w x i) = ℙrmElimSet.abase x
 ℙrmElimSet.aloop (w x i) = ℙrmElimSet.aloop x

record ℙrmElimSet₂ (A : {n m : ℕₐ⁺¹} →
                ℙrmₐ {true} n →
                ℙrmₐ {true} m → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  asquash₂ : ∀ {n m} → ∀ x y → isSet (A {n} {m} x y)

  abase₂ : ∀ {n m } → A {n} {m} 𝕡base 𝕡base
  aloopₙ : ∀ {n m} (ab : AB n)
    → PathP (λ i → A {n} {m} (𝕡loop ab i) 𝕡base) abase₂ abase₂
  aloopₘ : ∀ {n m} (ab : AB m)
    → PathP (λ i → A {n} {m} 𝕡base (𝕡loop ab i)) abase₂ abase₂
  
 open ℙrmElimSet

 f** : ∀ {n m} → ℙrmElimSet m (A {n} {m} 𝕡base)
 asquash f** _ = asquash₂ 𝕡base _
 abase f** = abase₂
 aloop f** = aloopₘ

 f* : ∀ {n m} → ℙrmElimSet n
           (λ v → ℙrmElimSet m (A v))
 asquash f* _ = isSetℙrmElimSet
 abase f* = f**
 asquash (aloop f* ab i) = asquash₂ (𝕡loop ab i) 
 abase (aloop f* ab i) = aloopₙ ab i
 aloop (aloop f* _ i) _ j = 
   isSet→SquareP (λ i j → asquash₂ (𝕡loop _ i) (𝕡loop _ j))
     (aloopₘ _) (aloopₘ _) (aloopₙ _) (aloopₙ _) i j
 
 f₂ :  ∀ {n m} → ∀ x y → A {n} {m} x y
 f₂ {n} {m} x = ℙrmElimSet.f (ℙrmElimSet.f (f* {n} {m}) x )

record ℙrmElimProp₂ (A : {n m : ℕₐ⁺¹} →
                ℙrmₐ {true} n →
                ℙrmₐ {true} m → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  asquash₂ : ∀ {n m} → ∀ x y → isProp (A {n} {m} x y)

  abase₂ : ∀ {n m } → A {n} {m} 𝕡base 𝕡base

 f₂ : ∀ {n m} → ∀ x y → A {n} {m} x y
 f₂ = ℙrmElimSet₂.f₂ w
  where
  w : ℙrmElimSet₂ A
  ℙrmElimSet₂.asquash₂ w _ _ = isProp→isSet (asquash₂ _ _)
  ℙrmElimSet₂.abase₂ w = abase₂
  ℙrmElimSet₂.aloopₙ w ab =
   isProp→PathP (λ i → asquash₂ (𝕡loop ab i) 𝕡base) _ _
  ℙrmElimSet₂.aloopₘ w ab =
   isProp→PathP (λ i → asquash₂ 𝕡base (𝕡loop ab i) ) _ _


record ℙrmElimSet₃ (A : {n m o : ℕₐ⁺¹} →
                ℙrmₐ {true} n →
                ℙrmₐ {true} m →
                ℙrmₐ {true} o → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  asquash₃ : ∀ {n m o} → ∀ x y z → isSet (A {n} {m} {o} x y z)

  abase₃ : ∀ {n m o} → A {n} {m} {o} 𝕡base 𝕡base 𝕡base
  aloopₙ : ∀ {n m o} (ab : AB n)
    → PathP (λ i → A {n} {m} {o} (𝕡loop ab i) 𝕡base 𝕡base) abase₃ abase₃
  aloopₘ : ∀ {n m o} (ab : AB m)
    → PathP (λ i → A {n} {m} {o}  𝕡base (𝕡loop ab i) 𝕡base) abase₃ abase₃
  aloopₒ : ∀ {n m o} (ab : AB o)
    → PathP (λ i → A {n} {m} {o}  𝕡base 𝕡base (𝕡loop ab i)) abase₃ abase₃
  
 open ℙrmElimSet

 f** : ∀ {n m o} → ℙrmElimSet o (A {n} {m} 𝕡base 𝕡base)
 asquash f** _ = asquash₃ _ _ _
 abase f** = abase₃
 aloop f** = aloopₒ

 f*** : ∀ {n m o} → ∀ ab →
   PathP (λ i → (ℙrmElimSet o ∘ A {n} {m} {o} 𝕡base) (𝕡loop ab i))
     (f** {n} {m} {o}) (f** {n} {m} {o})
 asquash (f*** ab i)  = asquash₃ 𝕡base (𝕡loop ab i)
 abase (f*** ab i) = aloopₘ ab i
 aloop (f*** _ i) _ =
      isSet→SquareP (λ i j → asquash₃ _ (𝕡loop _ i) (𝕡loop _ j))
     (aloopₒ _) (aloopₒ _) (aloopₘ _) (aloopₘ _) i


 f* : ∀ {n m o} → ℙrmElimSet m (ℙrmElimSet o ∘ (A {n} 𝕡base))
 asquash f* _ = isSetℙrmElimSet
 abase f* = f**
 aloop f* = f***

 f**** : ∀ {n m o} →
    (ab : AB n) →
      PathP (λ i → (ℙrmElimSet m ∘ _∘_ (ℙrmElimSet o) ∘ A) (𝕡loop ab i))
      f* f*
 asquash (f**** {n} {m} {o} ab i) =
   (isProp→PathP (λ i → isPropΠ λ _ → isPropIsSet
     {A = ℙrmElimSet o (A (𝕡loop ab i) _)})
    (asquash (f* {n} {m} {o})) (asquash (f* {n} {m} {o})) i)
 asquash (abase (f**** ab i)) p = asquash₃ (𝕡loop _ i) 𝕡base p
 abase (abase (f**** ab i)) = aloopₙ ab i

 aloop (abase (f**** _ i)) _ =
     isSet→SquareP
      (λ i j → asquash₃ (𝕡loop _ i) 𝕡base  (𝕡loop _ j))
          (aloopₒ _) (aloopₒ _) (aloopₙ _) (aloopₙ _) i
 asquash (aloop (f**** ab i) ab' i₁) p =
   asquash₃ (𝕡loop ab i) (𝕡loop ab' i₁) p
 abase (aloop (f**** ab i) ab' i₁) =
   isSet→SquareP
      (λ i j → asquash₃ (𝕡loop _ i)  (𝕡loop _ j)  𝕡base)
          (aloopₘ _) (aloopₘ _) (aloopₙ _) (aloopₙ _) i i₁
 aloop (aloop (f**** {n} {m} {o} ab i) ab' i₁) ab'' = 
  isSet→SquareP {A = λ i i₁ →
      PathP (λ i₂ → A (𝕡loop ab i) (𝕡loop ab' i₁) (𝕡loop ab'' i₂))
      (isSet→SquareP
       (λ i₂ j → asquash₃ (𝕡loop ab i₂) (𝕡loop ab' j) 𝕡base) (aloopₘ ab')
       (aloopₘ ab') (aloopₙ ab) (aloopₙ ab) i i₁)
      (isSet→SquareP
       (λ i₂ j → asquash₃ (𝕡loop ab i₂) (𝕡loop ab' j) 𝕡base) (aloopₘ ab')
       (aloopₘ ab') (aloopₙ ab) (aloopₙ ab) i i₁)}
   (λ i i₁ →  isOfHLevelPathP' 1 (isOfHLevelPathP 2
      (asquash₃ (𝕡loop ab i) (𝕡loop ab' i₁) 𝕡base) _ _) )
   (isSet→SquareP
         (λ i₂ j → asquash₃ {n} {m} {o} 𝕡base (𝕡loop ab' i₂) (𝕡loop ab'' j))
         (aloopₒ ab'') (aloopₒ ab'') (aloopₘ ab') (aloopₘ ab'))
   (isSet→SquareP
         (λ i₂ j → asquash₃ {n} {m} {o} 𝕡base (𝕡loop ab' i₂) (𝕡loop ab'' j))
         (aloopₒ ab'') (aloopₒ ab'') (aloopₘ ab') (aloopₘ ab'))
   (isSet→SquareP
          (λ i₂ j → asquash₃ {n} {m} {o} (𝕡loop ab i₂) 𝕡base (𝕡loop ab'' j))
          (aloopₒ ab'') (aloopₒ ab'') (aloopₙ ab) (aloopₙ ab))
   (isSet→SquareP
          (λ i₂ j → asquash₃ {n} {m} {o} (𝕡loop ab i₂) 𝕡base (𝕡loop ab'' j))
          (aloopₒ ab'') (aloopₒ ab'') (aloopₙ ab) (aloopₙ ab))
     i i₁

 f''' : ∀ {n m o} →
    ℙrmElimSet n (ℙrmElimSet m ∘ (ℙrmElimSet o ∘_) ∘ A)
 asquash f''' p = isSetℙrmElimSet
 abase f''' = f*
 aloop f''' = f****

 f₃ :  ∀ {n m o} → ∀ x y z → A {n} {m} {o} x y z
 f₃ x y = ℙrmElimSet.f (ℙrmElimSet.f (ℙrmElimSet.f f''' x) y)

record ℙrmElimProp₃ (A : {n m o : ℕₐ⁺¹} →
                ℙrmₐ {true} n →
                ℙrmₐ {true} m →
                ℙrmₐ {true} o → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  asquash₃ : ∀ {n m o} → ∀ x y z → isProp (A {n} {m} {o} x y z)

  abase₃ : ∀ {n m o} → A {n} {m} {o} 𝕡base 𝕡base 𝕡base
  

 f₃ : ∀ {n m o} → ∀ x y z → A {n} {m} {o} x y z 
 f₃ = ℙrmElimSet₃.f₃ w
  where
  w : ℙrmElimSet₃ A
  ℙrmElimSet₃.asquash₃ w _ _ _ = isProp→isSet (asquash₃ _ _ _)
  ℙrmElimSet₃.abase₃ w = abase₃
  ℙrmElimSet₃.aloopₙ w _ = isProp→PathP (λ i → asquash₃ _ _ _) _ _ 
  ℙrmElimSet₃.aloopₘ w _ = isProp→PathP (λ i → asquash₃ _ _ _) _ _ 
  ℙrmElimSet₃.aloopₒ w _ = isProp→PathP (λ i → asquash₃ _ _ _) _ _ 

record ℙrmElimProp (n : ℕₐ⁺¹) (A : ℙrmₐ {true} n → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  abase : A 𝕡base
  asquash : ∀ p → isProp (A p)

 fR : ℙrmElimSet n A
 ℙrmElimSet.abase fR = abase
 ℙrmElimSet.aloop fR ab = isProp→PathP (λ i → asquash (𝕡loop ab i)) _ _
 ℙrmElimSet.asquash fR = isProp→isSet ∘ asquash

 f : (p : ℙrmₐ {true} n) → A p
 f =  ℙrmElimSet.f fR




+𝕡* : ∀ n {m} → ℙrmₐ {true} m → ℙrmₐ {true} (n + m) 
+𝕡* n = ℙrmRecElimN.f w
 where
 open ℙrmRecElimN
 w : ℙrmRecElimN (λ m → ℙrmₐ (n + m))
 abase w _ = 𝕡base
 aloop w m x = 𝕡loop (m+AB n x)
 ainvol w _ _ _ g =  𝕡invol _ _ (map-fst (cong (n ₐ⊹_)) g)   
 ahex w m _ _ _ g = 𝕡hex _ _ _ (map-fst (cong (n ₐ⊹_)) g)    
 acomm w m _ _ g = 𝕡comm _ _
    (map-snd (λ p → cong (n ₐ⊹_) p ∙ cong just +-+ₐ≡ₐ+-+) g)    
 aover w m _ _ p₋ᵢ g = 𝕡over _ _ _
   (map-snd (λ {a} → map-fst (λ q → cong (n ₐ⊹_) q ∙
       cong just (ₐ+ₐ-assoc'  n (p₋ᵢ .AB.lPad) (fst a))))
     g)

 asquash w _ = 𝕡squash _


+𝕡 : ∀ n {m} → ℙrmₐ {true} m → ℙrmₐ {true} (n + m) 
+𝕡 n = ℙrmRecElimN.f w
 where
 open ℙrmRecElimN
 w : ℙrmRecElimN (λ m → ℙrmₐ (n + m))
 abase w _ = 𝕡base
 aloop w m x = 𝕡loop (m+AB n x)
 ainvol w _ _ _ g =  𝕡invol _ _ (map-fst (cong (n ₐ⊹_)) g)   
 ahex w m _ _ _ g = 𝕡hex _ _ _ (map-fst (cong (n ₐ⊹_)) g)    
 acomm w m _ _ g = 𝕡comm _ _
    (map-snd (λ p → cong (n ₐ⊹_) p ∙ cong just +-+ₐ≡ₐ+-+) g)    
 aover w m _ _ p₋ᵢ g = 𝕡over _ _ _
   (map-snd (λ {a} → map-fst (λ q → cong (n ₐ⊹_) q ∙
       cong just (ₐ+ₐ-assoc'  n (p₋ᵢ .AB.lPad) (fst a))))
     g)

 asquash w _ = 𝕡squash _

𝕡+ : ∀ n {m} → ℙrmₐ {true} m → ℙrmₐ {true} (m + n) 
𝕡+ n = ℙrmRecElimN.f w
 where
 open ℙrmRecElimN
 w : ℙrmRecElimN (λ m → ℙrmₐ (m + n))
 abase w _ = 𝕡base
 aloop w m x = 𝕡loop (AB+m n x)
 ainvol w _ _ _ g =
   𝕡invol _ _ (map-snd (map-snd (map-snd (cong (_⊹ₐ n)))) g)
 ahex w m _ _ _ g = 𝕡hex _ _ _ ((map-snd (map-fst (cong (_⊹ₐ n)))) g)    
 acomm w m _ _ g = 𝕡comm _ _ g    
 aover w m _ _ p₋ᵢ g = 𝕡over _ _ _
   (map-snd (λ {a} → map-snd (map-fst
     (λ p → cong (_⊹ₐ n) p ∙ ₐ+ₐ-assoc'' (snd a) (p₋ᵢ .AB.rPad) n))) g)    
 asquash w _ = 𝕡squash _


𝕡· : ∀ {n} → ℙrmₐ {true} n → ∀ {m} →  ℙrmₐ {true} m → ℙrmₐ {true} (n + m) 
𝕡· = ℙrmRecElimN.f
   {A = λ n → ∀ {m} →  ℙrmₐ {true} m → ℙrmₐ {true} (n + m)} w
 where
 open ℙrmRecElimN
 open AB


 wL : (n : ℕₐ⁺¹) → AB n →
        Path (∀ {m} → ℙrmₐ m → ℙrmₐ (n + m))
        _ _
 wL n abₙ = implicitFunExt
   λ {m} → funExt (ℙrmElimSet.f {n = m} (w' m))
  where
  open ℙrmElimSet
  w' : ∀ m → ℙrmElimSet m _
  abase (w' m) = cong (𝕡+ m {n}) (𝕡loop abₙ) 
  aloop (w' m) abₘ =
    𝕡comm (AB+m m abₙ) (m+AB n abₘ)
      (rPad abₙ ⊹ lPad abₘ
      , sym (cong (_ₐ⊹ lPad abₘ) (<n abₙ)) ∙
      (cong just (+ₐ-lem {lPad abₙ} {l abₙ} {r abₙ} {rPad abₙ} {lPad abₘ}) ))  
   
  asquash (w' m) _ = 𝕡squash _ _ _

 wInv : (n : ℕₐ⁺¹) (p₀₋ p₁₋ : AB n) →
          involGuard p₀₋ p₁₋ →
          wL n p₀₋ ≡ sym (wL n p₁₋)
 wInv n p₀₋ p₁₋ g = 
  implicitFunExtSq _ _ _ _
   λ m → funExtSq _ _ _ _ (ℙrmElimProp.f (w' m))
   where
   open ℙrmElimProp
   w' : ∀ m → ℙrmElimProp m _
   abase (w' m) =
    𝕡invol _ _
       (map-snd (map-snd (map-snd (cong (_⊹ₐ m)))) g)

   asquash (w' m) p = 
     isOfHLevelPathP' 1
       (isOfHLevelPathP' 2 (𝕡squash _)
         _ _) _ _

 wHex : (n₁ : ℕₐ⁺¹) (p₀₋ p₁₋ p₋₁ : AB n₁) →
      hexGuard p₀₋ p₁₋ p₋₁ →
      Square (wL n₁ p₀₋) (wL n₁ p₁₋) refl (wL n₁ p₋₁)
 wHex n p₀₋ p₁₋ p₋₁ g =
  implicitFunExtSq _ _ _ _
  λ m → funExtSq _ _ _ _ (ℙrmElimProp.f (w' m))
  where
  open ℙrmElimProp
  w' : ∀ m → ℙrmElimProp m _
  abase (w' m) =
   𝕡hex _ _ _ (map-snd (map-fst (cong (_⊹ₐ m))) g)
  asquash (w' m) p = 
    isOfHLevelPathP' 1
      (isOfHLevelPathP' 2 (𝕡squash _)
        _ _) _ _


 wComm : (n₁ : ℕₐ⁺¹) (pᵢ₋ p₋ᵢ : AB n₁) →
      commGuard pᵢ₋ p₋ᵢ →
      Square (wL n₁ pᵢ₋) (wL n₁ pᵢ₋) (wL n₁ p₋ᵢ) (wL n₁ p₋ᵢ)
 wComm _ _ _ g =
  implicitFunExtSq _ _ _ _
  λ m → funExtSq _ _ _ _ (ℙrmElimProp.f (w' m))
  where
  open ℙrmElimProp
  w' : ∀ m → ℙrmElimProp m _
  abase (w' m) = 𝕡comm _ _ g

  asquash (w' m) p = 
    isOfHLevelPathP' 1
      (isOfHLevelPathP' 2 (𝕡squash _)
        _ _) _ _


 wOver : (n₁ : ℕₐ⁺¹) (p₀₋ p₁₋ p₋ᵢ : AB n₁) →
      overGuard p₀₋ p₁₋ p₋ᵢ →
      Square (wL n₁ p₀₋) (wL n₁ p₁₋) (wL n₁ p₋ᵢ) (wL n₁ p₋ᵢ)
 wOver _ _ _ p₋ᵢ g =
  implicitFunExtSq _ _ _ _
  λ m → funExtSq _ _ _ _ (ℙrmElimProp.f (w' m))
  where
  open ℙrmElimProp
  w' : ∀ m → ℙrmElimProp m _
  abase (w' m) = 
    𝕡over _ _ _
    (map-snd (λ {a} → map-snd (map-fst
     (λ p → cong (_⊹ₐ m) p ∙ ₐ+ₐ-assoc'' (snd a) (p₋ᵢ .rPad) m)
     )) g)

  asquash (w' m) p = 
    isOfHLevelPathP' 1
      (isOfHLevelPathP' 2 (𝕡squash _)
        _ _) _ _


 w : ℙrmRecElimN _
 abase w = +𝕡
 aloop w = wL

 ainvol w = wInv

 ahex w = wHex
 acomm w = wComm
 aover w = wOver
 asquash w _ =
   isOfHLevelRespectEquiv 3
     (invEquiv implicit≃Explicit)
     (isGroupoidΠ2 λ _ _ → 𝕡squash _)



𝕡loopP : ∀ lPad l r rPad →
     PathP (λ i → ℙrmₐ {true} (lPad +ₐ +-sym l r i ₐ+ rPad))
       𝕡base
       𝕡base
𝕡loopP lPad l r rPad i =
 𝕡loop (𝕒𝕓 lPad l r rPad λ j → lPad +ₐ +-sym l r (j ∧ i) ₐ+ rPad) i


𝕡·-comm : ∀ {n m} → (x : ℙrmₐ {true} n)
         (y : ℙrmₐ {true} m) → 
     PathP (λ i → ℙrmₐ {true} (+-sym n m i))
       (𝕡· x y)
       (𝕡· y x)
𝕡·-comm = ℙrmElimSet₂.f₂ w
 where
 open AB
 open ℙrmElimSet₂
 w : ℙrmElimSet₂ λ {n m} (x : ℙrmₐ {true} n)
         (y : ℙrmₐ {true} m) → 
     PathP (λ i → ℙrmₐ {true} (+-sym n m i))
       (𝕡· x y)
       (𝕡· y x)
 asquash₂ w _ _ = isOfHLevelPathP' 2 (𝕡squash _) _ _
 abase₂ w = 𝕡loopP nothing _ _ nothing
 aloopₙ w {n} {m} ab =
   let z : PathP
         (λ i →
         PathP (λ i₁ → ℙrmₐ {true} (+-sym n m i₁)) (𝕡· (𝕡loop ab i) 𝕡base)
         (𝕡· 𝕡base (𝕡loop ab i)))
           _ _
       z = (λ i j → 𝕡over
          
          (𝕒𝕓 (lPad (m+AB m ab))
           (l (m+AB m ab))
           (r (m+AB m ab))
           (rPad (m+AB m ab))
           λ i₁ → isSet→SquareP
                   (λ _ _ → isSetℕₐ⁺¹)
                   refl
                   (sym (+-sym n m)) --(+-sym n m)
                   (<n (m+AB m ab))
                   (<n (m+AB m ab) ∙ +-sym m n)
                   i₁ (~ j))
          (𝕒𝕓 (lPad (AB+m m ab))
           (l (AB+m m ab))
           (r (AB+m m ab))
           (rPad (AB+m m ab))
            λ i₁ → isSet→SquareP
                   (λ _ _ → isSetℕₐ⁺¹)
                   refl
                   (sym (+-sym n m))
                   (<n (AB+m m ab) ∙ +-sym n m) --(<n (AB+m m ab) ∙ ?)
                   (<n (AB+m m ab)) --(<n (AB+m m ab))
                    --(<n (AB+m m ab) ∙ +-sym n m)
                   i₁ (~ j))
          (𝕒𝕓 nothing m n nothing (λ j₁ → +-sym n m (j ∨ ~ j₁)))
          ((lPad ab , rPad ab) ,
            refl , ((sym ⊹-0) ,
              (refl , (refl , (ₐ+ₐ-assoc (lPad ab) _ _) ∙ <n ab))))
          (~ j) i)
   in  (λ i j → (𝕡invol (𝕒𝕓 nothing n m nothing  λ i₁ → +-sym n m (i₁ ∧ j))
                        (𝕒𝕓 nothing m n nothing λ i₁ → +-sym n m (j ∨ ~ i₁))
                        (refl , (refl , refl , refl)) i j))
        ◁ z ▷
        (λ i j → (𝕡invol
           (𝕒𝕓 nothing n m nothing λ i₁ → +-sym n m (i₁ ∧ j))
           (𝕒𝕓 nothing m n nothing λ i₁ → +-sym n m (j ∨ ~ i₁))
           (refl , (refl , refl , refl)) (~ i) j))  
       
 aloopₘ w {n} {m} ab i j =
   𝕡over
      (𝕒𝕓 (lPad (m+AB n ab))
           (l (m+AB n ab))
           (r (m+AB n ab))
           (rPad (m+AB n ab))
           λ i₁ → isSet→SquareP
                   (λ _ _ → isSetℕₐ⁺¹)
                   refl
                   (+-sym n m)
                   (<n (m+AB n ab))
                   (<n (m+AB n ab) ∙ +-sym n m)
                   i₁ j)

      (𝕒𝕓 (lPad (AB+m n ab))
           (l (AB+m n ab))
           (r (AB+m n ab))
           (rPad (AB+m n ab))
                      λ i₁ → isSet→SquareP
                   (λ _ _ → isSetℕₐ⁺¹)
                   refl
                   (+-sym n m)                                      
                   (<n (AB+m n ab) ∙ +-sym m n)
                   (<n (AB+m n ab))
                   i₁ j)
      (𝕒𝕓 nothing n m nothing (λ j₁ → +-sym n m (j₁ ∧ j)))
      ((lPad ab , rPad ab ) ,
         refl , (sym ⊹-0 , (refl ,
          (refl , (ₐ+ₐ-assoc (lPad ab) _ _) ∙ <n ab))))
          j i 
    where
    open AB

𝕡·-assoc : ∀ {n m o} → (x : ℙrmₐ {true} n)
         (y : ℙrmₐ {true} m)
         (z : ℙrmₐ {true} o) → 
     PathP (λ i → ℙrmₐ {true} (+-assoc n m o i))
       (𝕡· x (𝕡· y z))
       (𝕡· (𝕡· x y) z)
𝕡·-assoc = ℙrmElimSet₃.f₃ w
 where
 open ℙrmElimSet₃
 open AB
 w : ℙrmElimSet₃ λ {n m o} (x : ℙrmₐ {true} n)
         (y : ℙrmₐ {true} m)
         (z : ℙrmₐ {true} o) → 
     PathP (λ i → ℙrmₐ {true} (+-assoc n m o i))
       (𝕡· x (𝕡· y z))
       (𝕡· (𝕡· x y) z)
 asquash₃ w _ _ _ =
  isOfHLevelPathP' 2 (𝕡squash _) _ _ 
 abase₃ w _ = 𝕡base
 aloopₙ w ab = flipSquareP (congP (λ _ → 𝕡loop)
   (congP₂ (λ _ → 𝕒𝕓 (lPad ab) (l ab) (r ab))
         (cong just +-+ₐ≡ₐ+-+')
           (isSet→SquareP (λ _ _ → isSetℕₐ⁺¹)
            _ _ _ _)))
   

 aloopₘ  w {n} {m} {o} ab =
   flipSquareP (congP (λ _ → 𝕡loop)
     (congP (λ _ → 𝕒𝕓 (just (n ₐ+ lPad ab)) (l ab) (r ab)
             (just (rPad ab +ₐ o)))
       (isSet→SquareP (λ _ _ → isSetℕₐ⁺¹)
            _ _ _ _)))
 aloopₒ w {n} {m} {o} ab = flipSquareP (congP (λ _ → 𝕡loop)
    (congP₂ (λ i x → 𝕒𝕓 {n = +-assoc n m o i} x (l ab) (r ab)
             (rPad ab))
             (cong just +-ₐ+≡ₐ+-+')
       (isSet→SquareP (λ _ _ → isSetℕₐ⁺¹)
            _ _ _ _)))



infixr 5 _·_


data FCSG⊤ : Type where
 ● : FCSG⊤
 _·_ : FCSG⊤ → FCSG⊤ → FCSG⊤
 ·-assoc :  ∀ m n o → m · (n · o) ≡ (m · n) · o
 ·-comm :  ∀ m n → m · n ≡ n · m
 ·-comminvol :  ∀ m n → ·-comm m n ≡ sym (·-comm n m)
 ·-hex-diag : ∀ l c r →
      ((l · c) · r) ≡ (c · (r · l))
 ·-hex-up : ∀ l c r →
      Square 
        (·-comm l (c · r))
        (·-hex-diag l c r)
        (·-assoc l c r)
        (sym (·-assoc c r l))
 ·-hex-down :  ∀ l c r →
      Square 
        (·-hex-diag l c r)
        (sym (·-assoc c l r))
        (cong (_· r) (·-comm l c))
        (cong (c ·_) (·-comm r l))

 ·-pentagon-diag : ∀ xs ys zs ws
      → ((xs · ys) · zs) · ws ≡ xs · ys · zs · ws
 ·-pentagon-△ : ∀ xs ys zs ws  →
       Square refl (·-pentagon-diag xs ys zs ws)
         (·-assoc _ _ _) (sym (·-assoc _ _ _))
 ·-pentagon-□ : ∀ xs ys zs ws →
       Square (·-pentagon-diag xs ys zs ws)
          (sym (·-assoc xs (ys · zs) ws))
          (sym (cong (_· ws) (·-assoc _ _ _)))           
          ((cong (xs ·_) (·-assoc _ _ _)))
 trunc : isGroupoid FCSG⊤
 
record ElimFCSG {ℓ} (A : FCSG⊤ → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  asquash : ∀ x → isGroupoid (A x)
  ●a : A ●
  ·a : ∀ {n m} → A n → A m → A (n · m)
  ·a-assoc : ∀ {n m o} → (a : A n) → (b : A m) → (c : A o) →
                PathP
                  (λ i → A (·-assoc n m o i))
                  (·a a (·a b c))
                  (·a (·a a b) c)
  ·a-comm : ∀ {n m} → (a : A n) → (b : A m) →
                PathP
                  (λ i → A (·-comm n m i))
                  (·a a b)
                  (·a b a)
  ·a-comminvol : ∀ {n m} → (a : A n) → (b : A m) →
                SquareP
                  (λ i j → A (·-comminvol n m i j))
                  (·a-comm a b)
                  (symP (·a-comm b a))
                  refl
                  refl
  ·a-hexDiag : ∀ {n m o} → (a : A n) → (b : A m) → (c : A o) →
                PathP
                  (λ i → A (·-hex-diag n m o i))
                  (·a (·a a b) c)
                  (·a b (·a c a))
  ·a-hex-up : ∀ {n m o} → (l : A n) → (c : A m) → (r : A o)  →
       SquareP (λ i j → A (·-hex-up n m o i j))
         (·a-comm l (·a c  r))
         (·a-hexDiag l c r)
         (·a-assoc l c r)
         (symP (·a-assoc c r l))
  ·a-hex-down : ∀ {n m o} → (l : A n) → (c : A m) → (r : A o)  →
       SquareP (λ i j → A (·-hex-down n m o i j))
         (·a-hexDiag l c r)
         (symP (·a-assoc c l r))
         (congP (λ _ x → ·a x r) (·a-comm l c))
         (congP (λ _ → ·a c) (·a-comm r l))

  ·a-pentagon-diag : ∀ {n m o p} → ∀ xs ys zs ws
      → PathP (λ i → A (·-pentagon-diag n m o p i))
        (·a (·a (·a xs ys) zs) ws)
        (·a xs (·a ys (·a zs ws)))


  ·a-pentagon-△ : ∀ {n m o p} → ∀ xs ys zs ws
      → SquareP (λ i j → A (·-pentagon-△ n m o p i j))
        refl (·a-pentagon-diag xs ys zs ws)
          (·a-assoc _ _ _) (symP (·a-assoc _ _ _))
  ·a-pentagon-□ : ∀ {n m o p} → ∀ xs ys zs ws →
        SquareP (λ i j → A (·-pentagon-□ n m o p i j))
           (·a-pentagon-diag xs ys zs ws)
           (symP (·a-assoc xs (·a ys zs) ws))
           (symP (congP (λ _ x → ·a x ws) (·a-assoc _ _ _)))           
           ((congP (λ _ → ·a xs) (·a-assoc _ _ _)))

 f : ∀ x → A x
 f ● = ●a
 f (x · x₁) = ·a (f x) (f x₁)
 f (·-assoc x x₁ x₂ i) =
   ·a-assoc (f x) (f x₁) (f x₂) i
 f (·-comm x x₁ i) =
   ·a-comm (f x) (f x₁) i
 f (·-comminvol x x₁ i i₁) =
   ·a-comminvol (f x) (f x₁) i i₁
 f (·-hex-diag x x₁ x₂ i) =
      ·a-hexDiag (f x) (f x₁) (f x₂) i
 f (·-hex-up x x₁ x₂ i i₁) =
    ·a-hex-up (f x) (f x₁) (f x₂) i i₁
 f (·-hex-down x x₁ x₂ i i₁) =
       ·a-hex-down (f x) (f x₁) (f x₂) i i₁
 f (·-pentagon-diag x x₁ x₂ x₃ i) =
     ·a-pentagon-diag (f x) (f x₁) (f x₂) (f x₃) i 
 f (·-pentagon-△ x x₁ x₂ x₃ i i₁) =
     ·a-pentagon-△ (f x) (f x₁) (f x₂) (f x₃) i i₁
 f (·-pentagon-□ x x₁ x₂ x₃ i i₁) = 
     ·a-pentagon-□ (f x) (f x₁) (f x₂) (f x₃) i i₁
 f (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
     isOfHLevel→isOfHLevelDep 3 (asquash)
      _ _ _ _
     (λ i j → f (x₃ i j)) (λ i j → f (y₁ i j))
     (trunc x x₁ x₂ y x₃ y₁) i i₁ x₄

record RecFCSG {ℓ} (A : Type ℓ) : Type ℓ where
 no-eta-equality
 field
  asquash : isGroupoid A
  ●a : A
  ·a : A → A → A
  ·a-assoc : ∀ a b c → (·a a (·a b c)) ≡ (·a (·a a b) c)
  ·a-comm : ∀ a b → (·a a b) ≡ (·a b a)
  ·a-comminvol : ∀ a b → (·a-comm a b) ≡ sym (·a-comm b a)
  ·a-hexDiag : ∀ a b c →  
                     (·a (·a a b) c)
                  ≡ (·a b (·a c a))
  ·a-pentagon-diag : ∀ xs ys zs ws
      → (·a (·a (·a xs ys) zs) ws) ≡ (·a xs (·a ys (·a zs ws)))
  ·a-hex-up : ∀ l c r →
        Square
        (·a-comm l (·a c r))
        (·a-hexDiag l c r)
        (·a-assoc l c r)
        (sym (·a-assoc c r l))
  ·a-hex-down : ∀ l c r →
    Square 
        (·a-hexDiag l c r)
        (sym (·a-assoc c l r))
        (cong (λ x → ·a x r) (·a-comm l c))
        (cong (·a c) (·a-comm r l))
  ·a-pentagon-△ : ∀ xs ys zs ws →
         Square refl (·a-pentagon-diag xs ys zs ws)
         (·a-assoc _ _ _) (sym (·a-assoc _ _ _))
  ·a-pentagon-□ : ∀ xs ys zs ws →
             Square (·a-pentagon-diag xs ys zs ws)
          (sym (·a-assoc xs (·a ys zs) ws))
          (sym (cong (λ x → ·a x ws) (·a-assoc _ _ _)))           
          ((cong (·a xs) (·a-assoc _ _ _)))
  


 f : FCSG⊤ → A
 f ● = ●a
 f (x · x₁) = ·a (f x) (f x₁)
 f (·-assoc x x₁ x₂ i) =
   ·a-assoc (f x) (f x₁) (f x₂) i
 f (·-comm x x₁ i) =
   ·a-comm (f x) (f x₁) i
 f (·-comminvol x x₁ i i₁) =
   ·a-comminvol (f x) (f x₁) i i₁
 f (·-hex-diag x x₁ x₂ i) =
      ·a-hexDiag (f x) (f x₁) (f x₂) i
 f (·-hex-up x x₁ x₂ i i₁) =
    ·a-hex-up (f x) (f x₁) (f x₂) i i₁
 f (·-hex-down x x₁ x₂ i i₁) =
       ·a-hex-down (f x) (f x₁) (f x₂) i i₁
 f (·-pentagon-diag x x₁ x₂ x₃ i) =
     ·a-pentagon-diag (f x) (f x₁) (f x₂) (f x₃) i 
 f (·-pentagon-△ x x₁ x₂ x₃ i i₁) =
     ·a-pentagon-△ (f x) (f x₁) (f x₂) (f x₃) i i₁
 f (·-pentagon-□ x x₁ x₂ x₃ i i₁) = 
     ·a-pentagon-□ (f x) (f x₁) (f x₂) (f x₃) i i₁
 f (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
     (asquash)
      _ _ _ _
     (λ i j → f (x₃ i j)) (λ i j → f (y₁ i j))
      i i₁ x₄

 
record ElimSetFCSG {ℓ} (A : FCSG⊤ → Type ℓ) : Type ℓ where
 no-eta-equality
 field
  asquash : ∀ x → isSet (A x)
  ●a : A ●
  ·a : ∀ {n m} → A n → A m → A (n · m)
  ·a-assoc : ∀ {n m o} → (a : A n) → (b : A m) → (c : A o) →
                PathP
                  (λ i → A (·-assoc n m o i))
                  (·a a (·a b c))
                  (·a (·a a b) c)
  ·a-comm : ∀ {n m} → (a : A n) → (b : A m) →
                PathP
                  (λ i → A (·-comm n m i))
                  (·a a b)
                  (·a b a)
  ·a-hexDiag : ∀ {n m o} → (a : A n) → (b : A m) → (c : A o) →
                PathP
                  (λ i → A (·-hex-diag n m o i))
                  (·a (·a a b) c)
                  (·a b (·a c a))
  ·a-pentagon-diag : ∀ {n m o p} → ∀ xs ys zs ws
      → PathP (λ i → A (·-pentagon-diag n m o p i))
        (·a (·a (·a xs ys) zs) ws)
        (·a xs (·a ys (·a zs ws)))

 f : ∀ x → A x
 f = ElimFCSG.f w
  where
  w : ElimFCSG (λ z → A z)
  ElimFCSG.asquash w = isSet→isGroupoid ∘ asquash
  ElimFCSG.●a w = ●a
  ElimFCSG.·a w = ·a
  ElimFCSG.·a-assoc w = ·a-assoc
  ElimFCSG.·a-comm w = ·a-comm
  ElimFCSG.·a-comminvol w _ _ =
    isSet→SquareP (λ _ _ → asquash _)
      _ _ _ _
  ElimFCSG.·a-hexDiag w = ·a-hexDiag
  ElimFCSG.·a-hex-up w _ _ _ =
    isSet→SquareP (λ _ _ → asquash _)
      _ _ _ _
  ElimFCSG.·a-hex-down w _ _ _ =
    isSet→SquareP (λ _ _ → asquash _)
      _ _ _ _
  ElimFCSG.·a-pentagon-diag w = ·a-pentagon-diag 
  ElimFCSG.·a-pentagon-△ w _ _ _ _ =
    isSet→SquareP (λ _ _ → asquash _)
      _ _ _ _
  ElimFCSG.·a-pentagon-□ w _ _ _ _ =
    isSet→SquareP (λ _ _ → asquash _)
      _ _ _ _

-- record RecSetFCSG' {ℓ} (A : Type ℓ) : Type ℓ where
--  no-eta-equality
--  field
--   asquash : isSet A
--   ●a : A
--   ·a : A → A → A
--   ·a-assoc : ∀ a b c → (·a a (·a b c)) ≡ (·a (·a a b) c)
--   ·a-comm : ∀ a b → (·a a b) ≡ (·a b a)
--   -- ·a-hexDiag : ∀ a b c →  
--   --                    (·a (·a a b) c)
--   --                 ≡ (·a b (·a c a))
--   -- ·a-pentagon-diag : ∀ xs ys zs ws
--   --     → (·a (·a (·a xs ys) zs) ws) ≡ (·a xs (·a ys (·a zs ws)))

--  f : FCSG⊤ → A
--  f ● = ●a
--  f (x · x₁) = ·a (f x) (f x₁)
--  f (·-assoc x x₁ x₂ i) =
--    ·a-assoc (f x) (f x₁) (f x₂) i
--  f (·-comm x x₁ i) =
--    ·a-comm (f x) (f x₁) i
--  f (·-comminvol x x₁ i i₁) =
--    asquash (·a (f x) (f x₁)) (·a (f x₁) (f x))
--      (·a-comm (f x) (f x₁)) (sym (·a-comm (f x₁) (f x))) i i₁
--  f (·-hex-diag x x₁ x₂ i) = ({!!} ∙∙ {!!} ∙∙ {!!}) i
--       -- ·a-hexDiag (f x) (f x₁) (f x₂) i
--  f (·-hex-up x x₁ x₂ i i₁) = {!!}
--     -- ·a-hex-up (f x) (f x₁) (f x₂) i i₁
--  f (·-hex-down x x₁ x₂ i i₁) = {!!}
--        -- ·a-hex-down (f x) (f x₁) (f x₂) i i₁
--  f (·-pentagon-diag x x₁ x₂ x₃ i) =
--      ·a-pentagon-diag (f x) (f x₁) (f x₂) (f x₃) i 
--  f (·-pentagon-△ x x₁ x₂ x₃ i i₁) = {!!}
--      -- ·a-pentagon-△ (f x) (f x₁) (f x₂) (f x₃) i i₁
--  f (·-pentagon-□ x x₁ x₂ x₃ i i₁) = {!!}
--      -- ·a-pentagon-□ (f x) (f x₁) (f x₂) (f x₃) i i₁
--  f (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
--      isOfHLevel→isOfHLevelDep 3 (λ _ → isSet→isGroupoid asquash)
--       _ _ _ _
--      (λ i j → f (x₃ i j)) (λ i j → f (y₁ i j))
--      (trunc x x₁ x₂ y x₃ y₁) i i₁ x₄


record RecSetFCSG {ℓ} (A : Type ℓ) : Type ℓ where
 no-eta-equality
 field
  asquash : isSet A
  ●a : A
  ·a : A → A → A
  ·a-assoc : ∀ a b c → (·a a (·a b c)) ≡ (·a (·a a b) c)
  ·a-comm : ∀ a b → (·a a b) ≡ (·a b a)
  ·a-hexDiag : ∀ a b c →  
                     (·a (·a a b) c)
                  ≡ (·a b (·a c a))
  ·a-pentagon-diag : ∀ xs ys zs ws
      → (·a (·a (·a xs ys) zs) ws) ≡ (·a xs (·a ys (·a zs ws)))

 f : FCSG⊤ → A
 f = ElimSetFCSG.f w
  where
  w : ElimSetFCSG (λ _ → A)
  ElimSetFCSG.asquash w _ = asquash
  ElimSetFCSG.●a w = ●a
  ElimSetFCSG.·a w = ·a
  ElimSetFCSG.·a-assoc w = ·a-assoc
  ElimSetFCSG.·a-comm w = ·a-comm
  ElimSetFCSG.·a-hexDiag w = ·a-hexDiag
  ElimSetFCSG.·a-pentagon-diag w = ·a-pentagon-diag 

 -- f ● = ●a
 -- f (x · x₁) = ·a (f x) (f x₁)
 -- f (·-assoc x x₁ x₂ i) =
 --   ·a-assoc (f x) (f x₁) (f x₂) i
 -- f (·-comm x x₁ i) =
 --   ·a-comm (f x) (f x₁) i
 -- f (·-comminvol x x₁ i i₁) =
 --   {!!}
 -- f (·-hex-diag x x₁ x₂ i) =
 --      ·a-hexDiag (f x) (f x₁) (f x₂) i
 -- f (·-hex-up x x₁ x₂ i i₁) =
 --    {!!}
 -- f (·-hex-down x x₁ x₂ i i₁) =
 --      {!!}
 -- f (·-pentagon-diag x x₁ x₂ x₃ i) =
 --     ·a-pentagon-diag (f x) (f x₁) (f x₂) (f x₃) i 
 -- f (·-pentagon-△ x x₁ x₂ x₃ i i₁) =
 --     isSet→isSet'
 -- f (·-pentagon-□ x x₁ x₂ x₃ i i₁) = 
 --     {!? isSet→isSet' asquash
 --       !}
 -- f (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
 --   (isSet→isGroupoid asquash) _ _ _ _
 --     (λ i j → f (x₃ i j)) (λ i j → f (y₁ i j)) i i₁ x₄


-- -- -- repFCSG⊥ℕ : ℕ.ℕ → FCSG⊤
-- -- -- repFCSG⊥ℕ ℕ.zero = ●
-- -- -- repFCSG⊥ℕ (ℕ.suc x) = ● · repFCSG⊥ℕ x 

-- -- -- rep+ : ∀ n m → repFCSG⊥ℕ (ℕ.predℕ (ℕ.suc n))
-- -- --                 · repFCSG⊥ℕ (ℕ.predℕ (ℕ.suc m)) ≡
-- -- --                repFCSG⊥ℕ (ℕ.predℕ  ((ℕ.suc n) ℕ.+ (ℕ.suc m))) 
-- -- -- rep+ ℕ.zero m = refl
-- -- -- rep+ (ℕ.suc n) m = sym (·-assoc _ _ _) ∙ cong (● ·_) (rep+ n m)

-- -- -- repFCSG⊥ℕsingl : (n : ℕₐ⁺¹) → singl (repFCSG⊥ℕ (ℕ.predℕ (ℕₐ⁺¹→ℕ n)))
-- -- -- repFCSG⊥ℕsingl = ℕₐ⁺¹elim.f w
-- -- --  where
-- -- --  h : ∀ n m → (ℕ.predℕ (((ℕₐ⁺¹→ℕ n) ℕ.+ ℕₐ⁺¹→ℕ m))) ≡
      
-- -- --       (ℕ.predℕ (ℕₐ⁺¹→ℕ n) ℕ.+
-- -- --        ℕ.suc
-- -- --        (ℕ.predℕ (ℕₐ⁺¹→ℕ m)))
-- -- --  h = ℕₐ⁺¹→ℕ-elimProp
-- -- --       {A = λ n → ∀ m →
-- -- --         (ℕ.predℕ ((n ℕ.+ ℕₐ⁺¹→ℕ m))) ≡
      
-- -- --       (ℕ.predℕ n ℕ.+
-- -- --        ℕ.suc
-- -- --        (ℕ.predℕ (ℕₐ⁺¹→ℕ m)))}
-- -- --     (λ n → isPropΠ λ _ → ℕprops.isSetℕ _ _)
-- -- --      λ n → ℕₐ⁺¹→ℕ-elimProp
-- -- --            {A = λ m → ( ((n ℕ.+ m))) ≡ ( n ℕ.+ ℕ.suc (ℕ.predℕ m))}
-- -- --              (λ _ → ℕprops.isSetℕ _ _)
-- -- --               λ _ → refl
 
-- -- --  w : ℕₐ⁺¹elim (λ z → singl (repFCSG⊥ℕ (ℕ.predℕ (ℕₐ⁺¹→ℕ z))))
-- -- --  ℕₐ⁺¹elim.aOne w = _ , refl
-- -- --  fst ((w ℕₐ⁺¹elim.a+ (x , _)) (y , _)) = x · y
-- -- --  snd (ℕₐ⁺¹elim._a+_ w {n} {m} (x , x=) (y , y=)) =
-- -- --     -- cong′ (repFCSG⊥ℕ ∘' ℕ.predℕ) {!!}
-- -- --      (cong (repFCSG⊥ℕ) (cong ℕ.predℕ (+ₐ≡+ n m) ∙ h n m))
-- -- --     ∙∙ sym (rep+ _ _)
-- -- --          ∙∙ cong₂ _·_ x= y=
  

-- -- --  ℕₐ⁺¹elim.a-assoc w {n} {m} {o} x y z =
-- -- --    ΣPathP (·-assoc _ _ _
-- -- --         , {!!}) 
-- -- --  ℕₐ⁺¹elim.a-sym w = {!!}
-- -- --  ℕₐ⁺¹elim.asquash w = {!!}



-- -- -- repFCSG⊥ℕₐ⁺¹ : ℕₐ⁺¹ → FCSG⊤
-- -- -- repFCSG⊥ℕₐ⁺¹ = fst ∘ repFCSG⊥ℕsingl

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


-- -- -- toFCSG⊥'loop : ∀ n → AB n →      
-- -- --         repFCSG⊥ℕₐ⁺¹ n ≡ repFCSG⊥ℕₐ⁺¹ n
-- -- -- toFCSG⊥'loop n (𝕒𝕓 nothing l r nothing <n) =
-- -- --    cong repFCSG⊥ℕₐ⁺¹ (sym <n ∙ +-sym _ _) ∙∙ ·-comm _ _ ∙∙ cong repFCSG⊥ℕₐ⁺¹ <n
-- -- -- toFCSG⊥'loop n (𝕒𝕓 nothing l r (just x) <n) = {!!}
-- -- -- toFCSG⊥'loop n (𝕒𝕓 (just x) l r nothing <n) = {!!}
-- -- -- toFCSG⊥'loop n (𝕒𝕓 (just x) l r (just x₁) <n) = {!!}

-- -- -- -- ℕₐ⁺¹elim.f w
-- -- -- --  where
-- -- -- --  w : ℕₐ⁺¹elim λ z → AB z → repFCSG⊥ℕₐ⁺¹ z ≡ repFCSG⊥ℕₐ⁺¹ z
-- -- -- --  ℕₐ⁺¹elim.aOne w _ = refl
-- -- -- --  ℕₐ⁺¹elim._a+_ w = {!!}
-- -- -- --  ℕₐ⁺¹elim.a-assoc w = {!!}
-- -- -- --  ℕₐ⁺¹elim.a-sym w = {!!}
-- -- -- --  ℕₐ⁺¹elim.asquash w = {!!}

-- -- -- -- toFCSG⊥' : ∀ n → ℙrmₐ {true} n → FCSG⊤
-- -- -- -- toFCSG⊥' n 𝕡base = repFCSG⊥ℕₐ⁺¹ n
-- -- -- -- toFCSG⊥' n (𝕡loop x i) = toFCSG⊥'loop n x i
-- -- -- -- toFCSG⊥' n (𝕡invol (𝕒𝕓 lPad l r rPad <n) p i i₁) = {!lPad rPad!}
-- -- -- -- toFCSG⊥' n (𝕡hex lPad rPad l c r p p' p'' i i₁) = {!!}
-- -- -- -- toFCSG⊥' n (𝕡comm lPad cPad rPad l r l' r' p p' i i₁) = {!!}
-- -- -- -- toFCSG⊥' n (𝕡over lPad rPad l x x' p p' p'' i i₁) = {!!}
-- -- -- -- toFCSG⊥' n (𝕡squash x x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) = {!!}

-- -- -- -- fromFCSG⊥' : (x : FCSG⊤) → ℙrmₐ {true} (lenFCSG⊥ x)
-- -- -- -- fromFCSG⊥' ● = 𝕡base
-- -- -- -- fromFCSG⊥' (x · x₁) = 𝕡· (fromFCSG⊥' x) (fromFCSG⊥' x₁)
-- -- -- -- fromFCSG⊥' (·-assoc x x₁ x₂ i) =
-- -- -- --  𝕡·-assoc (fromFCSG⊥' x) (fromFCSG⊥' x₁) (fromFCSG⊥' x₂) i
-- -- -- -- fromFCSG⊥' (·-comm x x₁ i) = {!!}
-- -- -- -- fromFCSG⊥' (·-hex-diag x x₁ x₂ i) = {!!}
-- -- -- -- fromFCSG⊥' (·-hex-up x x₁ x₂ i i₁) = {!!}
-- -- -- -- fromFCSG⊥' (·-hex-down x x₁ x₂ i i₁) = {!!}
-- -- -- -- fromFCSG⊥' (·-pentagon-diag x x₁ x₂ x₃ i) = {!!}
-- -- -- -- fromFCSG⊥' (·-pentagon-△ x x₁ x₂ x₃ i i₁) = {!!}
-- -- -- -- fromFCSG⊥' (·-pentagon-□ x x₁ x₂ x₃ i i₁) = {!!}


-- -- -- -- -- -- -- 𝕡hex : ∀ lPad rPad l c r → ∀ p p' p'' →
-- -- -- -- -- -- --          SquareP (λ i j → ℙrmₐ {true}
-- -- -- -- -- -- --              (isSet→isSet' isSetℕₐ⁺¹
-- -- -- -- -- -- --              (λ j → lPad + +-sym l c j + (r + rPad))
-- -- -- -- -- -- --              (λ j → lPad + +-sym l (c + r) j + rPad)
-- -- -- -- -- -- --              -- (λ j → lPad + +-sym l c j + (r + rPad))
-- -- -- -- -- -- --              -- (λ j → c + lPad + +-sym l r j + rPad)
-- -- -- -- -- -- --              {!!}
-- -- -- -- -- -- --              ({!!} ∙∙ (λ i → (lPad + c) + +-sym l r i + rPad) ∙∙ {!!})
-- -- -- -- -- -- --              -- (+-assoc _ _ _ ∙ cong (_+ _) {!!})
-- -- -- -- -- -- --              --(λ i → (lPad + +-sym l (c + r) i + rPad))
-- -- -- -- -- -- --              i j)
-- -- -- -- -- -- --              )
-- -- -- -- -- -- --        -- {𝕡base {n = {!!}}}
-- -- -- -- -- -- --        -- {𝕡base {n = lPad + (l + (c + r)) + rPad}}
-- -- -- -- -- -- --        -- (𝕡loop lPad l c (r + rPad))
-- -- -- -- -- -- --        -- {𝕡base {n = {!!}}}
-- -- -- -- -- -- --        -- {𝕡base {n = {!!}}}
-- -- -- -- -- -- --        -- (𝕡loop (c + lPad) l r rPad)
-- -- -- -- -- -- --        -- {!!}
-- -- -- -- -- -- --        (𝕡loop lPad l c (r + rPad))
-- -- -- -- -- -- --        (𝕡loop lPad l (c + r) rPad)
-- -- -- -- -- -- --        {!!}
-- -- -- -- -- -- --        {!!}
-- -- -- -- -- -- --        -- (𝕡loop (lPad + c) l r rPad)
       
-- -- -- -- -- -- -- 𝕡hex = {!!}
