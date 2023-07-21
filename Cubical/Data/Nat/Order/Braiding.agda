{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.Braiding where

open import Cubical.Data.Nat.Base as ℕ hiding (_·_)
open import Cubical.Data.Nat.Properties


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution

open import Cubical.Foundations.Everything
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Bool using (false ; true) renaming (Bool to 𝟚) 
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group

open import Cubical.Algebra.SymmetricGroup

import Cubical.Functions.Logic as L

open import Cubical.Functions.Embedding

open import Cubical.Data.List as Li

open import Cubical.HITs.S1 renaming (_·_ to _·S₁_)


import Cubical.Data.Nat.FinGenAut2 as A

import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


open import Cubical.Algebra.Group.Morphisms

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SequentialColimit as SC

import Cubical.Algebra.Group.Abelianization.Base as GA
open import Cubical.Algebra.Group.Abelianization.Properties 
open import Cubical.Data.Int hiding (_·_)


private
  variable
    ℓ : Level




infixr 4  _=→_



_=→_ : ∀ {ℓ} {A : ℕ → Type ℓ} {f g : ∀ k → A k}
            → f zero ≡ g zero
            → (f ∘ suc ≡ g ∘ suc )
            → f ≡ g
_=→_ x x₁ i zero = x i
_=→_ x x₁ i (suc x₂) = x₁ i x₂


infixr 4  _sq→_

_sq→_ : ∀ {ℓ} {A : Type ℓ} {f g f' g'  : ℕ → A}
            → {fg : f ≡ g}
              {f'g' : f' ≡ g'}
              {ff' : f ≡ f'}
              {gg' : g ≡ g'}
            → Square (funExt⁻ fg zero)
                     (funExt⁻ f'g' zero)
                     (funExt⁻ ff' zero)
                     (funExt⁻ gg' zero)  
            → Square (cong (_∘ suc) fg)
                     (cong (_∘ suc) f'g')
                     (cong (_∘ suc) ff')
                     (cong (_∘ suc) gg') 
            → Square (fg)
                     (f'g')
                     (ff')
                     (gg')
(x sq→ x₁) i i₁ zero = x i i₁
(x sq→ x₁) i i₁ (suc x₂) = x₁ i i₁ x₂

-- infixr 4  _P→_



-- _P→_ : ∀ {ℓ} {A : ℕ → Type ℓ} {f g : ∀ k → A k}
--             → f zero ≡ g zero
--             → (f ∘ suc ≡ g ∘ suc )
--             → f ≡ g
-- _P→_ x x₁ i zero = x i
-- _P→_ x x₁ i (suc x₂) = x₁ i x₂



    
infixr 5 _′_∷_


data Braid (n : ℕ) : Type where
  
  ε     : Braid n
  _ʻ_∷_ : 𝟚 → (Σ ℕ  λ k → (suc k < n)) → Braid n → Braid n
  inv∷ : ∀ b x xs → 𝟚.not b ʻ x ∷  (b ʻ x ∷ xs) ≡ xs
  braid : ∀ b k k< → ∀ xs →  
            b ʻ (k , <-weaken {n = n} k<) ∷ (b ʻ (suc k , k<)
              ∷ (b ʻ (k , <-weaken {n = n} k<) ∷ xs))
         ≡ b ʻ (suc k , k<) ∷ (b ʻ (k , <-weaken {n = n} k<) ∷ (b ʻ (suc k , k<) ∷ xs))
  comm : ∀ b b' k l → commT (fst k) (fst l) → ∀ xs →
      b ʻ k ∷ (b' ʻ l ∷ xs) ≡ b' ʻ l ∷ (b ʻ k ∷ xs)
  
  trunc : isSet (Braid n)

record Rrec {ℓ} {n : ℕ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    isSetA : isSet A
    εA : A
    ∷A : 𝟚 → (Σ ℕ  λ k → (suc k < n)) → A → A
    inv∷A : ∀ b k → ∀ x →
                     ∷A (𝟚.not b) k (∷A b k  x) ≡ x    
    braidA : ∀ b k → ∀ k< → ∀ x →
         ∷A b (k , <-weaken {n = n} k<) (∷A b (suc k , k<)
          (∷A b (k , <-weaken {n = n} k<) x))
       ≡ ∷A b (suc k , k<) (∷A b (k , <-weaken {n = n} k<) (∷A b (suc k , k<) x))
    commA : ∀ b b' k l → commT (fst k) (fst l) → ∀ x →
                     ∷A b k (∷A b' l x) ≡ ∷A b' l (∷A b k x)

  f : (Braid n) → A
  f ε = εA
  f (b ʻ x ∷ xs) = ∷A b x (f xs)
  f (inv∷ b x x₁ i) = inv∷A b x (f x₁) i
  f (braid b k k< x i) = braidA b k k< (f x) i
  f (comm b b' k l x x₁ i) = commA b b' k l x (f x₁) i
  f (trunc _ _ p q i i₁) = isSetA _ _ (cong f p) (cong f q) i i₁

record RelimProp {ℓ} {n : ℕ} (A : (Braid n) → Type ℓ) : Type ℓ where
  no-eta-equality
  field
    isPropA : ∀ x → isProp (A x)
    εA : A ε
    ∷A : ∀ b k → ∀ {xs} → A xs → A (b ʻ k ∷ xs)

  f : ∀ x → A x
  f ε = εA
  f (x ʻ x₁ ∷ x₂) = ∷A x x₁ (f x₂)
  f (inv∷ b k x i) =
    isProp→PathP (λ i → isPropA (inv∷ b k x i))
      (∷A (𝟚.not b) k
       (∷A b k (f x)))
      (f x) i
  f (braid b k k< x i) =
         isProp→PathP (λ i → isPropA (braid b k k< x i))
      (∷A b (k , <-weaken {n = n} k<) (∷A b (suc k , k<)
       (∷A b (k , <-weaken {n = n}  k<) (f x))))
      (∷A b (suc k , k<) (∷A b (k , <-weaken {n = n}  k<)
        (∷A b (suc k , k<) (f x)))) i
  f (comm b b' k l x x₁ i) =
    isProp→PathP (λ i → isPropA (comm b b' k l x x₁  i))
      (∷A b k (∷A b' l (f x₁)))
      (∷A b' l (∷A b k (f x₁))) i
  f (trunc x y p q i i₁) =
         isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (isPropA x))
         _ _ (cong f p) (cong f q) (trunc x y p q) i i₁


-- -- invoA-hlp : ∀ {ℓ} {n : ℕ} (A : (Braid n) → Type ℓ) →
-- --        (εA : A ε)
-- --        (∷A : ∀ k → ∀ {xs} → A xs → A (k ∷ xs))
-- --      → (∀ k {xs : Braid n} (x : A xs) →
-- --           PathP (λ i → {!!})
-- --              (∷A k {xs} x) {!!}
-- --           )
-- --      → (∀ k {x : Braid n} (x' : A x) → PathP (λ i → A (invo k x i))
-- --        (∷A k (∷A k x')) x')
    
-- -- invoA-hlp = {!!}

-- record Relim {ℓ} {n : ℕ} (A : (Braid n) → Type ℓ) : Type ℓ where
--   no-eta-equality
--   field
--     isSetA : ∀ x → isSet (A x)
--     εA : A ε
--     ∷A : ∀ k → ∀ {xs} → A xs → A (k ∷ xs)
--     braidA : ∀ k k< {x} x' → PathP (λ i → A (braid k k< x i))
--                (∷A (k , <-weaken {n = n} k<) (∷A (suc k , k<)
--           (∷A (k , <-weaken {n = n} k<) x')))
--        (∷A (suc k , k<) (∷A (k , <-weaken {n = n} k<) (∷A (suc k , k<) x')))
--     commA : ∀ k l z {x} x' → PathP (λ i → A (comm k l z x  i))
--       (∷A k (∷A l x'))
--       (∷A l (∷A k x'))

--   f : ∀ x → A x
--   f ε = εA
--   f (x ∷ x₁) = ∷A x (f x₁)
--   f (braid k k< x i) = braidA k k< (f x) i

--   f (comm k l x x₁ i) = commA k l x (f x₁) i
--   f (trunc x y p q i i₁) =
--          isOfHLevel→isOfHLevelDep 2 (λ x → (isSetA x))
--          _ _ (cong f p) (cong f q) (trunc x y p q) i i₁





-- -- -- record RelimSingl {ℓ} {n : ℕ} (A : (Braid n) → Type ℓ) : Type ℓ where
-- -- --   no-eta-equality
-- -- --   field
-- -- --     a₀ : ∀ {x} → A x
-- -- --     εA : A ε
-- -- --     εA≡ : a₀ ≡ εA
-- -- --     ∷A : ∀ k → ∀ {xs} → A xs → A (k ∷ xs)
-- -- --     ∷A≡ : ∀ k → ∀ {xs} → ∀ (x : A xs) → a₀ ≡ x → a₀ ≡ ∷A k x
-- -- --     invoA : ∀ k {x} x' → PathP (λ i → A (invo k x i))
-- -- --       (∷A k (∷A k x'))
-- -- --       x'    
    
-- -- --   --   braidA : ∀ k k< {x} x' → PathP (λ i → A (braid k k< x i))
-- -- --   --              (∷A (k , <-weaken {n = n} k<) (∷A (suc k , k<)
-- -- --   --         (∷A (k , <-weaken {n = n} k<) x')))
-- -- --   --      (∷A (suc k , k<) (∷A (k , <-weaken {n = n} k<) (∷A (suc k , k<) x')))
-- -- --   --   commA : ∀ k l z {x} x' → PathP (λ i → A (comm k l z x  i))
-- -- --   --     (∷A k (∷A l x'))
-- -- --   --     (∷A l (∷A k x'))

-- -- --   -- fR = 

-- -- --   r : Relim λ x → singl (a₀ {x})
-- -- --   Relim.isSetA r _ = isOfHLevelPlus 2 (isContrSingl _)
-- -- --   fst (Relim.εA r) = εA
-- -- --   snd (Relim.εA r) = εA≡ 
-- -- --   fst (Relim.∷A r k x) = ∷A k (fst x)
-- -- --   snd (Relim.∷A r k x) = ∷A≡ k (fst x) (snd x)
-- -- --   Relim.invoA r = {!!}
-- -- --   Relim.braidA r = {!!}
-- -- --   Relim.commA r = {!!}

𝟚→ΩS¹ : 𝟚 → ΩS¹
𝟚→ΩS¹ false = sym loop
𝟚→ΩS¹ true = loop

toΩS1 : ∀ {n} → Braid n → ΩS¹
toΩS1 = Rrec.f w
 where
 w : Rrec ΩS¹
 Rrec.isSetA w = isSetΩS¹
 Rrec.εA w = refl
 Rrec.∷A w x _ = 𝟚→ΩS¹ x ∙'_
 Rrec.inv∷A w b k x = {!!}
 Rrec.braidA w _ _ _ _ = refl
 Rrec.commA w false false _ _ _ _ = refl
 Rrec.commA w false true _ _ _ _ = {!!}
 Rrec.commA w true false _ _ _ _ = {!!}
 Rrec.commA w true true _ _ _ _ = refl
 
_·_ : ∀ {n} → Braid n → Braid n → Braid n
ε · x₁ = x₁
(x ʻ x₂ ∷ x₃) · x₁ = x ʻ x₂ ∷ (x₃ · x₁)
inv∷ b x₁ x₂ i · x = inv∷ b x₁ (x₂ · x) i
braid b k k< x i · x₁ = braid b k k< (x · x₁) i 
comm b b' k l x x₂ i · x₁ = comm b b' k l x (x₂ · x₁) i 
trunc x x₂ x₃ y i i₁ · x₁ =
  trunc (x · x₁) (x₂ · x₁)
    (cong  (_· x₁) x₃) (cong  (_· x₁) y) i i₁

assoc· : ∀ {n} (x y z : Braid n) → x · (y · z) ≡ (x · y) · z
assoc· = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = isPropΠ2 λ _ _ → trunc _ _
   RelimProp.εA w _ _ = refl
   RelimProp.∷A w _ _ p _ _  = cong (_ ʻ _ ∷_) (p _ _)
   

idr : ∀ {n} → ∀ (x : Braid n) → (x · ε) ≡ x
idr = RelimProp.f
    (record { isPropA = λ _ → trunc _ _
            ; εA = refl
            ; ∷A = λ _ _ → cong (_ ʻ _ ∷_) })
   
η : ∀ {n} → (Σ ℕ  λ k → (suc k < n)) → Braid n
η = true ʻ_∷ ε 


inv : ∀ {n} → Braid n → Braid n
inv = Rrec.f w

  where
    w : Rrec _
    Rrec.isSetA w = trunc
    Rrec.εA w = ε
    Rrec.∷A w x x₁ = _· (𝟚.not x ʻ x₁ ∷ ε )
    Rrec.inv∷A w b k x =
      sym (assoc· x (𝟚.not b ʻ k ∷ ε) (𝟚.not  (𝟚.not b) ʻ k ∷ ε)) ∙∙
       (cong  (x ·_) {!inv∷ b k ε!}) ∙∙ idr x
    Rrec.braidA w = {!!}
    Rrec.commA w = {!!}
    -- Rrec.isSetA w = trunc 
    -- Rrec.εA w = ε
    -- Rrec.∷A w k = _· (η k) 
    -- Rrec.braidA w k k< x =
    --    (cong (_· η _) (sym (assoc· x (η _) (η _))) ∙ sym (assoc· x (η _ · η _) (η _)))
    --     ∙∙ cong (x ·_) (sym (assoc· (η _) (η _) (η _))
    --            ∙∙ braid k k< ε ∙∙ 
    --             (assoc· (η _) (η _) (η _))) ∙∙
    --    ((assoc· x (η _ · η _) (η _)) ∙
    --     cong (_· η _) (assoc· x (η _) (η _)))
    -- Rrec.commA w k l z x = 
    --    sym (assoc· x _ _)
    --     ∙∙ cong (x ·_) (sym (comm k l z ε)) ∙∙
    --    (assoc· x _ _)

invr : ∀ {n} → (x : Braid n) → (x · inv x) ≡ ε
invr = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = trunc _ _ 
   RelimProp.εA w = refl
   RelimProp.∷A w b k {xs} p = 
     cong′ (b ʻ k ∷_) (assoc· xs (inv xs) _ ∙ cong (_· _) p)
      ∙∙ cong (_ʻ k ∷ (𝟚.not b ʻ k ∷ ε)) (sym (𝟚.notnot b))
      ∙∙ inv∷ (𝟚.not b) k ε

invl : ∀ {n} → (x : Braid n) → (inv x · x) ≡ ε
invl = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = trunc _ _ 
   RelimProp.εA w = refl
   RelimProp.∷A w b k {xs} p = 
    sym (assoc· (inv xs) _ _) ∙∙ cong (inv xs ·_) (inv∷ _ _ _) ∙∙ p
      

BraidG : ∀ n →  Group ℓ-zero
fst (BraidG n) = Braid n
GroupStr.1g (snd (BraidG n)) = ε
GroupStr._·_ (snd (BraidG n)) = _·_
GroupStr.inv (snd (BraidG n)) = inv
GroupStr.isGroup (snd (BraidG n)) =
  makeIsGroup trunc assoc· idr (λ _ → refl) invr invl

-- toAB : ∀ n → ℤ → GA.Abelianization (BraidG n)
-- toAB n (pos n₁) = GA.η ({!!} · {!!})
-- -- toAB n (pos (suc n₁)) = {!!}
-- toAB n (negsuc n₁) = {!!}

-- fromAB : ∀ n → GA.Abelianization (BraidG n) → ℤ
-- fromAB n (GA.η g) = winding (toΩS1 g)
-- fromAB n (GA.comm a b c i) = {!!}
-- fromAB n (GA.isset x x₁ p q i i₁) = {!!}

-- IsoAb : ∀ n → Iso ℤ (GA.Abelianization (BraidG n))
-- Iso.fun (IsoAb n) = {!!}
-- Iso.inv (IsoAb n) = {!!}
-- Iso.rightInv (IsoAb n) = {!!}
-- Iso.leftInv (IsoAb n) = {!!}

-- -- -- -- -- sucBraidR : ∀ n → Rrec {n = n} (Braid (suc n))
-- -- -- -- -- Rrec.isSetA (sucBraidR n) = trunc
-- -- -- -- -- Rrec.εA (sucBraidR n) = ε
-- -- -- -- -- Rrec.∷A (sucBraidR n) (k , k<) = ((suc k , k<) ) ∷_
-- -- -- -- -- Rrec.invoA (sucBraidR n) _ _ = invo _ _
-- -- -- -- -- Rrec.braidA (sucBraidR n) _ _ _ = braid _ _ _
-- -- -- -- -- Rrec.commA (sucBraidR n) (k , _) (suc l , _) t _ = comm _ _ t _

-- -- -- -- -- sucBraid : ∀ {n} → Braid n → Braid (suc n)
-- -- -- -- -- sucBraid {n} = Rrec.f (sucBraidR n) 

-- -- -- -- -- sucBraid·R  : ∀ n → RelimProp
-- -- -- -- --       (λ z →
-- -- -- -- --          (y : fst (BraidG n)) →
-- -- -- -- --          sucBraid ((snd (BraidG n) GroupStr.· z) y) ≡
-- -- -- -- --          (snd (BraidG (suc n)) GroupStr.· sucBraid z) (sucBraid y))
-- -- -- -- -- RelimProp.isPropA (sucBraid·R n) _ = isPropΠ λ _ →  trunc _ _
-- -- -- -- -- RelimProp.εA (sucBraid·R n) = λ _ → refl
-- -- -- -- -- RelimProp.∷A (sucBraid·R n) k = cong ((suc (fst k) , snd k) ∷_) ∘_

-- -- -- -- -- sucBraid· : ∀ {n} (g h : Braid n) →
-- -- -- -- --     sucBraid (g · h) ≡ sucBraid g · sucBraid h 
-- -- -- -- -- sucBraid· = RelimProp.f (sucBraid·R _)

-- -- -- -- -- sucBraidInv : ∀ n → RelimProp
-- -- -- -- --       (λ z →
-- -- -- -- --          sucBraid (GroupStr.inv (snd (BraidG n)) z) ≡
-- -- -- -- --          GroupStr.inv (snd (BraidG (suc n))) (sucBraid z))
-- -- -- -- -- RelimProp.isPropA (sucBraidInv n) _ = trunc _ _ 
-- -- -- -- -- RelimProp.εA (sucBraidInv n) = refl
-- -- -- -- -- RelimProp.∷A (sucBraidInv n) k {xs} X =
-- -- -- -- --    RelimProp.f (sucBraid·R n) (inv xs) (η k)
-- -- -- -- --      ∙ cong (_· (η (suc (fst k) , snd k))) X

-- -- -- -- -- sucBraidGH : ∀ n → IsGroupHom (snd (BraidG n))
-- -- -- -- --    (sucBraid)
-- -- -- -- --    (snd (BraidG (suc n)))
-- -- -- -- -- IsGroupHom.pres· (sucBraidGH n) =
-- -- -- -- --    RelimProp.f (sucBraid·R n)
-- -- -- -- -- IsGroupHom.pres1 (sucBraidGH n) = refl
-- -- -- -- -- IsGroupHom.presinv (sucBraidGH n) =
-- -- -- -- --   RelimProp.f (sucBraidInv n)

-- -- -- -- -- sucBraidComm : ∀ {n} → (g : Braid n) →
-- -- -- -- --      η (zero , _) · sucBraid (sucBraid g)
-- -- -- -- --    ≡ sucBraid (sucBraid g) · η (zero , _) 
-- -- -- -- -- sucBraidComm = RelimProp.f w
-- -- -- -- --  where
-- -- -- -- --    w : RelimProp _
-- -- -- -- --    RelimProp.isPropA w _ = trunc _ _
-- -- -- -- --    RelimProp.εA w = refl
-- -- -- -- --    RelimProp.∷A w k {xs} X =
-- -- -- -- --      comm _ _ _ _ ∙ cong ((suc (suc (fst k)) , snd k) ∷_) X

-- -- -- -- -- weakBraidR : ∀ n → Rrec {n = n} (Braid (suc n))
-- -- -- -- -- Rrec.isSetA (weakBraidR n) = trunc
-- -- -- -- -- Rrec.εA (weakBraidR n) = ε
-- -- -- -- -- Rrec.∷A (weakBraidR n) (k , k<) = ((k , <-weaken {n = n} k<) ) ∷_
-- -- -- -- -- Rrec.invoA (weakBraidR n) _ _ = invo _ _
-- -- -- -- -- Rrec.braidA (weakBraidR n) _ _ _ = braid _ _ _
-- -- -- -- -- Rrec.commA (weakBraidR n) (k , _) (suc l , _) t _ = comm _ _ t _

-- -- -- -- -- +Braid : ∀ {n} m → Braid n → Braid (m + n)
-- -- -- -- -- +Braid zero x = x
-- -- -- -- -- +Braid (suc m) x = sucBraid (+Braid m x)

-- -- -- -- -- weakBraid : ∀ n → Braid n → Braid (suc n)
-- -- -- -- -- weakBraid n = Rrec.f (weakBraidR n)


-- -- -- -- -- +WeakBraid : ∀ n {m} → Braid m → Braid (m + n)
-- -- -- -- -- +WeakBraid zero = subst Braid (sym (+-zero _))
-- -- -- -- -- +WeakBraid (suc n) x = subst Braid (sym (+-suc _ _)) (weakBraid _ (+WeakBraid n x))

-- -- -- -- -- +WeakBraid' : ∀ n {m} → Braid m → Braid (n + m)
-- -- -- -- -- +WeakBraid' zero x = x
-- -- -- -- -- +WeakBraid' (suc n) x = weakBraid _ (+WeakBraid' _ x)

-- -- -- -- -- weakBraid·  : ∀ n → RelimProp      
-- -- -- -- --       (λ z →
-- -- -- -- --          (y : Braid n) →
-- -- -- -- --          weakBraid n ((snd (BraidG n) GroupStr.· z) y) ≡
-- -- -- -- --          (weakBraid n z · weakBraid n y))
-- -- -- -- -- RelimProp.isPropA (weakBraid· n) _ = isPropΠ λ _ →  trunc _ _
-- -- -- -- -- RelimProp.εA (weakBraid· n) y = refl
-- -- -- -- -- RelimProp.∷A (weakBraid· n) k = cong ((fst k , <-weaken {n = n} (snd k)) ∷_) ∘_

-- -- -- -- -- weakBraidInv : ∀ n → RelimProp
-- -- -- -- --       (λ z →
-- -- -- -- --          weakBraid n (GroupStr.inv (snd (BraidG n)) z) ≡
-- -- -- -- --          GroupStr.inv (snd (BraidG (suc n))) (weakBraid n z))
-- -- -- -- -- RelimProp.isPropA (weakBraidInv n) _ = trunc _ _ 
-- -- -- -- -- RelimProp.εA (weakBraidInv n) = refl
-- -- -- -- -- RelimProp.∷A (weakBraidInv n) k {xs} X =
-- -- -- -- --    RelimProp.f (weakBraid· n) (inv xs) (η k)
-- -- -- -- --      ∙ cong (_· (η ((fst k) , <-weaken {n = n} (snd k)))) X


-- -- -- -- -- weakBraidGH : ∀ n → IsGroupHom (snd (BraidG n))
-- -- -- -- --    (weakBraid n)
-- -- -- -- --    (snd (BraidG (suc n)))
-- -- -- -- -- IsGroupHom.pres· (weakBraidGH n) =
-- -- -- -- --    RelimProp.f (weakBraid· n)
-- -- -- -- -- IsGroupHom.pres1 (weakBraidGH n) = refl
-- -- -- -- -- IsGroupHom.presinv (weakBraidGH n) =
-- -- -- -- --   RelimProp.f (weakBraidInv n)


-- -- -- -- -- -- discreteBraid'ε : ∀ n → RelimProp {n = n} (λ z → Dec (ε ≡ z))
-- -- -- -- -- -- RelimProp.isPropA (discreteBraid'ε n) _ = isPropDec (trunc _ _)
-- -- -- -- -- -- RelimProp.εA (discreteBraid'ε n) = yes refl
-- -- -- -- -- -- RelimProp.∷A (discreteBraid'ε n) _ _ = no {!!}

-- -- -- -- -- -- discreteBraid' : ∀ n → RelimProp (λ z → (y : Braid n) → Dec (z ≡ y))
-- -- -- -- -- -- RelimProp.isPropA (discreteBraid' n) _ = isPropΠ λ _ → isPropDec (trunc _ _)
-- -- -- -- -- -- RelimProp.εA (discreteBraid' n) =
-- -- -- -- -- --   RelimProp.f {!!}
-- -- -- -- -- -- RelimProp.∷A (discreteBraid' n) = {!!}

-- -- -- -- -- -- discreteBraid : ∀ n → Discrete (Braid n)
-- -- -- -- -- -- discreteBraid n = RelimProp.f {!!}

-- -- -- -- -- -- -- WeakComm :  ∀ {n m} → (h : Braid m) (k : ℕ)
-- -- -- -- -- -- --     (k< : suc (m + k) < m + suc (suc n)) →
-- -- -- -- -- -- --        +WeakBraid (suc (suc n)) h · η (m + k , k<)
-- -- -- -- -- -- --      ≡ (η (m + k , k<)
-- -- -- -- -- -- --         · +WeakBraid (suc (suc n)) h)
-- -- -- -- -- -- -- WeakComm = {!!}




-- -- -- -- -- -- weakSuc-comm : ∀ {n m} → (h : Braid m) (g : Braid n) →
-- -- -- -- -- --        +WeakBraid _ h · +Braid _ ((sucBraid _ (sucBraid _ g)))
-- -- -- -- -- --      ≡ (+Braid  _ (sucBraid _ (sucBraid _ g) )
-- -- -- -- -- --         · +WeakBraid _ h)
-- -- -- -- -- -- weakSuc-comm = {!!}




-- -- -- -- -- adjT< : ∀ n k j → suc k < n → j < n → A.adjTransposition k j < n
-- -- -- -- -- adjT< (suc (suc n)) zero zero x x₁ = _
-- -- -- -- -- adjT< (suc (suc n)) zero (suc zero) x x₁ = _
-- -- -- -- -- adjT< (suc (suc n)) zero (suc (suc j)) x x₁ = x₁
-- -- -- -- -- adjT< (suc (suc n)) (suc k) zero x x₁ = x₁
-- -- -- -- -- adjT< (suc (suc n)) (suc k) (suc j) x x₁ = adjT< (suc n) k j x x₁

-- -- -- -- -- adjT : ∀ n → Σ ℕ (λ k₁ → suc k₁ < n) → Σ ℕ (λ k₁ → k₁ < n) → Σ ℕ (λ k₁ → k₁ < n)
-- -- -- -- -- adjT n (k , k<) (j , j<) = A.adjTransposition k j , adjT< n k j k< j<
-- -- -- -- -- -- fst (adjT n (k , _) (j , _)) = A.adjTransposition k j
-- -- -- -- -- -- snd (adjT n (k , k<) (j , j<)) = adjT< n k j k< j<

-- -- -- -- -- extOnℕ : ∀ n → {f f' : Fin n → Fin n} →
-- -- -- -- --  (Path (∀ (k : ℕ) → {_ : k < n} → ℕ)
-- -- -- -- --     (λ k {k<} → fst (f (k , k<))) (λ k {k<} → fst (f' (k , k<))))
-- -- -- -- --  → f ≡ f'
-- -- -- -- -- extOnℕ n x = funExt λ x₁ → ≡Fin {n = n} λ i → x i (fst x₁) {snd x₁} 

-- -- -- -- -- isInvolution-adjT : ∀ n k → isInvolution (adjT n k)
-- -- -- -- -- isInvolution-adjT (suc (suc n)) (zero , snd₁) (zero , snd₂) = refl
-- -- -- -- -- isInvolution-adjT (suc (suc n)) (zero , snd₁) (suc zero , snd₂) = refl
-- -- -- -- -- isInvolution-adjT (suc (suc n)) (zero , snd₁) (suc (suc fst₁) , snd₂) = refl
-- -- -- -- -- isInvolution-adjT (suc (suc (suc n))) (suc k , snd₁) (zero , snd₂) = refl
-- -- -- -- -- isInvolution-adjT (suc (suc (suc n))) (suc k , snd₁) (suc fst₁ , snd₂) =
-- -- -- -- --   cong sucF (isInvolution-adjT (suc (suc n)) (k , snd₁) (fst₁ , snd₂))

-- -- -- -- -- adjT-braid : ∀ n k k< →
-- -- -- -- --       ( adjT n (k , <-weaken {n = n} k<)
-- -- -- -- --       ∘ adjT n (suc k , k<)
-- -- -- -- --       ∘ adjT n (k , <-weaken {n = n} k<))
-- -- -- -- --   ≡ ( adjT n (suc k , k<)
-- -- -- -- --       ∘ adjT n (k , <-weaken {n = n} k<)
-- -- -- -- --       ∘ adjT n (suc k , k<))
-- -- -- -- -- adjT-braid (suc (suc (suc n))) zero k< i (zero , _) = 2 , _
-- -- -- -- -- adjT-braid (suc (suc (suc n))) zero k< i (suc zero , _) = 1 , _
-- -- -- -- -- adjT-braid (suc (suc (suc n))) zero k< i (suc (suc zero) , _) = 0 , _
-- -- -- -- -- adjT-braid (suc (suc (suc n))) zero k< i (suc (suc (suc l)) , l<) =
-- -- -- -- --   (suc (suc (suc l)) , l<)
-- -- -- -- -- adjT-braid (suc (suc (suc (suc n)))) (suc k) k< i (zero , _) = 0 , _
-- -- -- -- -- adjT-braid (suc (suc (suc (suc n)))) (suc k) k< i (suc l , l<) =
-- -- -- -- --   sucF (adjT-braid (suc (suc (suc n))) k k< i (l , l<))

-- -- -- -- -- adjT-comm : ∀ n k l → commT (fst k) (fst l) → ∀ a →
-- -- -- -- --       (( adjT n l
-- -- -- -- --       ∘ adjT n k) a)
-- -- -- -- --   ≡ (( adjT n k
-- -- -- -- --       ∘ adjT n l) a)
-- -- -- -- -- adjT-comm (suc (suc n)) (zero , k<) (suc (suc l) , l<) x (zero , a<) = refl
-- -- -- -- -- adjT-comm (suc (suc n)) (zero , k<) (suc (suc l) , l<) x (suc zero , a<) = refl
-- -- -- -- -- adjT-comm (suc (suc n)) (zero , k<) (suc (suc l) , l<) x (suc (suc a) , a<) = refl
-- -- -- -- -- adjT-comm (suc (suc n)) (suc k , k<) (suc (suc (suc l)) , l<) x (zero , a<) = refl
-- -- -- -- -- adjT-comm (suc (suc n)) (suc k , k<) (suc (suc (suc l)) , l<) x (suc a , a<) =
-- -- -- -- --   cong sucF (adjT-comm (suc n) (k , k<) (suc (suc l) , l<) x (a , a<))

-- -- -- -- -- adjT≃ : ∀ {n} → Fin n → Fin (suc n) ≃ Fin (suc n)
-- -- -- -- -- adjT≃ {n} k = involEquiv {f = adjT (suc n) k} (isInvolution-adjT (suc n)  k)

-- -- -- -- -- adjTIso : ∀ {n} → Fin n → Iso (Fin (suc n)) (Fin (suc n))
-- -- -- -- -- adjTIso {n} k = involIso {f = adjT (suc n) k} (isInvolution-adjT (suc n)  k)

-- -- -- -- -- adjTIso' : ∀ {n} → (Σ ℕ  λ k → (suc k < n)) → Iso (Fin n) (Fin n)
-- -- -- -- -- adjTIso' {n} k = involIso {f = adjT n k} (isInvolution-adjT n k)

-- -- -- -- -- adjT'≃ : ∀ {n} → (Σ ℕ  λ k → (suc k < n)) → (Fin n) ≃ (Fin n)
-- -- -- -- -- adjT'≃ {n = n} = isoToEquiv ∘ adjTIso' {n}


-- -- -- -- -- toℕFGℕ≃ℕ : ∀ {n} → Braid n → A.FGℕ≃ℕ
-- -- -- -- -- toℕFGℕ≃ℕ ε = A.ε
-- -- -- -- -- toℕFGℕ≃ℕ ((x , _) ∷ xs) = x A.∷  toℕFGℕ≃ℕ xs
-- -- -- -- -- toℕFGℕ≃ℕ (invo (k , _) x i) = A.invo k (toℕFGℕ≃ℕ x) i
-- -- -- -- -- toℕFGℕ≃ℕ (braid k k< x i) = A.braid k (toℕFGℕ≃ℕ x) i
-- -- -- -- -- toℕFGℕ≃ℕ (comm (k , _) (l , _) z x i) = A.comm k l z (toℕFGℕ≃ℕ x) i
-- -- -- -- -- toℕFGℕ≃ℕ (trunc _ _ p q i i₁) =
-- -- -- -- --   A.trunc _ _ (cong toℕFGℕ≃ℕ p) (cong toℕFGℕ≃ℕ q) i i₁ 

-- -- -- -- -- toℕFGℕ≃ℕ· : ∀ {n} f g → (toℕFGℕ≃ℕ {n} f) A.· (toℕFGℕ≃ℕ g) ≡ toℕFGℕ≃ℕ (f · g) 
-- -- -- -- -- toℕFGℕ≃ℕ· = RelimProp.f w
-- -- -- -- --  where
-- -- -- -- --   w : RelimProp _
-- -- -- -- --   RelimProp.isPropA w _ = isPropΠ λ _ → A.trunc _ _
-- -- -- -- --   RelimProp.εA w _ = refl
-- -- -- -- --   RelimProp.∷A w (k , _) = cong (k A.∷_) ∘_

-- -- -- -- -- toℕFGℕ≃ℕinv :  ∀ {n} f → A.inv (toℕFGℕ≃ℕ {n} f) ≡ toℕFGℕ≃ℕ (inv f) 
-- -- -- -- -- toℕFGℕ≃ℕinv = RelimProp.f w
-- -- -- -- --  where
-- -- -- -- --   w : RelimProp _
-- -- -- -- --   RelimProp.isPropA w _ = A.trunc _ _
-- -- -- -- --   RelimProp.εA w = refl
-- -- -- -- --   RelimProp.∷A w (k , _) {xs} X =
-- -- -- -- --      cong (A._· A.η k) X ∙ toℕFGℕ≃ℕ· (inv xs) _

-- -- -- -- -- GroupHomToℕFGℕ≃ℕ : ∀ n → IsGroupHom (snd (BraidG n))
-- -- -- -- --                               toℕFGℕ≃ℕ (snd (A.FinGenℕ≃ℕ))
-- -- -- -- -- IsGroupHom.pres· (GroupHomToℕFGℕ≃ℕ n) x y = sym (toℕFGℕ≃ℕ· {n} x y)
-- -- -- -- -- IsGroupHom.pres1 (GroupHomToℕFGℕ≃ℕ n) = refl
-- -- -- -- -- IsGroupHom.presinv (GroupHomToℕFGℕ≃ℕ n) = sym ∘ toℕFGℕ≃ℕinv {n}



-- -- -- -- -- -- injectiveToℕFGℕ≃ℕ : ∀ n → ∀ x y →
-- -- -- -- -- --      toℕFGℕ≃ℕ {n = n} x ≡ toℕFGℕ≃ℕ {n = n} y
-- -- -- -- -- --      → x ≡ y
-- -- -- -- -- -- injectiveToℕFGℕ≃ℕ n = RelimProp.f w
-- -- -- -- -- --  where
-- -- -- -- -- --    w : RelimProp _
-- -- -- -- -- --    RelimProp.isPropA w x = isPropΠ2 λ _ _ → trunc _ _
-- -- -- -- -- --    RelimProp.εA w x = {!!}
-- -- -- -- -- --    RelimProp.∷A w x {xs} X p =
-- -- -- -- -- --     let z = {!X ?!}
-- -- -- -- -- --     in {!!}


-- -- -- -- -- -- injectiveToℕFGℕ≃ℕ : ∀ n → isInjective (_ , GroupHomToℕFGℕ≃ℕ n)
-- -- -- -- -- -- injectiveToℕFGℕ≃ℕ n = RelimProp.f w
-- -- -- -- -- --  where
-- -- -- -- -- --    w : RelimProp _
-- -- -- -- -- --    RelimProp.isPropA w x = isPropΠ λ _ → trunc _ _
-- -- -- -- -- --    RelimProp.εA w = λ _ → refl
-- -- -- -- -- --    RelimProp.∷A w x {xs} X p =
-- -- -- -- -- --     let z = {!X ?!}
-- -- -- -- -- --     in {!!}
    
-- -- -- -- -- to≃ : ∀ {n} → Braid n → Iso ℕ ℕ
-- -- -- -- -- to≃ {n} = A.to≃ ∘ toℕFGℕ≃ℕ

-- -- -- -- -- to≃CF : ∀ {n} → (x : Braid n) →  ⟨ A.constFromIsoH (to≃ x) n ⟩
-- -- -- -- -- to≃CF {n} = RelimProp.f w
-- -- -- -- --  where
-- -- -- -- --    w : RelimProp _
-- -- -- -- --    RelimProp.isPropA w x = snd (A.constFromIsoH (to≃ x) n)
-- -- -- -- --    RelimProp.εA w _ _ = refl
-- -- -- -- --    RelimProp.∷A w (k , k<) {xs} X m n≤m =
-- -- -- -- --      let z = A.isConstFrom-adjTransposition k m
-- -- -- -- --               (≤-trans {suc (suc k)} {n} {m} k< n≤m)
-- -- -- -- --      in X _ (subst (n ≤_) (sym z) n≤m) ∙ z

-- -- -- -- -- to≃' : ∀ {n} → Braid n → A.IsoCF n
-- -- -- -- -- fst (to≃' x) = to≃ x
-- -- -- -- -- snd (to≃' x) = to≃CF x

-- -- -- -- -- -- rotFG : ∀ {n} → Fin n → Braid (suc n)
-- -- -- -- -- -- rotFG (zero , _) = ε
-- -- -- -- -- -- rotFG {suc n} (suc k , sk<) =
-- -- -- -- -- --  (zero , _) ∷ sucBraid (rotFG (k , sk<))

-- -- -- -- -- rotFG : ∀ {n} → Fin n → Braid n
-- -- -- -- -- rotFG (zero , _) = ε
-- -- -- -- -- rotFG {suc n} (suc k , sk<) =
-- -- -- -- --   (zero , ≤-trans {1} {suc k} {n} _ sk<) ∷ sucBraid (rotFG (k , sk<))
  


-- -- -- -- -- from≃ : ∀ {n} → ∀ e → ⟨ A.constFromIsoH e n ⟩ → Braid n 
-- -- -- -- -- from≃ {zero} _ _ = ε
-- -- -- -- -- from≃ {suc n} e X = 
-- -- -- -- --   let (k , (x' , X')) = Iso.fun (A.unwindIsoIsoCF n)
-- -- -- -- --           ( e , X)
-- -- -- -- --   in sucBraid (from≃ {n} x' X') · rotFG {suc n} k

-- -- -- -- -- toℕFGℕ≃ℕ∘sucBraid≡sucFGℕ≃ℕ∘toℕFGℕ≃ℕ : ∀ {n} x → 
-- -- -- -- --    toℕFGℕ≃ℕ (sucBraid {n} x) ≡ A.sucFGℕ≃ℕ (toℕFGℕ≃ℕ x)
-- -- -- -- -- toℕFGℕ≃ℕ∘sucBraid≡sucFGℕ≃ℕ∘toℕFGℕ≃ℕ = RelimProp.f w
-- -- -- -- --  where
-- -- -- -- --    w : RelimProp _
-- -- -- -- --    RelimProp.isPropA w _ = A.trunc _ _
-- -- -- -- --    RelimProp.εA w = refl
-- -- -- -- --    RelimProp.∷A w (k , _) = cong (suc k A.∷_)


-- -- -- -- -- rotFG'CohA : ∀ {n} k → toℕFGℕ≃ℕ (rotFG {n} k) ≡ A.rotFG (fst k)
-- -- -- -- -- rotFG'CohA (zero , k<) = refl
-- -- -- -- -- rotFG'CohA {suc (suc n)} (suc k , k<) = 
-- -- -- -- --   cong′ (zero A.∷_)
-- -- -- -- --     (toℕFGℕ≃ℕ∘sucBraid≡sucFGℕ≃ℕ∘toℕFGℕ≃ℕ (rotFG (k , k<))
-- -- -- -- --       ∙ cong′ A.sucFGℕ≃ℕ (rotFG'CohA (k , k<)))

-- -- -- -- -- fromCohA : ∀ {n} → ∀ e → (p : ⟨ A.constFromIsoH e n ⟩)
-- -- -- -- --              → toℕFGℕ≃ℕ (from≃ {n} e p) ≡
-- -- -- -- --                  A.from≃ e n p 
-- -- -- -- -- fromCohA {zero} e p = refl
-- -- -- -- -- fromCohA {suc n} e X =
-- -- -- -- --   let (k , (x' , X')) = Iso.fun (A.unwindIsoIsoCF n) ( e , X)
-- -- -- -- --   in sym (toℕFGℕ≃ℕ· {n = suc n}
-- -- -- -- --         ((sucBraid
-- -- -- -- --         (from≃ (fst (snd (Iso.fun (A.unwindIsoIsoCF n) (e , X))))
-- -- -- -- --          (snd (snd (Iso.fun (A.unwindIsoIsoCF n) (e , X)))))))
-- -- -- -- --          ((rotFG (fst (Iso.fun (A.unwindIsoIsoCF n) (e , X)))))) 
-- -- -- -- --         ∙ cong₂' A._·_
-- -- -- -- --       (toℕFGℕ≃ℕ∘sucBraid≡sucFGℕ≃ℕ∘toℕFGℕ≃ℕ {n = n} (from≃ {n} x' X')
-- -- -- -- --                 ∙ cong′ A.sucFGℕ≃ℕ (fromCohA {n = n} x' X'))
-- -- -- -- --       (rotFG'CohA {suc n} k)


-- -- -- -- -- from≃' : ∀ {n} → A.IsoCF n → Braid n
-- -- -- -- -- from≃' = uncurry from≃


-- -- -- -- -- from≃IdIso : ∀ {n} p → from≃ {n} idIso p ≡ ε
-- -- -- -- -- from≃IdIso {zero} _ = refl
-- -- -- -- -- from≃IdIso {suc n} p =
-- -- -- -- --   cong′ (_· ε) (cong′ sucBraid
-- -- -- -- --     (cong from≃' (Σ≡Prop (λ x → snd (A.constFromIsoH x n)) A.unwindIsoIdIso)
-- -- -- -- --     ∙ from≃IdIso {n} (A.unwindConstFromIso n idIso p)))


-- -- -- -- -- isFGliK0 : ∀ k n m p p' → ¬ n ≡ m →
-- -- -- -- --               Path (Braid (suc (suc k)))
-- -- -- -- --               ((sucBraid
-- -- -- -- --                 (rotFG
-- -- -- -- --                   ((predℕ (Iso.inv (A.rotIso' (fst n)) (fst m))
-- -- -- -- --                      , p)))) · rotFG n)
-- -- -- -- --               ((zero , _) ∷ ((sucBraid (rotFG (
-- -- -- -- --                 (predℕ (Iso.inv (A.rotIso' (fst m)) (fst n)) , p')))
-- -- -- -- --                   · rotFG m)))
-- -- -- -- -- isFGliK0 k n m p p' ¬p = 
-- -- -- -- --   A.rotRotElim
-- -- -- -- --   (λ n m n' m' → ∀ k → ∀ {p0} {p1} {p2} {p3} →
-- -- -- -- --      (sucBraid {n = suc k} (rotFG (m' , p0))) · rotFG (n , p1)
-- -- -- -- --               ≡ (zero , _) ∷ ((sucBraid (rotFG (n' , p2)) · rotFG (m , p3))))
-- -- -- -- --   caseA
-- -- -- -- --   (λ e0 e1 x k → sym (invo _ _) ∙ sym (cong′ ((zero , _) ∷_) (caseA e1 e0 x k)))
-- -- -- -- --   (fst n) (fst m) (¬p ∘ ≡Fin {n = suc (suc k)}) k
-- -- -- -- --  where
-- -- -- -- --    caseA : (e0 e1 : ℕ) →
-- -- -- -- --              e1 < suc e0 → ∀ k →
-- -- -- -- --              {p0 : e1 < suc k} {p1 : suc e0 < suc (suc k)} {p2 : e0 < suc k}
-- -- -- -- --              {p3 : e1 < suc (suc k)} →
-- -- -- -- --              (sucBraid (rotFG (e1 , p0)) · rotFG (suc e0 , p1)) ≡
-- -- -- -- --              (zero , tt) ∷ (sucBraid (rotFG (e0 , p2)) · rotFG (e1 , p3))
-- -- -- -- --    caseA e0 zero x k {p1 = p1} {p2 = p2} = 
-- -- -- -- --      cong′ (λ y → (zero , tt) ∷ sucBraid (rotFG (e0 , y)))
-- -- -- -- --         (isProp≤ {m = e0} {n = k} p1 p2)
-- -- -- -- --       ∙ sym (idr ((zero , _) ∷ sucBraid (rotFG (e0 , p2))))
-- -- -- -- --    caseA (suc e0) (suc e1) x (suc k) {p0} {p1} {p2} {p3} = 
-- -- -- -- --      let z = caseA e0 e1 x k {p0} {p1} {p2} {p3}
         
-- -- -- -- --      in cong′ ((1 , tt) ∷_)
-- -- -- -- --            (assoc· ((sucBraid (sucBraid (rotFG (e1 , _))))) ((zero , _) ∷ ε) _
-- -- -- -- --              ∙ cong′ (_· (sucBraid ((zero , _) ∷ sucBraid (rotFG (e0 , _)))))
-- -- -- -- --              (sym (sucBraidComm (rotFG (e1 , _))))
-- -- -- -- --             ∙ (sym (assoc· ((0 , _) ∷ ε) (sucBraid (sucBraid (rotFG (e1 , _)))) _))
-- -- -- -- --             ∙ cong′ ((0 , _) ∷_)
-- -- -- -- --                  (sym (sucBraid· (sucBraid (rotFG (e1 , _)))
-- -- -- -- --                      (((zero , _) ∷ sucBraid (rotFG (e0 , _)))))
-- -- -- -- --             ∙  cong sucBraid z))
-- -- -- -- --          ∙ (λ i → braid zero _
-- -- -- -- --              (sucBraid· (sucBraid (rotFG (e0 , p2)))
-- -- -- -- --                        (rotFG (e1 , p3)) i) (~ i)) 
-- -- -- -- --          ∙ cong′ (λ x → (0 , _) ∷ (1 , _) ∷ x)
-- -- -- -- --              ( (assoc· ((zero , tt) ∷ ε)
-- -- -- -- --                        (sucBraid (sucBraid (rotFG (e0 , _))))
-- -- -- -- --                        (sucBraid (rotFG (e1 , p3)))
-- -- -- -- --                  ∙ cong (_· _) (sucBraidComm (rotFG (e0 , _))))
-- -- -- -- --               ∙ sym (assoc·
-- -- -- -- --                  (sucBraid (sucBraid (rotFG (e0 , _))))
-- -- -- -- --                  ((zero , tt) ∷ ε)
-- -- -- -- --                  (sucBraid (rotFG (e1 , p3)))))


-- -- -- -- -- piiR : ∀ n → RelimProp
-- -- -- -- --       (λ z → from≃' (to≃' {n} z) ≡ z)
-- -- -- -- -- piiR =
-- -- -- -- --  (ℕ.elim {A = λ n → RelimProp (λ z → from≃' (to≃' {n} z) ≡ z)}
-- -- -- -- --    w0 (λ n → wN n ∘ RelimProp.f) )
-- -- -- -- --  where
-- -- -- -- --   w0 : RelimProp (λ z → from≃' (to≃' z) ≡ z)
-- -- -- -- --   RelimProp.isPropA w0 _ = trunc _ _
-- -- -- -- --   RelimProp.εA w0 = refl
-- -- -- -- --   RelimProp.∷A w0 ()

-- -- -- -- --   h : ∀ n e 𝑘 𝑘<sn p →
-- -- -- -- --        from≃' {suc n}
-- -- -- -- --           (compIso (A.adjTransposition≃ 𝑘) (fst e ) , p)
-- -- -- -- --          ≡ (𝑘 , 𝑘<sn) ∷ from≃' {suc n} e
-- -- -- -- --   h (suc n) (e , P) zero 𝑘<sn p = 
-- -- -- -- --    let ee1 = Iso.fun e 1
-- -- -- -- --        ee0 = Iso.fun e 0

-- -- -- -- --        ee0< = _
-- -- -- -- --        e0 = (Iso.inv (A.rotIso' (ee1)) (ee0)) 
-- -- -- -- --        e1 = _
-- -- -- -- --        e0' = ee0
-- -- -- -- --        e1' = Iso.inv (A.rotIso' ee0) ee1
-- -- -- -- --        pe1'< = _

-- -- -- -- --        eL = from≃ _ _
-- -- -- -- --        eR = from≃ _ _

-- -- -- -- --    in cong′ (_· rotFG e1) (sucBraid· (sucBraid eL) (rotFG _))
-- -- -- -- --     ∙ sym (assoc· (sucBraid (sucBraid eL)) _ _)
-- -- -- -- --     ∙ cong₂' _·_ (cong′ (sucBraid ∘' sucBraid ∘' from≃')
-- -- -- -- --            (Σ≡Prop (λ x →  snd (A.constFromIsoH x n))
-- -- -- -- --               (sym (A.unwindBraidHeadCompSwap0and1FST e))))
-- -- -- -- --         (isFGliK0 n _ _ _ _ (snotz ∘ isoFunInjective e _ _ ∘ cong′ fst))
-- -- -- -- --     ∙ assoc· (sucBraid (sucBraid eR)) _
-- -- -- -- --        (sucBraid (rotFG (predℕ e1' , pe1'<)) · _)      
-- -- -- -- --     ∙ cong′ (_· ((sucBraid (rotFG (predℕ e1' , pe1'<)) · rotFG (e0' , ee0<) )))
-- -- -- -- --         (sym (sucBraidComm eR))      
-- -- -- -- --     ∙ sym (assoc· (_ ∷ ε) (sucBraid (sucBraid eR)) _)      
-- -- -- -- --     ∙ cong′ (_ ∷_) (assoc· (sucBraid (sucBraid eR))
-- -- -- -- --         (sucBraid (rotFG (predℕ e1' , pe1'<))) _
-- -- -- -- --     ∙ cong′ (_· rotFG (e0' , ee0<)) (sym (sucBraid· (sucBraid eR) _)))


-- -- -- -- --   h (suc n) (e , P) 𝑘'@(suc 𝑘) 𝑘<sn p =
-- -- -- -- --    let (k , (x' , X')) = Iso.fun (A.unwindIsoIsoCF (suc n)) (e , P)
-- -- -- -- --        ((k* , k<*) , (x'* , X'*)) = Iso.fun (A.unwindIsoIsoCF (suc n))
-- -- -- -- --              ((compIso (A.adjTransposition≃ (suc 𝑘)) e) , p)
-- -- -- -- --        X* = A.isConstFrom∘ (Iso.fun x') (suc n) _ (suc (suc 𝑘))
-- -- -- -- --                X' (A.isConstFrom-adjTransposition 𝑘)
-- -- -- -- --        pp = subst 
-- -- -- -- --             (fst ∘ (A.constFromIsoH (compIso (A.adjTransposition≃ 𝑘) (x' ))))
-- -- -- -- --                (right-≤-→max≡ (suc n) (suc (suc 𝑘)) 𝑘<sn) X*
-- -- -- -- --    in cong₂ (_·_) (cong′ sucBraid (
-- -- -- -- --        cong′ from≃' (Σ≡Prop (λ x → snd (A.constFromIsoH x (suc n)))
-- -- -- -- --        {u = _ , X'*} {v = _ , pp} (Iso≡Set-fun isSetℕ isSetℕ _ _ (λ _ → refl)))
-- -- -- -- --          ∙ h n (x' , X') 𝑘 𝑘<sn pp)) (cong rotFG (≡Fin {n = suc (suc n)} refl))
-- -- -- -- --       ∙ sym (assoc· (η (𝑘' , 𝑘<sn)) (sucBraid (from≃ x' X')) (rotFG k))


-- -- -- -- --   wN : (n : ℕ) →
-- -- -- -- --          (∀ z → from≃' (to≃' {n} z) ≡ z) →
-- -- -- -- --          RelimProp (λ z → from≃' (to≃' {suc n} z) ≡ z)
-- -- -- -- --   RelimProp.isPropA (wN n _) _ = trunc _ _
-- -- -- -- --   RelimProp.εA (wN n _) = from≃IdIso (to≃CF {suc n} ε)
-- -- -- -- --   RelimProp.∷A (wN n X) k {xs} P =
-- -- -- -- --    uncurry (h n (to≃' xs)) k (to≃CF (k ∷ xs)) 
-- -- -- -- --      ∙ cong′ (k ∷_) P

-- -- -- -- -- BraidIsoIso : ∀ {n} → Iso (Braid n) (A.IsoCF n) 
-- -- -- -- -- Iso.fun (BraidIsoIso) = to≃'
-- -- -- -- -- Iso.inv (BraidIsoIso) = from≃'
-- -- -- -- -- Iso.rightInv (BraidIsoIso {n}) e =
-- -- -- -- --   let zz = A.getLeastB (Iso.fun (fst e)) (n , snd e)
-- -- -- -- --       z = A.retract-to≃'-from≃' (fst e , zz)
-- -- -- -- --   in Σ≡Prop (λ x → snd (A.constFromIsoH x n) ) 
-- -- -- -- --        (cong′ A.to≃ (fromCohA {n = n} (fst e) (snd e) ∙
-- -- -- -- --               A.from≃lem (fst e) (fst e) n (fst zz) _ _ refl)
-- -- -- -- --               ∙ cong′ fst z)
-- -- -- -- -- Iso.leftInv (BraidIsoIso) = RelimProp.f (piiR _)

-- -- -- -- -- BraidGIsoIso : ∀ n → GroupIso (BraidG n)
-- -- -- -- --                     (SetIso-Group _ (isSetFin {n = n})) 
-- -- -- -- -- fst (BraidGIsoIso n) = compIso BraidIsoIso (A.IsoIsoCFIsoFin n)
-- -- -- -- -- IsGroupHom.pres· (snd (BraidGIsoIso n)) =
-- -- -- -- --   λ x y →
-- -- -- -- --     let p =  cong A.to≃ (sym (toℕFGℕ≃ℕ· x y))
-- -- -- -- --             ∙ (A.to≃· (toℕFGℕ≃ℕ x) (toℕFGℕ≃ℕ y))
-- -- -- -- --     in Iso≡Set-fun (isSetFin {n = n}) (isSetFin {n = n}) _ _
-- -- -- -- --          λ k → ≡Fin {n = n} (funExt⁻ (cong (Iso.fun) p) (fst k))
    
-- -- -- -- -- IsGroupHom.pres1 (snd (BraidGIsoIso n)) =
-- -- -- -- --   Iso≡Set-fun (isSetFin {n = n}) (isSetFin {n = n}) _ _
-- -- -- -- --     λ x → ≡Fin {n = n} refl
-- -- -- -- -- IsGroupHom.presinv (snd (BraidGIsoIso n)) x =
-- -- -- -- --  let z = A.to≃Inv (toℕFGℕ≃ℕ x) ∙ cong A.to≃ (toℕFGℕ≃ℕinv x)
-- -- -- -- --  in Iso≡Set-fun (isSetFin {n = n}) (isSetFin {n = n}) _ _
-- -- -- -- --        λ k → ≡Fin {n = n}
-- -- -- -- --          (sym (funExt⁻ (cong Iso.fun z) (fst k)))
 

       
-- -- -- -- -- -- permuteF' : ∀ n → Braid n → Fin n → Fin n 
-- -- -- -- -- -- permuteF' n = Rrec.f {n = n} (w n)
-- -- -- -- -- --   where
-- -- -- -- -- --    open Rrec
 
-- -- -- -- -- --    w : ∀ n → Rrec {n = n} (Fin n → Fin n)
-- -- -- -- -- --    isSetA (w n) = isSet→ (isSetFin {n = n})
-- -- -- -- -- --    εA (w n) = idfun _
-- -- -- -- -- --    ∷A (w n) k X = adjT n k ∘ X 
-- -- -- -- -- --    invoA (w n) k x = cong (_∘ x) (funExt (isInvolution-adjT n k))
-- -- -- -- -- --    braidA (w n) k k< x =
-- -- -- -- -- --      funExt λ x' → ≡Fin {n = n}
-- -- -- -- -- --         (funExt⁻ (A.adjTranspositionBraid k) (fst (x x')))
-- -- -- -- -- --    commA (w n) (k , _) (l , _) q x = 
-- -- -- -- -- --          funExt λ x' → ≡Fin {n = n}
-- -- -- -- -- --         (funExt⁻ (sym (A.adjTranspositionComm k l q)) (fst (x x')))

-- -- -- -- -- permuteIso : ∀ n → Braid n → Iso (Fin n) (Fin n) 
-- -- -- -- -- permuteIso n = Rrec.f {n = n} (w n)
-- -- -- -- --   where
-- -- -- -- --    open Rrec
 
-- -- -- -- --    w : ∀ n → Rrec {n = n} (Iso (Fin n) (Fin n))
-- -- -- -- --    isSetA (w n) = isSet-SetsIso (isSetFin {n = n})
-- -- -- -- --                    (isSetFin {n = n})
-- -- -- -- --    εA (w n) = idIso
-- -- -- -- --    ∷A (w n) k = compIso (adjTIso' {n = n} k) --X ∘ adjT n k 
-- -- -- -- --    invoA (w n) k x = 
-- -- -- -- --     Iso≡Set (isSetFin {n = n}) (isSetFin {n = n})
-- -- -- -- --      _ _ (cong (Iso.fun x) ∘ (isInvolution-adjT n k))
-- -- -- -- --          (isInvolution-adjT n k ∘ Iso.inv x)

-- -- -- -- --    braidA (w n) k k< x = 
-- -- -- -- --     Iso≡Set (isSetFin {n = n})
-- -- -- -- --        (isSetFin {n = n})
-- -- -- -- --      _ _ (cong (Iso.fun x) ∘ funExt⁻ (adjT-braid n k k<))
-- -- -- -- --           (funExt⁻ (adjT-braid n k k<) ∘ (Iso.inv x) )
-- -- -- -- --    commA (w n) k l q x =
-- -- -- -- --     Iso≡Set (isSetFin {n = n})
-- -- -- -- --        (isSetFin {n = n})
-- -- -- -- --      _ _ (cong (Iso.fun x) ∘ (adjT-comm n k l q))
-- -- -- -- --          (sym ∘ adjT-comm n k l q ∘ (Iso.inv x))
-- -- -- -- -- permuteF : ∀ n → Braid n → Fin n → Fin n 
-- -- -- -- -- permuteF n = Iso.fun ∘ permuteIso n

-- -- -- -- -- permuteF' : ∀ n → Braid n → Fin n → Fin n 
-- -- -- -- -- permuteF' n = Iso.inv ∘ permuteIso n

-- -- -- -- -- -- Rrec.f {n = n} (w n)
-- -- -- -- -- --   where
-- -- -- -- -- --    open Rrec
 
-- -- -- -- -- --    w : ∀ n → Rrec {n = n} (Fin n → Fin n)
-- -- -- -- -- --    isSetA (w n) = isSet→ (isSetFin {n = n})
-- -- -- -- -- --    εA (w n) = idfun _
-- -- -- -- -- --    ∷A (w n) k X = X ∘ adjT n k 
-- -- -- -- -- --    invoA (w n) k x = cong (x ∘_) (funExt (isInvolution-adjT n k))
-- -- -- -- -- --    braidA (w n) k k< x = 
-- -- -- -- -- --      funExt λ x' → 
-- -- -- -- -- --        (cong′ x
-- -- -- -- -- --           (≡Fin {n = n} (
-- -- -- -- -- --             funExt⁻ (A.adjTranspositionBraid k) _) ) )
-- -- -- -- -- --    commA (w n) (k , _) (l , _) q x =
-- -- -- -- -- --      funExt λ x' → 
-- -- -- -- -- --        (cong′ x
-- -- -- -- -- --           (≡Fin {n = n} (
-- -- -- -- -- --             funExt⁻ (A.adjTranspositionComm k l q) _) ) )



-- -- -- -- -- permuteIso· : ∀ n → (g h : Braid n) →
-- -- -- -- --                    compIso (permuteIso n g) (permuteIso n h)
-- -- -- -- --                       ≡ (permuteIso n (g · h))
-- -- -- -- -- permuteIso· n = RelimProp.f w
-- -- -- -- --  where
-- -- -- -- --   open RelimProp

-- -- -- -- --   w : RelimProp _
-- -- -- -- --   isPropA w _ = isPropΠ λ _ → isSet-SetsIso (isSetFin {n = n})
-- -- -- -- --                    (isSetFin {n = n}) _ _
-- -- -- -- --   εA w _ = compIsoIdL _
-- -- -- -- --   ∷A w k {xs} X h = Iso≡Set-fun (isSetFin {n = n})
-- -- -- -- --        (isSetFin {n = n})
-- -- -- -- --      _ _ (funExt⁻ (cong Iso.fun (X h)) ∘ _)



-- -- -- -- -- module List-perm {A : Type ℓ} where

-- -- -- -- --  module _ {ℓ'} {B : Type ℓ'} (e : B ≃ B) (f₀ f₁ : B → A) where

-- -- -- -- --   substDom :
-- -- -- -- --     (PathP (λ i → ua e (~ i) → A)
-- -- -- -- --       f₀ f₁)
-- -- -- -- --      ≃
-- -- -- -- --     (f₀ ∘ fst e ≡ f₁)
-- -- -- -- --   substDom =
-- -- -- -- --      PathP≃Path _ _ _ ∙ₑ
-- -- -- -- --       compPathlEquiv (sym zz)

-- -- -- -- --    where
-- -- -- -- --     zz : transport (λ i → (ua e (~ i)) → A) f₀ ≡ f₀ ∘ fst e
-- -- -- -- --     zz = fromPathP (funTypeTransp' (idfun _) A (sym (ua e)) f₀)
-- -- -- -- --           ∙ cong (f₀ ∘_) (funExt (uaβ e))
          
-- -- -- -- --  List→×^ : (l : List A) → A ×^ (length l)
-- -- -- -- --  List→×^ [] = tt*
-- -- -- -- --  List→×^ (x ∷ l) = x , List→×^ l 

-- -- -- -- --  ×^→List : ∀ n → A ×^ n → List A
-- -- -- -- --  ×^→List zero x = []
-- -- -- -- --  ×^→List (suc n) x = fst x ∷ ×^→List n (snd x)

-- -- -- -- --  sec-IsoList-×^-fst : ∀ k v → length (×^→List k v) ≡ k
-- -- -- -- --  sec-IsoList-×^-fst zero v = refl
-- -- -- -- --  sec-IsoList-×^-fst (suc k) v = cong suc (sec-IsoList-×^-fst k (snd v))

-- -- -- -- --  sec-IsoList-×^-snd : ∀ k → (v : A ×^ k) →
-- -- -- -- --      PathP (λ i → A ×^ (sec-IsoList-×^-fst k v i))
-- -- -- -- --        (List→×^ (×^→List k v))
-- -- -- -- --        v
-- -- -- -- --  sec-IsoList-×^-snd zero v = refl
-- -- -- -- --  sec-IsoList-×^-snd (suc k) v =
-- -- -- -- --    congP (λ _ → (fst v) ,_) (sec-IsoList-×^-snd k (snd v))

-- -- -- -- --  IsoList-×^ : Iso (List A) (Σ _ (A ×^_))
-- -- -- -- --  Iso.fun IsoList-×^ = (_ ,_) ∘ List→×^
-- -- -- -- --  Iso.inv IsoList-×^ (k , v) = ×^→List k v
-- -- -- -- --  fst (Iso.rightInv IsoList-×^ (k , v) i) = sec-IsoList-×^-fst k v i
-- -- -- -- --  snd (Iso.rightInv IsoList-×^ (k , v) i) = sec-IsoList-×^-snd k v i
-- -- -- -- --  Iso.leftInv IsoList-×^ = ind' refl λ _ → cong (_ ∷_)


-- -- -- -- --  -- permuteList' : ∀ {n} → (l : List A) → (Fin n → Fin (length l)) → List A
-- -- -- -- --  -- permuteList' {n} l x =
-- -- -- -- --  --    ×^→List n (tabulate (lookup (List→×^ l) ∘' x))


-- -- -- -- --  -- permuteList : (l : List A) →
-- -- -- -- --  --    Braid (length l) → List A
-- -- -- -- --  -- permuteList l = permuteList' {n = (length l)} l ∘ permuteF (length l)

-- -- -- -- --  ListOfLen : ℕ → Type ℓ
-- -- -- -- --  ListOfLen n = Σ (List A) λ l → length l ≡ n

-- -- -- -- --  -- mkOfLen : List A → ListOfLen n
-- -- -- -- --  -- mkOfLen = ?
 
-- -- -- -- --  IsoListOfLen×^ : ∀ n → Iso (ListOfLen n) (A ×^ n)
-- -- -- -- --  IsoListOfLen×^ = w
-- -- -- -- --   where

-- -- -- -- --   w→ : ∀ n → (ListOfLen n) → (A ×^ n)
-- -- -- -- --   w→ zero x = tt*
-- -- -- -- --   w→ (suc n) ([] , snd₁) = ⊥.rec (znots snd₁) 
-- -- -- -- --   w→ (suc n) (x ∷ fst₁ , snd₁) = x , w→ n (fst₁ , cong predℕ snd₁)

-- -- -- -- --   w← : ∀ n → (A ×^ n) → (ListOfLen n)
-- -- -- -- --   w← zero x = [] , refl
-- -- -- -- --   w← (suc n) x =
-- -- -- -- --    let (l , p) = w← n (snd x)
-- -- -- -- --    in fst x ∷ l , cong suc p

-- -- -- -- --   w-ri : ∀ n → section (w→ n) (w← n)
-- -- -- -- --   w-ri zero b = refl
-- -- -- -- --   w-ri (suc n) b = cong (fst b ,_) (w-ri n (snd b))

-- -- -- -- --   w-li : ∀ n → retract (w→ n) (w← n)
-- -- -- -- --   w-li zero ([] , snd₁) = Σ≡Prop (λ _ → isSetℕ _ _) refl
-- -- -- -- --   w-li zero (x ∷ fst₁ , snd₁) = ⊥.rec (snotz snd₁) 
-- -- -- -- --   w-li (suc n) ([] , snd₁) = ⊥.rec (znots snd₁)
-- -- -- -- --   w-li (suc n) (x ∷ fst₁ , snd₁) =
-- -- -- -- --    let z = w-li n (fst₁ , cong predℕ snd₁)
-- -- -- -- --    in Σ≡Prop (λ _ → isSetℕ _ _) (cong (x ∷_) (cong fst z)) 
 
-- -- -- -- --   w : ∀ n → Iso _ _
-- -- -- -- --   Iso.fun (w n) = w→ n
-- -- -- -- --   Iso.inv (w n) = w← n
-- -- -- -- --   Iso.rightInv (w n) = w-ri n
-- -- -- -- --   Iso.leftInv (w n) = w-li n


-- -- -- -- --  permuteList : (l : List A) →
-- -- -- -- --     Braid (length l) → List A
-- -- -- -- --  permuteList l p =
-- -- -- -- --    fst (Iso.inv (IsoListOfLen×^ (length l))
-- -- -- -- --          (tabulate (lookup (Iso.fun (IsoListOfLen×^ (length l)) (l , refl))
-- -- -- -- --               ∘' permuteF' _ p)))
-- -- -- -- --    -- permuteList' {n = (length l)} l ∘ permuteF (length l)


-- -- -- -- --  listOfLenBraid : ∀ n → Braid n → (ListOfLen n) ≃ (ListOfLen n)
-- -- -- -- --  listOfLenBraid n p =
-- -- -- -- --    --  compIso {!!}
-- -- -- -- --    -- (compIso {!preCompIso!}
-- -- -- -- --    --          {!!})
-- -- -- -- --     isoToEquiv (compIso (IsoListOfLen×^ n) (Iso-×^-F→ n))
-- -- -- -- --      ∙ₑ preCompEquiv {C = A} (isoToEquiv (permuteIso n p)) ∙ₑ
-- -- -- -- --      isoToEquiv (invIso (compIso (IsoListOfLen×^ n) (Iso-×^-F→ n)))

-- -- -- -- --  permuteList-len : (x : List A) →
-- -- -- -- --      (p : Braid (length x)) → length (permuteList x p) ≡ length x
-- -- -- -- --  permuteList-len l p =
-- -- -- -- --    snd (Iso.inv (IsoListOfLen×^ (length l))
-- -- -- -- --          (tabulate (lookup (Iso.fun (IsoListOfLen×^ (length l)) (l , refl))
-- -- -- -- --               ∘' permuteF' _ p)))

-- -- -- -- --  lookupList : (x : List A) → Fin (length x) → A
-- -- -- -- --  lookupList x = Iso.fun (compIso (IsoListOfLen×^ (length x)) (Iso-×^-F→ _)) (x , refl)
   
 
-- -- -- -- --  permuteList-lemma : (x y : List A) → (l= : length x ≡ length y) →
-- -- -- -- --      (p : Braid (length x)) →
-- -- -- -- --     _ -- PathP _ _ _
-- -- -- -- --        ≃
-- -- -- -- --    (permuteList x p ≡ y)
-- -- -- -- --  permuteList-lemma x y l= p =
-- -- -- -- --    --    PathP (λ i → ua (isoToEquiv (invIso (permuteIso _ p))) (~ i) → A)
-- -- -- -- --    --      ((equivFun
-- -- -- -- --    --        (isoToEquiv
-- -- -- -- --    --         (compIso (IsoListOfLen×^ (length x)) (Iso-×^-F→ (length x))))
-- -- -- -- --    --        (x , refl)))
-- -- -- -- --    --      ((equivFun
-- -- -- -- --    --        (isoToEquiv
-- -- -- -- --    --         (compIso (IsoListOfLen×^ (length x)) (Iso-×^-F→ (length x))))
-- -- -- -- --    --        (y , (λ i → l= (~ i)))))
-- -- -- -- --    -- ≃⟨ substDom _ _ _ ⟩ 
-- -- -- -- --       Path (Fin (length x) → A)
-- -- -- -- --         ((equivFun
-- -- -- -- --           (isoToEquiv
-- -- -- -- --            (compIso (IsoListOfLen×^ (length x)) (Iso-×^-F→ (length x))))
-- -- -- -- --           (x , refl)) ∘' permuteF' _ p)
-- -- -- -- --         (equivFun
-- -- -- -- --           (isoToEquiv
-- -- -- -- --            (compIso (IsoListOfLen×^ (length x)) (Iso-×^-F→ (length x))))
-- -- -- -- --           (y , (λ i → l= (~ i))))
-- -- -- -- --    ≃⟨ compPathlEquiv (Iso.rightInv
-- -- -- -- --         ((compIso (IsoListOfLen×^ (length x)) (Iso-×^-F→ (length x))))
-- -- -- -- --          (lookup (Iso.fun (IsoListOfLen×^ (length x)) (x , refl)) ∘'
-- -- -- -- --            permuteF' (length x) p))
-- -- -- -- --        ∙ₑ invEquiv (congEquiv (
-- -- -- -- --        isoToEquiv (compIso (IsoListOfLen×^ (length x))
-- -- -- -- --                            (Iso-×^-F→ (length x))))) ⟩ 
-- -- -- -- --      Path (ListOfLen (length x)) (permuteList x p , permuteList-len x p)
-- -- -- -- --                                  (y , sym l=)
-- -- -- -- --    ≃⟨ isoToEquiv zz ⟩ 
-- -- -- -- --       Path (List A) _ _ ■
-- -- -- -- --    where
-- -- -- -- --     zz : Iso _ _
-- -- -- -- --     Iso.fun zz = cong fst
-- -- -- -- --     Iso.inv zz = Σ≡Prop λ _ → isSetℕ _ _
-- -- -- -- --     Iso.rightInv zz b = refl
-- -- -- -- --     Iso.leftInv zz a = invEq (congEquiv (invEquiv ΣPath≃PathΣ))
-- -- -- -- --                        (Σ≡Prop
-- -- -- -- --                          (λ _ → isProp→isPropPathP (λ _ → isSetℕ _ _) _ _) refl)
    

     

-- -- -- -- --  -- permuteList-lemma : (x y : List A) → (l= : length x ≡ length y) →
-- -- -- -- --  --     (p : Braid (length x)) →
-- -- -- -- --  --    PathP (λ i → ua (listOfLenBraid (length x) p) i)
-- -- -- -- --  --       (x , refl) (y , sym l=)
-- -- -- -- --  --       ≃
-- -- -- -- --  --   (permuteList x p ≡ y)



-- -- -- -- --  -- permuteList-lemma = {!!}



-- -- -- -- --  -- isBraidutedBy : ∀ n → Braid n → (x y : List A) → Type ℓ
-- -- -- -- --  -- isBraidutedBy = {!!}


 
