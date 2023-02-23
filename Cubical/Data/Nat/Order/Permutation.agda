{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.Permutation where

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
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive

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

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SequentialColimit as SC

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



    
infixr 5 _∷_

data Perm (n : ℕ) : Type where
  
  ε     : Perm n
  _∷_ : (Σ ℕ  λ k → (suc k < n)) → Perm n → Perm n

  invo : ∀ k → isInvolution {A = Perm n} (k ∷_ )
  braid : ∀ k k< → ∀ xs →  
            (k , <-weaken {n = n} k<) ∷ (suc k , k<)
              ∷ (k , <-weaken {n = n} k<) ∷ xs
         ≡ (suc k , k<) ∷ (k , <-weaken {n = n} k<) ∷ (suc k , k<) ∷ xs
  comm : ∀ k l → commT (fst k) (fst l) → ∀ xs →
      k ∷ l ∷ xs ≡ l ∷ k ∷ xs
  
  trunc : isSet (Perm n)

record Rrec {ℓ} {n : ℕ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    isSetA : isSet A
    εA : A
    ∷A : (Σ ℕ  λ k → (suc k < n)) → A → A
    invoA : ∀ k x → ∷A k (∷A k x) ≡ x
    braidA : ∀ k → ∀ k< → ∀ x →
         ∷A (k , <-weaken {n = n} k<) (∷A (suc k , k<)
          (∷A (k , <-weaken {n = n} k<) x))
       ≡ ∷A (suc k , k<) (∷A (k , <-weaken {n = n} k<) (∷A (suc k , k<) x))
    commA : ∀ k l → commT (fst k) (fst l) → ∀ x →
                     ∷A k (∷A l x) ≡ ∷A l (∷A k x)

  f : (Perm n) → A
  f ε = εA
  f (x ∷ x₁) = ∷A x (f x₁)
  f (invo k x i) = invoA k (f x) i
  f (braid k k< x i) = braidA k k< (f x) i
  f (comm k l x x₁ i) = commA k l x (f x₁) i
  f (trunc x y p q i i₁) =
    isSetA _ _ (cong f p) (cong f q) i i₁

record RelimProp {ℓ} {n : ℕ} (A : (Perm n) → Type ℓ) : Type ℓ where
  no-eta-equality
  field
    isPropA : ∀ x → isProp (A x)
    εA : A ε
    ∷A : ∀ k → ∀ {xs} → A xs → A (k ∷ xs)

  f : ∀ x → A x
  f ε = εA
  f (x ∷ x₁) = ∷A x (f x₁)
  f (invo k x i) =
      isProp→PathP (λ i → isPropA (invo k x i))
      (∷A k (∷A k (f x)))
      (f x) i
  f (braid k k< x i) =
     isProp→PathP (λ i → isPropA (braid k k< x i))
      (∷A (k , <-weaken {n = n} k<) (∷A (suc k , k<)
       (∷A (k , <-weaken {n = n}  k<) (f x))))
      (∷A (suc k , k<) (∷A (k , <-weaken {n = n}  k<) (∷A (suc k , k<) (f x)))) i
  f (comm k l x x₁ i) =
          isProp→PathP (λ i → isPropA (comm k l x x₁  i))
      (∷A k (∷A l (f x₁)))
      (∷A l (∷A k (f x₁))) i
  f (trunc x y p q i i₁) =
         isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (isPropA x))
         _ _ (cong f p) (cong f q) (trunc x y p q) i i₁


-- invoA-hlp : ∀ {ℓ} {n : ℕ} (A : (Perm n) → Type ℓ) →
--        (εA : A ε)
--        (∷A : ∀ k → ∀ {xs} → A xs → A (k ∷ xs))
--      → (∀ k {xs : Perm n} (x : A xs) →
--           PathP (λ i → {!!})
--              (∷A k {xs} x) {!!}
--           )
--      → (∀ k {x : Perm n} (x' : A x) → PathP (λ i → A (invo k x i))
--        (∷A k (∷A k x')) x')
    
-- invoA-hlp = {!!}

record Relim {ℓ} {n : ℕ} (A : (Perm n) → Type ℓ) : Type ℓ where
  no-eta-equality
  field
    isSetA : ∀ x → isSet (A x)
    εA : A ε
    ∷A : ∀ k → ∀ {xs} → A xs → A (k ∷ xs)
    invoA : ∀ k {x} x' → PathP (λ i → A (invo k x i))
      (∷A k (∷A k x'))
      x'
    braidA : ∀ k k< {x} x' → PathP (λ i → A (braid k k< x i))
               (∷A (k , <-weaken {n = n} k<) (∷A (suc k , k<)
          (∷A (k , <-weaken {n = n} k<) x')))
       (∷A (suc k , k<) (∷A (k , <-weaken {n = n} k<) (∷A (suc k , k<) x')))
    commA : ∀ k l z {x} x' → PathP (λ i → A (comm k l z x  i))
      (∷A k (∷A l x'))
      (∷A l (∷A k x'))

  f : ∀ x → A x
  f ε = εA
  f (x ∷ x₁) = ∷A x (f x₁)
  f (invo k x i) = invoA k (f x) i
  f (braid k k< x i) = braidA k k< (f x) i

  f (comm k l x x₁ i) = commA k l x (f x₁) i
  f (trunc x y p q i i₁) =
         isOfHLevel→isOfHLevelDep 2 (λ x → (isSetA x))
         _ _ (cong f p) (cong f q) (trunc x y p q) i i₁


-- record RelimSingl {ℓ} {n : ℕ} (A : (Perm n) → Type ℓ) : Type ℓ where
--   no-eta-equality
--   field
--     a₀ : ∀ {x} → A x
--     εA : A ε
--     εA≡ : a₀ ≡ εA
--     ∷A : ∀ k → ∀ {xs} → A xs → A (k ∷ xs)
--     ∷A≡ : ∀ k → ∀ {xs} → ∀ (x : A xs) → a₀ ≡ x → a₀ ≡ ∷A k x
--     invoA : ∀ k {x} x' → PathP (λ i → A (invo k x i))
--       (∷A k (∷A k x'))
--       x'    
    
--   --   braidA : ∀ k k< {x} x' → PathP (λ i → A (braid k k< x i))
--   --              (∷A (k , <-weaken {n = n} k<) (∷A (suc k , k<)
--   --         (∷A (k , <-weaken {n = n} k<) x')))
--   --      (∷A (suc k , k<) (∷A (k , <-weaken {n = n} k<) (∷A (suc k , k<) x')))
--   --   commA : ∀ k l z {x} x' → PathP (λ i → A (comm k l z x  i))
--   --     (∷A k (∷A l x'))
--   --     (∷A l (∷A k x'))

--   -- fR = 

--   r : Relim λ x → singl (a₀ {x})
--   Relim.isSetA r _ = isOfHLevelPlus 2 (isContrSingl _)
--   fst (Relim.εA r) = εA
--   snd (Relim.εA r) = εA≡ 
--   fst (Relim.∷A r k x) = ∷A k (fst x)
--   snd (Relim.∷A r k x) = ∷A≡ k (fst x) (snd x)
--   Relim.invoA r = {!!}
--   Relim.braidA r = {!!}
--   Relim.commA r = {!!}

_·_ : ∀ {n} → Perm n → Perm n → Perm n
ε · x₁ = x₁
(x ∷ x₂) · x₁ = x ∷ (x₂ · x₁)
invo k x i · x₁ = invo k (x · x₁) i
braid k k< x i · x₁ = braid k k< (x  · x₁) i
comm k l x x₂ i · x₁ = comm k l x (x₂  · x₁) i
trunc x x₂ x₃ y i i₁ · x₁ =
  trunc (x · x₁) (x₂ · x₁)
    (cong  (_· x₁) x₃) (cong  (_· x₁) y) i i₁

assoc· : ∀ {n} (x y z : Perm n) → x · (y · z) ≡ (x · y) · z
assoc· = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = isPropΠ2 λ _ _ → trunc _ _
   RelimProp.εA w _ _ = refl
   RelimProp.∷A w _ p _ _  = cong (_ ∷_) (p _ _)
   

idr : ∀ {n} → ∀ (x : Perm n) → (x · ε) ≡ x
idr = RelimProp.f
    (record { isPropA = λ _ → trunc _ _
            ; εA = refl
            ; ∷A = λ _ → cong (_ ∷_) })
   
η : ∀ {n} → (Σ ℕ  λ k → (suc k < n)) → Perm n
η = _∷ ε 


inv : ∀ {n} → Perm n → Perm n
inv = Rrec.f w

  where
    w : Rrec _
    Rrec.isSetA w = trunc 
    Rrec.εA w = ε
    Rrec.∷A w k = _· (η k) 
    Rrec.invoA w _ x = sym (assoc· x _ _) ∙ cong (x ·_) (invo _ ε) ∙ idr  x
    Rrec.braidA w k k< x =
       (cong (_· η _) (sym (assoc· x (η _) (η _))) ∙ sym (assoc· x (η _ · η _) (η _)))
        ∙∙ cong (x ·_) (sym (assoc· (η _) (η _) (η _))
               ∙∙ braid k k< ε ∙∙ 
                (assoc· (η _) (η _) (η _))) ∙∙
       ((assoc· x (η _ · η _) (η _)) ∙
        cong (_· η _) (assoc· x (η _) (η _)))
    Rrec.commA w k l z x = 
       sym (assoc· x _ _)
        ∙∙ cong (x ·_) (sym (comm k l z ε)) ∙∙
       (assoc· x _ _)

invr : ∀ {n} → (x : Perm n) → (x · inv x) ≡ ε
invr = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = trunc _ _ 
   RelimProp.εA w = refl
   RelimProp.∷A w k {xs} p =
     cong′ (k ∷_)
      (assoc· xs (inv xs) _ ∙ cong (_· η k) p) ∙ invo k ε 

invl : ∀ {n} → (x : Perm n) → (inv x · x) ≡ ε
invl = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = trunc _ _ 
   RelimProp.εA w = refl
   RelimProp.∷A w k {xs} p = sym (assoc· (inv xs) (η k) _) ∙ 
      (cong ((inv xs) ·_) (invo k xs)) ∙ p

PermG : ∀ n →  Group ℓ-zero
fst (PermG n) = Perm n
GroupStr.1g (snd (PermG n)) = ε
GroupStr._·_ (snd (PermG n)) = _·_
GroupStr.inv (snd (PermG n)) = inv
GroupStr.isGroup (snd (PermG n)) =
  makeIsGroup trunc assoc· idr (λ _ → refl) invr invl

sucPermR : ∀ n → Rrec {n = n} (Perm (suc n))
Rrec.isSetA (sucPermR n) = trunc
Rrec.εA (sucPermR n) = ε
Rrec.∷A (sucPermR n) (k , k<) = ((suc k , k<) ) ∷_
Rrec.invoA (sucPermR n) _ _ = invo _ _
Rrec.braidA (sucPermR n) _ _ _ = braid _ _ _
Rrec.commA (sucPermR n) (k , _) (suc l , _) t _ = comm _ _ t _

sucPerm : ∀ {n} → Perm n → Perm (suc n)
sucPerm {n} = Rrec.f (sucPermR n) 

sucPerm·R  : ∀ n → RelimProp
      (λ z →
         (y : fst (PermG n)) →
         sucPerm ((snd (PermG n) GroupStr.· z) y) ≡
         (snd (PermG (suc n)) GroupStr.· sucPerm z) (sucPerm y))
RelimProp.isPropA (sucPerm·R n) _ = isPropΠ λ _ →  trunc _ _
RelimProp.εA (sucPerm·R n) = λ _ → refl
RelimProp.∷A (sucPerm·R n) k = cong ((suc (fst k) , snd k) ∷_) ∘_

sucPerm· : ∀ {n} (g h : Perm n) →
    sucPerm (g · h) ≡ sucPerm g · sucPerm h 
sucPerm· = RelimProp.f (sucPerm·R _)

sucPermInv : ∀ n → RelimProp
      (λ z →
         sucPerm (GroupStr.inv (snd (PermG n)) z) ≡
         GroupStr.inv (snd (PermG (suc n))) (sucPerm z))
RelimProp.isPropA (sucPermInv n) _ = trunc _ _ 
RelimProp.εA (sucPermInv n) = refl
RelimProp.∷A (sucPermInv n) k {xs} X =
   RelimProp.f (sucPerm·R n) (inv xs) (η k)
     ∙ cong (_· (η (suc (fst k) , snd k))) X

sucPermGH : ∀ n → IsGroupHom (snd (PermG n))
   (sucPerm)
   (snd (PermG (suc n)))
IsGroupHom.pres· (sucPermGH n) =
   RelimProp.f (sucPerm·R n)
IsGroupHom.pres1 (sucPermGH n) = refl
IsGroupHom.presinv (sucPermGH n) =
  RelimProp.f (sucPermInv n)

sucPermComm : ∀ {n} → (g : Perm n) →
     η (zero , _) · sucPerm (sucPerm g)
   ≡ sucPerm (sucPerm g) · η (zero , _) 
sucPermComm = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = trunc _ _
   RelimProp.εA w = refl
   RelimProp.∷A w k {xs} X =
     comm _ _ _ _ ∙ cong ((suc (suc (fst k)) , snd k) ∷_) X

weakPermR : ∀ n → Rrec {n = n} (Perm (suc n))
Rrec.isSetA (weakPermR n) = trunc
Rrec.εA (weakPermR n) = ε
Rrec.∷A (weakPermR n) (k , k<) = ((k , <-weaken {n = n} k<) ) ∷_
Rrec.invoA (weakPermR n) _ _ = invo _ _
Rrec.braidA (weakPermR n) _ _ _ = braid _ _ _
Rrec.commA (weakPermR n) (k , _) (suc l , _) t _ = comm _ _ t _

+Perm : ∀ {n} m → Perm n → Perm (m + n)
+Perm zero x = x
+Perm (suc m) x = sucPerm (+Perm m x)

weakPerm : ∀ n → Perm n → Perm (suc n)
weakPerm n = Rrec.f (weakPermR n)


+WeakPerm : ∀ n {m} → Perm m → Perm (m + n)
+WeakPerm zero = subst Perm (sym (+-zero _))
+WeakPerm (suc n) x = subst Perm (sym (+-suc _ _)) (weakPerm _ (+WeakPerm n x))

+WeakPerm' : ∀ n {m} → Perm m → Perm (n + m)
+WeakPerm' zero x = x
+WeakPerm' (suc n) x = weakPerm _ (+WeakPerm' _ x)

weakPerm·  : ∀ n → RelimProp      
      (λ z →
         (y : Perm n) →
         weakPerm n ((snd (PermG n) GroupStr.· z) y) ≡
         (weakPerm n z · weakPerm n y))
RelimProp.isPropA (weakPerm· n) _ = isPropΠ λ _ →  trunc _ _
RelimProp.εA (weakPerm· n) y = refl
RelimProp.∷A (weakPerm· n) k = cong ((fst k , <-weaken {n = n} (snd k)) ∷_) ∘_

weakPermInv : ∀ n → RelimProp
      (λ z →
         weakPerm n (GroupStr.inv (snd (PermG n)) z) ≡
         GroupStr.inv (snd (PermG (suc n))) (weakPerm n z))
RelimProp.isPropA (weakPermInv n) _ = trunc _ _ 
RelimProp.εA (weakPermInv n) = refl
RelimProp.∷A (weakPermInv n) k {xs} X =
   RelimProp.f (weakPerm· n) (inv xs) (η k)
     ∙ cong (_· (η ((fst k) , <-weaken {n = n} (snd k)))) X


weakPermGH : ∀ n → IsGroupHom (snd (PermG n))
   (weakPerm n)
   (snd (PermG (suc n)))
IsGroupHom.pres· (weakPermGH n) =
   RelimProp.f (weakPerm· n)
IsGroupHom.pres1 (weakPermGH n) = refl
IsGroupHom.presinv (weakPermGH n) =
  RelimProp.f (weakPermInv n)


-- discretePerm'ε : ∀ n → RelimProp {n = n} (λ z → Dec (ε ≡ z))
-- RelimProp.isPropA (discretePerm'ε n) _ = isPropDec (trunc _ _)
-- RelimProp.εA (discretePerm'ε n) = yes refl
-- RelimProp.∷A (discretePerm'ε n) _ _ = no {!!}

-- discretePerm' : ∀ n → RelimProp (λ z → (y : Perm n) → Dec (z ≡ y))
-- RelimProp.isPropA (discretePerm' n) _ = isPropΠ λ _ → isPropDec (trunc _ _)
-- RelimProp.εA (discretePerm' n) =
--   RelimProp.f {!!}
-- RelimProp.∷A (discretePerm' n) = {!!}

-- discretePerm : ∀ n → Discrete (Perm n)
-- discretePerm n = RelimProp.f {!!}

-- -- WeakComm :  ∀ {n m} → (h : Perm m) (k : ℕ)
-- --     (k< : suc (m + k) < m + suc (suc n)) →
-- --        +WeakPerm (suc (suc n)) h · η (m + k , k<)
-- --      ≡ (η (m + k , k<)
-- --         · +WeakPerm (suc (suc n)) h)
-- -- WeakComm = {!!}




-- weakSuc-comm : ∀ {n m} → (h : Perm m) (g : Perm n) →
--        +WeakPerm _ h · +Perm _ ((sucPerm _ (sucPerm _ g)))
--      ≡ (+Perm  _ (sucPerm _ (sucPerm _ g) )
--         · +WeakPerm _ h)
-- weakSuc-comm = {!!}




adjT< : ∀ n k j → suc k < n → j < n → A.adjTransposition k j < n
adjT< (suc (suc n)) zero zero x x₁ = _
adjT< (suc (suc n)) zero (suc zero) x x₁ = _
adjT< (suc (suc n)) zero (suc (suc j)) x x₁ = x₁
adjT< (suc (suc n)) (suc k) zero x x₁ = x₁
adjT< (suc (suc n)) (suc k) (suc j) x x₁ = adjT< (suc n) k j x x₁

adjT : ∀ n → Σ ℕ (λ k₁ → suc k₁ < n) → Σ ℕ (λ k₁ → k₁ < n) → Σ ℕ (λ k₁ → k₁ < n)
adjT n (k , k<) (j , j<) = A.adjTransposition k j , adjT< n k j k< j<
-- fst (adjT n (k , _) (j , _)) = A.adjTransposition k j
-- snd (adjT n (k , k<) (j , j<)) = adjT< n k j k< j<

extOnℕ : ∀ n → {f f' : Fin n → Fin n} →
 (Path (∀ (k : ℕ) → {_ : k < n} → ℕ)
    (λ k {k<} → fst (f (k , k<))) (λ k {k<} → fst (f' (k , k<))))
 → f ≡ f'
extOnℕ n x = funExt λ x₁ → ≡Fin {n = n} λ i → x i (fst x₁) {snd x₁} 

isInvolution-adjT : ∀ n k → isInvolution (adjT n k)
isInvolution-adjT (suc (suc n)) (zero , snd₁) (zero , snd₂) = refl
isInvolution-adjT (suc (suc n)) (zero , snd₁) (suc zero , snd₂) = refl
isInvolution-adjT (suc (suc n)) (zero , snd₁) (suc (suc fst₁) , snd₂) = refl
isInvolution-adjT (suc (suc (suc n))) (suc k , snd₁) (zero , snd₂) = refl
isInvolution-adjT (suc (suc (suc n))) (suc k , snd₁) (suc fst₁ , snd₂) =
  cong sucF (isInvolution-adjT (suc (suc n)) (k , snd₁) (fst₁ , snd₂))

adjT-braid : ∀ n k k< →
      ( adjT n (k , <-weaken {n = n} k<)
      ∘ adjT n (suc k , k<)
      ∘ adjT n (k , <-weaken {n = n} k<))
  ≡ ( adjT n (suc k , k<)
      ∘ adjT n (k , <-weaken {n = n} k<)
      ∘ adjT n (suc k , k<))
adjT-braid (suc (suc (suc n))) zero k< i (zero , _) = 2 , _
adjT-braid (suc (suc (suc n))) zero k< i (suc zero , _) = 1 , _
adjT-braid (suc (suc (suc n))) zero k< i (suc (suc zero) , _) = 0 , _
adjT-braid (suc (suc (suc n))) zero k< i (suc (suc (suc l)) , l<) =
  (suc (suc (suc l)) , l<)
adjT-braid (suc (suc (suc (suc n)))) (suc k) k< i (zero , _) = 0 , _
adjT-braid (suc (suc (suc (suc n)))) (suc k) k< i (suc l , l<) =
  sucF (adjT-braid (suc (suc (suc n))) k k< i (l , l<))

adjT-comm : ∀ n k l → commT (fst k) (fst l) → ∀ a →
      (( adjT n l
      ∘ adjT n k) a)
  ≡ (( adjT n k
      ∘ adjT n l) a)
adjT-comm (suc (suc n)) (zero , k<) (suc (suc l) , l<) x (zero , a<) = refl
adjT-comm (suc (suc n)) (zero , k<) (suc (suc l) , l<) x (suc zero , a<) = refl
adjT-comm (suc (suc n)) (zero , k<) (suc (suc l) , l<) x (suc (suc a) , a<) = refl
adjT-comm (suc (suc n)) (suc k , k<) (suc (suc (suc l)) , l<) x (zero , a<) = refl
adjT-comm (suc (suc n)) (suc k , k<) (suc (suc (suc l)) , l<) x (suc a , a<) =
  cong sucF (adjT-comm (suc n) (k , k<) (suc (suc l) , l<) x (a , a<))

adjT≃ : ∀ {n} → Fin n → Fin (suc n) ≃ Fin (suc n)
adjT≃ {n} k = involEquiv {f = adjT (suc n) k} (isInvolution-adjT (suc n)  k)

adjTIso : ∀ {n} → Fin n → Iso (Fin (suc n)) (Fin (suc n))
adjTIso {n} k = involIso {f = adjT (suc n) k} (isInvolution-adjT (suc n)  k)

adjTIso' : ∀ {n} → (Σ ℕ  λ k → (suc k < n)) → Iso (Fin n) (Fin n)
adjTIso' {n} k = involIso {f = adjT n k} (isInvolution-adjT n k)

adjT'≃ : ∀ {n} → (Σ ℕ  λ k → (suc k < n)) → (Fin n) ≃ (Fin n)
adjT'≃ {n = n} = isoToEquiv ∘ adjTIso' {n}


toℕFGℕ≃ℕ : ∀ {n} → Perm n → A.FGℕ≃ℕ
toℕFGℕ≃ℕ ε = A.ε
toℕFGℕ≃ℕ ((x , _) ∷ xs) = x A.∷  toℕFGℕ≃ℕ xs
toℕFGℕ≃ℕ (invo (k , _) x i) = A.invo k (toℕFGℕ≃ℕ x) i
toℕFGℕ≃ℕ (braid k k< x i) = A.braid k (toℕFGℕ≃ℕ x) i
toℕFGℕ≃ℕ (comm (k , _) (l , _) z x i) = A.comm k l z (toℕFGℕ≃ℕ x) i
toℕFGℕ≃ℕ (trunc _ _ p q i i₁) =
  A.trunc _ _ (cong toℕFGℕ≃ℕ p) (cong toℕFGℕ≃ℕ q) i i₁ 

toℕFGℕ≃ℕ· : ∀ {n} f g → (toℕFGℕ≃ℕ {n} f) A.· (toℕFGℕ≃ℕ g) ≡ toℕFGℕ≃ℕ (f · g) 
toℕFGℕ≃ℕ· = RelimProp.f w
 where
  w : RelimProp _
  RelimProp.isPropA w _ = isPropΠ λ _ → A.trunc _ _
  RelimProp.εA w _ = refl
  RelimProp.∷A w (k , _) = cong (k A.∷_) ∘_

toℕFGℕ≃ℕinv :  ∀ {n} f → A.inv (toℕFGℕ≃ℕ {n} f) ≡ toℕFGℕ≃ℕ (inv f) 
toℕFGℕ≃ℕinv = RelimProp.f w
 where
  w : RelimProp _
  RelimProp.isPropA w _ = A.trunc _ _
  RelimProp.εA w = refl
  RelimProp.∷A w (k , _) {xs} X =
     cong (A._· A.η k) X ∙ toℕFGℕ≃ℕ· (inv xs) _



to≃ : ∀ {n} → Perm n → Iso ℕ ℕ
to≃ {n} = A.to≃ ∘ toℕFGℕ≃ℕ

to≃CF : ∀ {n} → (x : Perm n) →  ⟨ A.constFromIsoH (to≃ x) n ⟩
to≃CF {n} = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w x = snd (A.constFromIsoH (to≃ x) n)
   RelimProp.εA w _ _ = refl
   RelimProp.∷A w (k , k<) {xs} X m n≤m =
     let z = A.isConstFrom-adjTransposition k m
              (≤-trans {suc (suc k)} {n} {m} k< n≤m)
     in X _ (subst (n ≤_) (sym z) n≤m) ∙ z

to≃' : ∀ {n} → Perm n → A.IsoCF n
fst (to≃' x) = to≃ x
snd (to≃' x) = to≃CF x

-- rotFG : ∀ {n} → Fin n → Perm (suc n)
-- rotFG (zero , _) = ε
-- rotFG {suc n} (suc k , sk<) =
--  (zero , _) ∷ sucPerm (rotFG (k , sk<))

rotFG : ∀ {n} → Fin n → Perm n
rotFG (zero , _) = ε
rotFG {suc n} (suc k , sk<) =
  (zero , ≤-trans {1} {suc k} {n} _ sk<) ∷ sucPerm (rotFG (k , sk<))
  


from≃ : ∀ {n} → ∀ e → ⟨ A.constFromIsoH e n ⟩ → Perm n 
from≃ {zero} _ _ = ε
from≃ {suc n} e X = 
  let (k , (x' , X')) = Iso.fun (A.unwindIsoIsoCF n)
          ( e , X)
  in sucPerm (from≃ {n} x' X') · rotFG {suc n} k

toℕFGℕ≃ℕ∘sucPerm≡sucFGℕ≃ℕ∘toℕFGℕ≃ℕ : ∀ {n} x → 
   toℕFGℕ≃ℕ (sucPerm {n} x) ≡ A.sucFGℕ≃ℕ (toℕFGℕ≃ℕ x)
toℕFGℕ≃ℕ∘sucPerm≡sucFGℕ≃ℕ∘toℕFGℕ≃ℕ = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = A.trunc _ _
   RelimProp.εA w = refl
   RelimProp.∷A w (k , _) = cong (suc k A.∷_)


rotFG'CohA : ∀ {n} k → toℕFGℕ≃ℕ (rotFG {n} k) ≡ A.rotFG (fst k)
rotFG'CohA (zero , k<) = refl
rotFG'CohA {suc (suc n)} (suc k , k<) = 
  cong′ (zero A.∷_)
    (toℕFGℕ≃ℕ∘sucPerm≡sucFGℕ≃ℕ∘toℕFGℕ≃ℕ (rotFG (k , k<))
      ∙ cong′ A.sucFGℕ≃ℕ (rotFG'CohA (k , k<)))

fromCohA : ∀ {n} → ∀ e → (p : ⟨ A.constFromIsoH e n ⟩)
             → toℕFGℕ≃ℕ (from≃ {n} e p) ≡
                 A.from≃ e n p 
fromCohA {zero} e p = refl
fromCohA {suc n} e X =
  let (k , (x' , X')) = Iso.fun (A.unwindIsoIsoCF n) ( e , X)
  in sym (toℕFGℕ≃ℕ· {n = suc n}
        ((sucPerm
        (from≃ (fst (snd (Iso.fun (A.unwindIsoIsoCF n) (e , X))))
         (snd (snd (Iso.fun (A.unwindIsoIsoCF n) (e , X)))))))
         ((rotFG (fst (Iso.fun (A.unwindIsoIsoCF n) (e , X)))))) 
        ∙ cong₂' A._·_
      (toℕFGℕ≃ℕ∘sucPerm≡sucFGℕ≃ℕ∘toℕFGℕ≃ℕ {n = n} (from≃ {n} x' X')
                ∙ cong′ A.sucFGℕ≃ℕ (fromCohA {n = n} x' X'))
      (rotFG'CohA {suc n} k)


from≃' : ∀ {n} → A.IsoCF n → Perm n
from≃' = uncurry from≃


from≃IdIso : ∀ {n} p → from≃ {n} idIso p ≡ ε
from≃IdIso {zero} _ = refl
from≃IdIso {suc n} p =
  cong′ (_· ε) (cong′ sucPerm
    (cong from≃' (Σ≡Prop (λ x → snd (A.constFromIsoH x n)) A.unwindIsoIdIso)
    ∙ from≃IdIso {n} (A.unwindConstFromIso n idIso p)))


isFGliK0 : ∀ k n m p p' → ¬ n ≡ m →
              Path (Perm (suc (suc k)))
              ((sucPerm
                (rotFG
                  ((predℕ (Iso.inv (A.rotIso' (fst n)) (fst m))
                     , p)))) · rotFG n)
              ((zero , _) ∷ ((sucPerm (rotFG (
                (predℕ (Iso.inv (A.rotIso' (fst m)) (fst n)) , p')))
                  · rotFG m)))
isFGliK0 k n m p p' ¬p = 
  A.rotRotElim
  (λ n m n' m' → ∀ k → ∀ {p0} {p1} {p2} {p3} →
     (sucPerm {n = suc k} (rotFG (m' , p0))) · rotFG (n , p1)
              ≡ (zero , _) ∷ ((sucPerm (rotFG (n' , p2)) · rotFG (m , p3))))
  caseA
  (λ e0 e1 x k → sym (invo _ _) ∙ sym (cong′ ((zero , _) ∷_) (caseA e1 e0 x k)))
  (fst n) (fst m) (¬p ∘ ≡Fin {n = suc (suc k)}) k
 where
   caseA : (e0 e1 : ℕ) →
             e1 < suc e0 → ∀ k →
             {p0 : e1 < suc k} {p1 : suc e0 < suc (suc k)} {p2 : e0 < suc k}
             {p3 : e1 < suc (suc k)} →
             (sucPerm (rotFG (e1 , p0)) · rotFG (suc e0 , p1)) ≡
             (zero , tt) ∷ (sucPerm (rotFG (e0 , p2)) · rotFG (e1 , p3))
   caseA e0 zero x k {p1 = p1} {p2 = p2} = 
     cong′ (λ y → (zero , tt) ∷ sucPerm (rotFG (e0 , y)))
        (isProp≤ {m = e0} {n = k} p1 p2)
      ∙ sym (idr ((zero , _) ∷ sucPerm (rotFG (e0 , p2))))
   caseA (suc e0) (suc e1) x (suc k) {p0} {p1} {p2} {p3} = 
     let z = caseA e0 e1 x k {p0} {p1} {p2} {p3}
         
     in cong′ ((1 , tt) ∷_)
           (assoc· ((sucPerm (sucPerm (rotFG (e1 , _))))) ((zero , _) ∷ ε) _
             ∙ cong′ (_· (sucPerm ((zero , _) ∷ sucPerm (rotFG (e0 , _)))))
             (sym (sucPermComm (rotFG (e1 , _))))
            ∙ (sym (assoc· ((0 , _) ∷ ε) (sucPerm (sucPerm (rotFG (e1 , _)))) _))
            ∙ cong′ ((0 , _) ∷_)
                 (sym (sucPerm· (sucPerm (rotFG (e1 , _)))
                     (((zero , _) ∷ sucPerm (rotFG (e0 , _)))))
            ∙  cong sucPerm z))
         ∙ (λ i → braid zero _
             (sucPerm· (sucPerm (rotFG (e0 , p2)))
                       (rotFG (e1 , p3)) i) (~ i)) 
         ∙ cong′ (λ x → (0 , _) ∷ (1 , _) ∷ x)
             ( (assoc· ((zero , tt) ∷ ε)
                       (sucPerm (sucPerm (rotFG (e0 , _))))
                       (sucPerm (rotFG (e1 , p3)))
                 ∙ cong (_· _) (sucPermComm (rotFG (e0 , _))))
              ∙ sym (assoc·
                 (sucPerm (sucPerm (rotFG (e0 , _))))
                 ((zero , tt) ∷ ε)
                 (sucPerm (rotFG (e1 , p3)))))


piiR : ∀ n → RelimProp
      (λ z → from≃' (to≃' {n} z) ≡ z)
piiR =
 (ℕ.elim {A = λ n → RelimProp (λ z → from≃' (to≃' {n} z) ≡ z)}
   w0 (λ n → wN n ∘ RelimProp.f) )
 where
  w0 : RelimProp (λ z → from≃' (to≃' z) ≡ z)
  RelimProp.isPropA w0 _ = trunc _ _
  RelimProp.εA w0 = refl
  RelimProp.∷A w0 ()

  h : ∀ n e 𝑘 𝑘<sn p →
       from≃' {suc n}
          (compIso (A.adjTransposition≃ 𝑘) (fst e ) , p)
         ≡ (𝑘 , 𝑘<sn) ∷ from≃' {suc n} e
  h (suc n) (e , P) zero 𝑘<sn p = 
   let ee1 = Iso.fun e 1
       ee0 = Iso.fun e 0

       ee0< = _
       e0 = (Iso.inv (A.rotIso' (ee1)) (ee0)) 
       e1 = _
       e0' = ee0
       e1' = Iso.inv (A.rotIso' ee0) ee1
       pe1'< = _

       eL = from≃ _ _
       eR = from≃ _ _

   in cong′ (_· rotFG e1) (sucPerm· (sucPerm eL) (rotFG _))
    ∙ sym (assoc· (sucPerm (sucPerm eL)) _ _)
    ∙ cong₂' _·_ (cong′ (sucPerm ∘' sucPerm ∘' from≃')
           (Σ≡Prop (λ x →  snd (A.constFromIsoH x n))
              (sym (A.unwindPermHeadCompSwap0and1FST e))))
        (isFGliK0 n _ _ _ _ (snotz ∘ isoFunInjective e _ _ ∘ cong′ fst))
    ∙ assoc· (sucPerm (sucPerm eR)) _
       (sucPerm (rotFG (predℕ e1' , pe1'<)) · _)      
    ∙ cong′ (_· ((sucPerm (rotFG (predℕ e1' , pe1'<)) · rotFG (e0' , ee0<) )))
        (sym (sucPermComm eR))      
    ∙ sym (assoc· (_ ∷ ε) (sucPerm (sucPerm eR)) _)      
    ∙ cong′ (_ ∷_) (assoc· (sucPerm (sucPerm eR))
        (sucPerm (rotFG (predℕ e1' , pe1'<))) _
    ∙ cong′ (_· rotFG (e0' , ee0<)) (sym (sucPerm· (sucPerm eR) _)))


  h (suc n) (e , P) 𝑘'@(suc 𝑘) 𝑘<sn p =
   let (k , (x' , X')) = Iso.fun (A.unwindIsoIsoCF (suc n)) (e , P)
       ((k* , k<*) , (x'* , X'*)) = Iso.fun (A.unwindIsoIsoCF (suc n))
             ((compIso (A.adjTransposition≃ (suc 𝑘)) e) , p)
       X* = A.isConstFrom∘ (Iso.fun x') (suc n) _ (suc (suc 𝑘))
               X' (A.isConstFrom-adjTransposition 𝑘)
       pp = subst 
            (fst ∘ (A.constFromIsoH (compIso (A.adjTransposition≃ 𝑘) (x' ))))
               (right-≤-→max≡ (suc n) (suc (suc 𝑘)) 𝑘<sn) X*
   in cong₂ (_·_) (cong′ sucPerm (
       cong′ from≃' (Σ≡Prop (λ x → snd (A.constFromIsoH x (suc n)))
       {u = _ , X'*} {v = _ , pp} (Iso≡Set-fun isSetℕ isSetℕ _ _ (λ _ → refl)))
         ∙ h n (x' , X') 𝑘 𝑘<sn pp)) (cong rotFG (≡Fin {n = suc (suc n)} refl))
      ∙ sym (assoc· (η (𝑘' , 𝑘<sn)) (sucPerm (from≃ x' X')) (rotFG k))


  wN : (n : ℕ) →
         (∀ z → from≃' (to≃' {n} z) ≡ z) →
         RelimProp (λ z → from≃' (to≃' {suc n} z) ≡ z)
  RelimProp.isPropA (wN n _) _ = trunc _ _
  RelimProp.εA (wN n _) = from≃IdIso (to≃CF {suc n} ε)
  RelimProp.∷A (wN n X) k {xs} P =
   uncurry (h n (to≃' xs)) k (to≃CF (k ∷ xs)) 
     ∙ cong′ (k ∷_) P

PermIsoIso : ∀ {n} → Iso (Perm n) (A.IsoCF n) 
Iso.fun (PermIsoIso) = to≃'
Iso.inv (PermIsoIso) = from≃'
Iso.rightInv (PermIsoIso {n}) e =
  let zz = A.getLeastB (Iso.fun (fst e)) (n , snd e)
      z = A.retract-to≃'-from≃' (fst e , zz)
  in Σ≡Prop (λ x → snd (A.constFromIsoH x n) ) 
       (cong′ A.to≃ (fromCohA {n = n} (fst e) (snd e) ∙
              A.from≃lem (fst e) (fst e) n (fst zz) _ _ refl)
              ∙ cong′ fst z)
Iso.leftInv (PermIsoIso) = RelimProp.f (piiR _)

PermGIsoIso : ∀ n → GroupIso (PermG n)
                    (SetIso-Group _ (isSetFin {n = n})) 
fst (PermGIsoIso n) = compIso PermIsoIso (A.IsoIsoCFIsoFin n)
IsGroupHom.pres· (snd (PermGIsoIso n)) =
  λ x y →
    let p =  cong A.to≃ (sym (toℕFGℕ≃ℕ· x y))
            ∙ (A.to≃· (toℕFGℕ≃ℕ x) (toℕFGℕ≃ℕ y))
    in Iso≡Set-fun (isSetFin {n = n}) (isSetFin {n = n}) _ _
         λ k → ≡Fin {n = n} (funExt⁻ (cong (Iso.fun) p) (fst k))
    
IsGroupHom.pres1 (snd (PermGIsoIso n)) =
  Iso≡Set-fun (isSetFin {n = n}) (isSetFin {n = n}) _ _
    λ x → ≡Fin {n = n} refl
IsGroupHom.presinv (snd (PermGIsoIso n)) x =
 let z = A.to≃Inv (toℕFGℕ≃ℕ x) ∙ cong A.to≃ (toℕFGℕ≃ℕinv x)
 in Iso≡Set-fun (isSetFin {n = n}) (isSetFin {n = n}) _ _
       λ k → ≡Fin {n = n}
         (sym (funExt⁻ (cong Iso.fun z) (fst k)))
 

       
-- permuteF' : ∀ n → Perm n → Fin n → Fin n 
-- permuteF' n = Rrec.f {n = n} (w n)
--   where
--    open Rrec
 
--    w : ∀ n → Rrec {n = n} (Fin n → Fin n)
--    isSetA (w n) = isSet→ (isSetFin {n = n})
--    εA (w n) = idfun _
--    ∷A (w n) k X = adjT n k ∘ X 
--    invoA (w n) k x = cong (_∘ x) (funExt (isInvolution-adjT n k))
--    braidA (w n) k k< x =
--      funExt λ x' → ≡Fin {n = n}
--         (funExt⁻ (A.adjTranspositionBraid k) (fst (x x')))
--    commA (w n) (k , _) (l , _) q x = 
--          funExt λ x' → ≡Fin {n = n}
--         (funExt⁻ (sym (A.adjTranspositionComm k l q)) (fst (x x')))

permuteIso : ∀ n → Perm n → Iso (Fin n) (Fin n) 
permuteIso n = Rrec.f {n = n} (w n)
  where
   open Rrec
 
   w : ∀ n → Rrec {n = n} (Iso (Fin n) (Fin n))
   isSetA (w n) = isSet-SetsIso (isSetFin {n = n})
                   (isSetFin {n = n})
   εA (w n) = idIso
   ∷A (w n) k = compIso (adjTIso' {n = n} k) --X ∘ adjT n k 
   invoA (w n) k x = 
    Iso≡Set (isSetFin {n = n}) (isSetFin {n = n})
     _ _ (cong (Iso.fun x) ∘ (isInvolution-adjT n k))
         (isInvolution-adjT n k ∘ Iso.inv x)

   braidA (w n) k k< x = 
    Iso≡Set (isSetFin {n = n})
       (isSetFin {n = n})
     _ _ (cong (Iso.fun x) ∘ funExt⁻ (adjT-braid n k k<))
          (funExt⁻ (adjT-braid n k k<) ∘ (Iso.inv x) )
   commA (w n) k l q x =
    Iso≡Set (isSetFin {n = n})
       (isSetFin {n = n})
     _ _ (cong (Iso.fun x) ∘ (adjT-comm n k l q))
         (sym ∘ adjT-comm n k l q ∘ (Iso.inv x))
permuteF : ∀ n → Perm n → Fin n → Fin n 
permuteF n = Iso.fun ∘ permuteIso n

permuteF' : ∀ n → Perm n → Fin n → Fin n 
permuteF' n = Iso.inv ∘ permuteIso n

-- Rrec.f {n = n} (w n)
--   where
--    open Rrec
 
--    w : ∀ n → Rrec {n = n} (Fin n → Fin n)
--    isSetA (w n) = isSet→ (isSetFin {n = n})
--    εA (w n) = idfun _
--    ∷A (w n) k X = X ∘ adjT n k 
--    invoA (w n) k x = cong (x ∘_) (funExt (isInvolution-adjT n k))
--    braidA (w n) k k< x = 
--      funExt λ x' → 
--        (cong′ x
--           (≡Fin {n = n} (
--             funExt⁻ (A.adjTranspositionBraid k) _) ) )
--    commA (w n) (k , _) (l , _) q x =
--      funExt λ x' → 
--        (cong′ x
--           (≡Fin {n = n} (
--             funExt⁻ (A.adjTranspositionComm k l q) _) ) )



permuteIso· : ∀ n → (g h : Perm n) →
                   compIso (permuteIso n g) (permuteIso n h)
                      ≡ (permuteIso n (g · h))
permuteIso· n = RelimProp.f w
 where
  open RelimProp

  w : RelimProp _
  isPropA w _ = isPropΠ λ _ → isSet-SetsIso (isSetFin {n = n})
                   (isSetFin {n = n}) _ _
  εA w _ = compIsoIdL _
  ∷A w k {xs} X h = Iso≡Set-fun (isSetFin {n = n})
       (isSetFin {n = n})
     _ _ (funExt⁻ (cong Iso.fun (X h)) ∘ _)
