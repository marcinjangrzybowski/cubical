{-# OPTIONS --safe #-}
module Cubical.Data.FinData.PermutationPrim where

open import Cubical.Foundations.Everything
open import Cubical.Data.FinData
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.FinData.Properties

open import Cubical.Algebra.Group

open import Cubical.Algebra.Group.Morphisms

open import Cubical.Algebra.Group.Generators


private
  variable
    ℓ : Level

sucF : ∀ n → Fin (predℕ (predℕ n)) → Fin (predℕ n)
sucF (suc (suc n)) = suc

weakF : ∀ n → Fin (predℕ (predℕ n)) → Fin (predℕ n)
weakF (suc (suc n)) = weakenFin

commT : ∀ n → Fin (predℕ n) → Fin (predℕ n) → Type
commT (suc (suc n)) k zero = ⊥
commT (suc (suc (suc n))) k one = ⊥
commT (suc (suc (suc n))) zero (suc (suc l)) = Unit
commT (suc (suc (suc n))) (suc k) (suc (suc l)) = commT (suc (suc n)) k (suc l)

infixr 5 _∷_

data Perm (n : ℕ) : Type where
  
  ε     : Perm n
  _∷_ : Fin (predℕ n) → Perm n → Perm n

  invo : ∀ k xs → k ∷ k ∷ xs  ≡ xs
  braid : (k : Fin (predℕ (predℕ n))) → ∀ xs →  
               weakF n k ∷ sucF n k ∷ weakF n k ∷ xs
             ≡ sucF n k ∷ weakF n k ∷ sucF n k ∷ xs
  comm : ∀ k l → commT n k l → ∀ xs →   k ∷ l ∷ xs ≡ l ∷ k ∷ xs
  
  trunc : isSet (Perm n)

η : ∀ {n} → Fin (predℕ n) → Perm n
η = _∷ ε 

record RelimProp {ℓ} {n : ℕ} (A : (Perm n) → Type ℓ) : Type ℓ where
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
  f (braid k x i) =
     isProp→PathP (λ i → isPropA (braid k x i))
      (∷A (weakF n k) (∷A (sucF n k) (∷A (weakF n k) (f x))))
      (∷A (sucF n k) (∷A (weakF n k) (∷A (sucF n k) (f x)))) i
  f (comm k l x x₁ i) =
          isProp→PathP (λ i → isPropA (comm k l x x₁  i))
      (∷A k (∷A l (f x₁)))
      (∷A l (∷A k (f x₁))) i
  f (trunc x y p q i i₁) =
         isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (isPropA x))
         _ _ (cong f p) (cong f q) (trunc x y p q) i i₁

record Relim {ℓ} {n : ℕ} (A : (Perm n) → Type ℓ) : Type ℓ where
  field
    isSetA : ∀ x → isSet (A x)
    εA : A ε
    ∷A : ∀ k → ∀ {xs} → A xs → A (k ∷ xs)
    invoA : ∀ k {x} x' → PathP (λ i → A (invo k x i))
      (∷A k (∷A k x'))
      x'
    braidA : ∀ k {x} x' → PathP (λ i → A (braid k x i))
      (∷A (weakF n k) (∷A (sucF n k) (∷A (weakF n k) x')))
      (∷A (sucF n k) (∷A (weakF n k) (∷A (sucF n k) x')))
    commA : ∀ k l z {x} x' → PathP (λ i → A (comm k l z x  i))
      (∷A k (∷A l x'))
      (∷A l (∷A k x'))

  f : ∀ x → A x
  f ε = εA
  f (x ∷ x₁) = ∷A x (f x₁)
  f (invo k x i) = invoA k (f x) i
  f (braid k x i) = braidA k (f x) i

  f (comm k l x x₁ i) = commA k l x (f x₁) i
  f (trunc x y p q i i₁) =
         isOfHLevel→isOfHLevelDep 2 (λ x → (isSetA x))
         _ _ (cong f p) (cong f q) (trunc x y p q) i i₁


record Rrec {ℓ} {n : ℕ} (A : Type ℓ) : Type ℓ where
  field
    isSetA : isSet A
    εA : A
    ∷A : Fin (predℕ n) → A → A
    invoA : ∀ k x → ∷A k (∷A k x) ≡ x
    braidA : ∀ k x → ∷A (weakF n k) (∷A (sucF n k) (∷A (weakF n k) x))
                   ≡ ∷A (sucF n k) (∷A (weakF n k) (∷A (sucF n k) x))
    commA : ∀ k l → commT n k l → ∀ x →
                     ∷A k (∷A l x)
                   ≡ ∷A l (∷A k x)

  f : (Perm n) → A
  f ε = εA
  f (x ∷ x₁) = ∷A x (f x₁)
  f (invo k x i) = invoA k (f x) i
  f (braid k x i) = braidA k (f x) i
  f (comm k l x x₁ i) = commA k l x (f x₁) i
  f (trunc x y p q i i₁) =
    isSetA _ _ (cong f p) (cong f q) i i₁


_·_ : ∀ {n} → Perm n → Perm n → Perm n
ε · x₁ = x₁
(x ∷ x₂) · x₁ = x ∷ (x₂ · x₁)
invo k x i · x₁ = invo k (x · x₁) i
braid k x i · x₁ = braid k (x  · x₁) i
comm k l x x₂ i · x₁ = comm k l x (x₂  · x₁) i
trunc x x₂ x₃ y i i₁ · x₁ =
  trunc (x · x₁) (x₂ · x₁)
    (cong  (_· x₁) x₃) (cong  (_· x₁) y) i i₁



assoc· : ∀ {n} → ∀ (x y z : Perm n) → x · (y · z) ≡ (x · y) · z
assoc· = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = isPropΠ2 λ _ _ → trunc _ _
   RelimProp.εA w _ _ = refl
   RelimProp.∷A w _ p _ _  = cong (_ ∷_) (p _ _)
   

idr : ∀ {n} (x : Perm n) → (x · ε) ≡ x
idr = RelimProp.f
    (record { isPropA = λ _ → trunc _ _
            ; εA = refl
            ; ∷A = λ _ → cong (_ ∷_) })
   
inv : ∀ {n} → Perm n → Perm n
inv {n} = Rrec.f w

  where
    w : Rrec (Perm _)
    Rrec.isSetA w = trunc 
    Rrec.εA w = ε
    Rrec.∷A w k = _· (η k) 
    Rrec.invoA w _ x = sym (assoc· x _ _) ∙ cong (x ·_) (invo _ ε) ∙ idr  x
    Rrec.braidA w k x =
       (cong (_· η _) (sym (assoc· x (η _) (η _))) ∙ sym (assoc· x (η _ · η _) (η _)))
        ∙∙ cong (x ·_) (sym (assoc· (η _) (η _) (η _))
               ∙∙ braid k ε ∙∙ 
                (assoc· (η _) (η _) (η _))) ∙∙
       ((assoc· x (η _ · η _) (η _)) ∙
        cong (_· η _) (assoc· x (η _) (η _)))
    Rrec.commA w k l z x = 
       sym (assoc· x _ _)
        ∙∙ cong (x ·_) (sym (comm k l z ε)) ∙∙
       (assoc· x _ _)

invr : ∀ {n} (x : Perm n) → (x · inv x) ≡ ε
invr = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = trunc _ _ 
   RelimProp.εA w = refl
   RelimProp.∷A w k {xs} p =
     cong (k ∷_)
      (assoc· xs (inv xs) _ ∙ cong (_· η k) p) ∙ invo k ε 

invl : ∀ {n} (x : Perm n) → (inv x · x) ≡ ε
invl = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = trunc _ _ 
   RelimProp.εA w = refl
   RelimProp.∷A w k {xs} p = sym (assoc· (inv xs) (η k) _) ∙ 
      (cong ((inv xs) ·_) (invo k xs)) ∙ p

Permutation : ℕ → Group ℓ-zero
Permutation n = makeGroup {G = Perm n}
  ε
  _·_
  (inv)
  trunc
  assoc·
  idr
  (λ _ → refl)
  invr
  invl


adjTransposition*Braid : ∀ n →  (k : Fin (predℕ (predℕ n))) →
      adjTransposition* {n} (weakF n k) ∙ₑ
      adjTransposition* (sucF n k) ∙ₑ adjTransposition* (weakF n k)
      ≡
      adjTransposition* (sucF n k) ∙ₑ
      adjTransposition* (weakF n k) ∙ₑ adjTransposition* (sucF n k)
adjTransposition*Braid (suc (suc (suc n))) zero =
 equivEq (refl =→ refl =→  refl =→ refl)
adjTransposition*Braid (suc (suc (suc n))) (suc k) =
 equivEq (refl =→ 
   cong ((suc ∘_ ) ∘ fst)  (adjTransposition*Braid (suc (suc n)) k))


adjTransposition*Comm : ∀ n → (k l : Fin (predℕ n)) →
      commT n k l →
      adjTransposition* {n} k ∙ₑ adjTransposition* l ≡
      adjTransposition* l ∙ₑ adjTransposition* k
adjTransposition*Comm (suc .(suc (suc _))) zero (suc (suc l)) x =
  commSwap0and1SucSuc _
adjTransposition*Comm (suc .(suc (suc _))) (suc k) (suc (suc l)) x =
  equivEq (refl =→ 
   cong ((suc ∘_ ) ∘ fst)  (adjTransposition*Comm _ k (suc l) x))


to≃ : ∀ {n} → Perm n → fst (SymData n)
to≃ {n = n} = Rrec.f (to≃R)
  where

   open GroupStr (snd (SymData n))

   to≃R : Rrec {n = n} (fst (SymData n))
   Rrec.isSetA to≃R = is-set
   Rrec.εA to≃R = 1g
   Rrec.∷A to≃R k = adjTransposition* k ∙ₑ_
   Rrec.invoA to≃R k x = equivEq (cong ((fst x) ∘_) (cong fst (adjTransposition*²=idEquiv k)))
   Rrec.braidA to≃R k x = equivEq (cong ((fst x) ∘_) (cong fst (adjTransposition*Braid _ k)))
   Rrec.commA to≃R k l z x = equivEq (cong ((fst x) ∘_) (cong fst (adjTransposition*Comm _ k l z)))

to≃· : ∀ {n} → (f g : Perm n) → fst (to≃ (f · g)) ≡ fst (to≃ f ∙ₑ to≃ g)
to≃· = RelimProp.f w
  where
    w : RelimProp _
    RelimProp.isPropA w _ = isPropΠ λ _ → isSet→ isSetFin _ _ 
    RelimProp.εA w x = refl
    RelimProp.∷A w k x x₁ = cong (_∘ fst (adjTransposition* k)) (x x₁)



-- --    open GroupStr (snd (SymData n))

-- --    to≃R : Rrec {n = n} (fst (SymData n))
-- --    Rrec.isSetA to≃R = is-set
-- --    Rrec.εA to≃R = 1g
-- --    Rrec.ηA to≃R = adjTransposition*
-- --    Rrec.·A to≃R = _∙ₑ_
-- --    Rrec.assoc·A to≃R = ·Assoc
-- --    Rrec.idr·A to≃R = ·IdR
-- --    Rrec.idl·A to≃R = ·IdL
-- --    Rrec.invo·A to≃R = adjTransposition*²=idEquiv
-- --    Rrec.braid·A to≃R = adjTransposition*Braid n
-- --    Rrec.comm·A to≃R = adjTransposition*Comm n


-- record Rrec {ℓ} {n : ℕ} (A : Type ℓ) : Type ℓ where
--   field
--     isSetA : isSet A
--     εA : A
--     ηA : Fin (predℕ n) → A
--     ·A : A → A → A
--     assoc·A : ∀ x x₁ x₂ →
--       ·A x (·A x₁ x₂) ≡ ·A (·A x x₁) x₂
--     idr·A : ∀ x → ·A x εA ≡ x
--     idl·A : ∀ x → ·A εA x ≡ x

--     invo·A : ∀ k → ·A (ηA k) (ηA k) ≡ εA
--     braid·A : ∀ k → ·A (ηA (weakF n k)) (·A (ηA (sucF n k)) (ηA (weakF n k)))
--                     ≡ ·A (ηA (sucF n k)) (·A (ηA (weakF n k)) (ηA (sucF n k)))
--     comm·A : ∀ k l → commT n k l →
--                ·A (ηA k) (ηA l) ≡ ·A (ηA l) (ηA k)
 

--   f : Perm n → A
--   f (η x) = ηA x
--   f ε = εA
--   f (x · x₁) = ·A (f x) (f x₁)
--   f (assoc· x x₁ x₂ i) = assoc·A (f x) (f x₁) (f x₂) i
--   f (idr x i) = idr·A (f x) i
--   f (idl x i) = idl·A (f x) i
--   f (invo k i) = invo·A k i
--   f (braid k i) = braid·A k i
--   f (comm k l x i) = comm·A k l x i
--   f (trunc x y p q i i₁) =
--     isSetA
--          _ _ (cong f p) (cong f q) i i₁


-- record Relim {ℓ} {n : ℕ} (A : (Perm n) → Type ℓ) : Type ℓ where
--   field
--     isSetA : ∀ x → isSet (A x)
--     εA : A ε
--     ηA : ∀ k → A (η k)
--     ·A : ∀ {x y} → A x → A y → A (x · y)
--     assoc·A : ∀ {x y z} → (x' : A x) → (y' : A y) → (z' : A z) →
--        PathP (λ i → A (assoc· x y z i))
--          (·A x' (·A y' z'))  (·A (·A x' y') z')
--     idr·A : ∀ {x} → (x' : A x) →
--        PathP (λ i → A (idr x i))
--          (·A x' εA)  x'
--     idl·A : ∀ {x} → (x' : A x) →
--        PathP (λ i → A (idl x i))
--          (·A εA x')  x'

 
--   f : ∀ x → A x
--   f (η x) = ηA x
--   f ε = εA
--   f (x · x₁) = ·A (f x) (f x₁)
--   f (assoc· x x₁ x₂ i) = assoc·A  (f x) (f x₁) (f x₂) i

--   f (idr x i) = idr·A (f x) i
--   f (idl x i) = idl·A (f x) i
--   f (invo k i) = {!!}
--   f (braid k i) = {!!}
--   f (comm k l x i) = {!!}
--   f (trunc x y p q i i₁) =
--     isOfHLevel→isOfHLevelDep 2 (λ x → (isSetA x))
--          _ _ (cong f p) (cong f q) (trunc x y p q) i i₁


-- -- record RelimProp {ℓ} {n : ℕ} (A : (Perm n) → Type ℓ) : Type ℓ where
-- --   field
-- --     isPropA : ∀ x → isProp (A x)
-- --     εA : A ε
-- --     ηA : ∀ k → A (η k)
-- --     ·A : ∀ {x y} → A x → A y → A (x · y)

-- --   f : ∀ x → A x
-- --   f (η x) = ηA x
-- --   f ε = εA
-- --   f (x · x₁) = ·A (f x) (f x₁)
-- --   f (assoc· x x₁ x₂ i) =
-- --     isProp→PathP (λ i → isPropA (assoc· x x₁ x₂ i))
-- --       (·A (f x) (·A (f x₁) (f x₂)))
-- --       (·A (·A (f x) (f x₁)) (f x₂)) i
-- --   f (idr x i) =
-- --     isProp→PathP (λ i → isPropA (idr x i))
-- --       (·A (f x) εA)
-- --       (f x) i
-- --   f (idl x i) =
-- --     isProp→PathP (λ i → isPropA (idl x i))
-- --       (·A εA (f x))
-- --       (f x) i
-- --   f (invo k i) =
-- --      isProp→PathP (λ i → isPropA (invo k i))
-- --       (·A (ηA k) (ηA k))
-- --       (εA) i
-- --   f (braid k i) =
-- --     isProp→PathP (λ i → isPropA (braid k i))
-- --       (·A (ηA (weakF n k)) (·A (ηA (sucF n k)) (ηA (weakF n k))))
-- --       (·A (ηA (sucF n k)) (·A (ηA (weakF n k)) (ηA (sucF n k)))) i
-- --   f (comm k l x i) =
-- --     isProp→PathP (λ i → isPropA (comm k l x i))
-- --       (·A (ηA k) (ηA l))
-- --       (·A (ηA l) (ηA k)) i
-- --   f (trunc x y p q i i₁) =
-- --     isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (isPropA x))
-- --          _ _ (cong f p) (cong f q) (trunc x y p q) i i₁

-- -- invP : ∀ n → Perm n → Perm n
-- -- invP n (η x) = η x
-- -- invP n ε = ε
-- -- invP n (x · x₁) = invP n x₁ · invP n x
-- -- invP n (assoc· x x₁ x₂ i) = assoc· (invP n x₂) (invP n x₁) (invP n x) (~ i)

-- -- invP n (idr x i) = idl (invP n x) i
-- -- invP n (idl x i) = idr (invP n x) i

-- -- invP n (invo k i) = invo k i
-- -- invP n (braid k i) = (sym (assoc· _ _ _) ∙∙ braid k ∙∙ assoc· _ _ _) i
-- -- invP n (comm k l x i) = comm k l x (~ i)
-- -- invP n (trunc x x₁ x₂ y i i₁) =
-- --   trunc (invP n x) (invP n x₁) (cong (invP n) x₂) (cong (invP n) y
-- --   ) i i₁


-- -- invr : ∀ n → (x : Perm n) → (x · invP n x) ≡ ε
-- -- invr n = RelimProp.f w
-- --   where
-- --     w : RelimProp (λ z → (z · invP n z) ≡ ε)
-- --     RelimProp.isPropA w _ = trunc _ _
-- --     RelimProp.εA w = idr ε
-- --     RelimProp.ηA w k = invo k  
-- --     RelimProp.·A w {x} {x₁} p p₁ =
-- --      (assoc· _ _ _ ∙ cong (_· (invP n x)) (sym (assoc· _ _ _)
-- --           ∙ cong (x ·_) p₁ ∙ idr x))
-- --           ∙ p

-- -- invl : ∀ n → (x : Perm n) → (invP n x · x) ≡ ε
-- -- invl n = RelimProp.f w
-- --   where
-- --     w : RelimProp (λ z → (invP n z · z) ≡ ε)
-- --     RelimProp.isPropA w _ = trunc _ _
-- --     RelimProp.εA w = idl ε
-- --     RelimProp.ηA w k = invo k  
-- --     RelimProp.·A w {x} {x₁} p p₁ =
-- --       assoc· _ _ _ ∙ cong (_· x₁) (sym (assoc· _ _ _) ∙
-- --       cong (invP n x₁ ·_) p ∙ idr _ ) ∙
-- --       p₁

-- -- Permutation : ℕ → Group ℓ-zero
-- -- Permutation n = makeGroup {G = Perm n}
-- --   ε
-- --   _·_
-- --   (invP n)
-- --   trunc
-- --   assoc·
-- --   idr
-- --   idl
-- --   (invr n)
-- --   (invl n) 

-- -- adjTransposition*Braid : ∀ n →  (k : Fin (predℕ (predℕ n))) →
-- --       adjTransposition* {n} (weakF n k) ∙ₑ
-- --       adjTransposition* (sucF n k) ∙ₑ adjTransposition* (weakF n k)
-- --       ≡
-- --       adjTransposition* (sucF n k) ∙ₑ
-- --       adjTransposition* (weakF n k) ∙ₑ adjTransposition* (sucF n k)
-- -- adjTransposition*Braid (suc (suc (suc n))) zero =
-- --  equivEq (refl =→ refl =→  refl =→ refl)
-- -- adjTransposition*Braid (suc (suc (suc n))) (suc k) =
-- --  equivEq (refl =→ 
-- --    cong ((suc ∘_ ) ∘ fst)  (adjTransposition*Braid (suc (suc n)) k))


-- -- adjTransposition*Comm : ∀ n → (k l : Fin (predℕ n)) →
-- --       commT n k l →
-- --       adjTransposition* {n} k ∙ₑ adjTransposition* l ≡
-- --       adjTransposition* l ∙ₑ adjTransposition* k
-- -- adjTransposition*Comm (suc .(suc (suc _))) zero (suc (suc l)) x =
-- --   commSwap0and1SucSuc _
-- -- adjTransposition*Comm (suc .(suc (suc _))) (suc k) (suc (suc l)) x =
-- --   equivEq (refl =→ 
-- --    cong ((suc ∘_ ) ∘ fst)  (adjTransposition*Comm _ k (suc l) x))

-- -- to≃ : ∀ n → Perm n → fst (SymData n)
-- -- to≃ n = Rrec.f (to≃R)
-- --   where

-- --    open GroupStr (snd (SymData n))

-- --    to≃R : Rrec {n = n} (fst (SymData n))
-- --    Rrec.isSetA to≃R = is-set
-- --    Rrec.εA to≃R = 1g
-- --    Rrec.ηA to≃R = adjTransposition*
-- --    Rrec.·A to≃R = _∙ₑ_
-- --    Rrec.assoc·A to≃R = ·Assoc
-- --    Rrec.idr·A to≃R = ·IdR
-- --    Rrec.idl·A to≃R = ·IdL
-- --    Rrec.invo·A to≃R = adjTransposition*²=idEquiv
-- --    Rrec.braid·A to≃R = adjTransposition*Braid n
-- --    Rrec.comm·A to≃R = adjTransposition*Comm n

-- -- adjTransposition*Inv : ∀ n k → adjTransposition* {n} k
-- --                             ≡ invEquiv (adjTransposition* {n} k) 
-- -- adjTransposition*Inv (suc (suc n)) zero = swap0and1≃=invEquivSwap0and1
-- -- adjTransposition*Inv (suc (suc n)) (suc k) =
-- --   equivEq (refl =→  (cong ((suc ∘_) ∘ fst) (adjTransposition*Inv (suc n) k)))

-- -- to≃GH : ∀ n → IsGroupHom (snd (Permutation n)) (to≃ n) (snd (SymData n))
-- -- IsGroupHom.pres· (to≃GH n) _ _ = refl
-- -- IsGroupHom.pres1 (to≃GH n) = refl
-- -- IsGroupHom.presinv (to≃GH n) = RelimProp.f w
-- --   where
-- --     w : RelimProp _
-- --     RelimProp.isPropA w _ = isOfHLevel≃ 2 isSetFin isSetFin _ _
-- --     RelimProp.εA w = equivEq refl
-- --     RelimProp.ηA w k = adjTransposition*Inv n k
-- --     RelimProp.·A w p p₁ = cong₂ _∙ₑ_ p₁ p ∙ equivEq refl 

sucPerm*R : ∀ n → Rrec {n = n} (Perm (suc n))
Rrec.isSetA (sucPerm*R n) = trunc
Rrec.εA (sucPerm*R n) = ε
Rrec.∷A (sucPerm*R (suc n)) = _∷_ ∘ suc
Rrec.invoA (sucPerm*R (suc n)) _ = invo _
Rrec.braidA (sucPerm*R (suc (suc n))) _ = braid _
Rrec.commA (sucPerm*R (suc (suc n))) k (suc l) v = comm _ _ v

sucPerm* : ∀ n → Perm n →  Perm (suc n)
sucPerm* n = Rrec.f (sucPerm*R n)

-- -- PunchHeadInOutPerm : ∀ n → Fin n → Perm n
-- -- PunchHeadInOutPerm (suc n) zero = ε
-- -- PunchHeadInOutPerm (suc (suc n)) (suc x) =
-- --  η zero · sucPerm* _ (PunchHeadInOutPerm _ x)


-- -- from≃ : ∀ n → fst (SymData n) → Perm n
-- -- from≃ zero _ = ε
-- -- from≃ (suc n) e =
-- --   let  (e' , p) = unwindPermHead e
-- --   in sucPerm* n (from≃ n e')
-- --        · PunchHeadInOutPerm _ (fst e zero)

-- -- to≃∘sucPerm*≡sucPerm∘to≃R : ∀ n →
-- --   RelimProp (λ z → to≃ (suc n) (sucPerm* n z) ≡ sucPerm (to≃ n z))
-- -- RelimProp.isPropA (to≃∘sucPerm*≡sucPerm∘to≃R n) _ =
-- --  isOfHLevel≃ 2 isSetFin isSetFin _ _
-- -- RelimProp.εA (to≃∘sucPerm*≡sucPerm∘to≃R n) = equivEq (refl =→ refl)
-- -- RelimProp.ηA (to≃∘sucPerm*≡sucPerm∘to≃R (suc n)) k = refl
-- -- RelimProp.·A (to≃∘sucPerm*≡sucPerm∘to≃R n) p p₁ =
-- --  cong₂ _∙ₑ_ p p₁ ∙ respectsCompSucPerm _ _ 

-- -- to≃∘sucPerm*≡sucPerm∘to≃ : ∀ n → ∀ x →
-- --     to≃ (suc n) (sucPerm* n x) ≡ sucPerm (to≃ n x)
-- -- to≃∘sucPerm*≡sucPerm∘to≃ n = RelimProp.f (to≃∘sucPerm*≡sucPerm∘to≃R n)

-- -- to≃PunchHeadInOutPerm≡rot≃ : ∀ n k →
-- --    to≃ n (PunchHeadInOutPerm n k) ≡ rot≃ {n = n} k
-- -- to≃PunchHeadInOutPerm≡rot≃ (suc n) zero = refl
-- -- to≃PunchHeadInOutPerm≡rot≃ (suc (suc n)) (suc k) =
-- --  cong (_ ∙ₑ_) (to≃∘sucPerm*≡sucPerm∘to≃ (suc n) (PunchHeadInOutPerm (suc n) k)
-- --   ∙ cong sucPerm (to≃PunchHeadInOutPerm≡rot≃ (suc n) k))

-- -- perSymSec : ∀ n → section (to≃ n) (from≃ n)
-- -- perSymSec zero b = equivEq =■
-- -- perSymSec (suc n) e =
-- --   let  (e' , p) = unwindPermHead e
-- --   in  
-- --     cong₂ _∙ₑ_ (to≃∘sucPerm*≡sucPerm∘to≃ n (from≃ n e')
-- --         ∙ cong sucPerm (perSymSec n e'))
-- --       (to≃PunchHeadInOutPerm≡rot≃ (suc n) (fst e zero))
-- --       ∙ sym p


-- -- -- perSymRet : ∀ n → retract (to≃ n) (from≃ n)

-- -- -- perSymRetR-lem : ∀ n → (e f : _) → 
-- -- --    from≃ (suc n) e · from≃ (suc n) f ≡
-- -- --       (from≃ (suc n) (e ∙ₑ f))
-- -- -- perSymRetR-lem n =
-- -- --    GeneratedElimConstr'
-- -- --     (SymData (suc n) )
-- -- --     (generatedSym n)
-- -- --     _
-- -- --     (λ f → (cong (_· from≃ _ f) {!!} ∙ idl _)
-- -- --       ∙ cong (from≃ (suc n)) (sym (compEquivIdEquiv f)))
-- -- --     {!!}

-- -- -- perSymRetR : ∀ n → Relim (λ z → from≃ (suc n) (to≃ (suc n) z) ≡ z)
-- -- -- Relim.isPropA (perSymRetR n) _ = trunc _ _
-- -- -- Relim.εA (perSymRetR n) =
-- -- --   idr _ ∙
-- -- --      cong (sucPerm* n ∘ from≃ n) unwindPermId 
-- -- --      ∙ cong (sucPerm* n) (perSymRet (n) ε)
-- -- -- Relim.ηA (perSymRetR .one) (zero {zero}) =
-- -- --  cong₂ _·_ (idl ε) (idr _) ∙ idl _
-- -- -- Relim.ηA (perSymRetR .(suc (suc n))) (zero {suc n}) = 
-- -- --  cong₂ _·_ (cong (_· ε) (cong {y = idEquiv _} (sucPerm* (suc (suc n))
-- -- --    ∘ sucPerm* (suc n) ∘ from≃ (suc n))
-- -- --      (equivEq refl)) ∙ {!!} ) (idr _) ∙ (idl _)
-- -- -- Relim.ηA (perSymRetR .(suc (suc n))) (suc {suc n} k) =
-- -- --   idr _ ∙ 
-- -- --     cong {x = (from≃ (suc (suc n))
-- -- --        (fst (unwindPermHead (to≃ (suc (suc (suc n))) (η (suc k))))))}
-- -- --        (sucPerm* _) (
-- -- --       cong (_· PunchHeadInOutPerm (suc _) (fst (adjTransposition k) zero))
-- -- --         (cong {x = (fst
-- -- --         (unwindPermHead
-- -- --          (fst (unwindPermHead (to≃ (suc (suc (suc n))) (η (suc k)))))))}
-- -- --             {y = (fst (unwindPermHead (to≃ (suc (suc n)) (η k))))}
-- -- --             (sucPerm* (suc n) ∘ from≃ (suc n))
-- -- --              (equivEq refl))
-- -- --        ∙ Relim.ηA (perSymRetR _) k)

-- -- -- Relim.·A (perSymRetR n) {x} {y} pX pY =
-- -- --   sym (perSymRetR-lem n _ _) ∙ cong₂ _·_ pX pY
 


-- -- -- perSymRet zero = Relim.f
-- -- --  (record { isPropA = λ _ → trunc _ _ ; εA = refl ; ηA = ⊥.rec ∘ ¬Fin0
-- -- --          ; ·A = λ pX pY → sym (idl _) ∙ cong₂ _·_ pX pY  })
-- -- -- perSymRet (suc n) = Relim.f (perSymRetR n)

-- -- -- GroupIsoPermSymData : ∀ n → GroupIso (Permutation n)  (SymData n)
-- -- -- Iso.fun (fst (GroupIsoPermSymData n)) = to≃ n
-- -- -- Iso.inv (fst (GroupIsoPermSymData n)) = from≃ n
-- -- -- Iso.rightInv (fst (GroupIsoPermSymData n)) = perSymSec n
-- -- -- Iso.leftInv (fst (GroupIsoPermSymData n)) = perSymRet n
-- -- -- snd (GroupIsoPermSymData n) = to≃GH n
