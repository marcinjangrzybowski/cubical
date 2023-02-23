{-

This file contains:

- An implementation of the free group of a type of generators as a HIT

-}
{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.IPresentation2 where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.FreeGroup.Base
open import Cubical.HITs.FreeGroup.Properties renaming (elimProp to elimPropFG)
open import Cubical.HITs.PropositionalTruncation renaming (map to map₁ ; map2 to map2₁)
open import Cubical.HITs.SetQuotients renaming (rec to rec/ ; [_] to [_]/ ; rec2 to rec2/)
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.FinData as FD
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Sum as ⊎

open import Cubical.Data.List.FinData

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Group.Subgroup
-- open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.Foundations.HLevels



open import Cubical.Algebra.Group.Generators

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

-- fromList : ∀ {A : Type ℓ} → List A → FreeGroup A 
-- fromList [] = ε
-- -- fromList (x ∷ []) = η x
-- fromList (x ∷ xs) = η x · fromList (xs)

-- PRR : (A : Type ℓ) (R : List A → Type ℓ') → FreeGroup A → FreeGroup A → Type (ℓ-max ℓ ℓ')
-- PRR A R = (λ x x₁ → Σ _ λ r → R r ×
--            ((x · inv x₁) ≡ fromList r))

-- PresentedGroup : (A : Type ℓ) (R : List A → Type ℓ') → Type (ℓ-max ℓ ℓ')
-- PresentedGroup A R = FreeGroup A / (PRR A R)


-- module _ {A : Type ℓ} {R : List A → Type ℓ'} where

--   module FG = GroupTheory (freeGroupGroup A)


--   concatFG = concatG (freeGroupGroup A)


--   -- toList : ∀ {A : Type ℓ} → (a : FreeGroup A) →  ∥ Σ (List A) (λ l → fromList l ≡ a ) ∥₁
--   -- toList = elimPropFG (λ _ → squash₁)
--   --  (λ a →  ∣ [ a ] , sym (idr (η a)) ∣₁)
--   --  (λ _ _ → map2₁ λ (x , p) (y , q) → x ++ y , {!!} )
--   --     ∣ [] , refl ∣₁ λ _ → map₁ λ x → rev (fst x) , {!!} ∙ cong inv (snd x)


--   _≡'_ = Path (PresentedGroup A R)




--   lem : ∀ (a b c : FreeGroup A) → ((a · c) · inv (b · c)) ≡ (a · inv b)
--   lem a b c = cong ((a · c) ·_) (FG.invDistr b c) ∙
--              sym (assoc _ _ _) ∙ cong (a ·_)
--                ((assoc _ _ _) ∙ cong (_· (inv b)) (invr c) ∙ sym (idl (inv b))) 

 
--   law1 : ∀ l → R l → [ fromList l ]/ ≡' [ ε ]/ 
--   law1 l ∈l = eq/ _ _ (l , ∈l , cong ((fromList l) ·_) FG.inv1g ∙ sym (idr (fromList l)))


--   -- prInvRestLem : ∀ a b → [ a ]/ ≡' [ b ]/ → [ inv a ]/ ≡' [ inv b ]/
--   -- prInvRestLem a b x = eq/ _ _ {!!}
--   --   where
--   --     z : {!!}
--   --     z = {!!}


--   -- prInvRest : (a b : List A) → PRR A R (fromList a) (fromList b)
--   --     → [ inv (fromList a) ]/ ≡' [ inv (fromList b) ]/
--   -- -- prInvRest [] [] _ = refl
--   -- prInvRest [] l (r , r∈ , p) = cong [_]/ ({!!} ∙ sym p ∙ {!!})
--   -- prInvRest (x₁ ∷ []) l (r , r∈ , p) = {!p!}
--   -- prInvRest (x₁ ∷ x ∷ a) l (r , r∈ , p) = {!!}
--   -- -- prInvRest (x₁ ∷ a) (x₂ ∷ b) x = {!!}

--   prInvRestLem : ∀ l → R l → ∀ b → [ (fromList b) · inv (fromList l) ]/ ≡' [ (fromList b) ]/
--   prInvRestLem l x [] = {!!}
--   prInvRestLem l x (x₁ ∷ b) = {!!}
--     -- eq/ _ _ (l , x , {!!})

--   prInvRest : (a b : FreeGroup A) → PRR A R a b → [ inv a ]/ ≡' [ inv b ]/
--   prInvRest a b (r , r∈ , p) =
--    {!!}
--     ∙ cong [_]/ (sym (cong (inv a ·_) p) ∙ assoc _ _ _ ∙ {!!})

--   compRest : (a b c : FreeGroup A) → PRR A R b c → [ a · b ]/ ≡' [ a · c ]/

--   prInv : PresentedGroup A R → PresentedGroup A R
--   prInv [ a ]/ = [ inv a ]/
--   prInv (eq/ a b r i) = prInvRest a b r i
--   prInv (squash/ x x₁ p q i i₁) = {!!}

-- -- rec/ squash/ ([_]/ ∘ inv) prInvRest

--   _pr·_ : PresentedGroup A R → PresentedGroup A R  → PresentedGroup A R
--   _pr·_ = rec2/ squash/ (λ a b → [ a · b ]/)
--    (λ a b c (r , r∈ , p) →  eq/ _ _ (r , r∈ , lem a b c ∙ p)) compRest

--   presentedGroupGroupStr : GroupStr (PresentedGroup A R)
--   GroupStr.1g (presentedGroupGroupStr) = [ ε ]/
--   GroupStr._·_ (presentedGroupGroupStr) = _pr·_ 

--   GroupStr.inv presentedGroupGroupStr = prInv
--   GroupStr.isGroup presentedGroupGroupStr =
--     makeIsGroup
--       squash/
--       (elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → cong [_]/ (assoc _ _ _))
--       (elimProp (λ _ → squash/ _ _) (cong [_]/ ∘ sym ∘ idr))
--       (elimProp (λ _ → squash/ _ _) (cong [_]/ ∘ sym ∘ idl))
--       (elimProp (λ _ → squash/ _ _) (cong [_]/ ∘ invr))
--       (elimProp (λ _ → squash/ _ _) (cong [_]/ ∘ invl))

--   module PG = GroupStr presentedGroupGroupStr


--   module PGT = GroupTheory (_ , presentedGroupGroupStr)

--   -- concatFG = concatG (freeGroupGroup A)



--   -- elimPa : (B : FreeGroup A → FreeGroup A → Type ℓ'') →
--   --   (B : FreeGroup A → FreeGroup A → Type ℓ'') →
--   --     ∀ a b → [ a ]/ ≡' [ b ]/ → {!!}
--   -- elimPa = {!!}

--   -- -- η· : ∀ a x y  → [ concatFG x ]/ ≡' [ concatFG y ]/
--   -- --      → [ a · concatFG x ]/ ≡' [ a · concatFG y ]/
--   -- -- -- η· a [] [] = {!!}
--   -- -- η· a [] l = {!!}
--   -- -- -- η· a (x ∷ x₁) [] = {!!}
--   -- -- -- η· a (x ∷ x₁) [] = {!!}
--   -- -- η· a (x ∷ x₁) l p =
--   -- --   let z = η· (a · x) x₁ l {!p!}
--   -- --   in {!!} ∙ {!!}
--   -- -- exchange-η : ∀ a x y → [ concatFG x ]/ ≡' [ η a · concatFG y ]/
--   -- --    → [ inv (η a) · concatFG x ]/ ≡' [  concatFG y ]/
--   -- -- exchange-η a [] y x₁ = {!a!}
--   -- -- exchange-η a (x ∷ x₂) y x₁ = {!!}

--   -- toList : {!!}
--   -- toList = {!!}

--   ++Lem' : ∀ l l' → R (l ++ rev l') → [ fromList l ]/ ≡' [ concatFG (map (λ x → inv (η x)) l') ]/
--   ++Lem' l l' x = eq/ (fromList l) (concatFG (map (inv ∘ η) l')) (_ , x , {!!})

--   ++Lem : ∀ l l' → R (rev l ++ l') → [ inv (fromList (rev l)) ]/ ≡' [ (fromList l') ]/
--   ++Lem [] l' x = cong [_]/ (FG.inv1g) ∙ sym (law1 l' x)
--   ++Lem (x₁ ∷ l) l' x =
--     let z = ++Lem l (x₁ ∷ l') (subst R (++-assoc (rev l) _ _) x) 
--     in {!!}
--     -- cong [_]/ ({!!} ∙ FG.invDistr _ _) ∙ {!!} ∙ exchange-η {!!} {!!} {!!} {!!} ∙ {!!}
--     -- eq/ _ _ ((rev (x₁ ∷ l) ++ l') , (x , {!!}))

--   -- -- ++Lem [] l' x =  cong [_]/ (FG.inv1g) ∙ sym (law1 l' x)
--   -- -- ++Lem (x₁ ∷ l) l' x =
--   -- --   let z = {!++Lem l (!}
--   -- --   in {!!}

--   prInvRestLem : ∀ l → R l → ∀ b → [ b · inv (fromList l) ]/ ≡' [ b ]/
--   prInvRestLem l r b = {!!}
--     -- where
--       -- z : {!prInvRestLem  (b · η x₁) !}
--       -- z = {!!}
--   -- prInvRestLem : ∀ l → R l → ∀ b → [ inv (fromList l · b) ]/ ≡' [ inv b ]/
--   -- prInvRestLem [] x b = cong [_]/ (cong inv (sym (idl b)))
--   -- prInvRestLem (x₁ ∷ l) x b = 
--   --   eq/ _ _ (x₁ ∷ l , (x ,
--   --     cong₂ _·_
--   --       (FG.invDistr _ _
--   --        ∙ cong ((inv b) ·_) (FG.invDistr _ _))
--   --      (FG.invInv b) ∙ {!!}))
--   --   where
--   --     w : {!prInvRestLem l x (b · !}
--   --     w = {!!}

--   prInvRest a b (r , r∈ , p) =
--     cong ([_]/ {R = PRR A R} ∘ inv) pA ∙ cong [_]/ (FG.invDistr _ _) ∙ prInvRestLem r r∈ (inv b) 
--     where

--       pA : a ≡ (fromList r · b )
--       pA = (idr a ∙ cong (a ·_) (sym (invl b)) ∙ assoc _ _ _) ∙ cong (_· b) p 
 
      
--   compRest a b c (r , r∈ , p) = Z
--     where
--       z : {!!}
--       z = {!!}


--       Z : [ a · b ]/ ≡' [ a · c ]/
--       Z = {!!}



pattern _η∷_ x xs = inl x ∷ xs

pattern inv_η∷_ x xs = inr x ∷ xs


-- data ℕ₁ : Type where
--   zero : ℕ₁
--   suc : ℕ₁ → ℕ₁
--   squashℕ₁ : ∀ x y → x ≡ y

-- data PresentedGroup (m n : ℕ) : (m n l : ℕ) → ? → Type₀


-- data PresentedGroup where
--    _∷_ : Fin m → PresentedGroup → PresentedGroup
--    _∷'_ : Fin m → PresentedGroup → PresentedGroup
--    ε     : PresentedGroup
--    invr  : ∀ x xs → x ∷ x ∷' xs ≡ xs
--    invl  : ∀ x xs → x ∷' x ∷ xs ≡ xs
--    -- rel : ∀ k xs → RR (relator k) xs → xs ≡ ε
--    trunc : isSet (PresentedGroup)


record Presentation (m n l : ℕ) : Type₀ where
  field
    relator : Fin n → Fin l → (Bool × Fin m)

  data PresentedGroup : Type₀

  rlt : Fin n → PresentedGroup

  infixr 5 _∷_
  -- infixr 5 _∷'_


  -- data RR : ∀ {k'} → (Fin k' → Bool × Fin m) → PresentedGroup → Type₀

  -- _·PG_ : PresentedGroup → PresentedGroup → PresentedGroup

  data PresentedGroup where
    _∷_ : (Bool × Fin m) → PresentedGroup → PresentedGroup
    ε     : PresentedGroup
    invr  : ∀ x xs → (true , x) ∷ (false , x) ∷ xs ≡ xs
    invl  : ∀ x xs → (false , x) ∷ (true , x) ∷ xs ≡ xs
    rel : ∀ k → rlt k ≡ ε
    trunc : isSet (PresentedGroup)

  rlt = (foldrFin (_∷_) ε) ∘ relator

open Presentation

module _ (m n : ℕ) where

  _·PG_ : ∀ l → ∀ P → PresentedGroup {m} {n} {l} P → PresentedGroup P → PresentedGroup P
  (l ·PG P) (x ∷ x₁) y = x ∷ (_·PG_ l P x₁ y) 
  (l ·PG P) ε y = y
  (l ·PG P) (invr x x₁ i) y = {!!}
  (l ·PG P) (invl x x₁ i) y = {!!}
  (l ·PG P) (rel k i) y = {!!}
  (l ·PG P) (trunc x x₁ x₂ y₁ i i₁) y = {!!}

-- (x ∷ x₂) ·PG x₁ = x ∷ (x₂ ·PG x₁)
-- (x ∷' x₂) ·PG x₁ = x ∷' (x₂ ·PG x₁)
-- ε ·PG x₁ = x₁
-- invr x x₂ i ·PG x₁ = invr x (x₂ ·PG x₁) i 
-- invl x x₂ i ·PG x₁ = invl x (x₂ ·PG x₁) i
-- rel xs ys z i ·PG x = {!(cong (_·PG x) x₂ ∙ ?) i !}
-- trunc x x₂ x₃ y i i₁ ·PG x₁ = {!!}





  -- data RR where
  --   rr : ∀ {k} → ∀ xs ys f → RR f xs ys
  --   rr↓ : ∀ {xs ys k f} → RR {suc k} f xs ys → RR {k} (f ∘ suc) (? ∷ xs) ys
    
  -- (x ∷ x₂) ·PG x₁ = x ∷ (x₂ ·PG x₁)
  -- (x ∷' x₂) ·PG x₁ = x ∷' (x₂ ·PG x₁)
  -- ε ·PG x₁ = x₁
  -- invr x x₂ i ·PG x₁ = invr x (x₂ ·PG x₁) i 
  -- invl x x₂ i ·PG x₁ = invl x (x₂ ·PG x₁) i
  -- -- rel xs ys z i ·PG x = {!(cong (_·PG x) x₂ ∙ ?) i !}
  -- trunc x x₂ x₃ y i i₁ ·PG x₁ = {!!}


--   assocPG : ∀ x y z → x ·PG (y ·PG z) ≡ (x ·PG y) ·PG z
--   assocPG (x ∷ x₁) y z i = x ∷ assocPG x₁ y z i
--   assocPG (x ∷' x₁) y z i = x ∷' assocPG x₁ y z i 
--   assocPG ε y z = refl
--   assocPG (invr x x₁ i) y z = {!!}
--   assocPG (invl x x₁ i) y z = {!!}
--   assocPG (trunc x x₁ x₂ y₁ i i₁) y z = {!!}
  
--   invPG : PresentedGroup → PresentedGroup
--   invPG (x ∷ xs) = invPG xs ·PG (x ∷' ε)
--   invPG (x ∷' xs) = invPG xs ·PG (x ∷ ε)
--   invPG ε = ε
--   invPG (invr x x₁ i) = (sym (assocPG (invPG x₁) (x ∷ ε) (x ∷' ε))
--         ∙ cong ((invPG x₁) ·PG_) (invr x _) ∙ {!!} ) i
--   invPG (invl x x₁ i) =
--     (sym (assocPG (invPG x₁) (x ∷' ε) (x ∷ ε))
--      ∙ cong ((invPG x₁) ·PG_) (invl x _) ∙ {!!}) i
--   invPG (trunc x x₁ x₂ y i i₁) = {!!}

--   -- len₁ : PresentedGroup → ℕ₁
--   -- len₁ (x ∷ x₁) = suc (len₁ x₁)
--   -- len₁ (x ∷' x₁) = suc (len₁ x₁)
--   -- len₁ ε = zero
--   -- len₁ (invr x x₁ i) = squashℕ₁ (suc (suc (len₁ x₁))) (len₁ x₁) i
--   -- len₁ (invl x x₁ i) = squashℕ₁ (suc (suc (len₁ x₁))) (len₁ x₁) i
--   -- len₁ (trunc x x₁ x₂ y i i₁) = {!!}

--   -- len₁ : PresentedGroup → ℕ₁
--   -- len₁ (x ∷ x₁) = zero
--   -- len₁ (x ∷' x₁) = zero
--   -- len₁ ε = zero
--   -- len₁ (invr x x₁ i) = squashℕ₁ zero (len₁ x₁) i
--   -- len₁ (invl x x₁ i) = squashℕ₁ zero (len₁ x₁) i
--   -- --squashℕ₁ (suc (suc (len₁ x₁))) (len₁ x₁) i
--   -- len₁ (trunc x x₁ x₂ y i i₁) = {!!}

 

--   -- presentedGroupGroupStr : GroupStr PresentedGroup
--   -- GroupStr.1g presentedGroupGroupStr = ε
--   -- GroupStr._·_ presentedGroupGroupStr = _·_
--   -- GroupStr.inv presentedGroupGroupStr = inv
--   -- GroupStr.isGroup presentedGroupGroupStr =
--   --  makeIsGroup trunc assoc (sym ∘ idr) (sym ∘ idl) invr invl 

--   -- presentedGroupGroup : Group {!!}
--   -- presentedGroupGroup = _ , presentedGroupGroupStr
  
-- -- open Presentation


-- -- module elimProp {A : Type ℓ} {n : ℕ} {P : _} (B : PresentedGroup {A = A} {n = n} P)
-- --                   -- {Ix : Type ℓ'} {R : Ix → List A × List A}
-- --                   {B : ∀ {n} → ∀ {P} → PresentedGroup {A = A} {n = n} P → Type ℓ''}
-- --                   -- (bTrunc : ∀ {n} {P} → ∀ x → isProp (B {n} {P} x))
-- --                   (b : {!!})
-- --                   (b∷ : {!!})
-- --                   (b∷' : {!!})
-- --                   -- (bε : ∀ {n} {P} → B {n} {P} ε) 
-- --                   -- (bInv : ∀ {n} {P} → ∀ {x} → B {n} {P} x → B (inv x))
-- --                     where
-- --                   -- (onF : ∀ x → B (fromFree x))

-- --   f : ∀ x → B  x
-- --   f = {!!}



-- -- -- module elimProp {A : Type ℓ}
-- -- --                   -- {Ix : Type ℓ'} {R : Ix → List A × List A}
-- -- --                   {B : ∀ {n} → ∀ {P} → PresentedGroup {A = A} {n = n} P → Type ℓ''}
-- -- --                   (bTrunc : ∀ {n} {P} → ∀ x → isProp (B {n} {P} x))
-- -- --                   (b : ∀ {n} {P} → ∀ x → B {n} {P} (η x))
-- -- --                   (b· : ∀ {n} {P} → ∀ {x y} → B {n} {P} x → B {n} {P} y → B (x · y))
-- -- --                   (bε : ∀ {n} {P} → B {n} {P} ε) 
-- -- --                   (bInv : ∀ {n} {P} → ∀ {x} → B {n} {P} x → B (inv x))
-- -- --                     where
-- -- --                   -- (onF : ∀ x → B (fromFree x))

-- -- --   f : ∀ {n} {P} → ∀ x → B {n} {P} x
-- -- --   f (η x) = b x
-- -- --   f (x · x₁) = b· (f x) (f x₁)
-- -- --   f ε = bε
-- -- --   f (inv x) = bInv (f x)
-- -- --   f {n} (rel ix i) = {!ix!}

-- -- -- -- PresentedGeneratedBy : ∀ n → (R : Presentation A n)
-- -- -- --    → ⟨ GeneratedBy (presentedGroupGroup R) (η) ⟩
-- -- -- -- PresentedGeneratedBy n R x = {!x!}


-- -- -- -- -- fromList : ∀ {A : Type ℓ}  {Ix : Type ℓ'} {R : Ix → List A × List A}
-- -- -- -- --                   → List A → PresentedGroup A R 




-- -- -- -- -- fromList [] = ε
-- -- -- -- -- -- fromList (x ∷ []) = η x
-- -- -- -- -- fromList (x ∷ xs) = η x · fromList (xs)




-- -- -- -- -- -- module elimProp {A : Type ℓ}
-- -- -- -- -- --                   {Ix : Type ℓ'} {R : Ix → List A × List A}
-- -- -- -- -- --                   {B : PresentedGroup A R → Type ℓ''}
-- -- -- -- -- --                   (bTrunc : ∀ x → isProp (B x))
-- -- -- -- -- --                   (b : ∀ x → B (η x))
-- -- -- -- -- --                   (b· : ∀ {x y} → B x → B y → B (x · y))
-- -- -- -- -- --                   (bε : B ε) 
-- -- -- -- -- --                   (bInv : ∀ {x} → B x → B (inv x))
-- -- -- -- -- --                     where
-- -- -- -- -- --                   -- (onF : ∀ x → B (fromFree x))



-- -- -- -- -- --   f : ∀ n → Fin n ≃ Ix → ∀ x → B x


-- -- -- -- -- --   f' : ∀ n → (e : Fin n ≃ Ix) → ∀ ix  →
-- -- -- -- -- --          PathP (λ i → B (rel ix i))
-- -- -- -- -- --            (f n e (fromList (fst (R ix))))
-- -- -- -- -- --            (f n e (fromList (snd (R ix))))
-- -- -- -- -- --   -- f' = ?

-- -- -- -- -- --   f n e (η x) = b x
-- -- -- -- -- --   f n e (x · x₁) = b· (f n e x) (f n e  x₁)
-- -- -- -- -- --   f n e  ε = bε
-- -- -- -- -- --   f n e  (inv x) = bInv (f n e  x)
-- -- -- -- -- --   f n e (assoc x x₁ x₂ i) =
-- -- -- -- -- --     isProp→PathP
-- -- -- -- -- --       (λ i → bTrunc (assoc x x₁ x₂ i))
-- -- -- -- -- --       (b· (f n e x) (b· (f n e x₁) (f n e x₂)))
-- -- -- -- -- --       (b· (b· (f n e x) (f n e x₁)) (f n e x₂))
-- -- -- -- -- --        i 
-- -- -- -- -- --   f n e (idr x i) =
-- -- -- -- -- --         isProp→PathP
-- -- -- -- -- --       (λ i → bTrunc (idr x i))
-- -- -- -- -- --       (f n e x)
-- -- -- -- -- --       (b· (f n e x) bε)
-- -- -- -- -- --        i 

-- -- -- -- -- --   f n e (idl x i) =
-- -- -- -- -- --       isProp→PathP
-- -- -- -- -- --       (λ i → bTrunc (idl x i))
-- -- -- -- -- --       (f n e x)
-- -- -- -- -- --       (b· bε (f n e x))
-- -- -- -- -- --        i 

-- -- -- -- -- --   f n e (invr x i) =
-- -- -- -- -- --       isProp→PathP
-- -- -- -- -- --       (λ i → bTrunc (invr x i))
-- -- -- -- -- --       (b· (f n e x) (bInv (f n e x)))
-- -- -- -- -- --       bε
-- -- -- -- -- --        i 

-- -- -- -- -- --   f n e (invl x i) =
-- -- -- -- -- --      isProp→PathP
-- -- -- -- -- --       (λ i → bTrunc (invl x i))
-- -- -- -- -- --       (b· (bInv (f n e x)) (f n e x))
-- -- -- -- -- --       bε
-- -- -- -- -- --        i 
-- -- -- -- -- --   f n e (rel ix i) = {!!}
-- -- -- -- -- --   -- f (suc n) e (rel ix i) = {!!}

-- -- -- -- -- --   -- f' ix i
-- -- -- -- -- --       -- let z = isProp→PathP
-- -- -- -- -- --       --          (λ i → bTrunc (rel ix i))
-- -- -- -- -- --       --          (f (fromFree (fst (R ix))))
-- -- -- -- -- --       --          (f (fromFree (snd (R ix))))
-- -- -- -- -- --       --           i
-- -- -- -- -- --       -- in {!z!}
-- -- -- -- -- --   f n e (trunc x x₁ x₂ y i i₁) = {!!}

-- -- -- -- -- --   f' = {!!}



-- -- -- -- -- -- -- -- module elimProp {A : Type ℓ} {R : List A → List A → Type ℓ''}
-- -- -- -- -- -- -- --                   {B : PresentedGroup A  R → Type ℓ''}
-- -- -- -- -- -- -- --                   (bTrunc : ∀ x → isProp (B x))
-- -- -- -- -- -- -- --                   (b : ∀ x → B (η x))
-- -- -- -- -- -- -- --                   (b· : ∀ {x y} → B x → B y → B (x · y))
-- -- -- -- -- -- -- --                   (bε : B ε)
-- -- -- -- -- -- -- --                   (bInv : ∀ {x} → B x → B (inv x))
-- -- -- -- -- -- -- --                   -- (onF : ∀ x → B (fromFree x))
                  
-- -- -- -- -- -- -- --                     where


-- -- -- -- -- -- -- --   f : ∀ x → B x
  
-- -- -- -- -- -- -- --   f' : ∀ {a a'} → (r : R a a') →
-- -- -- -- -- -- -- --          PathP (λ i → B (rel r i))
-- -- -- -- -- -- -- --            (f (fromList a))
-- -- -- -- -- -- -- --            (f (fromList a'))
-- -- -- -- -- -- -- --   -- f' = {!!}

-- -- -- -- -- -- -- -- -- Goal: B (rel ix i)
-- -- -- -- -- -- -- -- -- ———— Boundary ——————————————————————————————————————————————
-- -- -- -- -- -- -- -- -- i = i0 ⊢ f (fromList a)
-- -- -- -- -- -- -- -- -- i = i1 ⊢ f (fromList a')

-- -- -- -- -- -- -- --   f (η x) = b x
-- -- -- -- -- -- -- --   f (x · x₁) = b· (f x) (f x₁)
-- -- -- -- -- -- -- --   f ε = bε
-- -- -- -- -- -- -- --   f (inv x) = bInv (f x)
-- -- -- -- -- -- -- --   f (assoc x x₁ x₂ i) =
-- -- -- -- -- -- -- --     isProp→PathP
-- -- -- -- -- -- -- --       (λ i → bTrunc (assoc x x₁ x₂ i))
-- -- -- -- -- -- -- --       (b· (f x) (b· (f x₁) (f x₂)))
-- -- -- -- -- -- -- --       (b· (b· (f x) (f x₁)) (f x₂))
-- -- -- -- -- -- -- --        i 
-- -- -- -- -- -- -- --   f (idr x i) =
-- -- -- -- -- -- -- --         isProp→PathP
-- -- -- -- -- -- -- --       (λ i → bTrunc (idr x i))
-- -- -- -- -- -- -- --       (f x)
-- -- -- -- -- -- -- --       (b· (f x) bε)
-- -- -- -- -- -- -- --        i 

-- -- -- -- -- -- -- --   f (idl x i) =
-- -- -- -- -- -- -- --       isProp→PathP
-- -- -- -- -- -- -- --       (λ i → bTrunc (idl x i))
-- -- -- -- -- -- -- --       (f x)
-- -- -- -- -- -- -- --       (b· bε (f x))
-- -- -- -- -- -- -- --        i 

-- -- -- -- -- -- -- --   f (invr x i) =
-- -- -- -- -- -- -- --       isProp→PathP
-- -- -- -- -- -- -- --       (λ i → bTrunc (invr x i))
-- -- -- -- -- -- -- --       (b· (f x) (bInv (f x)))
-- -- -- -- -- -- -- --       bε
-- -- -- -- -- -- -- --        i 

-- -- -- -- -- -- -- --   f (invl x i) =
-- -- -- -- -- -- -- --      isProp→PathP
-- -- -- -- -- -- -- --       (λ i → bTrunc (invl x i))
-- -- -- -- -- -- -- --       (b· (bInv (f x)) (f x))
-- -- -- -- -- -- -- --       bε
-- -- -- -- -- -- -- --        i 
-- -- -- -- -- -- -- --   f (rel {a} {a'} ix i) = f' ix i

-- -- -- -- -- -- -- --   -- f' ix i
-- -- -- -- -- -- -- --       -- let z = isProp→PathP
-- -- -- -- -- -- -- --       --          (λ i → bTrunc (rel ix i))
-- -- -- -- -- -- -- --       --          (f (fromFree (fst (R ix))))
-- -- -- -- -- -- -- --       --          (f (fromFree (snd (R ix))))
-- -- -- -- -- -- -- --       --           i
-- -- -- -- -- -- -- --       -- in {!z!}
-- -- -- -- -- -- -- --   f (trunc x x₁ x₂ y i i₁) = {!!}

-- -- -- -- -- -- -- --   f' {[]} {[]} r = {!!}
-- -- -- -- -- -- -- --   f' {[]} {x ∷ a'} r = {!!}
-- -- -- -- -- -- -- --   f' {x ∷ a} {[]} r = {!!}
-- -- -- -- -- -- -- --   f' {x ∷ a} {x₁ ∷ a'} r =
-- -- -- -- -- -- -- --     {!!}



-- -- -- -- -- -- -- Presented : {A : Type ℓ} (R : List A → List A → Type ℓ') → Group (ℓ-max ℓ ℓ')
-- -- -- -- -- -- -- Presented R = _ , (presentedGroupGroupStr {R = R})

-- -- -- -- -- -- -- Presented/ : (A : Type ℓ) {Ix : Type ℓ'} (R : Ix → FreeGroup A × FreeGroup A) →
-- -- -- -- -- -- --                Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- -- Presented/ A {Ix} R = FreeGroup A /
-- -- -- -- -- -- --                  λ x y → Σ Ix λ ix → (fst (R ix) ≡ x) × (snd (R ix) ≡ y)  



-- -- -- -- -- -- -- -- IsoPresentedQt : {A : Type ℓ} {Ix : Type ℓ'} (R : Ix → FreeGroup A × FreeGroup A)
-- -- -- -- -- -- -- --       → Iso ((PresentedGroup A {Ix} R)) (Presented/ A R)
-- -- -- -- -- -- -- -- IsoPresentedQt {A = A} {Ix} R = w
-- -- -- -- -- -- -- --   where


-- -- -- -- -- -- -- --     w : Iso (PresentedGroup A R) (Presented/ A R)
-- -- -- -- -- -- -- --     Iso.fun w (η x) = {!!}
-- -- -- -- -- -- -- --     Iso.fun w (x · x₁) = {!!}
-- -- -- -- -- -- -- --     Iso.fun w ε = {!!}
-- -- -- -- -- -- -- --     Iso.fun w (inv x) = {!!}
-- -- -- -- -- -- -- --     Iso.fun w (assoc x x₁ x₂ i) = {!!}
-- -- -- -- -- -- -- --     Iso.fun w (idr x i) = {!!}
-- -- -- -- -- -- -- --     Iso.fun w (idl x i) = {!!}
-- -- -- -- -- -- -- --     Iso.fun w (invr x i) = {!!}
-- -- -- -- -- -- -- --     Iso.fun w (invl x i) = {!!}
-- -- -- -- -- -- -- --     Iso.fun w (rel ix i) =
-- -- -- -- -- -- -- --       {!eq/ ? ? ? i!}
-- -- -- -- -- -- -- --     Iso.fun w (trunc x x₁ x₂ y i i₁) = {!!}
-- -- -- -- -- -- -- --     Iso.inv w =
-- -- -- -- -- -- -- --       rec/ trunc fromFree
-- -- -- -- -- -- -- --         λ a b r → sym (cong fromFree (fst (snd r))) ∙∙  rel (fst r) ∙∙ cong fromFree (snd (snd r)) 
-- -- -- -- -- -- -- --     Iso.rightInv w = {!!}
-- -- -- -- -- -- -- --     Iso.leftInv w = {!!}

-- -- -- -- -- -- -- -- PresentedGeneratedBy' : {A : Type ℓ} {Ix : Type ℓ'} (R : Ix → FreeGroup A × FreeGroup A) →
-- -- -- -- -- -- -- --                           (∀ a → Σ _ λ b → Path (PresentedGroup A {Ix} R) (η b) (inv (η a)))
-- -- -- -- -- -- -- --                            →  ⟨ GeneratedBy (Presented R) (η) ⟩
-- -- -- -- -- -- -- -- PresentedGeneratedBy' {A = A} {Ix} R invGens =
-- -- -- -- -- -- -- --    elimProp.f
-- -- -- -- -- -- -- --      (λ _ → squash₁)
-- -- -- -- -- -- -- --      (λ x → ∣ [ x ] , sym (idr (η x)) ∣₁)
-- -- -- -- -- -- -- --      (map2₁ λ (x , p) (y , q) → x ++ y ,
-- -- -- -- -- -- -- --        (cong (concatG (Presented R)) (map-++ η x y)
-- -- -- -- -- -- -- --          ∙∙ sym (concatG· {G = Presented R} (map η x) (map η y))
-- -- -- -- -- -- -- --          ∙∙ cong₂ _·_ p q ))
-- -- -- -- -- -- -- --      ∣ [] , refl ∣₁
-- -- -- -- -- -- -- --      (map₁ (uncurry
-- -- -- -- -- -- -- --        (ind (λ p →  [] , sym inv1g ∙ cong inv p )
-- -- -- -- -- -- -- --             λ {a} {l} z y →
-- -- -- -- -- -- -- --                let (a' , p') = invGens a
-- -- -- -- -- -- -- --                    (l' , p'') = concatGRev (Presented R) η
-- -- -- -- -- -- -- --                      invGens l
-- -- -- -- -- -- -- --                in l' ++ [ a' ] ,
-- -- -- -- -- -- -- --                       (cong (concatG (Presented R)) ( map-++ η l' [ a' ]))  ∙
-- -- -- -- -- -- -- --                     (sym (concatG· {G = (Presented R)} (map η l') [ η a' ])) ∙
-- -- -- -- -- -- -- --                    cong₂ {B = λ _ → PresentedGroup A R} 
-- -- -- -- -- -- -- --                          {x = concatG (Presented R) (map η l')}
-- -- -- -- -- -- -- --                          {y = inv (concatG (Presented R) (map η l))}
-- -- -- -- -- -- -- --                          {C = λ _ _ → PresentedGroup A R}
-- -- -- -- -- -- -- --                           _·_ (sym p'') (sym (idr _) ∙ p')
-- -- -- -- -- -- -- --                     ∙ sym (invDistr _ _) ∙ cong inv y)))
-- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- --     open GroupTheory (Presented R)







-- -- -- -- -- -- -- -- --(map₁ λ (x , p) → (rev x) , {!!} ∙ cong inv p )  
-- -- -- -- -- -- -- --   -- λ x → ∣ [ {!x!} ] , {!!} ∣₁ 
