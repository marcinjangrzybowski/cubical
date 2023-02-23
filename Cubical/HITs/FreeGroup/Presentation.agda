{-

This file contains:

- An implementation of the free group of a type of generators as a HIT

-}
{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.Presentation where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.FreeGroup.Base
open import Cubical.HITs.FreeGroup.Properties
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients renaming (_/_ to _/₁_)
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Functions.Logic

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base

open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup


private
  variable
    ℓ : Level



data PresentedGroup (A : Type ℓ) (R : ℙ (FreeGroup A)) : Type ℓ

fromFree : ∀ {A : Type ℓ} {R : ℙ (FreeGroup A)} → FreeGroup A → PresentedGroup A R 

data PresentedGroup A R where
  η     : A → PresentedGroup A R
  _·_   : PresentedGroup A R → PresentedGroup A R → PresentedGroup A R
  ε     : PresentedGroup A R
  inv   : PresentedGroup A R → PresentedGroup A R
  assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
  idr   : ∀ x → x ≡ x · ε
  idl   : ∀ x → x ≡ ε · x
  invr  : ∀ x → x · (inv x) ≡ ε
  invl  : ∀ x → (inv x) · x ≡ ε
  rel   : ∀ {y x} → η y · x ∈ R → fromFree (η y · x) ≡ ε 
  trunc : isSet (PresentedGroup A R)

fromFree (η x) = η x
fromFree (x · x₁) = fromFree x · fromFree x₁
fromFree ε = ε
fromFree (inv x) = inv (fromFree x)
fromFree (assoc x x₁ x₂ i) = assoc (fromFree x) (fromFree x₁) (fromFree x₂) i
fromFree (idr x i) = (idr (fromFree x) i)
fromFree (idl x i) = (idl (fromFree x) i)
fromFree (invr x i) = (invr (fromFree x) i)
fromFree (invl x i) = (invl (fromFree x) i)
fromFree (trunc x x₁ x₂ y i i₁) = 
  (trunc (fromFree x) (fromFree x₁)
    (cong (λ a → fromFree a) x₂)
    (cong (λ a → fromFree a) y) i i₁)


data HH : Type₀ where
  H0 : HH
  HP : ∀ x y → x ≡ y

hh : ∀ {A : Type ℓ} {R : ℙ (FreeGroup A)} → PresentedGroup A R → HH
hh (η x) = H0
hh (x · x₁) = H0
hh ε = H0
hh (inv x) = H0
hh (assoc x x₁ x₂ i) = H0
hh (idr x i) = HP (hh x) H0 i
hh (idl x i) = HP (hh x) H0 i
hh (invr x i) = HP H0 H0 i
hh (invl x i) = HP H0 H0 i
hh (rel x i) = HP H0 H0 i
hh (trunc x x₁ x₂ y i i₁) = {!!}

module elimProp {ℓ''}  {A : Type ℓ} {R : ℙ (FreeGroup A)} 
                  {B : PresentedGroup A R → Type ℓ''}
                  (bTrunc : ∀ x → isProp (B x))
                  (b : ∀ x → B (η x))
                  (b· : ∀ {x y} → B x → B y → B (x · y))
                  (bε : B ε)
                  (bInv : ∀ {x} → B x → B (inv x))
                  (onF : ∀ x → B (fromFree x))
                  
                    where


  f : ∀ x → {h : HH} → h ≡ hh x → B x

  -- f' : ∀ ix → PathP (λ i → B (rel ix i))
  --        (f (fromFree (fst (R ix)))) (f (fromFree (snd (R ix))))
  -- f' ix = {!!}

  f (η x) _ = b x
  f (x · x₁) _ = b· (f x {H0} (HP _ _)) (f x₁ {H0} (HP _ _))
  f ε _ = bε
  f (inv x) _ = bInv (f x {H0} (HP _ _))
  f (assoc x x₁ x₂ i) _ =
    isProp→PathP
      (λ i → bTrunc (assoc x x₁ x₂ i))
      (b· (f x {H0} (HP _ _)) (b· (f x₁ {H0} (HP _ _)) (f x₂ {H0} (HP _ _))))
      (b· (b· (f x {H0} (HP _ _)) (f x₁ {H0} (HP _ _))) (f x₂ {H0} (HP _ _)))
       i 
  f (idr x i) _ =
        isProp→PathP
      (λ i → bTrunc (idr x i))
      (f x {!!})
      (b· (f x {!!}) bε)
       i 

  f (idl x i) _ =
      isProp→PathP
      (λ i → bTrunc (idl x i))
      (f x {!!})
      (b· bε (f x {!!}))
       i 

  f (invr x i) _ =
      isProp→PathP
      (λ i → bTrunc (invr x i))
      (b· (f x {!!}) (bInv (f x {!!})))
      bε
       i 

  f (invl x i) _ =
     isProp→PathP
      (λ i → bTrunc (invl x i))
      (b· (bInv (f x {!!})) (f x {!!}))
      bε
       i 
  f (rel {x} ix i) _ = {!x!}

  -- f' ix i
      -- let z = isProp→PathP
      --          (λ i → bTrunc (rel ix i))
      --          (f (fromFree (fst (R ix))))
      --          (f (fromFree (snd (R ix))))
      --           i
      -- in {!z!}
  f (trunc x x₁ x₂ y i i₁) _ = {!!}



-- presentedGroupGroupStr : {A : Type ℓ} {R : ℙ (FreeGroup A)} → GroupStr (PresentedGroup A R)
-- GroupStr.1g presentedGroupGroupStr = ε
-- GroupStr._·_ presentedGroupGroupStr = _·_
-- GroupStr.inv presentedGroupGroupStr = inv
-- GroupStr.isGroup presentedGroupGroupStr =
--  makeIsGroup trunc assoc (sym ∘ idr) (sym ∘ idl) invr invl 

-- Presented : {A : Type ℓ} (R : ℙ (FreeGroup A)) → Group ℓ
-- Presented R = _ , (presentedGroupGroupStr {R = R})

-- data P' {A : Type ℓ} (P : ℙ (FreeGroup A)) (x : FreeGroup A)  : Type ℓ where 
--   η : x ∈ P → P' P x
--   id∈ : x ≡ ε → P' P x
--   ·∈ : ∀ {x' y} → (x ≡ x' · y) → P' P x' → P' P y   → P' P x
--   inv∈ : ∀ {x'} → x ≡ inv x' → P' P x' → P' P x
--   norm∈ : ∀ g h →  P' P h → x ≡  (g · (h · inv g)) → P' P x 
--   -- truncP' : isProp (P' P x)


-- -- Pclo : (A : Type ℓ) (P : ℙ (FreeGroup A)) → ℙ ((FreeGroup A))
-- -- Pclo A P x = P' P x , {!!} --truncP' x 

-- -- FromPres : (A : Type ℓ) (P : ℙ (FreeGroup A)) → Group ℓ
-- -- FromPres A P = freeGroupGroup A /
-- --    ((Pclo A P , record { id-closed = id∈ refl ; op-closed = ·∈ refl ; inv-closed = inv∈ refl }) ,
-- --     λ g h x → norm∈ g h x refl)

-- -- FromPresHom : (A : Type ℓ) (P : ℙ (FreeGroup A)) → GroupHom (FromPres A P) (Presented P)
-- -- fst (FromPresHom A P) =
-- --  Cubical.HITs.SetQuotients.rec
-- --  trunc fromFree w
-- --    where
-- --      module GT = GroupTheory (Presented P)
-- --      module GT' = GroupTheory (freeGroupGroup A)


-- --      w : _
-- --      w a b (η x) =  GT.invUniqueL (rel {x = a · (inv b)} x) ∙ GT.invInv _
-- --      w a b (id∈ x) = cong fromFree (GT'.invUniqueL x ∙ GT'.invInv _)
-- --      w a b (·∈ x r r₁) = {!!}
-- --      w a b (inv∈ x r) = {!!}
-- --      w a b (norm∈ g h r x) = {!!}



-- -- snd (FromPresHom A P) = {!!}

-- -- FromPresHom⁻ : (A : Type ℓ) (P : ℙ (FreeGroup A)) → GroupHom (Presented P) (FromPres A P)
-- -- fst (FromPresHom⁻ A P) = w

-- --   where
-- --     w : _
-- --     w (η x) = [ η x ]
-- --     w (x · x₁) = {! map2!}
-- --     w ε = {!!}
-- --     w (inv x) = {!!}
-- --     w (assoc x x₁ x₂ i) = {!!}
-- --     w (idr x i) = {!!}
-- --     w (idl x i) = {!!}
-- --     w (invr x i) = {!!}
-- --     w (invl x i) = {!!}
-- --     w (rel x i) = {!!}
-- --     w (trunc x x₁ x₂ y i i₁) = {!!}

-- -- snd (FromPresHom⁻ A P) = {!!}
