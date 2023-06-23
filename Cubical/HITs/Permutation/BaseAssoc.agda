{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.BaseAssoc where

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
open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
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

-- infix 20 ⌞_⌟_⌟

-- record AdjacentBundles (n : ℕ) : Type₀ where
--  constructor ⌞_⌟_⌟
--  field
--   k⌞' k⌟' l⌟' : ℕ
--   k⌞≤k⌟ : k⌞' ≤ k⌟'
--   k⌟<l⌟ : k⌟' < l⌟' 
--   l⌟<n : l⌟' < n

--  k⌞ k⌟ l⌟ : Fin n
--  k⌞ = k⌞' , ≤<-trans {n = n} k⌞≤k⌟ (<-trans {n = n} k⌟<l⌟ l⌟<n)
--  k⌟ = k⌟' , <-trans {n = n} k⌟<l⌟ l⌟<n
--  l⌟ = _ , l⌟<n




record AdjacentBundles (n : ℕ) : Type₀ where
 constructor 𝕒𝕓
 field
  lPad l r rPad : ℕ
  <n : (l + r) + ((lPad + rPad) + 2) ≡ n

sucAB : ∀ {n} → AdjacentBundles n → AdjacentBundles (suc n)
AdjacentBundles.lPad (sucAB x) = suc (AdjacentBundles.lPad x)
AdjacentBundles.l (sucAB x) = AdjacentBundles.l x
AdjacentBundles.r (sucAB x) = AdjacentBundles.r x
AdjacentBundles.rPad (sucAB x) = AdjacentBundles.rPad x
AdjacentBundles.<n (sucAB x) = 
   +-suc _ _ ∙ cong suc (AdjacentBundles.<n x)

swapAB : ∀ {n} → AdjacentBundles n → AdjacentBundles n
swapAB (𝕒𝕓 lPad l r rPad <n) =
  𝕒𝕓 lPad r l rPad (cong (_+ (lPad + rPad + 2)) (+-comm r l) ∙ <n)

swapAB' : ∀ {n} → (x : AdjacentBundles n) → _ → AdjacentBundles n
swapAB' (𝕒𝕓 lPad l r rPad <n) p =
  𝕒𝕓 lPad r l rPad p

swapAB-invol : ∀ {n} → isInvolution (swapAB {n})
swapAB-invol {n} = w
 where
 open AdjacentBundles
 w : isInvolution swapAB
 lPad (w (𝕒𝕓 x _ _ _ _) i) = x
 l (w (𝕒𝕓 _ x _ _ _) i) = x
 r (w (𝕒𝕓 _ _ x _ _) i) = x
 rPad (w (𝕒𝕓 _ _ _ x _) i) = x
 <n (w x@(𝕒𝕓 _ _ _ _ p) i) j =
   isSet→isSet' isSetℕ
     (<n (swapAB (swapAB x))) p refl refl i j

swapAB≃ : ∀ {n} → (AdjacentBundles n) ≃ (AdjacentBundles n)
swapAB≃ = involEquiv {f = swapAB} swapAB-invol

data ℙrmₐ {trunc : Bool} (n : ℕ) : Type₀ where 
  𝕡base : ℙrmₐ n
  
  𝕡loop : AdjacentBundles n → 𝕡base ≡ 𝕡base

  𝕡invol : ∀ ab p → 𝕡loop (swapAB' ab p) ≡ sym (𝕡loop ab)
  𝕡hex : ∀ lPad rPad l c r → ∀ p p' p'' →
     Square {A = ℙrmₐ {trunc} n}
       (𝕡loop (𝕒𝕓 lPad l c (r + rPad) p''))       
       (𝕡loop (𝕒𝕓 (c + lPad) l r rPad p'))
       refl
       (𝕡loop (𝕒𝕓 lPad l (c + r) rPad p))
  𝕡comm :
      ∀ lPad rPad l r l' r' → ∀ p p' →
     Square {A = ℙrmₐ {trunc} n}
       (𝕡loop (𝕒𝕓 lPad l r ((l' + r') + rPad) p'))       
       (𝕡loop (𝕒𝕓 lPad l r ((l' + r') + rPad) p'))
       (𝕡loop (𝕒𝕓 ((l + r) + lPad) l' r' rPad p))
       (𝕡loop (𝕒𝕓 ((l + r) + lPad) l' r' rPad p))

  𝕡over : ∀ lPad rPad l x x' → ∀ p p' p'' →
     Square {A = ℙrmₐ {trunc} n}
       (𝕡loop (𝕒𝕓 (l + lPad) x x' rPad p'))       
       (𝕡loop (𝕒𝕓 lPad x' x (l + rPad) p''))
       (𝕡loop (𝕒𝕓 lPad l (x' + x) rPad p))
       (𝕡loop (𝕒𝕓 lPad l (x' + x) rPad p))


  𝕡squash : Bool→Type trunc → isGroupoid (ℙrmₐ n)

sucℙrmₐ : {trunc : Bool} (n : ℕ) → ℙrmₐ {trunc} n → ℙrmₐ {trunc} (suc n)
sucℙrmₐ n 𝕡base = 𝕡base
sucℙrmₐ n (𝕡loop x i) = 𝕡loop (sucAB x) i
sucℙrmₐ n (𝕡invol ab p i i₁) =
  𝕡invol (sucAB ab) ((+-suc _ _
          ∙ (λ i₂ → suc (AdjacentBundles.<n (swapAB' ab p) i₂)))) i i₁
sucℙrmₐ n (𝕡hex lPad rPad l c r p p' p'' i i₁) = {!!}
sucℙrmₐ n (𝕡comm lPad rPad l r l' r' p p' i i₁) = {!!}
sucℙrmₐ n (𝕡over lPad rPad l x x' p p' p'' i i₁) = {!!}
sucℙrmₐ n (𝕡squash x x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) = {!!}

adjTrAB : {n : ℕ} → (Σ ℕ  λ k → (suc k < n)) → AdjacentBundles n
AdjacentBundles.lPad (adjTrAB (k , _)) = k
AdjacentBundles.l (adjTrAB (_ , _)) = zero
AdjacentBundles.r (adjTrAB (_ , _)) = zero
AdjacentBundles.rPad (adjTrAB {n} (k , _)) = n ∸ (suc (suc k)) 
AdjacentBundles.<n (adjTrAB {n} (k , k<)) = ∸<≡' {k} {n} k<

toₐR : ∀ n {trunc} → B.R𝕡rec {n = n} (ℙrmₐ {trunc} n)
B.R𝕡rec.abase (toₐR n) = 𝕡base
  -- 
B.R𝕡rec.aloop (toₐR (suc n)) (suc k , k<) =
   cong (sucℙrmₐ n) (B.R𝕡rec.aloop (toₐR (n)) (k , k<))
B.R𝕡rec.aloop (toₐR (suc (suc n))) (zero , k<) =
  𝕡loop (𝕒𝕓 zero zero zero n (+-comm n 2))

B.R𝕡rec.alooop (toₐR (suc n)) (suc k , k<) (suc l , l<) = 
  cong (sucℙrmₐ n) (B.R𝕡rec.alooop (toₐR (n)) (k , k<) (l , l<))
B.R𝕡rec.alooop (toₐR (suc (suc n))) (zero , k<) (zero , tt) = refl
B.R𝕡rec.alooop (toₐR (suc (suc n))) (suc (suc k) , k<) (zero , tt) =
  sym (𝕡loop (adjTrAB ((suc (suc k) , k<))))
   ∙∙ refl ∙∙
   𝕡loop (adjTrAB (zero , _))

B.R𝕡rec.alooop (toₐR (suc (suc (suc n)))) (suc zero , tt) (zero , tt) = 
   𝕡loop (𝕒𝕓 zero 1 zero n (cong suc (+-comm n 2)))

B.R𝕡rec.alooop (toₐR (suc (suc n))) (zero , tt) (suc (suc l) , l<) =
  sym (𝕡loop (adjTrAB (zero , _)))
   ∙∙ refl ∙∙
   𝕡loop (adjTrAB ((suc (suc l) , l<)))


B.R𝕡rec.alooop (toₐR (suc (suc (suc n)))) (zero , k<) (suc zero , l<) =
  𝕡loop (𝕒𝕓 zero zero 1 n (cong suc (+-comm n 2)))


B.R𝕡rec.acomp (toₐR (suc (suc n)) {t}) (suc k , k<) (suc l , l<) = 
  congSq (sucℙrmₐ {t} (suc n)) (B.R𝕡rec.acomp (toₐR (suc n)) (k , k<) (l , l<))
B.R𝕡rec.acomp (toₐR (suc (suc n))) (zero , k<) (zero , tt) = refl
B.R𝕡rec.acomp (toₐR (suc (suc n))) (suc (suc k) , k<) (zero , tt) =
  ?
  -- {!!} ◁ flipSquare (symP (doubleCompPath-filler
  --    (sym (𝕡loop (adjTrAB (suc (suc k) , k<))))
  --     refl
  --     (𝕡loop (adjTrAB (zero , _))))) ▷ {!!}
  -- flipSquare ( {!(doubleCompPath-filler ? refl ?)!})

B.R𝕡rec.acomp (toₐR (suc (suc (suc n)))) (suc zero , tt) (zero , tt) = 
   {!!}

B.R𝕡rec.acomp (toₐR (suc (suc n))) (zero , tt) (suc (suc l) , l<) =
  {!!}


B.R𝕡rec.acomp (toₐR (suc (suc (suc n)))) (zero , k<) (suc zero , l<) =
  {!!}



B.R𝕡rec.ainvol (toₐR n) k = {!!}
 -- 𝕡invol (adjTrAB {n} k) (AdjacentBundles.<n (adjTrAB k))
B.R𝕡rec.acomm (toₐR n) = {!!}
B.R𝕡rec.abraid (toₐR n) = {!!}
 

-- toₐ : {trunc : Bool} (n : ℕ) → B.ℙrm {trunc} n → ℙrmₐ {trunc} n
-- toₐ =

-- .f {!!} {!!} {!!}
-- toₐ n B.𝕡base = 𝕡base
-- toₐ n (B.𝕡loop x i) = 𝕡loop (adjTrAB x) i
-- toₐ n (B.𝕡looop k l i) = {!!}
-- toₐ n (B.𝕡comp k l i i₁) = {!!}
-- toₐ n (B.𝕡invol k i i₁) = 𝕡invol (adjTrAB k) (~ i) i₁
-- toₐ n (B.𝕡comm k l x i i₁) = {!!}
-- toₐ n (B.𝕡braid k k< i i₁) = {!!}
-- toₐ n (B.𝕡squash x x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) = {!!}
