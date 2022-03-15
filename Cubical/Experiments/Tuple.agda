{-

An experiment of transporting rev-++-distr from lists to lists where
the arguments to cons have been flipped inspired by section 2 of
https://arxiv.org/abs/2010.00774

Note that Agda doesn't care about the order of constructors so we
can't do exactly the same example.

-}
{-# OPTIONS --safe #-}
module Cubical.Experiments.Tuple where

open import Cubical.Foundations.Everything

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Prod
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Nat

-- open import Cubical.Experiments.List



TupleP : List (Type₀) → Type₀
TupleP [] = Unit
TupleP (x ∷ x₁) = x × TupleP x₁

lookoupTy : List (Type₀) → ℕ → Type₀
lookoupTy [] x₁ = Unit
lookoupTy (x ∷ x₂) zero = x
lookoupTy (x ∷ x₂) (suc x₁) = lookoupTy x₂ x₁

IsoSecProd : ∀ l → Iso (TupleP l) (∀ x → lookoupTy l x) 
Iso.fun (IsoSecProd []) _ _ = _
Iso.inv (IsoSecProd []) _ = _
Iso.rightInv (IsoSecProd []) _ = funExt λ _ → refl
Iso.leftInv (IsoSecProd []) _ = refl
Iso.fun (IsoSecProd (x ∷ l)) x₁ zero = proj₁ x₁
Iso.fun (IsoSecProd (x ∷ l)) x₁ (suc x₂) = Iso.fun (IsoSecProd l) (proj₂ x₁) x₂
Iso.inv (IsoSecProd (x ∷ l)) x₁ = x₁ zero , Iso.inv (IsoSecProd l) (x₁ ∘ suc) 
Iso.rightInv (IsoSecProd (x ∷ l)) b i zero = b zero
Iso.rightInv (IsoSecProd (x ∷ l)) b i (suc x₁) = Iso.rightInv (IsoSecProd l) (b ∘ suc) i x₁
Iso.leftInv (IsoSecProd (x ∷ l)) (x₁ , x₂) = cong (x₁ ,_) (Iso.leftInv (IsoSecProd l) x₂)






module _ (A : Type₀) (isSet-A : isSet A) where

  data Tree : Type₀ where
    leaf : A → Tree
    _no_ : Tree → Tree → Tree



  toList : Tree → List A
  toList (leaf x) = [ x ]
  toList (x no x₁) = toList x ++ toList x₁

  -- data Tree' : Type₀
  infixr 35 _no_

  data Tree' : Type₀ where
    leaf : A → Tree'
    _no_ : Tree' → Tree' → Tree'
    lrPa : ∀ {x y z} → 
             (x no y) no z ≡ x no y no z
    trunc : isSet Tree'

  toList' : Tree' → List A
  toList' (leaf x) = [ x ]
  toList' (x no x₁) = toList' x ++ toList' x₁
  toList' (lrPa {x} {y} {z} i) = ++-assoc (toList' x) (toList' y) (toList' z) i
  toList' (trunc x x₁ x₂ y i i₁) = (isOfHLevelList 0 isSet-A) (toList' x) ((toList' x₁)) (cong (toList') x₂) ((cong (toList') y)) i i₁
  
-- module _ (A : Type₀) where


--   toListInj : ∀ a b → toList a ≡ toList b → a ≡ b
--   toListInj (leaf x₁) (leaf x₂) x = cong leaf (cons-inj₁ x)
--   toListInj (leaf x₁) (b no b₁) x = {!!}
--   toListInj (leaf x₁) (lrPa x₂ x₃ x₄ i) x = {!!}
--   toListInj (a no a₁) (leaf x₁) x = {!!}
--   toListInj (a no a₁) (b no b₁) x = {!!}
--   toListInj (a no a₁) (lrPa x₁ x₂ x₃ i) x = {!!}
--   toListInj (lrPa x₁ x₂ x₃ i) (leaf x₄) x = {!!}
--   toListInj (lrPa x₁ x₂ x₃ i) (b no b₁) x = {!!}
--   toListInj (lrPa x₁ x₂ x₃ i) (lrPa x₄ x₅ x₆ i₁) x = {!!}


--   -- IsoTree : Iso (A × List A) (Tree' A)  
--   -- Iso.fun IsoTree = {!!}
--   -- Iso.inv IsoTree = {!!}
--   -- Iso.rightInv IsoTree = {!!}
--   -- Iso.leftInv IsoTree = {!!}
