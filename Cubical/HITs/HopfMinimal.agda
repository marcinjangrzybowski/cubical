{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.HopfMinimal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Equiv

data Susp {ℓ} (A : Set ℓ) : Set ℓ where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south

data S¹ : Set where
  base : S¹
  loop : base ≡ base

data join {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  inl : A → join A B
  inr : B → join A B
  push : ∀ a b → inl a ≡ inr b

rotLoop : (a : S¹) → a ≡ a
rotLoop base       = loop
rotLoop (loop i) j =
  hcomp (λ k → λ { (i = i0) → loop (j ∨ ~ k)
                 ; (i = i1) → loop (j ∧ k)
                 ; (j = i0) → loop (i ∨ ~ k)
                 ; (j = i1) → loop (i ∧ k)}) base

rot : S¹ → S¹ → S¹
rot base x     = x
rot (loop i) x = rotLoop x i

_*_ : S¹ → S¹ → S¹
a * b = rot a b

infixl 30 _*_

inv : S¹ → S¹
inv base = base
inv (loop i) = loop (~ i)

rotInv : (a b : S¹) → b * a * inv b ≡ a
rotInv base base i = base
rotInv base (loop k) i =
  hcomp (λ l → λ { (k = i0) → loop (i ∧ ~ l)
                 ; (k = i1) → base
                 ; (i = i0) → loop k * loop (~ k)
                 ; (i = i1) → loop (~ k ∧ ~ l) })
        (loop (k ∨ i) * loop (~ k))
rotInv (loop j) base i = loop j
rotInv (loop j) (loop k) i =
  hcomp (λ l → λ { (k = i0) → loop (i ∧ ~ l) * loop j
                 ; (k = i1) → loop j
                 ; (i = i0) → loop k * loop j * loop (~ k)
                 ; (i = i1) → loop (~ k ∧ ~ l) * loop j })
        (loop (k ∨ i) * loop j * loop (~ k))

isPropFamS¹ : ∀ {ℓ} (P : S¹ → Set ℓ) (pP : (x : S¹) → isProp (P x)) (b0 : P base) →
              PathP (λ i → P (loop i)) b0 b0
isPropFamS¹ P pP b0 i = pP (loop i) (transp (λ j → P (loop (i ∧ j))) (~ i) b0)
                                    (transp (λ j → P (loop (i ∨ ~ j))) i b0) i

rotIsEquiv : (a : S¹) → isEquiv (rot a)
rotIsEquiv base = idIsEquiv S¹
rotIsEquiv (loop i) = isPropFamS¹ (λ x → isEquiv (rot x))
                                  (λ x → isPropIsEquiv (rot x))
                                  (idIsEquiv _) i

HopfSuspS¹ : Susp S¹ → Set
HopfSuspS¹ north = S¹
HopfSuspS¹ south = S¹
HopfSuspS¹ (merid x i) =
  Glue S¹ (λ { (i = i0) → S¹ , rot x , rotIsEquiv x ; (i = i1) → S¹ , idEquiv S¹ })

TotalHopf→JoinS¹S¹ : (x : Susp S¹) → HopfSuspS¹ x → join S¹ S¹
TotalHopf→JoinS¹S¹ north x = inl x
TotalHopf→JoinS¹S¹ south x = inr x
TotalHopf→JoinS¹S¹ (merid y j) x =
  hcomp (λ t → λ { (j = i0) → inl (rotInv x y t)
                 ; (j = i1) → inr x })
        (push (unglue (j ∨ ~ j) x * inv y) (unglue (j ∨ ~ j) x) j)
