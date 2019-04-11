{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.FiniteMultiset.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

open import Cubical.HITs.FiniteMultiset.Base

private
  variable
    A : Type

infixr 30 _++_

_++_ : ∀ (xs ys : FMType A) → FMType A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
comm x y xs i ++ ys = comm x y (xs ++ ys) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j

unitl-++ : ∀ (xs : FMType A) → [] ++ xs ≡ xs
unitl-++ xs = refl

unitr-++ : ∀ (xs : FMType A) → xs ++ [] ≡ xs
unitr-++ = FMTypeElimProp.f (trunc _ _)
  refl
  (λ x p → cong (_∷_ x) p)

assoc-++ : ∀ (xs ys zs : FMType A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ = FMTypeElimProp.f (propPi (λ _ → propPi (λ _ → trunc _ _)))
  (λ ys zs → refl)
  (λ x p ys zs → cong (_∷_ x) (p ys zs))

cons-++ : ∀ (x : A) (xs : FMType A) → x ∷ xs ≡ xs ++ [ x ]
cons-++ x = FMTypeElimProp.f (trunc _ _)
  refl
  (λ y {xs} p → comm x y xs ∙ cong (_∷_ y) p)

comm-++ : ∀ (xs ys : FMType A) → xs ++ ys ≡ ys ++ xs
comm-++ = FMTypeElimProp.f (propPi (λ _ → trunc _ _))
  (λ ys → sym (unitr-++ ys))
  (λ x {xs} p ys → cong (x ∷_) (p ys)
                 ∙ cong (_++ xs) (cons-++ x ys)
                 ∙ sym (assoc-++ ys [ x ] xs))

module FMTypeUniversal {ℓ} {M : Type ℓ} (MType : isType M)
  (e : M) (_⊗_ : M → M → M)
  (comm-⊗ : ∀ x y → x ⊗ y ≡ y ⊗ x) (assoc-⊗ : ∀ x y z → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z)
  (unit-⊗ : ∀ x → e ⊗ x ≡ x)
  (f : A → M) where

  f-extend : FMType A → M
  f-extend = FMTypeRec.f MType e (λ x m → f x ⊗ m)
         (λ x y m → comm-⊗ (f x) (f y ⊗ m) ∙ sym (assoc-⊗ (f y) m (f x)) ∙ cong (f y ⊗_) (comm-⊗ m (f x)))

  f-extend-nil : f-extend [] ≡ e
  f-extend-nil = refl

  f-extend-cons : ∀ x xs → f-extend (x ∷ xs) ≡ f x ⊗ f-extend xs
  f-extend-cons x xs = refl

  f-extend-sing : ∀ x → f-extend [ x ] ≡ f x
  f-extend-sing x = comm-⊗ (f x) e ∙ unit-⊗ (f x)

  f-extend-++ : ∀ xs ys → f-extend (xs ++ ys) ≡ f-extend xs ⊗ f-extend ys
  f-extend-++ = FMTypeElimProp.f (propPi λ _ → MType _ _)
    (λ ys → sym (unit-⊗ (f-extend ys)))
    (λ x {xs} p ys → cong (f x ⊗_) (p ys) ∙ assoc-⊗ (f x) (f-extend xs) (f-extend ys))

  module _ (h : FMType A → M) (h-nil : h [] ≡ e) (h-sing : ∀ x → h [ x ] ≡ f x)
           (h-++ : ∀ xs ys → h (xs ++ ys) ≡ h xs ⊗ h ys) where

    f-extend-unique : h ≡ f-extend
    f-extend-unique = funExt (FMTypeElimProp.f (MType _ _)
                              h-nil
                              (λ x {xs} p → (h-++ [ x ] xs) ∙ cong (_⊗ h xs) (h-sing x) ∙ cong (f x ⊗_) p))
