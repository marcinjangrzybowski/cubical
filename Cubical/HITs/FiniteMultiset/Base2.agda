{-# OPTIONS --safe #-}
module Cubical.HITs.FiniteMultiset.Base2 where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetTruncation
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 5 _∷_

data FMSet2 (A : Type ℓ) : Type ℓ where
  []    : FMSet2 A
  _∷_   : (x : A) → (xs : FMSet2 A) → FMSet2 A
  comm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  comm-inv : ∀ x y xs → 
              comm x y xs ≡ sym (comm y x xs)
  hexDiag : ∀ x y z xs → x ∷ y ∷ z ∷  xs ≡ z ∷ y ∷ x ∷ xs
  hexU : ∀ x y z xs →
             Square
               (cong (y ∷_) (comm _ _ _))
               (hexDiag x y z xs)
               (comm _ _ _)
               (comm _ _ _)
  hexL : ∀ x y z xs →
             Square
               (hexDiag x y z xs)
               (comm _ _ _)
               (cong (x ∷_) (comm _ _ _))
               (cong (z ∷_) (comm _ _ _))
  trunc : isGroupoid (FMSet2 A)


pattern [_] x = x ∷ []


_++_ : ∀ {ℓ} {A : Type ℓ} → FMSet2 A → FMSet2 A → FMSet2 A
[] ++ y = y
(x ∷ x₁) ++ y = x ∷ x₁ ++ y
comm x y₁ x₁ i ++ y = comm x y₁ (x₁ ++ y) i
comm-inv x₁ y x₂ i i₁ ++ x = comm-inv x₁ y (x₂ ++ x) i i₁
hexDiag x y₁ z x₁ i ++ y = hexDiag x y₁ z (x₁ ++ y) i
hexU x y₁ z x₁ i i₁ ++ y = hexU x y₁ z (x₁ ++ y) i i₁
hexL x y₁ z x₁ i i₁ ++ y = hexL x y₁ z (x₁ ++ y) i i₁
trunc x x₁ x₂ y₁ x₃ y₂ i i₁ i₂ ++ y =
  trunc _ _ _ _
        (cong (cong (_++ y)) x₃) (cong (cong (_++ y)) y₂)
        i i₁ i₂ 


module ElimSet {ℓ'} {B : FMSet2 A → Type ℓ'}
  ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷ xs))
  (comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
         → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
  (hexDiag* : (x y z : A) {xs : FMSet2 A} (b : B xs)
         → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b))))
  (trunc* : (xs : FMSet2 A) → isSet (B xs)) where

  f : (xs : FMSet2 A) → B xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (comm x y xs i) = comm* x y (f xs) i
  f (comm-inv x y xs i j) =
     isOfHLevel→isOfHLevelDep 2 trunc*
         (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
         (comm* x y (f xs)) (symP (comm* y x (f xs)))
         (comm-inv x y xs) i j
  f (hexDiag x y z xs i) = hexDiag* x y z (f xs) i
  f (hexU x y z xs i j) =
    isSet→SquareP 
       (λ i j → trunc* (hexU x y z xs i j))
       (λ j → y ∷* comm* x z (f xs) j)
       (hexDiag* x y z (f xs))
       (comm* y x (z ∷* f xs))
       (comm* y z (x ∷* f xs)) i j
  f (hexL x y z xs i j) =
       isSet→SquareP 
       (λ i j → trunc* (hexL x y z xs i j))
       (hexDiag* x y z (f xs))
       (comm* x z (y ∷* f xs))
       (λ i₁ → x ∷* comm* y z (f xs) i₁)
       (λ i₁ → z ∷* comm* y x (f xs) i₁) i j
  f (trunc xs zs p q r s i j k) =
      isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
          _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k

module Rec {ℓ'} {B : Type ℓ'} (BType : isGroupoid B)
  ([]* : B) (_∷*_ : A → B → B)
  (comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b))
  (comm-inv* : ∀ x y b → comm* x y b ≡ sym (comm* y x b) )
  (hexDiag* : ∀ x y z b → x ∷* (y ∷* (z ∷* b)) ≡ z ∷* (y ∷* (x ∷* b)) )
  (hexU* : ∀ x y z b →
             Square (cong (_ ∷*_) (comm* _ _ b)) (hexDiag* x y z b)
                    (comm* _ _ _) (comm* _ _ _))
  (hexL* : ∀ x y z b →
             Square (hexDiag* x y z b) (comm* _ _ _)
                    (cong (_ ∷*_) (comm* _ _ b)) (cong (_ ∷*_) (comm* _ _ b)))

  where

  f : FMSet2 A → B
  f [] = []*
  f (x ∷ x₁) = x ∷* f x₁
  f (comm x y x₁ i) = comm* x y (f x₁) i
  f (comm-inv x y x₁ i i₁) = comm-inv* x y (f x₁) i i₁
  f (hexDiag x y z x₁ i) = hexDiag* x y z (f x₁) i
  f (hexU x y z x₁ i i₁) = hexU* x y z (f x₁) i i₁
  f (hexL x y z x₁ i i₁) = hexL* x y z (f x₁) i i₁
  f (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
     BType _ _ _ _
      (cong (cong f) x₃) (cong  (cong f) y₁) i i₁ x₄

module RecSet {ℓ'} {B : Type ℓ'} (BSet : isSet B)
  ([]* : B) (_∷*_ : A → B → B)
  (comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b))
  (hexDiag* : ∀ x y z b → x ∷* (y ∷* (z ∷* b)) ≡ z ∷* (y ∷* (x ∷* b)) )
  where

  f : FMSet2 A → B
  f [] = []*
  f (x ∷ x₁) = x ∷* f x₁
  f (comm x y x₁ i) = comm* x y (f x₁) i
  f (comm-inv x y x₁ i i₁) =
      isSet→isSet' BSet
        (comm* x y (f x₁))
        (sym (comm* y x (f x₁)))
        refl
        refl i i₁
  f (hexDiag x y z x₁ i) = hexDiag* x y z (f x₁) i
  f (hexU x y z x₁ i i₁) =
      isSet→isSet' BSet
        (λ i₂ → y ∷* comm* x z (f x₁) i₂)
        (λ i₂ → hexDiag* x y z (f x₁) i₂)
        (λ i₂ → comm* y x (z ∷* f x₁) i₂)
        (λ i₂ → comm* y z (x ∷* f x₁) i₂)
        i i₁
  f (hexL x y z xs i i₁) =
       isSet→isSet' BSet
       (hexDiag* x y z (f xs))
       (comm* x z (y ∷* f xs))
       (λ i₁ → x ∷* comm* y z (f xs) i₁)
       (λ i₁ → z ∷* comm* y x (f xs) i₁)
        i i₁
  f (trunc x y p r g h i i₁ i₂) =
    isSet→isGroupoid BSet _ _ _ _
     (λ i j → f (g i j)) (λ i j → f (h i j))
       i i₁ i₂
