{-# OPTIONS --safe  #-}  --experimental-lossy-unification
module Cubical.HITs.ListedFiniteSet.Base2Prim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Functions.Logic
open import Cubical.Foundations.Function

open import Cubical.Foundations.Function

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.Data.FinData.Properties

private
  variable
    ℓ : Level
    A B : Type ℓ




infixr 5 _∷2_


data FMSet2 (A : Type ℓ) : Type ℓ where
  []    : FMSet2 A
  _∷2_   : (x : A) → (xs : FMSet2 A) → FMSet2 A
  comm  : ∀ x y xs → x ∷2 y ∷2 xs ≡ y ∷2 x ∷2 xs
  comm-inv : ∀ x y xs → 
              comm x y xs ≡ sym (comm y x xs)
  hexDiag : ∀ x y z xs → x ∷2 y ∷2 z ∷2  xs ≡ z ∷2 y ∷2 x ∷2 xs
  hexU : ∀ x y z xs →
             Square
               (cong (y ∷2_) (comm _ _ _))
               (hexDiag x y z xs)
               (comm _ _ _)
               (comm _ _ _)
  hexL : ∀ x y z xs →
             Square
               (hexDiag x y z xs)
               (comm _ _ _)
               (cong (x ∷2_) (comm _ _ _))
               (cong (z ∷2_) (comm _ _ _))
  trunc : isGroupoid (FMSet2 A)

comm-invo : ∀ (x y : A) → ∀ xs → 
            comm x y xs ∙ comm _ _ xs ≡ refl
comm-invo x y xs = cong (_∙ comm y x xs) (comm-inv x y xs) ∙ lCancel _


hexUpa : ∀ (x y z : A) → ∀ xs → comm _ _ _ ∙∙ cong (y ∷2_) (comm _ _ _) ∙∙ comm _ _ _ ≡ hexDiag x y z xs
hexUpa x y z xs  =
    cong (_∙∙ cong (y ∷2_) (comm _ _ _) ∙∙ comm _ _ _) (comm-inv _ _ _)
     ◁ λ i j → hcomp (λ k → λ { (i = i1) → hexDiag x y z xs j
                  ; (j = i0) → (hexU x y z xs (i ∨ k) j)
                  ; (j = i1) → (hexU x y z xs (i ∨ k) j)
                  }) (hexU x y z xs i j)

hexLpa : ∀ (x y z : A) → ∀ xs → hexDiag x y z xs ≡ cong (x ∷2_) (comm _ _ _) ∙∙ comm _ _ _ ∙∙ cong (z ∷2_) (comm _ _ _)
hexLpa x y z xs  = 
    (λ i j → hcomp (λ k → λ { (i = i0) → hexDiag x y z xs j
                  ; (j = i0) → (hexL x y z xs (i ∧ ~ k) j)
                  ; (j = i1) → (hexL x y z xs (i ∧ ~ k) j)
                  }) (hexL x y z xs i j))
       ▷ cong (λ p → cong (x ∷2_) (comm _ _ _) ∙∙ comm _ _ _ ∙∙ cong (z ∷2_) p) (sym (comm-inv _ _ _))


comm-braid : ∀ (x y z : A) → ∀ xs →
              comm x y (z ∷2 xs) ∙ cong (y ∷2_) (comm _ _ _) ∙ comm _ _ _
                ≡ cong (x ∷2_) (comm y z xs) ∙ comm x z (y ∷2 xs) ∙ cong (z ∷2_) (comm _ _ _)
comm-braid _ _ _ _ =
  sym (doubleCompPath-elim' _ _ _)
   ∙ (hexUpa _ _ _ _ ∙ hexLpa _ _ _ _)
   ∙ doubleCompPath-elim' _ _ _

module _ {A : Type ℓ} where


  module RecSet {ℓ'} {B : Type ℓ'} (BSet : isSet B)
    ([]* : B) (_∷*_ : A → B → B)
    (comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b))
    (hexDiag* : ∀ x y z b → x ∷* (y ∷* (z ∷* b)) ≡ z ∷* (y ∷* (x ∷* b)) )
    where

    f : FMSet2 A → B
    f [] = []*
    f (x ∷2 x₁) = x ∷* f x₁
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


  module ElimSet {ℓ'} {B : FMSet2 A → Type ℓ'}
    ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs))
    (comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
           → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
    (hexDiag* : (x y z : A) {xs : FMSet2 A} (b : B xs)
           → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b))))
    (trunc* : (xs : FMSet2 A) → isSet (B xs)) where

    f : (xs : FMSet2 A) → B xs
    f [] = []*
    f (x ∷2 xs) = x ∷* f xs
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

  module ElimProp {ℓ'} {B : FMSet2 A → Type ℓ'}
    ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs))    
    (trunc* : (xs : FMSet2 A) → isProp (B xs)) where

    f : (xs : FMSet2 A) → B xs
    f = ElimSet.f
          []*
          _∷*_
          (λ x y b → isProp→PathP (λ _ → trunc* _) _ _)
          (λ x y z b → isProp→PathP (λ _ → trunc* _) _ _)
          (isProp→isSet ∘ trunc*)


  module Elim {ℓ'} {B : FMSet2 A → Type ℓ'}
    ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs))
    (comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
           → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
    (comm-inv* : ∀ x y {xs} (b : B xs) → SquareP (λ i j → B (comm-inv x y xs i j))
                        (comm* x y b ) (symP (comm* y x b))
                        refl refl )
    (hexDiag* : (x y z : A) {xs : FMSet2 A} (b : B xs)
           → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b))))
    (hexU* : ∀ x y z {xs : FMSet2 A} (b : B xs) →
               SquareP
               ((λ i j → B (hexU x y z xs i j)))
                 (congP (λ _ → y ∷*_) (comm* x z b))
                 (hexDiag* x y z b)
                 (comm* _ _ (z ∷* b))
                 (comm* _ _ (x ∷* b))
                  )
    (hexL* : ∀ x y z {xs : FMSet2 A} (b : B xs)  →
               SquareP
                 (λ i j → B (hexL x y z xs i j))
                 (hexDiag* _ _ _ b)
                 (comm* _ _ _)
                 (congP (λ _ → _ ∷*_) (comm* _ _ _))
                 (congP (λ _ → _ ∷*_) (comm* _ _ _))
                  )

    (trunc* : (xs : FMSet2 A) → isGroupoid (B xs)) where

    f : (xs : FMSet2 A) → B xs
    f [] = []*
    f (x ∷2 xs) = x ∷* f xs
    f (comm x y xs i) = comm* x y (f xs) i
    f (comm-inv x y xs i j) =
       comm-inv* x y (f xs) i j
    f (hexDiag x y z xs i) = hexDiag* x y z (f xs) i
    f (hexU x y z xs i j) = hexU* x y z (f xs) i j
    f (hexL x y z xs i j) = hexL* x y z (f xs) i j

    f (trunc xs ys p q r s i j k) =
      isOfHLevel→isOfHLevelDep 3 (λ a → trunc* a)
         _ _ _ _
         (λ j k → f (r j k)) (λ j k → f (s j k)) 
           (trunc xs ys p q r s) i j k


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
    f (x ∷2 x₁) = x ∷* f x₁
    f (comm x y x₁ i) = comm* x y (f x₁) i
    f (comm-inv x y x₁ i i₁) = comm-inv* x y (f x₁) i i₁
    f (hexDiag x y z x₁ i) = hexDiag* x y z (f x₁) i
    f (hexU x y z x₁ i i₁) = hexU* x y z (f x₁) i i₁
    f (hexL x y z x₁ i i₁) = hexL* x y z (f x₁) i i₁
    f (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
       BType _ _ _ _
        (cong (cong f) x₃) (cong  (cong f) y₁) i i₁ x₄



  len2 : FMSet2 A → ℕ
  len2 [] = zero
  len2 (x ∷2 x₁) = suc (len2 x₁)
  len2 (comm x y x₁ i) = suc (suc (len2 x₁))
  len2 (comm-inv x y x₁ i i₁) = suc (suc (len2 x₁))
  len2 (hexDiag x y z x₁ i) = suc (suc (suc (len2 x₁)))
  len2 (hexU x y z x₁ i i₁) = suc (suc (suc (len2 x₁)))
  len2 (hexL x y z x₁ i i₁) = suc (suc (suc (len2 x₁)))
  len2 (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) = 
     (isSet→isGroupoid isSetℕ) _ _ _ _
        (cong (cong len2) x₃) (cong  (cong len2) y₁) i i₁ x₄


  -- paPerm : {xs ys : FMSet2 A} → xs ≡ ys
  --    → EM₁ (SymData (len2 xs))
  -- paPerm {xs} = J (λ ys p → EM₁ (SymData (len2 xs)))
  --    (Elim.f {B = λ xs → EM₁ (SymData (len2 xs))}
  --      embase
  --      (λ _ → gh→em₂→ _ (sucPermFDMorphism _))
  --      (λ x y {xs}
  --        → elimSet (SymData (len2 xs))
  --          (λ _ → emsquash _ _) (emloop swap0and1≃)
  --            λ g → 
  --              ∙≡∙→square
  --              (emloop swap0and1≃)
  --              (emloop (sucPerm (sucPerm g)))                              
  --              (emloop (sucPerm (sucPerm g)))
  --               (emloop swap0and1≃)
  --              {!!}
  --              )

  --      {!!}
  --      {!!}
  --      {!!}
  --      {!!}
  --      (λ _ → emsquash)
  --      xs)

--   inj∷2 : (xs ys : FMSet2 A) → (x : A)
--            → x ∷2 xs ≡ x ∷2 ys → xs ≡ ys
--   inj∷2 = ElimSet.f
--     {!!}
--     -- (ElimSet.f
--     --    (λ _ _ → refl)
--     --    (λ x x₁ x₂ → {!!} ∘ cong len2  )
--     --    {!!}
--     --    {!!}
--     --    λ _ → isSetΠ2 λ _ _ → trunc _ _ )
--     (λ x {xs} b →
--       ElimSet.f
--        {!!}
--        (λ x' {ys} b' y' p →
--          {!!})
--          {!!} {!!}
--         λ _ → isSetΠ2 λ _ _ → trunc _ _)
--     {!!}
--     {!!}
--     λ _ → isSetΠ3 λ _ _ _ → trunc _ _ 

-- -- -- -- Rec.f
-- -- -- --      (isSet→isGroupoid isSetℕ) zero (λ _ → suc)
-- -- -- --        (λ _ _ _ → refl) (λ _ _ _ _ → refl)
-- -- -- --        (λ _ _ _ _ → refl) (λ _ _ _ _ → refl) (λ _ _ _ _ → refl)


-- -- -- -- RecSet.f isSetℕ zero (λ _ → suc) (λ _ _ _ → refl) (λ _ _ _ _ → refl)

-- -- --   -- open import Cubical.HITs.EilenbergMacLane1 as EM

module _ (A : Type ℓ) where
  -- open import Cubical.Data.List.FinData


  FMSet2OfLen : ℕ → Type ℓ
  FMSet2OfLen n = Σ (FMSet2 A) λ x → len2 x ≡ n

module _ {A : Type ℓ} where
  -- isSetLofLA : ∀ n → isSet (ListOfLen A n)
  -- isSetLofLA n = isOfHLevelListOfLen 0 isSetA n 

  FMSet2OfLen≡ : ∀ {n} → {x y : FMSet2OfLen A n} → fst x ≡ fst y → x ≡ y 
  FMSet2OfLen≡ = Σ≡Prop λ _ → isSetℕ _ _

  isGroupoidFMSet2OfLen : ∀ n → isGroupoid (FMSet2OfLen A n)
  isGroupoidFMSet2OfLen n = 
    (isOfHLevelΣ 3 trunc λ _ → isSet→isGroupoid (isProp→isSet (isSetℕ _ _)))

