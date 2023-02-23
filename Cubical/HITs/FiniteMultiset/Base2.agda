{-# OPTIONS --safe #-}
module Cubical.HITs.FiniteMultiset.Base2 where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetTruncation
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Data.Nat renaming (zero to ℕzero ; suc to ℕsuc
                                      ;znots to ℕznots ; snotz to  ℕsnotz; elim to ℕelim)

open import Cubical.Data.Empty as ⊥

open import Cubical.Data.FinData

open import Cubical.Algebra.SymmetricGroup

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Homotopy.Group.Base

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


comm² : ∀ (x y : A) → ∀ xs → 
           comm x y xs ∙ comm y x xs ≡ refl
comm² x y xs i j =
  hcomp (λ k → λ { (j = i0) → x ∷ y ∷ xs
                 ; (j = i1) → comm y x xs k
                 ; (i = i1) → comm y x xs (~ (j ∧ ~ k)) })
                 (comm-inv x y xs i j)

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


module ElimProp {ℓ'} {B : FMSet2 A → Type ℓ'}
  ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷ xs))
  (trunc* : (xs : FMSet2 A) → isProp (B xs)) where

  f : (xs : FMSet2 A) → B xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (comm x y xs i) = isProp→PathP (λ i → trunc* (comm x y xs i)) (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs)) i
  f (comm-inv x y xs i i₁) = {!!}
  f (hexDiag x y z xs i) = {!!}
  f (hexU x y z xs i i₁) = {!!}
  f (hexL x y z xs i i₁) = {!!}
  f (trunc xs xs₁ x y x₁ y₁ i i₁ x₂) = {!!}
  
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

lengthFM2 : FMSet2 A → ℕ
lengthFM2 =
  RecSet.f isSetℕ
    ℕzero (λ _ → ℕsuc) (λ _ _ _ → refl) λ _ _ _ _ → refl


swapHead : (x : FMSet2 A) → singl x
swapHead = ElimProp.f (_ , refl)
   (λ x {xs} _ →
     ElimProp.f {B = λ xs → singl (x ∷ xs)}
        (_ , refl)
        (λ y {xs} _ → (y ∷ x ∷ xs) , comm _ _ _)
        (λ _ → isContr→isProp (isContrSingl _))
        xs)
   λ _ → isContr→isProp (isContrSingl _)

swapHeadInvo : ∀ x → singl (snd (swapHead {A = A} x) ∙ snd (swapHead (fst (swapHead x))))
swapHeadInvo =
  ElimProp.f
    (refl , (sym (compPathRefl)))
    (λ x {xs} _ →
      ElimProp.f (refl , (sym (compPathRefl))) (λ y {xs} _ → refl , comm² _ _ _)
        (λ xs →  isContr→isProp (isContrSingl (
          (snd (swapHead (x ∷ xs)) ∙
           snd (swapHead (fst (swapHead (x ∷ xs)))))))) xs)
    λ _ → isContr→isProp (isContrSingl _)

mapTail : ((xs : FMSet2 A) → singl xs) → (xs : FMSet2 A) → singl xs  
mapTail f =
   ElimProp.f (_ , refl)
   (λ x {xs} _ →
     _ , cong (x ∷_) (snd (f xs)))
   λ _ → isContr→isProp (isContrSingl _)



insertAt' : (x : A) → (xs : FMSet2 A) → Fin (lengthFM2 (xs)) → singl (x ∷ xs) 
insertAt' x =
  ElimProp.f
    (⊥.elim ∘ ¬Fin0)
    (λ y {xs} f → λ { zero → _ , (comm _ _ _)
                    ; (suc k) → _ , comm _ _ _ ∙ cong (y ∷_) (snd (f k)) })
    λ _ → isPropΠ λ _ → isContr→isProp (isContrSingl _)


transpositionFM2 : (x x' : A) → (xs : FMSet2 A) → (k : Fin (lengthFM2 (xs)))
            → x ∷ (fst (insertAt' x' xs k)) ≡
             x' ∷ (fst (insertAt' x xs k)) 
transpositionFM2 x x' xs k =
  cong (x ∷_) (sym (snd (insertAt' x' xs k)))
  ∙∙ comm _ _ _ ∙∙
  cong (x' ∷_)  (snd (insertAt' x xs k))

transpositionFM2Invo : (x x' : A) → (xs : FMSet2 A) → (k : Fin (lengthFM2 (xs)))
     → transpositionFM2 x x' xs k ≡ sym (transpositionFM2 x' x xs k)
transpositionFM2Invo x x' xs k =
  cong (cong (x ∷_) (sym (snd (insertAt' x' xs k)))
    ∙∙_∙∙ cong (x' ∷_)  (snd (insertAt' x xs k)))
    (comm-inv _ _ _)

_++2_ : FMSet2 A → FMSet2 A → FMSet2 A
_++2_ = {!Rec.f ?!}

-- permPath : (xs : FMSet2 A)
-- permPath = {!!}

-- permPath : (xs : FMSet2 A) → GroupHom
--                                  (SymData (lengthFM2 (xs)))
--                                  (πGr 0 (_ , xs))
-- permPath xs = {!!}


  -- (cong (x ∷_) (sym (snd (insertAt' x' xs k)))
  -- ∙∙ comm _ _ _ ∙∙
  -- cong (x' ∷_)  (snd (insertAt' x xs k))) ≡⟨ {!!} ⟩
  --  (cong (x ∷_) ((sym (snd (insertAt' x' xs k))))
  -- ∙∙ sym (comm _ _ _) ∙∙
  -- cong (x' ∷_) ((snd (insertAt' x xs k)))) ∎

-- insertAt : (x : A) → (xs : FMSet2 A) → Fin (ℕsuc (lengthFM2 (xs))) → singl (x ∷ xs) 
-- insertAt x =
--   ElimProp.f
--     (λ _ → _ , refl )
--     {!!}
--     λ _ → isPropΠ λ _ → isContr→isProp (isContrSingl _)


-- transposeHeadFM2 : ℕ → (x : FMSet2 A) → singl x


-- transposeHeadFM2' : ℕ → (x y : A) → (xs : FMSet2 A) → singl (x ∷ y ∷ xs)
-- transposeHeadFM2' ℕzero _ _ _ = _ , refl
-- transposeHeadFM2' one _ _ _ = _ , comm _ _ _
-- transposeHeadFM2' (ℕsuc (ℕsuc k)) x y xs =
--   -- let --x = x ∷ y ∷ xs
--   --     -- (x' , p) = swapHead x
--   --     -- (x'' , p') = mapTail (transposeHeadFM2 (ℕsuc k)) x'
--   --     -- (x''' , p'') = swapHead x''
--   -- in
--   _ , (comm _ _ _ ∙∙
--     cong (y ∷_) (snd (transposeHeadFM2 (ℕsuc k) (x ∷ xs)))
--      ∙∙ snd (swapHead _))

-- transposeHeadFM2 k =
--   ElimProp.f (_ , refl)
--      (λ x {xs} _ →
--      ElimProp.f {B = λ xs → singl (x ∷ xs)}
--         (_ , refl)
--         (λ y {xs} _ → transposeHeadFM2' k x y xs)
--         (λ _ → isContr→isProp (isContrSingl _))
--         xs)
--    λ _ → isContr→isProp (isContrSingl _)


-- -- transposeHeadFM2 : ℕ → (x : FMSet2 A) → singl x


-- -- transposeHeadFM2 : ℕ → (x : FMSet2 A) → singl x
-- -- transposeHeadFM2 ℕzero _ = _ , refl
-- -- transposeHeadFM2 one = swapHead
-- -- transposeHeadFM2 (ℕsuc (ℕsuc k)) x =
-- --   {!!}
-- --   -- let (x' , p) = swapHead x
-- --   --     (x'' , p') = mapTail (transposeHeadFM2 (ℕsuc k)) x'
-- --   --     (x''' , p'') = swapHead x''
-- --   -- in _ , p ∙ p' ∙ p''

-- -- transposeHeadPathInvo : ∀ k → ∀ x →
-- --    singl ((snd (transposeHeadFM2 {A = A} k x)) ∙ snd (transposeHeadFM2 k (fst (transposeHeadFM2 k x))))
-- -- transposeHeadPathInvo ℕzero x = refl , sym (compPathRefl)
-- -- transposeHeadPathInvo one = swapHeadInvo
-- -- transposeHeadPathInvo (ℕsuc (ℕsuc k)) =
-- --   ElimProp.f
-- --   (refl , {!!})
-- --     -- cong₂ _∙_ (cong (refl ∙_) (sym (compPathRefl)) )
-- --     -- ((cong (refl ∙_) (sym (compPathRefl)) )) ∙
-- --     --   {!cong (refl ∙_) ?!} ∙ (sym compPathRefl))
-- --     --(cong₂ _∙_ {!!} {!sym (compPathRefl)!} ∙ sym (compPathRefl)))
-- --   (λ x {xs} →
-- --     ElimProp.f {B = λ xs →
-- --       singl
-- --          (snd (transposeHeadFM2 (ℕsuc (ℕsuc k)) xs) ∙
-- --           snd
-- --           (transposeHeadFM2 (ℕsuc (ℕsuc k))
-- --            (fst (transposeHeadFM2 (ℕsuc (ℕsuc k)) xs)))) →
-- --          singl
-- --          (snd (transposeHeadFM2 (ℕsuc (ℕsuc k)) (x ∷ xs)) ∙
-- --           snd
-- --           (transposeHeadFM2 (ℕsuc (ℕsuc k))
-- --            (fst (transposeHeadFM2 (ℕsuc (ℕsuc k)) (x ∷ xs)))))}
-- --      (λ z → {!!} , {!!}) {!!} {!!} xs)
-- --   λ _ → isContr→isProp (isContrSingl _)





-- --   -- let xC = fst ((mapTail (transposeHeadFM2 (ℕsuc k)) (fst (swapHead x))))
-- --   -- in
-- --   --   {!!} , cong (((snd (transposeHeadFM2 (ℕsuc (ℕsuc k)) x))) ∙_) (assoc _ _ _)
-- --   --     ∙ sym (assoc _ _ _) ∙
-- --   --      cong (snd (swapHead x) ∙_) ( (assoc _ _ _)
-- --   --        ∙ cong (_∙ (snd (swapHead _)))
-- --   --            ( sym (assoc _ _ _) ∙
-- --   --              cong (snd (mapTail (transposeHeadFM2 (ℕsuc k)) (fst (swapHead x))) ∙_)
-- --   --                (assoc _ _ _ ∙
-- --   --                  cong 
-- --   --                   (_∙ snd (mapTail (transposeHeadFM2 (ℕsuc k))
-- --   --                    (fst (swapHead ((fst (transposeHeadFM2 (ℕsuc (ℕsuc k)) x)))))))
-- --   --                    (snd (swapHeadInvo _)))
-- --   --                     ∙ {!!}))
-- --   --       ∙ {!!}







-- -- -- punchHeadIn : ℕ → (x : FMSet2 A) → singl x
-- -- -- punchHeadIn ℕzero _ = _ , refl
-- -- -- punchHeadIn one = swapHead
-- -- -- punchHeadIn (ℕsuc (ℕsuc k)) x =
-- -- --   let (x' , p) = swapHead x
-- -- --       (x'' , p') = mapTail (punchHeadIn (ℕsuc k)) x'
-- -- --   in x'' , p ∙ p'

-- -- -- punchHeadOut : ℕ → (x : FMSet2 A) → singl x
-- -- -- punchHeadOut ℕzero _ = _ , refl
-- -- -- punchHeadOut one = swapHead
-- -- -- punchHeadOut (ℕsuc (ℕsuc k)) x =
-- -- --   let (x' , p) = mapTail (punchHeadOut (ℕsuc k)) x
-- -- --       (x'' , p') = swapHead x'
-- -- --   in x'' , p ∙ p'


-- -- -- transposeHeadFM2 : ℕ → (x : FMSet2 A) → singl x
-- -- -- transposeHeadFM2 ℕzero _ = _ , refl
-- -- -- transposeHeadFM2 (ℕsuc n) x =
-- -- --   let (x' , p) = punchHeadIn (ℕsuc n) x
-- -- --       (x'' , p') = mapTail (punchHeadOut n) x'
-- -- --   in x'' , p ∙ p'


-- -- -- transposeHeadPathInvo : ∀ k → ∀ x →
-- -- --    singl ((snd (transposeHeadFM2 {A = A} k x)) ∙ snd (transposeHeadFM2 k (fst (transposeHeadFM2 k x))))
-- -- -- transposeHeadPathInvo ℕzero x = refl , sym (compPathRefl)
-- -- -- transposeHeadPathInvo one =
-- -- --   ElimProp.f
-- -- --     (refl , {!!})
-- -- --           (λ x x₁ → {!!})
-- -- --     {!!}
-- -- -- transposeHeadPathInvo (ℕsuc (ℕsuc k)) = {!!}


-- -- -- -- transposeHeadPathInvo : ∀ k → ∀ x → x ≡ fst (transposeHeadFM2 {A = A} k (fst (transposeHeadFM2 k x)))
-- -- -- -- transposeHeadPathInvo ℕzero x = refl
-- -- -- -- transposeHeadPathInvo one =
-- -- -- --   ElimProp.f {!!} {!!}
-- -- -- --    λ _ → {!trunc _ _ _ _!}
-- -- -- -- transposeHeadPathInvo (ℕsuc (ℕsuc k)) x = {!!}
-- -- -- -- -- transposeHeadPathInvo ℕzero x = x , refl
-- -- -- -- -- transposeHeadPathInvo one = ElimProp.f (_ , refl)
-- -- -- -- --    (λ x {xs} →
-- -- -- -- --      ElimProp.f {B = λ xs → singl ((fst (transposeHeadFM2 one (fst (transposeHeadFM2 one (xs)))))) →
-- -- -- -- --          singl (fst (transposeHeadFM2 one (fst (transposeHeadFM2 one (x ∷ xs)))))}
-- -- -- -- --         (λ _ → _ , refl)
-- -- -- -- --         (λ y {xs} _ _ → _ , refl)
-- -- -- -- --         (λ _ → isPropΠ λ _ → isContr→isProp (isContrSingl _))
-- -- -- -- --         xs)
-- -- -- -- --    λ _ → isContr→isProp (isContrSingl _)

-- -- -- -- -- transposeHeadPathInvo (ℕsuc (ℕsuc k)) = {!!}

-- -- -- -- transposeHeadPathInvoSq : ∀ k → ∀ x →
-- -- -- --    (snd (transposeHeadFM2 {A = A} k x)) ∙ snd (transposeHeadFM2 k (fst (transposeHeadFM2 k x)))
-- -- -- --     ≡ transposeHeadPathInvo k x
-- -- -- -- transposeHeadPathInvoSq = {!!}
