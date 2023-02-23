{-# OPTIONS --safe  #-}  --experimental-lossy-unification
module Cubical.HITs.ListedFiniteSet.Base3 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool

open import Cubical.Functions.Logic
open import Cubical.Foundations.Function

open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

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
  commmL commmR : ∀ x y z xs → x ∷2 y ∷2 z ∷2  xs ≡ z ∷2 x ∷2 y ∷2 xs
  commpL : ∀ x y z xs → Square
      (cong (x ∷2_) (comm y z xs))
      (comm x y (z ∷2 xs))
      refl
      (commmL x z y xs)

  commpR : ∀ x y z xs → Square     
      (cong (x ∷2_) (comm _ _ _))
      (comm z x (y ∷2 xs))
      (commmR x y z xs)
      refl      
  hex : ∀ x y z xs → Square          
          (comm x y (z ∷2 xs))
          (cong (z ∷2_) (comm _ _ _))
          (commmL x y z xs)
          (commmR y x z xs)
  trunc : isGroupoid (FMSet2 A)


fm2Map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → FMSet2 A → FMSet2 B 
fm2Map f = f'
 where
  f' : FMSet2 _ → FMSet2 _ 
  f' [] = []
  f' (x ∷2 x₁) = f x ∷2 (f' x₁)
  f' (comm x y x₁ i) = comm (f x) (f y) (f' x₁) i
  f' (comm-inv x y x₁ i i₁) = comm-inv (f x) (f y) (f' x₁) i i₁
  f' (commmL x y z x₁ i) = (commmL (f x) (f y) (f z) (f' x₁) i)
  f' (commmR x y z x₁ i) = (commmR (f x) (f y) (f z) (f' x₁) i)
  f' (commpL x y z x₁ i i₁) = (commpL (f x) (f y) (f z) (f' x₁) i i₁)
  f' (commpR x y z x₁ i i₁) = (commpR (f x) (f y) (f z) (f' x₁) i i₁) 
  f' (hex x y z x₁ i i₁) = (hex (f x) (f y) (f z) (f' x₁) i i₁)
  f' (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
    trunc _ _ _ _ (λ i j → f' (x₃ i j))
      (λ i j → f' (y₁ i j)) i i₁ x₄

commmL≡R : ∀ (x : A) y z xs → commmL x y z xs ≡ commmR x y z xs 
commmL≡R x y z xs i j =
  hcomp (λ l →
    λ { (i = i0) → commpL x z y xs j l
      ; (i = i1) → commpR x y z xs j (~ l)
      ; (j = i0) → x ∷2 comm-inv z y (xs) i l
      ; (j = i1) → comm-inv x z (y ∷2 xs) i l
      }) (x ∷2 z ∷2 y ∷2 xs)
      
-- comm-invo : ∀ (x y : A) → ∀ xs → 
--             comm x y xs ∙ comm _ _ xs ≡ refl
-- comm-invo x y xs = cong (_∙ comm y x xs) (comm-inv x y xs) ∙ lCancel _


-- -- hexUpa : ∀ (x y z : A) → ∀ xs → comm _ _ _ ∙∙ cong (y ∷2_) (comm _ _ _) ∙∙ comm _ _ _ ≡ hexDiag x y z xs
-- -- hexUpa x y z xs  =
-- --     cong (_∙∙ cong (y ∷2_) (comm _ _ _) ∙∙ comm _ _ _) (comm-inv _ _ _)
-- --      ◁ λ i j → hcomp (λ k → λ { (i = i1) → hexDiag x y z xs j
-- --                   ; (j = i0) → (hexU x y z xs (i ∨ k) j)
-- --                   ; (j = i1) → (hexU x y z xs (i ∨ k) j)
-- --                   }) (hexU x y z xs i j)

-- -- hexLpa : ∀ (x y z : A) → ∀ xs → hexDiag x y z xs ≡ cong (x ∷2_) (comm _ _ _) ∙∙ comm _ _ _ ∙∙ cong (z ∷2_) (comm _ _ _)
-- -- hexLpa x y z xs  = 
-- --     (λ i j → hcomp (λ k → λ { (i = i0) → hexDiag x y z xs j
-- --                   ; (j = i0) → (hexL x y z xs (i ∧ ~ k) j)
-- --                   ; (j = i1) → (hexL x y z xs (i ∧ ~ k) j)
-- --                   }) (hexL x y z xs i j))
-- --        ▷ cong (λ p → cong (x ∷2_) (comm _ _ _) ∙∙ comm _ _ _ ∙∙ cong (z ∷2_) p) (sym (comm-inv _ _ _))


comm-braid : ∀ (x y z : A) → ∀ xs → 
  cong (x ∷2_) (comm z y xs)  ∙ comm x y (z ∷2 xs) ∙ cong (y ∷2_) (comm x z xs)
    ≡
  comm x z (y ∷2 xs) ∙ cong (z ∷2_) (comm x y xs) ∙ comm z y (x ∷2 xs)
comm-braid x y z xs i j =
   (commpL x z y xs i ∙ hex x y z xs i ∙ commpR y x z xs i) j
     
-- -- sym (doubleCompPath-elim' _ _ _)

-- --   sym (doubleCompPath-elim' _ _ _)
-- -- --    ∙ (hexUpa _ _ _ _ ∙ hexLpa _ _ _ _)
-- --    ∙ doubleCompPath-elim' _ _ _

module _ {A : Type ℓ} where

  record RElim {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    field
     []* : B []
     _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
     comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
           → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
     comm-inv* : ∀ x y {xs} (b : B xs) → SquareP (λ i j → B (comm-inv x y xs i j))
                        (comm* x y b ) (symP (comm* y x b))
                        refl refl
     commmL* : (x y z : A) {xs : FMSet2 A} (b : B xs)
           → PathP (λ i → B (commmL x y z xs i))
              (x ∷* (y ∷* (z ∷* b)))
              (z ∷* (x ∷* (y ∷* b)))
     commmR* : (x y z : A) {xs : FMSet2 A} (b : B xs)
           → PathP (λ i → B (commmR x y z xs i))
              (x ∷* (y ∷* (z ∷* b)))
              (z ∷* (x ∷* (y ∷* b)))

     commpL* : ∀ x y z {xs : FMSet2 A} (b : B xs) →
               SquareP
               ((λ i j → B (commpL x y z xs i j)))
                       (congP (λ _ → x ∷*_) (comm* y z b))
                     (comm* x y (z ∷* b))
                     refl
                     (commmL* x z y b)
     commpR* : ∀ x y z {xs : FMSet2 A} (b : B xs) →
               SquareP (λ i j → B (commpR x y z xs i j))
               (congP (λ _ → x ∷*_) (comm* _ _ _))
               (comm* z x (y ∷* b))
               (commmR* x y z b)
               refl
     hex* : ∀ x y z {xs : FMSet2 A} (b : B xs) →
               SquareP (λ i j → B (hex x y z xs i j))
               (comm* x y (z ∷* b))
               (congP (λ _ → z ∷*_) (comm* _ _ _))
               (commmL* x y z b)
               (commmR* y x z b)
                  

     trunc* : (xs : FMSet2 A) → isGroupoid (B xs)

    f : (xs : FMSet2 A) → B xs
    f [] = []*
    f (x ∷2 xs) = x ∷* f xs
    f (comm x y xs i) = comm* x y (f xs) i
    f (comm-inv x y xs i j) =
       comm-inv* x y (f xs) i j
    f (commmL x y z xs i) = commmL* x y z (f xs) i
    f (commmR x y z xs i) = commmR* x y z (f xs) i
    f (commpL x y z xs i j) = commpL* x y z (f xs) i j 
    f (commpR x y z xs i j) = commpR* x y z (f xs) i j 
    f (hex x y z xs i j) = hex* x y z (f xs) i j 
    f (trunc xs ys p q r s i j k) =
      isOfHLevel→isOfHLevelDep 3 (λ a → trunc* a)
         _ _ _ _
         (λ j k → f (r j k)) (λ j k → f (s j k)) 
           (trunc xs ys p q r s) i j k


  -- record RElim' {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  --   no-eta-equality
  --   field
  --    []* : B []
  --    _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
  --    comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
  --          → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
  --    comm-inv* : ∀ x y {xs} (b : B xs) → SquareP (λ i j → B (comm-inv x y xs i j))
  --                       (comm* x y b ) (symP (comm* y x b))
  --                       refl refl                  

  --    trunc* : (xs : FMSet2 A) → isGroupoid (B xs)

  --   fR : RElim (λ z → B z)
  --   RElim.[]* fR = []*
  --   RElim._∷*_ fR = _∷*_
  --   RElim.comm* fR = comm*
  --   RElim.comm-inv* fR = comm-inv*
  --   RElim.commmL* fR = {!!}
  --   RElim.commmR* fR = {!!}
  --   RElim.commpL* fR = {!!}
  --   RElim.commpR* fR = {!!}
  --   RElim.hex* fR = {!!}
  --   RElim.trunc* fR = {!!}

  --   f : (xs : FMSet2 A) → B xs
  --   f = RElim.f fR

  record RRec {ℓ'} {B : Type ℓ'} (BType : isGroupoid B) : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    field
     []* : B
     _∷*_ : A → B → B
     comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b)
     comm-inv* : ∀ x y b → comm* x y b ≡ sym (comm* y x b) 
     commmL* : (x y z : A) → ∀ b
           → (x ∷* (y ∷* (z ∷* b))) ≡  (z ∷* (x ∷* (y ∷* b)))
     commmR* : (x y z : A) → ∀ b
           → (x ∷* (y ∷* (z ∷* b))) ≡ (z ∷* (x ∷* (y ∷* b)))

     commpL* : ∀ x y z → ∀ b → 
               Square
                 (cong (x ∷*_) (comm* y z b))
                 (comm* x y (z ∷* b))
                 refl
                 (commmL* x z y b)
     commpR* : ∀ x y z → ∀ b →
               Square 
               (cong (x ∷*_) (comm* _ _ _))
               (comm* z x (y ∷* b))
               (commmR* x y z b)
               refl
     hex* : ∀ x y z → ∀ b →
               Square
               (comm* x y (z ∷* b))
               (cong (z ∷*_) (comm* _ _ _))
               (commmL* x y z b)
               (commmR* y x z b)


    f : FMSet2 A → B
    f [] = []*
    f (x ∷2 x₁) = x ∷* f x₁
    f (comm x y x₁ i) = comm* x y (f x₁) i
    f (comm-inv x y x₁ i i₁) = comm-inv* x y (f x₁) i i₁
    f (commmL x y z xs i) = commmL* x y z (f xs) i
    f (commmR x y z xs i) = commmR* x y z (f xs) i
    f (commpL x y z xs i j) = commpL* x y z (f xs) i j 
    f (commpR x y z xs i j) = commpR* x y z (f xs) i j 
    f (hex x y z xs i j) = hex* x y z (f xs) i j     
    f (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
       BType _ _ _ _
        (cong (cong f) x₃)
        (cong  (cong f) y₁) i i₁ x₄


  record RElimSet' {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    field
     []* : B []
     _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
     comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
           → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
     trunc* : (xs : FMSet2 A) → isSet (B xs)

    fR : RElim B
    RElim.[]* fR = []*
    RElim._∷*_ fR = _∷*_
    RElim.comm* fR = comm*
    RElim.comm-inv* fR x y b =
      isSet→SquareP (λ _ _  → trunc* _) _ _ _ _
    RElim.commmL* fR x y z {xs} b i =
      comp (λ l → B (commpL x z y xs i l))
       (λ l → λ { (i = i0) → x ∷* comm* z y b l
                ; (i = i1) → comm* x z (y ∷* b) l
                })
       (x ∷* (z ∷* (y ∷* b)))
    RElim.commmR* fR x y z {xs} b i =
       comp (λ l → B (commpR x y z xs i (~ l)))
       (λ l → λ { (i = i0) → x ∷* comm* y z b (~ l)
                ; (i = i1) → comm* z x (y ∷* b) (~ l)
                })
       (x ∷* (z ∷* (y ∷* b)))
    RElim.commpL* fR x y z b =
      isSet→SquareP (λ _ _  → trunc* _) _ _ _ _
    RElim.commpR* fR x y z b =
      isSet→SquareP (λ _ _  → trunc* _) _ _ _ _
    RElim.hex* fR x y z b =
      isSet→SquareP (λ _ _  → trunc* _) _ _ _ _
    RElim.trunc* fR = isSet→isGroupoid ∘ trunc*

    f : ∀ xs → B xs
    f = RElim.f fR

    -- f : ∀ xs → B xs
    -- f [] = []*
    -- f (x ∷2 xs) = x ∷* f xs
    -- f (comm x y xs i) = comm* x y (f xs) i
    -- f (comm-inv x y xs i j) =
    --    isOfHLevel→isOfHLevelDep 2 trunc*
    --        (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
    --        (comm* x y (f xs)) (symP (comm* y x (f xs)))
    --        (comm-inv x y xs) i j
    -- f (commmL x y z xs i) =
    --   comp (λ l → B (commpL x z y xs i l))
    --    (λ l → λ { (i = i0) → x ∷* comm* z y (f xs) l
    --             ; (i = i1) → comm* x z (y ∷* (f xs)) l
    --             })
    --    (x ∷* (z ∷* (y ∷* f xs)))
    -- f (commmR x y z xs i) =
    --    comp (λ l → B (commpR x y z xs i (~ l)))
    --    (λ l → λ { (i = i0) → x ∷* comm* y z (f xs) (~ l)
    --             ; (i = i1) → comm* z x (y ∷* (f xs)) (~ l)
    --             })
    --    (x ∷* (z ∷* (y ∷* f xs)))
    -- f (commpL x y z xs i j) =
    --   {!isOfHLevel→isOfHLevelDep 2 trunc*
    --        ? ? ? ?
    --        (commpL x y z xs) i j!}
    -- f (commpR x y z xs i i₁) = {!!}
    -- f (hex x y z xs i i₁) = {!!}
    -- f (trunc xs xs₁ x y x₁ y₁ i i₁ x₂) = {!!}

--     hexDiag* : (x y z : A) {xs : FMSet2 A} (b : B xs)
--            → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b)))
--     hexDiag* x y z {xs} b i =
--       comp (λ j → B (hexU x y z xs j i))
--         (λ j →
--           λ { (i = i0) → comm* y x {(z ∷2 xs)} (z ∷* b) j
--             ; (i = i1) → comm* y z (x ∷* b) j
--             }) (y ∷* comm* x z b i) 

--     f : (xs : FMSet2 A) → B xs
--     f [] = []*
--     f (x ∷2 xs) = x ∷* f xs
--     f (comm x y xs i) = comm* x y (f xs) i
--     f (comm-inv x y xs i j) =
--        isOfHLevel→isOfHLevelDep 2 trunc*
--            (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
--            (comm* x y (f xs)) (symP (comm* y x (f xs)))
--            (comm-inv x y xs) i j
--     f (hexDiag x y z xs i) = 
--        hexDiag* x y z (f xs) i
--     f (hexU x y z xs i j) = 
--       isSet→SquareP 
--          (λ i j → trunc* (hexU x y z xs i j))
--          (λ j → y ∷* comm* x z (f xs) j)
--          (hexDiag* x y z (f xs))
--          (comm* y x (z ∷* f xs))
--          (comm* y z (x ∷* f xs)) i j
--     f (hexL x y z xs i j) = 
--          isSet→SquareP 
--          (λ i j → trunc* (hexL x y z xs i j))
--          (hexDiag* x y z (f xs))
--          (comm* x z (y ∷* f xs))
--          (λ i₁ → x ∷* comm* y z (f xs) i₁)
--          (λ i₁ → z ∷* comm* y x (f xs) i₁) i j
--     f (trunc xs zs p q r s i j k) =
--         isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
--             _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k


--     f : (xs : FMSet2 A B xs
--     f [] = []*
--     f (x ∷2 xs) = x ∷* f xs
--     f (comm x y xs i) = comm* x y (f xs) i
--     f (comm-inv x y xs i j) =
--        comm-inv* x y (f xs) i j
--     f (commmL x y z xs i) = commmL* x y z (f xs) i
--     f (commmR x y z xs i) = commmR* x y z (f xs) i
--     f (commpL x y z xs i j) = commpL* x y z (f xs) i j 
--     f (commpR x y z xs i j) = commpR* x y z (f xs) i j 
--     f (hex x y z xs i j) = hex* x y z (f xs) i j 
--     f (trunc xs ys p q r s i j k) = ?
--       -- isOfHLevel→isOfHLevelDep 3 (λ a → trunc* a)
--       --    _ _ _ _
--       --    (λ j k → f (r j k)) (λ j k → f (s j k)) 
--       --      (trunc xs ys p q r s) i j k



--   -- module ElimSet {ℓ'} {B : FMSet2 A → Type ℓ'}
--   --   ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs))
--   --   (comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
--   --          → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
--   --        comm-inv* : ∀ x y {xs} (b : B xs) → SquareP (λ i j → B (comm-inv x y xs i j))
--   --                       (comm* x y b ) (symP (comm* y x b))
--   --                       refl refl 
--   --   (commmL* : (x y z : A) {xs : FMSet2 A} (b : B xs)
--   --          → PathP (λ i → B (commmL x y z xs i))
--   --             (x ∷* (y ∷* (z ∷* b)))
--   --             (z ∷* (x ∷* (y ∷* b))))
--   --   (commmR* : (x y z : A) {xs : FMSet2 A} (b : B xs)
--   --          → PathP (λ i → B (commmR x y z xs i))
--   --             (x ∷* (y ∷* (z ∷* b)))
--   --             (z ∷* (x ∷* (y ∷* b))))
--   --   (trunc* : (xs : FMSet2 A) → isSet (B xs)) where

--   --   f : (xs : FMSet2 A) → B xs
--   --   f [] = []*
--   --   f (x ∷2 xs) = x ∷* f xs
--   --   f (comm x y xs i) = comm* x y (f xs) i
--   --   f (comm-inv x y xs i j) = {!!}
--   --      -- isOfHLevel→isOfHLevelDep 2 trunc*
--   --      --     (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
--   --      --     (comm* x y (f xs)) (symP (comm* y x (f xs)))
--   --      --     (comm-inv x y xs) i j
--   --   f (commmL x y z xs i) = {!!}
--   --   f (commmR x y z xs i) = {!!}
--   --   f (commpL x y z xs i i₁) = {!!}
--   --   f (commpR x y z xs i i₁) = {!!}
--   --   f (hex x y z xs i i₁) = {!!}    
--   --   f (trunc xs zs p q r s i j k) = {!!}
--   --       -- isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
--   --       --     _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k

-- --   module ElimSet {ℓ'} {B : FMSet2 A → Type ℓ'}
-- --     ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs))
-- --     (comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
-- --     (commmL* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- --            → PathP (λ i → B (commmL x y z xs i))
-- --               (x ∷* (y ∷* (z ∷* b)))
-- --               (z ∷* (x ∷* (y ∷* b))))
-- --     (commmR* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- --            → PathP (λ i → B (commmR x y z xs i))
-- --               (x ∷* (y ∷* (z ∷* b)))
-- --               (z ∷* (x ∷* (y ∷* b))))
-- --     (trunc* : (xs : FMSet2 A) → isSet (B xs)) where

-- --     f : (xs : FMSet2 A) → B xs
-- --     f [] = []*
-- --     f (x ∷2 xs) = x ∷* f xs
-- --     f (comm x y xs i) = comm* x y (f xs) i
-- --     f (comm-inv x y xs i j) =
-- --        isOfHLevel→isOfHLevelDep 2 trunc*
-- --            (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
-- --            (comm* x y (f xs)) (symP (comm* y x (f xs)))
-- --            (comm-inv x y xs) i j
-- --     f (commmL x y z xs i) = {!!}
-- --     f (commmR x y z xs i) = {!!}
-- --     f (commpL x y z xs i i₁) = {!!}
-- --     f (commpR x y z xs i i₁) = {!!}
-- --     f (hex x y z xs i i₁) = {!!}    
-- --     -- f (hexDiag x y z xs i) = hexDiag* x y z (f xs) i
-- --     -- f (hexU x y z xs i j) =
-- --     --   isSet→SquareP 
-- --     --      (λ i j → trunc* (hexU x y z xs i j))
-- --     --      (λ j → y ∷* comm* x z (f xs) j)
-- --     --      (hexDiag* x y z (f xs))
-- --     --      (comm* y x (z ∷* f xs))
-- --     --      (comm* y z (x ∷* f xs)) i j
-- --     -- f (hexL x y z xs i j) =
-- --     --      isSet→SquareP 
-- --     --      (λ i j → trunc* (hexL x y z xs i j))
-- --     --      (hexDiag* x y z (f xs))
-- --     --      (comm* x z (y ∷* f xs))
-- --     --      (λ i₁ → x ∷* comm* y z (f xs) i₁)
-- --     --      (λ i₁ → z ∷* comm* y x (f xs) i₁) i j
-- --     f (trunc xs zs p q r s i j k) =
-- --         isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
-- --             _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k


-- -- --   record RElimSet {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- --     no-eta-equality
-- -- --     field
-- -- --      []* : B []
-- -- --      _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
-- -- --      comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- -- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
-- -- --      hexDiag* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- --            → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b)))
-- -- --      trunc* : (xs : FMSet2 A) → isSet (B xs)

-- -- --     f : (xs : FMSet2 A) → B xs
-- -- --     f [] = []*
-- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- --     f (comm-inv x y xs i j) =
-- -- --        isOfHLevel→isOfHLevelDep 2 trunc*
-- -- --            (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
-- -- --            (comm* x y (f xs)) (symP (comm* y x (f xs)))
-- -- --            (comm-inv x y xs) i j
-- -- --     f (hexDiag x y z xs i) = hexDiag* x y z (f xs) i
-- -- --     f (hexU x y z xs i j) =
-- -- --       isSet→SquareP 
-- -- --          (λ i j → trunc* (hexU x y z xs i j))
-- -- --          (λ j → y ∷* comm* x z (f xs) j)
-- -- --          (hexDiag* x y z (f xs))
-- -- --          (comm* y x (z ∷* f xs))
-- -- --          (comm* y z (x ∷* f xs)) i j
-- -- --     f (hexL x y z xs i j) =
-- -- --          isSet→SquareP 
-- -- --          (λ i j → trunc* (hexL x y z xs i j))
-- -- --          (hexDiag* x y z (f xs))
-- -- --          (comm* x z (y ∷* f xs))
-- -- --          (λ i₁ → x ∷* comm* y z (f xs) i₁)
-- -- --          (λ i₁ → z ∷* comm* y x (f xs) i₁) i j
-- -- --     f (trunc xs zs p q r s i j k) =
-- -- --         isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
-- -- --             _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k


-- -- --   record RElimSet' {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- --     no-eta-equality
-- -- --     field
-- -- --      []* : B []
-- -- --      _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
-- -- --      comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- -- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
-- -- --      trunc* : (xs : FMSet2 A) → isSet (B xs)

-- -- --     hexDiag* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- --            → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b)))
-- -- --     hexDiag* x y z {xs} b i =
-- -- --       comp (λ j → B (hexU x y z xs j i))
-- -- --         (λ j →
-- -- --           λ { (i = i0) → comm* y x {(z ∷2 xs)} (z ∷* b) j
-- -- --             ; (i = i1) → comm* y z (x ∷* b) j
-- -- --             }) (y ∷* comm* x z b i) 

-- -- --     f : (xs : FMSet2 A) → B xs
-- -- --     f [] = []*
-- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- --     f (comm-inv x y xs i j) =
-- -- --        isOfHLevel→isOfHLevelDep 2 trunc*
-- -- --            (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
-- -- --            (comm* x y (f xs)) (symP (comm* y x (f xs)))
-- -- --            (comm-inv x y xs) i j
-- -- --     f (hexDiag x y z xs i) = 
-- -- --        hexDiag* x y z (f xs) i
-- -- --     f (hexU x y z xs i j) = 
-- -- --       isSet→SquareP 
-- -- --          (λ i j → trunc* (hexU x y z xs i j))
-- -- --          (λ j → y ∷* comm* x z (f xs) j)
-- -- --          (hexDiag* x y z (f xs))
-- -- --          (comm* y x (z ∷* f xs))
-- -- --          (comm* y z (x ∷* f xs)) i j
-- -- --     f (hexL x y z xs i j) = 
-- -- --          isSet→SquareP 
-- -- --          (λ i j → trunc* (hexL x y z xs i j))
-- -- --          (hexDiag* x y z (f xs))
-- -- --          (comm* x z (y ∷* f xs))
-- -- --          (λ i₁ → x ∷* comm* y z (f xs) i₁)
-- -- --          (λ i₁ → z ∷* comm* y x (f xs) i₁) i j
-- -- --     f (trunc xs zs p q r s i j k) =
-- -- --         isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
-- -- --             _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k

-- -- --   record RElimProp' {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- --     no-eta-equality
-- -- --     field
-- -- --      []* : B []
-- -- --      _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
-- -- --      trunc* : (xs : FMSet2 A) → isProp (B xs)

-- -- --     res : RElimSet B
-- -- --     RElimSet.[]* res = []*
-- -- --     RElimSet._∷*_ res = _∷*_
-- -- --     RElimSet.comm* res = (λ x y b → isProp→PathP (λ _ → trunc* _) _ _)
-- -- --     RElimSet.hexDiag* res = (λ x y z b → isProp→PathP (λ _ → trunc* _) _ _)
-- -- --     RElimSet.trunc* res = isProp→isSet ∘ trunc*

-- -- --     f = RElimSet.f res

-- -- --   record RElimProp'' {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- --     no-eta-equality
-- -- --     field
-- -- --      []* : B []
-- -- --      _∷*[_]_ : (x : A) (xs : FMSet2 A) → B xs → B (x ∷2 xs)
-- -- --      trunc* : (xs : FMSet2 A) → isProp (B xs)

-- -- --     res : RElimSet B
-- -- --     RElimSet.[]* res = []*
-- -- --     (res RElimSet.∷* x) {xs} x₁ = x ∷*[ xs ] x₁ 
-- -- --     RElimSet.comm* res = (λ x y b → isProp→PathP (λ _ → trunc* _) _ _)
-- -- --     RElimSet.hexDiag* res = (λ x y z b → isProp→PathP (λ _ → trunc* _) _ _)
-- -- --     RElimSet.trunc* res = isProp→isSet ∘ trunc*

-- -- --     f = RElimSet.f res


-- -- --   record RElim {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- --     no-eta-equality
-- -- --     field
-- -- --      []* : B []
-- -- --      _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
-- -- --      comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- -- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
-- -- --      comm-inv* : ∀ x y {xs} (b : B xs) → SquareP (λ i j → B (comm-inv x y xs i j))
-- -- --                         (comm* x y b ) (symP (comm* y x b))
-- -- --                         refl refl 
-- -- --      hexDiag* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- --            → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b)))
-- -- --      hexU* : ∀ x y z {xs : FMSet2 A} (b : B xs) →
-- -- --                SquareP
-- -- --                ((λ i j → B (hexU x y z xs i j)))
-- -- --                  (congP (λ _ → y ∷*_) (comm* x z b))
-- -- --                  (hexDiag* x y z b)
-- -- --                  (comm* _ _ (z ∷* b))
-- -- --                  (comm* _ _ (x ∷* b))
                  
-- -- --      hexL* : ∀ x y z {xs : FMSet2 A} (b : B xs)  →
-- -- --                SquareP
-- -- --                  (λ i j → B (hexL x y z xs i j))
-- -- --                  (hexDiag* _ _ _ b)
-- -- --                  (comm* _ _ _)
-- -- --                  (congP (λ _ → _ ∷*_) (comm* _ _ _))
-- -- --                  (congP (λ _ → _ ∷*_) (comm* _ _ _))
                  

-- -- --      trunc* : (xs : FMSet2 A) → isGroupoid (B xs)

-- -- --     f : (xs : FMSet2 A) → B xs
-- -- --     f [] = []*
-- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- --     f (comm-inv x y xs i j) =
-- -- --        comm-inv* x y (f xs) i j
-- -- --     f (hexDiag x y z xs i) = hexDiag* x y z (f xs) i
-- -- --     f (hexU x y z xs i j) = hexU* x y z (f xs) i j
-- -- --     f (hexL x y z xs i j) = hexL* x y z (f xs) i j

-- -- --     f (trunc xs ys p q r s i j k) =
-- -- --       isOfHLevel→isOfHLevelDep 3 (λ a → trunc* a)
-- -- --          _ _ _ _
-- -- --          (λ j k → f (r j k)) (λ j k → f (s j k)) 
-- -- --            (trunc xs ys p q r s) i j k


-- -- --   record RRec {ℓ'} {B : Type ℓ'} (BType : isGroupoid B) : Type (ℓ-max ℓ ℓ') where
-- -- --     no-eta-equality
-- -- --     field
-- -- --       []* : B
-- -- --       _∷*_ : A → B → B
-- -- --       comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b)
-- -- --       comm-inv* : ∀ x y b → comm* x y b ≡ sym (comm* y x b) 
-- -- --       hexDiag* : ∀ x y z b → x ∷* (y ∷* (z ∷* b)) ≡ z ∷* (y ∷* (x ∷* b)) 
-- -- --       hexU* : ∀ x y z b →
-- -- --                Square (cong (_ ∷*_) (comm* _ _ b)) (hexDiag* x y z b)
-- -- --                       (comm* _ _ _) (comm* _ _ _)
-- -- --       hexL* : ∀ x y z b →
-- -- --                Square (hexDiag* x y z b) (comm* _ _ _)
-- -- --                       (cong (_ ∷*_) (comm* _ _ b)) (cong (_ ∷*_) (comm* _ _ b))


-- -- --     f : FMSet2 A → B
-- -- --     f [] = []*
-- -- --     f (x ∷2 x₁) = x ∷* f x₁
-- -- --     f (comm x y x₁ i) = comm* x y (f x₁) i
-- -- --     f (comm-inv x y x₁ i i₁) = comm-inv* x y (f x₁) i i₁
-- -- --     f (hexDiag x y z x₁ i) = hexDiag* x y z (f x₁) i
-- -- --     f (hexU x y z x₁ i i₁) = hexU* x y z (f x₁) i i₁
-- -- --     f (hexL x y z x₁ i i₁) = hexL* x y z (f x₁) i i₁
-- -- --     f (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
-- -- --        BType _ _ _ _
-- -- --         (cong (cong f) x₃) (cong  (cong f) y₁) i i₁ x₄




  len2 : FMSet2 A → ℕ
  len2 [] = zero
  len2 (x ∷2 x₁) = suc (len2 x₁)
  len2 (comm x y x₁ i) = suc (suc (len2 x₁))
  len2 (comm-inv x y x₁ i i₁) = suc (suc (len2 x₁))
  len2 (commmL x y z x₁ i) = suc (suc (suc (len2 x₁)))
  len2 (commmR x y z x₁ i) = suc (suc (suc (len2 x₁)))
  len2 (commpL x y z x₁ i i₁) = suc (suc (suc (len2 x₁)))
  len2 (commpR x y z x₁ i i₁) = suc (suc (suc (len2 x₁)))
  len2 (hex x y z x₁ i i₁) = suc (suc (suc (len2 x₁)))
  len2 (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) = 
     (isSet→isGroupoid isSetℕ) _ _ _ _
        (cong (cong len2) x₃) (cong  (cong len2) y₁) i i₁ x₄


-- -- -- --   -- paPerm : {xs ys : FMSet2 A} → xs ≡ ys
-- -- -- --   --    → EM₁ (SymData (len2 xs))
-- -- -- --   -- paPerm {xs} = J (λ ys p → EM₁ (SymData (len2 xs)))
-- -- -- --   --    (Elim.f {B = λ xs → EM₁ (SymData (len2 xs))}
-- -- -- --   --      embase
-- -- -- --   --      (λ _ → gh→em₂→ _ (sucPermFDMorphism _))
-- -- -- --   --      (λ x y {xs}
-- -- -- --   --        → elimSet (SymData (len2 xs))
-- -- -- --   --          (λ _ → emsquash _ _) (emloop swap0and1≃)
-- -- -- --   --            λ g → 
-- -- -- --   --              ∙≡∙→square
-- -- -- --   --              (emloop swap0and1≃)
-- -- -- --   --              (emloop (sucPerm (sucPerm g)))                              
-- -- -- --   --              (emloop (sucPerm (sucPerm g)))
-- -- -- --   --               (emloop swap0and1≃)
-- -- -- --   --              {!!}
-- -- -- --   --              )

-- -- -- --   --      {!!}
-- -- -- --   --      {!!}
-- -- -- --   --      {!!}
-- -- -- --   --      {!!}
-- -- -- --   --      (λ _ → emsquash)
-- -- -- --   --      xs)

-- -- -- -- --   inj∷2 : (xs ys : FMSet2 A) → (x : A)
-- -- -- -- --            → x ∷2 xs ≡ x ∷2 ys → xs ≡ ys
-- -- -- -- --   inj∷2 = ElimSet.f
-- -- -- -- --     {!!}
-- -- -- -- --     -- (ElimSet.f
-- -- -- -- --     --    (λ _ _ → refl)
-- -- -- -- --     --    (λ x x₁ x₂ → {!!} ∘ cong len2  )
-- -- -- -- --     --    {!!}
-- -- -- -- --     --    {!!}
-- -- -- -- --     --    λ _ → isSetΠ2 λ _ _ → trunc _ _ )
-- -- -- -- --     (λ x {xs} b →
-- -- -- -- --       ElimSet.f
-- -- -- -- --        {!!}
-- -- -- -- --        (λ x' {ys} b' y' p →
-- -- -- -- --          {!!})
-- -- -- -- --          {!!} {!!}
-- -- -- -- --         λ _ → isSetΠ2 λ _ _ → trunc _ _)
-- -- -- -- --     {!!}
-- -- -- -- --     {!!}
-- -- -- -- --     λ _ → isSetΠ3 λ _ _ _ → trunc _ _ 

-- -- -- -- -- -- -- -- Rec.f
-- -- -- -- -- -- -- --      (isSet→isGroupoid isSetℕ) zero (λ _ → suc)
-- -- -- -- -- -- -- --        (λ _ _ _ → refl) (λ _ _ _ _ → refl)
-- -- -- -- -- -- -- --        (λ _ _ _ _ → refl) (λ _ _ _ _ → refl) (λ _ _ _ _ → refl)


-- -- -- -- -- -- -- -- RecSet.f isSetℕ zero (λ _ → suc) (λ _ _ _ → refl) (λ _ _ _ _ → refl)

-- -- -- -- -- -- --   -- open import Cubical.HITs.EilenbergMacLane1 as EM

-- -- -- fm2Map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → FMSet2 A → FMSet2 B 
-- -- -- fm2Map f = f'
-- -- --  where
-- -- --   f' : FMSet2 _ → FMSet2 _ 
-- -- --   f' [] = []
-- -- --   f' (x ∷2 x₁) = f x ∷2 (f' x₁)
-- -- --   f' (comm x y x₁ i) = comm (f x) (f y) (f' x₁) i
-- -- --   f' (comm-inv x y x₁ i i₁) = comm-inv (f x) (f y) (f' x₁) i i₁
-- -- --   f' (hexDiag x y z x₁ i) = (hexDiag (f x) (f y) (f z) (f' x₁) i)
-- -- --   f' (hexU x y z x₁ i i₁) = hexU (f x) (f y) (f z) (f' x₁) i i₁
-- -- --   f' (hexL x y z x₁ i i₁) = hexL (f x) (f y) (f z) (f' x₁) i i₁
-- -- --   f' (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
-- -- --     trunc _ _ _ _ (λ i j → f' (x₃ i j))
-- -- --       (λ i j → f' (y₁ i j)) i i₁ x₄

-- -- -- module _ (A : Type ℓ) where
-- -- --   -- open import Cubical.Data.List.FinData


-- -- --   FMSet2OfLen : ℕ → Type ℓ
-- -- --   FMSet2OfLen n = Σ (FMSet2 A) λ x → len2 x ≡ n

-- -- --   _++2_ : FMSet2 A → FMSet2 A → FMSet2 A
-- -- --   [] ++2 ys = ys
-- -- --   (x ∷2 xs) ++2 ys = x ∷2 (xs ++2 ys)
-- -- --   comm x y xs i ++2 ys = comm x y (xs ++2 ys) i
-- -- --   comm-inv x y xs i i₁ ++2 ys = comm-inv x y (xs ++2 ys) i i₁
-- -- --   hexDiag x y z xs i ++2 ys = hexDiag x y z (xs ++2 ys) i 
-- -- --   hexU x y z xs i i₁ ++2 ys = hexU x y z (xs ++2 ys) i i₁ 
-- -- --   hexL x y z xs i i₁ ++2 ys = hexL x y z (xs ++2 ys) i i₁ 
-- -- --   trunc _ _ _ _ r s i i₁ i₂ ++2 ys =
-- -- --    trunc _ _ _ _ (λ i j → r i j ++2 ys)
-- -- --     (λ i j → s i j ++2 ys) i i₁ i₂


-- -- --   assoc++ : ∀ xs ys zs → xs ++2 (ys ++2 zs) ≡ (xs ++2 ys) ++2 zs
-- -- --   assoc++ = RElimSet.f w
-- -- --     where
-- -- --      w : RElimSet _
-- -- --      RElimSet.[]* w _ _ = refl
-- -- --      RElimSet._∷*_ w _ p ys zs = cong (_ ∷2_) (p ys zs)
-- -- --      RElimSet.comm* w x y b = funExt₂ λ x' y' → λ i j → comm x y (b x' y' j) i 
-- -- --      RElimSet.hexDiag* w x y z b = funExt₂ λ x' y' → λ i j → hexDiag x y z (b x' y' j) i
-- -- --      RElimSet.trunc* w _ = isSetΠ2 λ _ _ → trunc _ _


-- -- --   rUnit++ : ∀ xs → xs ≡ xs ++2 []
-- -- --   rUnit++ = RElimSet.f w
-- -- --     where
-- -- --      w : RElimSet (λ z → z ≡ (z ++2 []))
-- -- --      RElimSet.[]* w = refl
-- -- --      RElimSet._∷*_ w a = cong (a ∷2_)
-- -- --      RElimSet.comm* w x y b i j = comm x y (b j) i
-- -- --      RElimSet.hexDiag* w x y z b i j = hexDiag x y z (b j) i
-- -- --      RElimSet.trunc* w _ = trunc _ _

-- -- --   -- sym++2 : ∀ xs ys → xs ++2 ys ≡ ys ++2 xs
-- -- --   -- sym++2 = RElimSet.f w
-- -- --   --   where
-- -- --   --     w : RElimSet (λ xs → ∀ ys → (xs ++2 ys) ≡ (ys ++2 xs))
-- -- --   --     RElimSet.[]* w = rUnit++
-- -- --   --     (w RElimSet.∷* a) {xs} p ys = {!p (a ∷2 [])!}
-- -- --   --     -- cong (a ∷2_) (p ys) ∙ 
-- -- --   --     --         cong (_++2 xs) {!!} ∙ sym (assoc++ ys (a ∷2 []) xs) 
-- -- --   --     RElimSet.comm* w = {!!}
-- -- --   --     RElimSet.hexDiag* w = {!!}
-- -- --   --     RElimSet.trunc* w _ = isSetΠ λ _ → trunc _ _
-- -- --   -- _++2_ = RRec.f w
-- -- --   --   where
-- -- --   --     w : RRec {B = FMSet2 A → FMSet2 A} {!!}
-- -- --   --     w = {!!}

-- -- -- module _ {A : Type ℓ} where
-- -- --   -- isSetLofLA : ∀ n → isSet (ListOfLen A n)
-- -- --   -- isSetLofLA n = isOfHLevelListOfLen 0 isSetA n 

-- -- --   FMSet2OfLen≡ : ∀ {n} → {x y : FMSet2OfLen A n} → fst x ≡ fst y → x ≡ y 
-- -- --   FMSet2OfLen≡ = Σ≡Prop λ _ → isSetℕ _ _

-- -- --   isGroupoidFMSet2OfLen : ∀ n → isGroupoid (FMSet2OfLen A n)
-- -- --   isGroupoidFMSet2OfLen n = 
-- -- --     (isOfHLevelΣ 3 trunc λ _ → isSet→isGroupoid (isProp→isSet (isSetℕ _ _)))

-- -- -- module mkFunTest {CD : hSet ℓ} where

-- -- --   hSet≡ : {A B : Type ℓ} {isSetA : isSet A} {isSetB : isSet B} → A ≡ B →
-- -- --               Path (hSet ℓ) (A , isSetA) (B , isSetB)  
-- -- --   fst (hSet≡ p i) = p i
-- -- --   snd (hSet≡  {isSetA = isSetA} {isSetB} p i) =
-- -- --     isProp→PathP
-- -- --      (λ i → isPropIsSet {A = p i})
-- -- --      isSetA
-- -- --      isSetB i

-- -- --   flipIso : {A B C : Type ℓ} → Iso (A → B → C) (B → A → C) 
-- -- --   Iso.fun flipIso = flip
-- -- --   Iso.inv flipIso = flip
-- -- --   Iso.rightInv flipIso b = refl
-- -- --   Iso.leftInv flipIso b = refl


-- -- --   flip≃ : {A B C : Type ℓ} → (A → B → C) ≃ (B → A → C) 
-- -- --   flip≃ = isoToEquiv flipIso

-- -- --   diagIso : {A B C D : Type ℓ} → Iso (A → B → C → D) (C → B → A → D) 
-- -- --   Iso.fun diagIso x x₁ x₂ x₃ = x x₃ x₂ x₁
-- -- --   Iso.inv diagIso x x₁ x₂ x₃ = x x₃ x₂ x₁
-- -- --   Iso.rightInv diagIso b = refl
-- -- --   Iso.leftInv diagIso b = refl

-- -- --   zzR : RRec {A = Type ℓ} (isGroupoidHSet {ℓ})
-- -- --   RRec.[]* zzR = CD
-- -- --   RRec._∷*_ zzR A HS = (A → fst HS) , isSet→ (snd HS)
-- -- --   RRec.comm* zzR _ _ _ = hSet≡ (ua flip≃) 
-- -- --   RRec.comm-inv* zzR _ _ _ =
-- -- --     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet)) (isInjectiveTransport refl)
-- -- --   RRec.hexDiag* zzR _ _ _ _ = hSet≡ (ua (isoToEquiv diagIso))
-- -- --   RRec.hexU* zzR _ _ _ _ =
-- -- --    ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport refl))
-- -- --   RRec.hexL* zzR _ _ _ _ =
-- -- --    ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport refl))
  
-- -- --   zz : FMSet2 (Type ℓ) → hSet ℓ
-- -- --   zz = RRec.f zzR

-- -- -- module mkRecTest (ℓ : Level) where

-- -- --   hSet≡ : {A B : Type ℓ} {isSetA : isSet A} {isSetB : isSet B} → A ≡ B →
-- -- --               Path (hSet ℓ) (A , isSetA) (B , isSetB)  
-- -- --   fst (hSet≡ p i) = p i
-- -- --   snd (hSet≡  {isSetA = isSetA} {isSetB} p i) =
-- -- --     isProp→PathP
-- -- --      (λ i → isPropIsSet {A = p i})
-- -- --      isSetA
-- -- --      isSetB i

-- -- --   swapIso : {A B C : Type ℓ} → Iso (A × B × C) (B × A × C) 
-- -- --   Iso.fun swapIso (x , y , z) = y , x , z
-- -- --   Iso.inv swapIso (x , y , z) = y , x , z
-- -- --   Iso.rightInv swapIso b = refl
-- -- --   Iso.leftInv swapIso b = refl

-- -- --   diagIso : {A B C D : Type ℓ} → Iso (A × B × C × D) (C × B × A × D) 
-- -- --   Iso.fun diagIso (x , y , z , w) = z , y , x , w
-- -- --   Iso.inv diagIso (x , y , z , w) = z , y , x , w
-- -- --   Iso.rightInv diagIso b = refl
-- -- --   Iso.leftInv diagIso b = refl


-- -- --   zzR : RRec {A = hSet ℓ} (isGroupoidHSet {ℓ})
-- -- --   RRec.[]* zzR = Unit* , isSetUnit*
-- -- --   RRec._∷*_ zzR A HS = fst A × (fst HS) , isSet× (snd A) (snd HS)
-- -- --   RRec.comm* zzR A B HS = hSet≡ (ua (isoToEquiv swapIso))
-- -- --   RRec.comm-inv* zzR A B HS =
-- -- --     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet)) (isInjectiveTransport refl)
-- -- --   RRec.hexDiag* zzR A B C HS =
-- -- --     hSet≡ (ua (isoToEquiv diagIso))
-- -- --   RRec.hexU* zzR _ _ _ _ =
-- -- --        ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport refl))

-- -- --   RRec.hexL* zzR _ _ _ _ =
-- -- --        ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport (
-- -- --        funExt λ _ → cong₂ _,_ refl (cong₂ _,_ refl (cong₂ _,_ refl refl)))))

-- -- -- -- module sum (ℓ : Level) where

-- -- -- --   hSet≡ : {A B : Type ℓ} {isSetA : isSet A} {isSetB : isSet B} → A ≡ B →
-- -- -- --               Path (hSet ℓ) (A , isSetA) (B , isSetB)  
-- -- -- --   fst (hSet≡ p i) = p i
-- -- -- --   snd (hSet≡  {isSetA = isSetA} {isSetB} p i) =
-- -- -- --     isProp→PathP
-- -- -- --      (λ i → isPropIsSet {A = p i})
-- -- -- --      isSetA
-- -- -- --      isSetB i

-- -- -- --   swapIso : {A B C : Type ℓ} → Iso (A × B × C) (B × A × C) 
-- -- -- --   Iso.fun swapIso (x , y , z) = y , x , z
-- -- -- --   Iso.inv swapIso (x , y , z) = y , x , z
-- -- -- --   Iso.rightInv swapIso b = refl
-- -- -- --   Iso.leftInv swapIso b = refl

-- -- -- --   diagIso : {A B C D : Type ℓ} → Iso (A × B × C × D) (C × B × A × D) 
-- -- -- --   Iso.fun diagIso (x , y , z , w) = z , y , x , w
-- -- -- --   Iso.inv diagIso (x , y , z , w) = z , y , x , w
-- -- -- --   Iso.rightInv diagIso b = refl
-- -- -- --   Iso.leftInv diagIso b = refl


-- -- -- --   zzR : RRec {A = hSet ℓ} (isGroupoidHSet {ℓ})
-- -- -- --   RRec.[]* zzR = Unit* , isSetUnit*
-- -- -- --   RRec._∷*_ zzR A HS = fst A × (fst HS) , isSet× (snd A) (snd HS)
-- -- -- --   RRec.comm* zzR A B HS = hSet≡ (ua (isoToEquiv swapIso))
-- -- -- --   RRec.comm-inv* zzR A B HS =
-- -- -- --     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet)) (isInjectiveTransport refl)
-- -- -- --   RRec.hexDiag* zzR A B C HS =
-- -- -- --     hSet≡ (ua (isoToEquiv diagIso))
-- -- -- --   RRec.hexU* zzR _ _ _ _ =
-- -- -- --        ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport refl))

-- -- -- --   RRec.hexL* zzR _ _ _ _ =
-- -- -- --        ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport (
-- -- -- --        funExt λ _ → cong₂ _,_ refl (cong₂ _,_ refl (cong₂ _,_ refl refl)))))




-- -- -- --   zz : FMSet2 (hSet ℓ) → hSet ℓ
-- -- -- --   zz = RRec.f zzR

-- -- -- --   -- uncR : RElim {A = hSet ℓ} λ S → fst (zz S) → FMSet2 (Σ (Type ℓ) λ X → X) 
-- -- -- --   -- RElim.[]* uncR _ = []
-- -- -- --   -- (uncR RElim.∷* x) {xs} x₁ (a , r) = (_ , a) ∷2 x₁ r
-- -- -- --   -- RElim.comm* uncR x y b i =
-- -- -- --   --   (λ b₁ → comm (fst x , fst (snd b₁)) (fst y , fst b₁) (b (snd (snd b₁))) i)
-- -- -- --   --     ∘ ua-unglue (isoToEquiv swapIso) i
-- -- -- --   -- -- toPathP (funExt λ z i → comm {!!} {!!} {!!} i)
-- -- -- --   -- RElim.comm-inv* uncR x y b i j x₁ =
-- -- -- --   --  let xx = {!!}
-- -- -- --   --  in comm-inv (fst x , {!fst x₁!}) {!!} {!!} i j
-- -- -- --   -- RElim.hexDiag* uncR = {!!}
-- -- -- --   -- RElim.hexU* uncR = {!!}
-- -- -- --   -- RElim.hexL* uncR = {!!}
-- -- -- --   -- RElim.trunc* uncR = {!!}

-- -- -- --   -- unc : ∀ S → fst (zz S) → FMSet2 (Σ (Type ℓ) λ X → X)
-- -- -- --   -- unc = {!!}

-- -- -- -- -- module ⊎' where
-- -- -- -- --   -- QL : Bool → Type₀
-- -- -- -- --   -- QL false = ___+_++{!!}
-- -- -- -- --   -- QL true = {!!}

-- -- -- -- --   -- QR : Bool → Type₀
-- -- -- -- --   -- QR x = {!!}

-- -- -- -- --   -- record _⊎'_ {ℓ ℓ'} (A : Type ℓ)(B : Type ℓ') : Type (ℓ-max ℓ ℓ') where 
-- -- -- -- --   --   field
-- -- -- -- --   --     sw : Bool
-- -- -- -- --   --     ll : (Bool→Type sw → A)
-- -- -- -- --   --     rr : (Bool→Type (not sw) → B)

-- -- -- -- --   _⊎'_ : ∀ {ℓ ℓ'} (A : Type ℓ)(B : Type ℓ') → Type (ℓ-max ℓ ℓ')
-- -- -- -- --   A ⊎' B = Σ Bool λ sw → (Bool→Type sw → A) × (Bool→Type (not sw) → B)

-- -- -- -- --   ⊎-swap-Path : ∀ {ℓ ℓ'} (A : Type ℓ)(B : Type ℓ') → (A ⊎' B) ≡ (B ⊎' A)
-- -- -- -- --   ⊎-swap-Path A B i =
-- -- -- -- --    Σ (notEq i)
-- -- -- -- --      ((λ b → ua (Σ-swap-≃ {A = {!Bool→Type b → A!}} {A' = Bool→Type b → B}) i)
-- -- -- -- --        ∘ ua-unglue notEquiv i)

-- -- -- -- --   -- ⊎-swap-Iso : ∀ {ℓ ℓ'} (A : Type ℓ)(B : Type ℓ') → Iso (A ⊎' B) (B ⊎' A)
-- -- -- -- --   -- Iso.fun (⊎-swap-Iso A B) = {!!}
-- -- -- -- --   -- Iso.inv (⊎-swap-Iso A B) = {!!}
-- -- -- -- --   -- Iso.rightInv (⊎-swap-Iso A B) = {!!}
-- -- -- -- --   -- Iso.leftInv (⊎-swap-Iso A B) = {!!}


-- -- -- -- -- module ⊎'2 where
-- -- -- -- --   -- QL : Bool → Type₀
-- -- -- -- --   -- QL false = ___+_++{!!}
-- -- -- -- --   -- QL true = {!!}

-- -- -- -- --   -- QR : Bool → Type₀
-- -- -- -- --   -- QR x = {!!}

-- -- -- -- --   record _⊎'_ {ℓ ℓ'} (A : Type ℓ)(B : Type ℓ') : Type (ℓ-max ℓ ℓ') where 
-- -- -- -- --     field
-- -- -- -- --       sw : Bool
-- -- -- -- --       ll : (Bool→Type sw → A)
-- -- -- -- --       rr : (Bool→Type (not sw) → B)
