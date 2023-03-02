{-# OPTIONS --safe  #-}  --experimental-lossy-unification
module Cubical.HITs.ListedFiniteSet.Base3C where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Path

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚

open import Cubical.Functions.Logic as L
open import Cubical.Foundations.Function

open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.Data.FinData.Properties

open import Cubical.Data.Nat.Order.Recursive

open import Cubical.Relation.Binary



open import Cubical.HITs.GroupoidTruncation as GT using (∥_∥₃ ; ∣_∣₃ ; squash₃) 

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Type ℓ




infixr 5 _∷2_


data FMSet2C {B : Type₀} (A : Type ℓ) : Type ℓ where
  []    : FMSet2C {B = B} A
  _∷2_   : (x : A) → (xs : FMSet2C {B = B} A) → FMSet2C A
  comm  : ∀ x y xs → x ∷2 y ∷2 xs ≡ y ∷2 x ∷2 xs
  comm-inv : ∀ x y xs → 
              comm x y xs ≡ sym (comm y x xs)
  commm : ∀ x y z xs → x ∷2 y ∷2 z ∷2  xs ≡ y ∷2 z ∷2 x ∷2 xs
  commp : ∀ x y z xs → Square
      (comm _ _ (_ ∷2 xs))
      (cong (x ∷2_) (comm y z xs))      
      (commm _ _ _ xs)
      refl
      
  hex : ∀ x y z xs → Square          
          (cong (z ∷2_) (comm x y xs))
          (comm _ _ (_ ∷2 xs))
          (commm _ _ _ xs)
          (commm _ _ _ xs)
  trunc : {guard : B} → isGroupoid (FMSet2C A)

FMSet2 : (A : Type ℓ) →  Type ℓ
FMSet2 = FMSet2C {B = Unit}

module _ {A : Type ℓ} where

 record RElim {ℓ'} {T} (B : FMSet2C {B = T} A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
   []* : B []
   _∷*_ : (x : A) {xs : FMSet2C A} → B xs → B (x ∷2 xs)
   comm* : (x y : A) {xs : FMSet2C A} (b : B xs)
         → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
   comm-inv* : ∀ x y {xs} (b : B xs) → SquareP (λ i j → B (comm-inv x y xs i j))
                      (comm* x y b ) (symP (comm* y x b))
                      refl refl
   commm* : (x y z : A) {xs : FMSet2C A} (b : B xs)
         → PathP (λ i → B (commm x y z xs i))
            (x ∷* (y ∷* (z ∷* b)))
            (y ∷* (z ∷* (x ∷* b)))
   commp* : ∀ x y z {xs : FMSet2C A} (b : B xs) →
             SquareP (λ i j → B (commp x y z xs i j))
             (comm* z x (y ∷* b))
             (congP (λ _ → x ∷*_) (comm* _ _ _))             
             (commm* _ _ _ b)
             refl
   hex* : ∀ x y z {xs : FMSet2C A} (b : B xs) →
             SquareP (λ i j → B (hex x y z xs i j))
             (congP (λ _ → z ∷*_) (comm* x y b))
             (comm* _ _ (_ ∷* b))
             (commm* _ _ _ b)
             (commm* _ _ _ b)              

  ff : (T → ∀ xs → isGroupoid (B xs)) →
      (xs : FMSet2C {B = T} _) → B xs
  ff trunc* = f
   where
   f : (xs : FMSet2C _) → B xs
   f [] = []*
   f (x ∷2 xs) = x ∷* f xs
   f (comm x y xs i) = comm* x y (f xs) i
   f (comm-inv x y xs i j) =
      comm-inv* x y (f xs) i j
   f (commm x y z xs i) = commm* x y z (f xs) i 
   f (commp x y z xs i j) = commp* x y z (f xs) i j 
   f (hex x y z xs i j) = hex* x y z (f xs) i j 
   f (trunc {guard = g} xs ys p q r s i j k) = 
     isOfHLevel→isOfHLevelDep 3 (λ a → trunc* g a)
        _ _ _ _
        (λ j k → f (r j k)) (λ j k → f (s j k)) 
          (trunc xs ys p q r s) i j k

 record RElimSet {ℓ'} {T} (B : FMSet2C {B = T} A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
   []* : B []
   _∷*_ : (x : A) {xs : FMSet2C A} → B xs → B (x ∷2 xs)
   comm* : (x y : A) {xs : FMSet2C A} (b : B xs)
         → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
   -- commm* : (x y z : A) {xs : FMSet2C A} (b : B xs)
   --       → PathP (λ i → B (commm x y z xs i))
   --          (x ∷* (y ∷* (z ∷* b)))
   --          (y ∷* (z ∷* (x ∷* b)))
   trunc* : ∀ xs → isSet (B xs)
   
  fR : RElim B
  RElim.[]* fR = []*
  RElim._∷*_ fR = _∷*_
  RElim.comm* fR = comm*
  RElim.comm-inv* fR = λ _ _ _ → 
    isOfHLevel→isOfHLevelDep 2 (trunc*)
      _ _ _ _ (comm-inv _ _ _)
  RElim.commm* fR x y z {xs} b i =
    comp (λ l → B (commp y z x xs i (~ l)))
       (λ l → λ { (i = i0) → comm* _ _ (_ ∷* b) (~ l)
                ; (i = i1) → _ ∷* comm* _ _ b (~ l)
                })
       (_ ∷* (_ ∷* (_ ∷* b)))
  RElim.commp* fR _ _ _ _ = isSet→SquareP (λ _ _  → trunc* _) _ _ _ _
  RElim.hex* fR _ _ _ _ = isSet→SquareP (λ _ _  → trunc* _) _ _ _ _

  f : (xs : FMSet2C {B = T} _) → B xs
  f = RElim.ff fR λ t → isSet→isGroupoid ∘ trunc*

 record RElimProp {ℓ'} {T} (B : FMSet2C {B = T} A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
   []* : B []
   _∷*_ : (x : A) {xs : FMSet2C A} → B xs → B (x ∷2 xs)
   trunc* : ∀ xs → isProp (B xs)

  fR : RElimSet B
  RElimSet.[]* fR = []*
  RElimSet._∷*_ fR = _∷*_
  RElimSet.comm* fR _ _ _ =
    isProp→PathP (λ i → trunc* (comm _ _ _ i)) _ _
  RElimSet.trunc* fR = isProp→isSet ∘ trunc*
  
  f : (xs : FMSet2C {B = T} _) → B xs
  f = RElimSet.f fR

 record RRec {ℓ'} (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
   []* : B
   _∷*_ : (x : A) → B → B
   comm* : (x y : A) → (b : B)
         →  (x ∷* (y ∷* b)) ≡ (y ∷* (x ∷* b))
   comm-inv* : ∀ x y b → Square {A = B}
                      (comm* x y b ) (sym (comm* y x b))
                      refl refl
   commm* : (x y z : A) (b : B)
         → (x ∷* (y ∷* (z ∷* b)))
           ≡  (y ∷* (z ∷* (x ∷* b)))
   commp* : ∀ x y z b →
             Square {A = B}
             (comm* z x (y ∷* b))
             (cong (x ∷*_) (comm* _ _ _))             
             (commm* _ _ _ b)
             refl
   hex* : ∀ x y z b →
             Square {A = B}
             (cong (z ∷*_) (comm* x y b))
             (comm* _ _ (_ ∷* b))
             (commm* _ _ _ b)
             (commm* _ _ _ b)              
   

  ff : ∀ {T} → (T → isGroupoid B) →
      (FMSet2C {B = T} A) → B
  ff trunc* = f
   where
   f : FMSet2C A → B
   f [] = []*
   f (x ∷2 xs) = x ∷* f xs
   f (comm x y xs i) = comm* x y (f xs) i
   f (comm-inv x y xs i j) =
      comm-inv* x y (f xs) i j
   f (commm x y z xs i) = commm* x y z (f xs) i 
   f (commp x y z xs i j) = commp* x y z (f xs) i j 
   f (hex x y z xs i j) = hex* x y z (f xs) i j 
   f (trunc {guard = g} xs ys p q r s i j k) =
     trunc* g _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k))
       i j k



 RecΣ : (B : Type ℓ') (P : B → hProp ℓ'') (RB : RRec B)
         → ⟨ P (RRec.[]* RB) ⟩ 
         → (∀ a {b} → ⟨ P b ⟩ → ⟨ P (RRec._∷*_ RB a b) ⟩) 
         → RRec (Σ B (fst ∘ P))
 RecΣ B P RB P[] P∷ = w
  where
  module R₁ = RRec RB
  -- module R₂ = RRec RB
  open RRec

  w : RRec (Σ B (fst ∘ P))
  []* w = R₁.[]* , P[]
  (w ∷* x) (xs , ys) = x R₁.∷* xs , P∷ x ys
  comm* w x y b = Σ≡Prop (snd ∘ P) (R₁.comm* x y (fst b))
  comm-inv* w x y b = ΣSquareSet (isProp→isSet ∘ snd ∘ P) (R₁.comm-inv* x y (fst b))
  commm* w x y z (b , _) = Σ≡Prop (snd ∘ P) (R₁.commm* x y z b)
  commp* w x y z b = ΣSquareSet (isProp→isSet ∘ snd ∘ P) (R₁.commp* x y z (fst b))
  hex* w x y z b = ΣSquareSet (isProp→isSet ∘ snd ∘ P) (R₁.hex* x y z (fst b))

 -- RecΣ' : (B : Type ℓ') (P : B → Type ℓ'') (RB : RRec B)
 --         → RElim {!!} 
 --         → RRec (Σ B P)
 -- RecΣ' B P RB RP = w
 --  where
 --  module R₁ = RRec RB
 --  -- module R₂ = RRec RB
 --  open RRec

 --  w : RRec (Σ B (P))
 --  w = {!!}


-- -- toTruncFM2 : ∀ {T T'} → (T → T') → FMSet2C {B = T} A → FMSet2C {B = T'} A
-- -- toTruncFM2 ft = w
-- --  where
-- --  w : FMSet2C _ → FMSet2C _
-- --  w [] = []
-- --  w (x ∷2 x₁) = x ∷2 (w x₁)
-- --  w (comm x y x₁ i) = {!!}
-- --  w (comm-inv x y x₁ i i₁) = {!!}
-- --  w (commm x y z x₁ i) = {!!}
-- --  w (commp x y z x₁ i i₁) = {!!}
-- --  w (hex x y z x₁ i i₁) = {!!}
-- --  w (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
-- --   {!!}
 
-- -- unTrunc : ∀ {T T'} → {!A!} → {!!}
-- -- unTrunc = {!!}

mapFM2 : ∀ {B' B : Type₀} {A' : Type ℓ'} {A : Type ℓ} → (fb : B' → B) (f : A' → A) →
             FMSet2C {B = B'} A' → FMSet2C {B = B} A
mapFM2 fb f = f'
 where
 f' : FMSet2C _ → FMSet2C _
 f' [] = []
 f' (x ∷2 x₁) = f x ∷2 (f' x₁)
 f' (comm x y x₁ i) = comm (f x) (f y) (f' x₁) i
 f' (comm-inv x y x₁ i i₁) = comm-inv (f x) (f y) (f' x₁) i i₁
 f' (commm x y z x₁ i) = commm (f x) (f y) (f z) (f' x₁) i
 f' (commp x y z x₁ i i₁) = commp (f x) (f y) (f z) (f' x₁) i i₁
 f' (hex x y z x₁ i i₁) = hex (f x) (f y) (f z) (f' x₁) i i₁
 f' (trunc {guard = b} x x₁ x₂ y r s i i₁ i₂) =
   trunc {guard = fb b}  _ _ _ _ (λ i j → f' (r i j)) (λ i j → f' (s i j)) i i₁ i₂

<$tt : FMSet2C {B = B} A → FMSet2C Unit
<$tt = mapFM2 (idfun _) (λ _ → tt)

length2 : ∀ {B : Type} {A : Type ℓ} → FMSet2C {B = B} A → ℕ
length2 [] = zero
length2 (x ∷2 x₁) = suc (length2 x₁)
length2 (comm x y x₁ i) = suc (suc (length2 x₁))
length2 (comm-inv x y x₁ i i₁) = suc (suc (length2 x₁))
length2 (commm x y z x₁ i) = suc (suc (suc (length2 x₁)))
length2 (commp x y z x₁ i i₁) = suc (suc (suc (length2 x₁)))
length2 (hex x y z x₁ i i₁) = suc (suc (suc (length2 x₁)))
length2 (trunc x x₁ x₂ y p q i i₁ x₄) =
  isSet→isGroupoid (isSetℕ) _ _ _ _
    (λ i j → length2 (p i j))
    (λ i j → length2 (q i j))
    i i₁ x₄

-- toTruncFM2 : ∀ {T T'} → (T → T') → FMSet2C {B = T} A → FMSet2C {B = T'} A
-- toTruncFM2 fb = mapFM2 fb (idfun _)

-- squashFM2 : ∀ {T T'} →  FMSet2C {B = T} A → ∥ FMSet2C {B = T'} A ∥₃
-- squashFM2 = RElim.ff w λ _ _ → squash₃
--  where
--  w : RElim (λ _ → ∥ FMSet2C _ ∥₃)
--  RElim.[]* w = ∣ [] ∣₃
--  RElim._∷*_ w x = GT.map (x ∷2_)
--  RElim.comm* w _ _ = GT.elim (λ _ → isSet→isGroupoid (squash₃ _ _))
--    (cong ∣_∣₃ ∘ (comm _ _))
--  RElim.comm-inv* w x y =
--    GT.elim (λ _ → isSet→isGroupoid (isProp→isSet (squash₃ _ _ _ _)))
--     λ xs i j →  ∣ comm-inv x y xs i j ∣₃
--  RElim.commm* w _ _ _ = GT.elim (λ _ → isSet→isGroupoid (squash₃ _ _))
--    (cong ∣_∣₃ ∘ (commm _ _ _))
--  RElim.commp* w x y z =
--    GT.elim (λ _ → 
--      isOfHLevelPathP 3
--       (isSet→isGroupoid (squash₃ _ _)) _ _)
--     λ xs i j →  ∣ commp x y z xs i j ∣₃
--  RElim.hex* w x y z =
--    GT.elim (λ _ → 
--      isOfHLevelPathP 3
--       (isSet→isGroupoid (squash₃ _ _)) _ _)
--     λ xs i j →  ∣ hex x y z xs i j ∣₃


-- truncℙ₂ : ∀ {T T'}-- → (fb : T → T')
--            → (C : Type ℓ')
--            → (isGroupoidC : isGroupoid C)
--            → (FMSet2C {B = T} A → C)
--            → FMSet2C {B = T'} A  → C
-- truncℙ₂ C isGrpC f =
--   GT.rec isGrpC f ∘ squashFM2


-- module _ {A' : Type ℓ'} {T} (A : Type ℓ) where

--  sR𝕃 : RRec {A = A'} (Σ (Type ℓ) λ X → X → FMSet2C {B = T} A)
--  RRec.[]* sR𝕃 =
--    Unit* , (λ _ → [])
--  (sR𝕃 RRec.∷* _) (X , e) =
--    A × X , λ (a , x) → a ∷2 e x
--  RRec.comm* sR𝕃 _ _ (X , e) i =
--    (ua (Σ-swap-01-≃ {A = A} {A} {X}) i) ,
--     (λ (a , a' , xs) → comm a' a (e xs) i) ∘' ua-unglue Σ-swap-01-≃ i
--  RRec.comm-inv* sR𝕃 _ _ (X , e) i j =
--    Σ-swap-01-≡-invol {A = A} (λ _ → X) i j ,
--      (λ (a , a' , xs) → comm-inv a a' (e xs) i j)
--       ∘' unglue (i ∨ ~ i) ∘' unglue (j ∨ ~ j)
--  RRec.commm* sR𝕃 _ _ _ (X , e) i =
--    (𝑮 (Σ-swap-01-≃ {A = A} {A} {A × X})
--            refl (≃-× (idEquiv A) (Σ-swap-01-≃ {A = A} {A} {X})) i) ,
--      (λ (a , a' , a'' , xs) → commm a' a a'' (e xs) i)
--        ∘' unglue (i ∨ ~ i)
--  RRec.commp* sR𝕃 _ _ _ (X , e) i j =
--   Σ-swap-012-≡-comp-ua (λ _ → A × A × A × X) (~ i) j ,
--     (λ (a , a' , a'' , xs) → commp a a'' a' (e xs) i j)
--      ∘' unglue (i ∨ j ∨ (~ j ∧ ~ i))
--  RRec.hex* sR𝕃 _ _ _ (X , e) i j =
--    hex.hexSq A X i j ,
--      (λ (a , a' , a'' , xs) →
--           hex a'' a a' (e xs) i j) ∘'
--           unglue (j ∨ ~ j) ∘' unglue (i ∨ ~ i)

--  sR𝕃IsEquiv : RRec {A = A'} {!!}
--  sR𝕃IsEquiv = RecΣ {!!} (λ x → _ , isPropIsEquiv (snd x)) sR𝕃
--    {!!} {!!}

module _ {A' : Type ℓ'} (A : Type ℓ) where

 R𝕃 : RRec {A = A'} (Type ℓ)
 RRec.[]* R𝕃 = Unit*
 RRec._∷*_ R𝕃 _ = A ×_ 
 RRec.comm* R𝕃 _ _ X = ua (Σ-swap-01-≃ {A = A} {A} {X})
 RRec.comm-inv* R𝕃 _ _ X = Σ-swap-01-≡-invol {A = A} (λ _ → X)
 RRec.commm* R𝕃 _ _ _ X =
         𝑮 (Σ-swap-01-≃ {A = A} {A} {A × X})
           refl (≃-× (idEquiv A) (Σ-swap-01-≃ {A = A} {A} {X}))     
 RRec.commp* R𝕃 _ _ _ X =
   symP (Σ-swap-012-≡-comp-ua (λ _ → A × A × A × X))
 RRec.hex* R𝕃 _ _ _ = hex.hexSq A


 module _ (isSetA : isSet A) {T} where
  Rh𝕃₂ : RRec {A = A'} (hSet ℓ)
  Rh𝕃₂ = RecΣ _ (λ x → isSet x , isPropIsSet) R𝕃
         isSetUnit* λ _ → isSet× isSetA

  𝕃₂ : FMSet2C {B = T} A' → Type ℓ
  𝕃₂ = fst ∘ RRec.ff Rh𝕃₂ λ _ → isGroupoidHSet

  isSet𝕃₂ : ∀ 𝕝 → isSet (𝕃₂ 𝕝)
  isSet𝕃₂ = snd ∘ RRec.ff Rh𝕃₂ λ _ → isGroupoidHSet
  -- 𝕃₂test : ∀ a xs → 𝕃₂ (a ∷2 xs) → 𝕃₂ (xs)
  -- 𝕃₂test _ _ = snd

module 𝕃Fin {T} {A' : Type ℓ'} where

 𝕃Bool = 𝕃₂ {A' = A'} Bool (isSetBool) {T}

 
 𝕃allFalse : ∀ 𝕝 → 𝕃Bool 𝕝 → hProp ℓ-zero
 𝕃allFalse = RElimSet.f w
  where
  w : RElimSet (λ z → 𝕃Bool z → hProp ℓ-zero)
  RElimSet.[]* w _ = L.⊤
  (w RElimSet.∷* _) f (b , xs) = if b then L.⊥ else f xs
  RElimSet.comm* w x y {xs} b =
    Σ-swap-01→hProp _ _ _ _
      w'
   where
   w' : _
   w' true true z = refl
   w' false y z = refl
   w' x false z = refl
   
  RElimSet.trunc* w _ = isSet→ isSetHProp

 repeatF : ∀ 𝕝 → 𝕃Bool 𝕝
 repeatF = RElimSet.f w
  where
  w : RElimSet 𝕃Bool
  RElimSet.[]* w = tt*
  RElimSet._∷*_ w a' {xs} = false ,_
  RElimSet.comm* w a' b' b i = ua-gluePathExt Σ-swap-01-≃ i (false , false , b)
  RElimSet.trunc* w =
    snd ∘
    RRec.ff (Rh𝕃₂ _ isSetBool {Unit})  (λ _ → isGroupoidHSet)
 
 repeat𝕃allFalse : ∀ 𝕝 → ⟨ 𝕃allFalse 𝕝 (repeatF 𝕝) ⟩ 
 repeat𝕃allFalse = RElimProp.f w
  where
  w : RElimProp (λ z → ⟨ 𝕃allFalse z (repeatF z) ⟩)
  RElimProp.[]* w = tt*
  (w RElimProp.∷* x) x₁ = x₁
  RElimProp.trunc* w 𝕝 = snd (𝕃allFalse 𝕝 (repeatF 𝕝))




 𝕃FinSnd : ∀ 𝕝 → 𝕃Bool 𝕝 → hProp ℓ-zero
 𝕃FinSnd = RElimSet.f w
  where
  w : RElimSet (λ z → 𝕃Bool z → hProp ℓ-zero)
  RElimSet.[]* w _ = L.⊥
  (w RElimSet.∷* _) {xs} f (b , bs) =
    if b then 𝕃allFalse xs bs else (f bs)

  RElimSet.comm* w x y {xs} b = Σ-swap-01→hProp _ _ _ _
      w'
   where
   w' : _
   w' true true z = refl
   w' false y z = refl
   w' x false z = refl

  RElimSet.trunc* w _ = isSet→ isSetHProp



 𝕃Fin : FMSet2C {B = T} A' → Type
 𝕃Fin 𝕝 = Σ (𝕃Bool 𝕝) (fst ∘ 𝕃FinSnd 𝕝)

 𝕃Fin0 : ∀ 𝕝 {a'} → 𝕃Fin (a' ∷2 𝕝)
 𝕃Fin0 𝕝 {a'} = (true , repeatF 𝕝) , repeat𝕃allFalse 𝕝 

 𝕃Fin-suc : ∀ 𝕝 {a'} → 𝕃Fin 𝕝 →  𝕃Fin (a' ∷2 𝕝)
 𝕃Fin-suc 𝕝 x = (false , (fst x)) , (snd x)

 -- 𝕃Fin-comm : ∀ 𝕝 {a' a''} → 𝕃Fin (a' ∷2 a'' ∷2 𝕝) →
 --              PathP (λ i → 𝕃Fin (comm a' a'' 𝕝 i))
 --                {!!}
 --                {!!}
 -- 𝕃Fin-comm 𝕝 x = {!!}


 𝕃Fin-comm : ∀ 𝕝 {a' a''} → (x : 𝕃Fin 𝕝) →
              PathP (λ i → 𝕃Fin (comm a' a'' 𝕝 i))
                (𝕃Fin-suc (a' ∷2 𝕝) {a''} (𝕃Fin-suc 𝕝 {a'} x))
                (𝕃Fin-suc (a'' ∷2 𝕝) {a'} (𝕃Fin-suc 𝕝 {a''} x))
 𝕃Fin-comm 𝕝 {a'} {a''} x =
   ΣPathPProp (snd ∘ 𝕃FinSnd (a'' ∷2 a' ∷2 𝕝))
        λ i → glue'-Σ-swap-01 refl i (false , false , fst x)

 𝕃Fin-swap01 : ∀ 𝕝 {a' a''} → 𝕃Fin (a' ∷2 a'' ∷2 𝕝) → 𝕃Fin (a'' ∷2 a' ∷2 𝕝)
 fst (𝕃Fin-swap01 𝕝 x) = swap-01 (fst x)
 snd (𝕃Fin-swap01 𝕝 ((false , false , _) , x)) = x
 snd (𝕃Fin-swap01 𝕝 ((false , true , _) , x)) = x
 snd (𝕃Fin-swap01 𝕝 ((true , false , _) , x)) = x

 𝕃Fin-comm-unglue : ∀ 𝕝 {a' a''} →
              PathP (λ i → 𝕃Fin (comm a' a'' 𝕝 i) → (𝕃Fin (a'' ∷2 a' ∷2 𝕝)))
                (𝕃Fin-swap01 𝕝 {a'} {a''})
                (idfun _)
                -- (𝕃Fin-suc (a' ∷2 𝕝) {a''} (𝕃Fin-suc 𝕝 {a'} x))
                -- (𝕃Fin-suc (a'' ∷2 𝕝) {a'} (𝕃Fin-suc 𝕝 {a''} x))
 fst (𝕃Fin-comm-unglue 𝕝 {a'} {a''} i (x , y)) =
   ua-unglue Σ-swap-01-≃ i x
 snd (𝕃Fin-comm-unglue 𝕝 {a'} {a''} i (x , y)) =
   isProp→PathP
     (λ i → isPropΠ λ (x : 𝕃Fin (comm a' a'' 𝕝 i)) → snd (𝕃FinSnd (a'' ∷2 a' ∷2 𝕝)
         (ua-unglue Σ-swap-01-≃ i (fst x))))
           (snd ∘ (𝕃Fin-swap01 𝕝 {a'} {a''})) snd i (x , y)


 𝕃Fin-01 : ∀ 𝕝 {a' a''} → 
       PathP (λ i → 𝕃Fin (comm a' a'' 𝕝 i) × 𝕃Fin (comm a' a'' 𝕝 i))
         (𝕃Fin0 (a' ∷2 𝕝) {a''} , 𝕃Fin-suc (a'' ∷2 𝕝) {a'} (𝕃Fin0 𝕝 {a''}))
         (𝕃Fin-suc (a' ∷2 𝕝) {a''} (𝕃Fin0 𝕝 {a'}) , (𝕃Fin0 (a'' ∷2 𝕝) {a'}))
 𝕃Fin-01 𝕝 {a'} {a''} =
   ΣPathP ((ΣPathPProp (snd ∘ 𝕃FinSnd (a'' ∷2 a' ∷2 𝕝))
               λ i → glue'-Σ-swap-01 refl i
                 (true , false , repeatF 𝕝)) ,
          (ΣPathPProp (snd ∘ 𝕃FinSnd (a'' ∷2 a' ∷2 𝕝))
               λ i → glue'-Σ-swap-01 refl i
                 (false , true , repeatF 𝕝)))

-- infix  0 dep-if_then_else_

-- dep-if_then_else_ : Bool → A → A → A
-- dep-if true  then x else y = x
-- dep-if false then x else y = y

-- singl' : Type ℓ → Type (ℓ-suc ℓ)
-- singl' {ℓ} A =
--   Σ (Type ℓ)
--   λ T → Σ (A → T)
--   λ f →
--    Σ (∀ (x : T) → A)
--    λ g → ∀ (x : T) → Σ (f (g x) ≡ x)
--      {!!}

open 𝕃Fin {T = Unit} {A' = Unit} public

FM2⊤ : Type
FM2⊤ = FMSet2C {ℓ-zero} {Unit} Unit


-- Iso-look-tab' : Iso (Σ FM2⊤ λ 𝕝 → (𝕃Fin 𝕝 → A)) (FMSet2 A)
-- Iso-look-tab' = {!!}


-- Iso-look-tabΩ : ∀ {x y : FMSet2 A} → (x ≡ y) ≃
--                   Σ {!!} {!!}
-- Iso-look-tabΩ = congEquiv (isoToEquiv (invIso  Iso-look-tab')) ∙ₑ
--     invEquiv ΣPath≃PathΣ 

-- module //↔ (A : Type ℓ) where

 
--  repFM2⊤ : ℕ → FM2⊤
--  repFM2⊤ zero = []
--  repFM2⊤ (suc x) = _ ∷2 repFM2⊤ x

--  -- List' : Type ℓ
--  -- List' = Σ ℕ λ n → 𝕃Fin (repFM2⊤ n) → A
--  𝕃ist : Type ℓ
--  𝕃ist = Σ _ λ 𝕝 → 𝕃Fin 𝕝 → A

--  List→List'snd : (l : List A) → 𝕃Fin (repFM2⊤ (length l)) → A
--  List→List'snd (x₁ ∷ l) ((false , snd₂) , snd₁) = List→List'snd l (snd₂ , snd₁)
--  List→List'snd (x₁ ∷ l) ((true , snd₂) , snd₁) = x₁

--  List→List' : List A → 𝕃ist
--  List→List' l = repFM2⊤ (length l) , List→List'snd l
 
 



-- subst-adjT : ∀ (a a' : A) (xs : FMSet2C _) →
--              subst (λ x → 𝕃Bool (mapFM2 (idfun Unit) (λ _ → tt) x))
--                (comm a a' xs) ≡
--                  λ x → (swap-01 x) 
-- subst-adjT a a' xs = funExt (uaβ Σ-swap-01-≃) 


module _ {A : Type ℓ} where
 fromList : List A → FMSet2 A
 fromList [] = []
 fromList (x ∷ xs) = x ∷2 fromList xs

 _↔_ : Rel (List A) (List A) ℓ
 _↔_ x y = fromList x ≡ fromList y

 _≡'_ : ℕ → ℕ → Type
 zero ≡' zero = Unit
 zero ≡' suc x₁ = ⊥.⊥
 suc x ≡' zero = ⊥.⊥
 suc x ≡' suc x₁ = x ≡' x₁

 sameL : (FMSet2 B) → (List A) → Type
 sameL p l = (length2 p) ≡' (length l)


--  ↔-trans : (a b c : List A) → a ↔ b → b ↔ c → a ↔ c
--  ↔-trans _ _ _ = _∙_

--  ↔// : Type ℓ
--  ↔// = (List A) // ↔-trans

--  infixr 5 _↔∷_

--  _↔∷_ : A → ↔// → ↔//
--  _↔∷_ a = GQ.Rrec.f w
--   where
--   w : Rrec// ↔//
--   Rrec//.Bgpd w = squash//
--   Rrec//.fb w = [_]// ∘' (a ∷_)
--   Rrec//.feq w = eq// ∘ cong (a ∷2_)
--   Rrec//.fsq w r s =
--     comp// _ _ ▷ cong eq// (sym (cong-∙ (a ∷2_) _ _)) 


--  -- comm-↔∷ : ∀ a a' l l' → (r : l ↔ l') →
--  --      PathP (λ i → (a ↔∷ (a' ↔∷ eq// r i)) ≡ (a' ↔∷ (a ↔∷ eq// r i)))
--  --      (eq// (comm a a' (fromList l))) (eq// (comm a a' (fromList l')))
--  -- comm-↔∷ a a' [] [] r =
--  --   flipSquare ( {!!} ◁ (λ _ → refl) ▷ {!!})
--  -- comm-↔∷ a a' [] (x ∷ l') r = {!cong length2!}
--  -- comm-↔∷ a a' (x ∷ l) [] r = {!!}
--  -- comm-↔∷ a a' (x ∷ l) (x₁ ∷ l') r =
--  --   {!!}
--  -- -- flipSquare
--  -- --   ( {!!} ◁ ({!(λ i → a' ↔∷ (a ↔∷ eq// r i))!}))

--  -- comm-↔∷ : ∀ a a' l l' → (r : l ↔ l') →
--  --      PathP (λ i → (a ↔∷ (a' ↔∷ eq// r i)) ≡ (a' ↔∷ (a ↔∷ eq// r i)))
--  --      (eq// (comm a a' (fromList l))) (eq// (comm a a' (fromList l')))
--  -- comm-↔∷ a a' l l' r = comm→PathP
--  --   (sym (comp'// _ _ _ _) ∙∙
--  --     cong eq// (PathP→comm
--  --       (λ i j → comm a a' (r i) j))
--  --     ∙∙ (comp'// _ _ _ _))

--  -- inv-↔∷ : (b : ↔//) →
--  --      Square (RRec.comm* w x y b) (sym (RRec.comm* w y x b)) refl refl

--  comm-↔∷ : (x y : A) (b : ↔//) → x ↔∷ y ↔∷ b ≡ y ↔∷ x ↔∷ b
--  comm-↔∷ a a' = GQ.RelimSet.f w'
--    where
--    w' : RelimSet _
--    RelimSet.truncB w' _ = squash// _ _
--    RelimSet.fb w' _ = eq// (comm _ _ _)
--    RelimSet.fbEq w' r = comm→PathP
--      (sym (comp'// _ _ _ _) ∙∙
--        cong eq// (PathP→comm
--          (λ i j → comm a a' (r i) j))
--        ∙∙ (comp'// _ _ _ _))

--  comm-↔∷-inv : (x y : A) (b : ↔//) →
--       Square (comm-↔∷ x y b) (sym (comm-↔∷ y x b)) refl refl
--  comm-↔∷-inv x y = GQ.RelimProp.f w'
--   where
--   w' : GQ.RelimProp _
--   RelimProp//.truncB w' _ = squash// _ _ _ _
--   RelimProp//.fb w' a = {!!}
--     -- flipSquareP (compPathR→PathP
--     --  (cong sym (sym (refl≡Id ↔-trans (comm _ _ _ ∙ comm _ _ _)
--     --    {!!})) ∙∙ {!comp'// _ _  _!} ∙∙ cong′ (comm-↔∷ x y [ a ]//  ∙_) (lUnit _))) 


--  FM2→// : (FMSet2 A) → ↔//
--  FM2→// = RRec.ff w λ _ → squash//
--   where
--   w : RRec ↔//
--   RRec.[]* w = [ [] ]//
--   RRec._∷*_ w = _↔∷_
--   RRec.comm* w = comm-↔∷
--   RRec.comm-inv* w = {!!}
--    --  GQ.RelimProp.f w'
--    -- where
--    -- w' : GQ.RelimProp _
--    -- RelimProp//.truncB w' _ = {!squash// _ _ _ _!}
--    -- RelimProp//.fb w' = {!!}
--   RRec.commm* w = {!!}
--   RRec.commp* w = {!!}
--   RRec.hex* w = {!!}

--  //→FM2 : ↔// → FMSet2 A 
--  //→FM2 = GQ.Rrec.f w
--   where
--   w : Rrec// (FMSet2 A)
--   Rrec//.Bgpd w _ = trunc _
--   Rrec//.fb w = fromList
--   Rrec//.feq w = idfun _
--   Rrec//.fsq w r s = compPath-filler _ _

--  -- ri-lem : RelimSet (λ z → FM2→// (//→FM2 z) ≡ z)
--  -- RelimSet.truncB ri-lem _ = squash// _ _
--  -- RelimSet.fb = ?
--  -- -- ri-lem [] = refl
--  -- -- RelimSet.fb ri-lem (a ∷ x) =
--  -- --   {!cong (a ↔∷_) (RelimSet.fb w (xs))!}
--  -- RelimSet.fbEq ri-lem = {!!}

--  ri-fb : (a : List A) → FM2→// (//→FM2 [ a ]//) ≡ [ a ]//
--  ri-fb [] = refl
--  ri-fb (a ∷ xs) =
--   cong (a ↔∷_) (ri-fb xs) 

--  ri-fbEq : ∀ a b → (r : a ↔ b) →
--       PathP (λ i → FM2→// (r i) ≡ eq// r i) (ri-fb a)
--       (ri-fb b)
--  ri-fbEq a b r = flipSquare
--    ( {!!} ◁ {!!})
 
-- --  Iso-FM2-// : Iso (FMSet2 A) ↔//
-- --  Iso.fun Iso-FM2-// = FM2→//
-- --  Iso.inv Iso-FM2-// = //→FM2
-- --  Iso.rightInv Iso-FM2-// = GQ.RelimSet.f w
-- --   where
-- --   w : RelimSet (λ z → Iso.fun Iso-FM2-// (Iso.inv Iso-FM2-// z) ≡ z)
-- --   RelimSet.truncB w _ = squash// _ _
-- --   RelimSet.fb w = ri-fb
-- --   RelimSet.fbEq w = ri-fbEq _ _
  
-- --  Iso.leftInv Iso-FM2-// = RElimSet.f w
-- --   where
-- --   w : RElimSet _
-- --   RElimSet.[]* w = refl
-- --   RElimSet._∷*_ w a {xs} p =
-- --     {!!} ∙ cong (a ∷2_) p
-- --   RElimSet.comm* w = {!!}
-- --   RElimSet.trunc* w _ = trunc _ _

-- --  -- 𝕃' : ∀ 𝕝 → Σ (Type ℓ) λ T → (𝕃Fin 𝕝 → A) ≃ T
-- --  -- 𝕃' = RElim.ff w {!!}
-- --  --  where
-- --  --  w : RElim (λ z → Σ (Type ℓ) (_≃_ (𝕃Fin z → A)))
-- --  --  fst (RElim.[]* w) = {!!}
-- --  --  fst (snd (RElim.[]* w)) = {!!}
-- --  --  snd (snd (RElim.[]* w)) = {!!}
-- --  --  fst ((w RElim.∷* x) {xs} x₁) = {!!}
-- --  --  snd ((w RElim.∷* x) x₁) = {!!}
-- --  --  RElim.comm* w = {!!}
-- --  --  RElim.comm-inv* w = {!!}
-- --  --  RElim.commm* w = {!!}
-- --  --  RElim.commp* w = {!!}
-- --  --  RElim.hex* w = {!!}



-- module _ (A : Type ℓ) where

--  𝕃tab : ∀ 𝕝 → (𝕃Fin 𝕝 → A) → FMSet2 A
--  𝕃tab = RElim.ff w λ _ → λ _ → isGroupoidΠ λ _ → trunc
--   where
--   w : RElim (λ z → (𝕃Fin z → A) → FMSet2 A)
--   RElim.[]* w _ = []
--   (w RElim.∷* x) {𝕝} X f =
--     f (𝕃Fin0 𝕝) ∷2 X (f ∘' 𝕃Fin-suc 𝕝)
--   RElim.comm* w x y {𝕝} X i f =
--    let (f0 , f1) = 𝕃Fin-01 𝕝 i
--    in comm (f f0) (f f1)
--         (X (f ∘' λ x → 𝕃Fin-comm 𝕝 x i )) i
--   RElim.comm-inv* w =
--    {!!}
--   RElim.commm* w = {!!}
--   RElim.commp* w = {!!}
--   RElim.hex* w = {!!}


 
--  module _ (isGroupoidA : isGroupoid A) where

--   𝕃look : (𝕝 : FMSet2 A) → (𝕃Fin (mapFM2 (idfun _) (λ _ → _) 𝕝) → A)
--   𝕃look = RElim.ff
--      w λ _ _ → isGroupoidΠ λ _ → isGroupoidA
--    where

--    open RElim

--    w∷ : (x : A) (xs : FMSet2C A) → 
--          (𝕃Fin (mapFM2 (idfun Unit) (λ _ → tt) xs) → A) →
--           𝕃Fin (mapFM2 (idfun Unit) (λ _ → tt) (x ∷2 xs)) → A
--    w∷ _ _ f ((false , bs) , p) = f (bs , p)
--    w∷ a _ _ ((true , _) , _) = a

--    w-comm : (a a' : A) (xs : FMSet2C A) → 
--          (f : 𝕃Fin (mapFM2 (idfun Unit) (λ _ → tt) xs) → A) →
--           w∷ a (a' ∷2 xs) (w∷ a' xs f) ≡
--           (λ x →
--             w∷ a' (a ∷2 xs) (w∷ a xs f)
--             (𝕃Fin-swap01 (mapFM2 (idfun Unit) (λ _ → tt) xs) x))
--    w-comm a a' xs f i ((false , false , bs) , snd₁) = f (bs , snd₁)
--    w-comm a a' xs f i ((false , true , bs) , snd₁) = a'
--    w-comm a a' xs f i ((true , false , bs) , snd₁) = a


--    w : RElim (λ z → 𝕃Fin (mapFM2 (idfun Unit) (λ _ → tt) z) → A)
--    []* w ()
--    (w ∷* x) {xs} = w∷ x xs
--    comm* w a a' {𝕝} b =
--       w-comm a a' 𝕝 b
--        ◁ (λ i → w∷ a' (a ∷2 𝕝) (w∷ a 𝕝 b)
--             ∘ (𝕃Fin-comm-unglue (mapFM2 (idfun Unit) (λ _ → _) 𝕝) i)) 

--    comm-inv* w = {!!}
--    commm* w = {!!}
--    commp* w = {!!}
--    hex* w = {!!}

--   look-tab : section (uncurry 𝕃tab)
--       (λ 𝕝 → mapFM2 (idfun Unit) (λ _ → tt) 𝕝 , 𝕃look 𝕝)
--   look-tab = RElimSet.f w
--    where
--    w : RElimSet
--          (λ z →
--             uncurry 𝕃tab (mapFM2 (idfun Unit) (λ _ → tt) z , 𝕃look z) ≡ z)
--    RElimSet.[]* w = refl
--    (w RElimSet.∷* a) x₁ = cong (a ∷2_) x₁
--    RElimSet.comm* w a a' {xs} b =
--      flipSquareP (
--        ({!!})
--        ◁ λ i j → comm-inv a a' (b i) (~ i) j)
--    RElimSet.trunc* w _ = trunc _ _

--   tab-look-fst : (x : FM2⊤) → (y : 𝕃Fin x → A) →
--      mapFM2 (idfun Unit) (λ _ → tt) (uncurry 𝕃tab (x , y)) ≡ x

--   tab-look-fst = RElimSet.f w
--    where
--    w : RElimSet
--          (λ z →
--             (y : 𝕃Fin z → A) →
--             mapFM2 (idfun Unit) (λ _ → tt) (uncurry 𝕃tab (z , y)) ≡ z)
--    RElimSet.[]* w _ = refl
--    (w RElimSet.∷* x ) {xs} x₁ y = cong (x ∷2_) (x₁ (y ∘ 𝕃Fin-suc xs)) 
--    RElimSet.comm* w x y {xs} b i f j =
--      {!!}
--    RElimSet.trunc* w = {!!}

-- --   tab-look-snd : (x : FM2⊤) → (y : 𝕃Fin x → A) →
-- --      PathP (λ i → 𝕃Fin (tab-look-fst x y i) → A)
-- --        (𝕃look (uncurry 𝕃tab (x , y))) y     

-- --   tab-look-snd = {!!}

   
-- --   Iso-look-tab : Iso (Σ FM2⊤ λ 𝕝 → (𝕃Fin 𝕝 → A)) (FMSet2 A)
-- --   Iso.fun Iso-look-tab = uncurry 𝕃tab
-- --   Iso.inv Iso-look-tab =
-- --     λ 𝕝 → (mapFM2 (idfun _) (λ _ → _) 𝕝) , 𝕃look 𝕝
-- --   Iso.rightInv Iso-look-tab = look-tab
-- --   fst (Iso.leftInv Iso-look-tab (x , y) i) = tab-look-fst x y i
-- --   snd (Iso.leftInv Iso-look-tab (x , y) i) = tab-look-snd x y i

-- -- -- --  -- 𝕃 : FMSet2C {B = ⊥.⊥} A' → Type ℓ
-- -- -- -- -- --  𝕃 [] = Unit*
-- -- -- -- -- --  𝕃 (x ∷2 xs) = A × 𝕃 xs
-- -- -- -- -- --  𝕃 (comm _ _ xs i) = ua (Σ-swap-01-≃ {A = A} {A} {𝕃 xs}) i 
-- -- -- -- -- --  𝕃 (comm-inv _ _ xs i i₁) = Σ-swap-01-≡-invol {A = A} (λ _ → 𝕃 xs)  i i₁
-- -- -- -- -- --  𝕃 (commm _ _ _ xs i) =
-- -- -- -- -- --        (𝑮 (Σ-swap-01-≃ {A = A} {A} {A × 𝕃 xs})
-- -- -- -- -- --            refl (≃-× (idEquiv A) (Σ-swap-01-≃ {A = A} {A} {𝕃 xs}))) i     
-- -- -- -- -- --  𝕃 (commp _ _ _ xs i i₁) = Σ-swap-012-≡-comp-ua (λ _ → A × A × A × 𝕃 xs) (~ i) i₁
-- -- -- -- -- --  𝕃 (hex x y z xs i i₁) = hex.hexSq A (𝕃 xs) i i₁

 


-- -- -- -- -- -- module _ {A' : Type ℓ'} (A : Type ℓ) where
-- -- -- -- -- --  𝕃 : FMSet2C {B = ⊥.⊥} A' → Type ℓ
-- -- -- -- -- --  𝕃 [] = Unit*
-- -- -- -- -- --  𝕃 (x ∷2 xs) = A × 𝕃 xs
-- -- -- -- -- --  𝕃 (comm _ _ xs i) = ua (Σ-swap-01-≃ {A = A} {A} {𝕃 xs}) i 
-- -- -- -- -- --  𝕃 (comm-inv _ _ xs i i₁) = Σ-swap-01-≡-invol {A = A} (λ _ → 𝕃 xs)  i i₁
-- -- -- -- -- --  𝕃 (commm _ _ _ xs i) =
-- -- -- -- -- --        (𝑮 (Σ-swap-01-≃ {A = A} {A} {A × 𝕃 xs})
-- -- -- -- -- --            refl (≃-× (idEquiv A) (Σ-swap-01-≃ {A = A} {A} {𝕃 xs}))) i     
-- -- -- -- -- --  𝕃 (commp _ _ _ xs i i₁) = Σ-swap-012-≡-comp-ua (λ _ → A × A × A × 𝕃 xs) (~ i) i₁
-- -- -- -- -- --  𝕃 (hex x y z xs i i₁) = hex.hexSq A (𝕃 xs) i i₁


-- -- -- -- -- --  isOfHLevel𝕃 : ∀ n → isOfHLevel n A → ∀ 𝕝 → isOfHLevel n (𝕃 𝕝)
-- -- -- -- -- --  isOfHLevel𝕃 n Hl = RElimProp.f w
-- -- -- -- -- --   where
-- -- -- -- -- --   w : RElimProp (λ z → isOfHLevel n (𝕃 z))
-- -- -- -- -- --   RElimProp.[]* w = isOfHLevelUnit* n
-- -- -- -- -- --   RElimProp._∷*_ w x = isOfHLevel× n Hl
-- -- -- -- -- --   RElimProp.trunc* w _ = isPropIsOfHLevel n

-- -- -- -- -- -- module _ (A : Type ℓ) where
-- -- -- -- -- --  𝕃' : FMSet2C A → Type ℓ
-- -- -- -- -- --  𝕃' = λ 𝕝 → 𝕃 A (mapFM2 {A' = A} (idfun _) (λ _ → tt) 𝕝)

-- -- -- -- -- --  from𝕃 : ∀ 𝕝 → 𝕃' 𝕝
-- -- -- -- -- --  from𝕃 [] = tt*
-- -- -- -- -- --  from𝕃 (x ∷2 𝕝) = x , from𝕃 𝕝
-- -- -- -- -- --  from𝕃 (comm x y 𝕝 i) = glue-Σ-swap-01 (λ _ → 𝕃' 𝕝) i (y , x , from𝕃 𝕝)
-- -- -- -- -- --  from𝕃 (comm-inv x y 𝕝 i i₁) = Σ-swap-01-≡-invol-ua-glue i i₁ (x , y , from𝕃 𝕝)
-- -- -- -- -- --  from𝕃 (commm x x' x'' 𝕝 i) = 
-- -- -- -- -- --     glue (λ { (i = i1) → _ ; (i = i0) → _ })
-- -- -- -- -- --       (x' , x , x'' , from𝕃 𝕝) 
-- -- -- -- -- --  from𝕃 (commp x y z 𝕝 i i₁) =
-- -- -- -- -- --    glue (λ { (i = i0)(i₁ = i0) → _
-- -- -- -- -- --         ; (i = i1) → x , glue (λ { (i₁ = i0) → _ ; (i₁ = i1) → _ }) ((z , y , from𝕃 𝕝))
-- -- -- -- -- --         ; (i₁ = i1) → _ }) (x , z , y , from𝕃 𝕝)     
-- -- -- -- -- --  from𝕃 (hex x' x'' x 𝕝 i j) =
-- -- -- -- -- --   let z = from𝕃 𝕝
-- -- -- -- -- --   in glue (λ {(i = i0) → _ , glue (λ {(j = i0) → _ ;(j = i1) → _ }) (x'' , x' , z)
-- -- -- -- -- --       ;(i = i1) → (glue (λ {(j = i0) → _ ;(j = i1) → _ }) (x'' , x' , x , z))
-- -- -- -- -- --       }) (glue (λ {(j = i0) → _ ;(j = i1) → _ }) (x'' , x , x' , z))


-- -- -- -- -- --  Σ𝕃 : Type ℓ
-- -- -- -- -- --  Σ𝕃 = Σ _ (𝕃 {A' = Unit} A)

-- -- -- -- -- --  from𝕃Σ : FMSet2C A → Σ𝕃
-- -- -- -- -- --  from𝕃Σ 𝕝 = mapFM2 {A' = A} (idfun _) (λ _ → tt) 𝕝 , from𝕃 𝕝

-- -- -- -- -- -- module _ {A' : Type ℓ'} {A : Type ℓ} (isSetA : isSet A) where
-- -- -- -- -- --  h𝕃₂ : FMSet2 A' → hSet ℓ
-- -- -- -- -- --  h𝕃₂ = truncℙ₂ _ isGroupoidHSet  λ 𝕝 → 𝕃 A 𝕝 , isOfHLevel𝕃 _ 2 isSetA 𝕝 

-- -- -- -- -- --  𝕃₂ : FMSet2 A' → Type ℓ
-- -- -- -- -- --  𝕃₂ = fst ∘' h𝕃₂ 

-- -- -- -- -- --  -- 𝕃₂test : ∀ a' xs → 𝕃₂ (a' ∷2 xs) → A
-- -- -- -- -- --  -- 𝕃₂test a' xs x = {!!}


-- -- -- -- -- --   -- RElim.ff w λ _ _ → isGroupoidHSet 
-- -- -- -- -- --   -- where
-- -- -- -- -- --   -- w : RElimProp (λ _ → hSet ℓ)
-- -- -- -- -- --   -- w = ?  
-- -- -- -- -- --  -- module  (isGrpA : isGroupoid A)

-- -- -- -- -- --  -- isEquivFrom𝕃 : {!!}
-- -- -- -- -- --  -- -- ∀ 𝕝 → isEquiv {!λ 𝕝 → from𝕃 𝕝!}
-- -- -- -- -- --  -- isEquivFrom𝕃 = {!!}


-- -- -- -- -- -- -- commmL≡R : ∀ (x : A) y z xs → commmL x y z xs ≡ commmR x y z xs 
-- -- -- -- -- -- -- commmL≡R x y z xs i j =
-- -- -- -- -- -- --   hcomp (λ l →
-- -- -- -- -- -- --     λ { (i = i0) → commpL x z y xs j l
-- -- -- -- -- -- --       ; (i = i1) → commpR x y z xs j (~ l)
-- -- -- -- -- -- --       ; (j = i0) → x ∷2 comm-inv z y (xs) i l
-- -- -- -- -- -- --       ; (j = i1) → comm-inv x z (y ∷2 xs) i l
-- -- -- -- -- -- --       }) (x ∷2 z ∷2 y ∷2 xs)
      
-- -- -- -- -- -- -- -- comm-invo : ∀ (x y : A) → ∀ xs → 
-- -- -- -- -- -- -- --             comm x y xs ∙ comm _ _ xs ≡ refl
-- -- -- -- -- -- -- -- comm-invo x y xs = cong (_∙ comm y x xs) (comm-inv x y xs) ∙ lCancel _


-- -- -- -- -- -- -- -- -- hexUpa : ∀ (x y z : A) → ∀ xs → comm _ _ _ ∙∙ cong (y ∷2_) (comm _ _ _) ∙∙ comm _ _ _ ≡ hexDiag x y z xs
-- -- -- -- -- -- -- -- -- hexUpa x y z xs  =
-- -- -- -- -- -- -- -- --     cong (_∙∙ cong (y ∷2_) (comm _ _ _) ∙∙ comm _ _ _) (comm-inv _ _ _)
-- -- -- -- -- -- -- -- --      ◁ λ i j → hcomp (λ k → λ { (i = i1) → hexDiag x y z xs j
-- -- -- -- -- -- -- -- --                   ; (j = i0) → (hexU x y z xs (i ∨ k) j)
-- -- -- -- -- -- -- -- --                   ; (j = i1) → (hexU x y z xs (i ∨ k) j)
-- -- -- -- -- -- -- -- --                   }) (hexU x y z xs i j)

-- -- -- -- -- -- -- -- -- hexLpa : ∀ (x y z : A) → ∀ xs → hexDiag x y z xs ≡ cong (x ∷2_) (comm _ _ _) ∙∙ comm _ _ _ ∙∙ cong (z ∷2_) (comm _ _ _)
-- -- -- -- -- -- -- -- -- hexLpa x y z xs  = 
-- -- -- -- -- -- -- -- --     (λ i j → hcomp (λ k → λ { (i = i0) → hexDiag x y z xs j
-- -- -- -- -- -- -- -- --                   ; (j = i0) → (hexL x y z xs (i ∧ ~ k) j)
-- -- -- -- -- -- -- -- --                   ; (j = i1) → (hexL x y z xs (i ∧ ~ k) j)
-- -- -- -- -- -- -- -- --                   }) (hexL x y z xs i j))
-- -- -- -- -- -- -- -- --        ▷ cong (λ p → cong (x ∷2_) (comm _ _ _) ∙∙ comm _ _ _ ∙∙ cong (z ∷2_) p) (sym (comm-inv _ _ _))


-- -- -- -- -- -- -- comm-braid : ∀ (x y z : A) → ∀ xs → 
-- -- -- -- -- -- --   cong (x ∷2_) (comm z y xs)  ∙ comm x y (z ∷2 xs) ∙ cong (y ∷2_) (comm x z xs)
-- -- -- -- -- -- --     ≡
-- -- -- -- -- -- --   comm x z (y ∷2 xs) ∙ cong (z ∷2_) (comm x y xs) ∙ comm z y (x ∷2 xs)
-- -- -- -- -- -- -- comm-braid x y z xs i j =
-- -- -- -- -- -- --    (commpL x z y xs i ∙ hex x y z xs i ∙ commpR y x z xs i) j
     
-- -- -- -- -- -- -- -- -- sym (doubleCompPath-elim' _ _ _)

-- -- -- -- -- -- -- -- --   sym (doubleCompPath-elim' _ _ _)
-- -- -- -- -- -- -- -- -- --    ∙ (hexUpa _ _ _ _ ∙ hexLpa _ _ _ _)
-- -- -- -- -- -- -- -- --    ∙ doubleCompPath-elim' _ _ _

-- -- -- -- -- -- -- module _ {A : Type ℓ} where

-- -- -- -- -- -- --   record RElim {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- --     no-eta-equality
-- -- -- -- -- -- --     field
-- -- -- -- -- -- --      []* : B []
-- -- -- -- -- -- --      _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
-- -- -- -- -- -- --      comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
-- -- -- -- -- -- --      comm-inv* : ∀ x y {xs} (b : B xs) → SquareP (λ i j → B (comm-inv x y xs i j))
-- -- -- -- -- -- --                         (comm* x y b ) (symP (comm* y x b))
-- -- -- -- -- -- --                         refl refl
-- -- -- -- -- -- --      commmL* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- --            → PathP (λ i → B (commmL x y z xs i))
-- -- -- -- -- -- --               (x ∷* (y ∷* (z ∷* b)))
-- -- -- -- -- -- --               (z ∷* (x ∷* (y ∷* b)))
-- -- -- -- -- -- --      commmR* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- --            → PathP (λ i → B (commmR x y z xs i))
-- -- -- -- -- -- --               (x ∷* (y ∷* (z ∷* b)))
-- -- -- -- -- -- --               (z ∷* (x ∷* (y ∷* b)))

-- -- -- -- -- -- --      commpL* : ∀ x y z {xs : FMSet2 A} (b : B xs) →
-- -- -- -- -- -- --                SquareP
-- -- -- -- -- -- --                ((λ i j → B (commpL x y z xs i j)))
-- -- -- -- -- -- --                        (congP (λ _ → x ∷*_) (comm* y z b))
-- -- -- -- -- -- --                      (comm* x y (z ∷* b))
-- -- -- -- -- -- --                      refl
-- -- -- -- -- -- --                      (commmL* x z y b)
-- -- -- -- -- -- --      commpR* : ∀ x y z {xs : FMSet2 A} (b : B xs) →
-- -- -- -- -- -- --                SquareP (λ i j → B (commpR x y z xs i j))
-- -- -- -- -- -- --                (congP (λ _ → x ∷*_) (comm* _ _ _))
-- -- -- -- -- -- --                (comm* z x (y ∷* b))
-- -- -- -- -- -- --                (commmR* x y z b)
-- -- -- -- -- -- --                refl
-- -- -- -- -- -- --      hex* : ∀ x y z {xs : FMSet2 A} (b : B xs) →
-- -- -- -- -- -- --                SquareP (λ i j → B (hex x y z xs i j))
-- -- -- -- -- -- --                (comm* x y (z ∷* b))
-- -- -- -- -- -- --                (congP (λ _ → z ∷*_) (comm* _ _ _))
-- -- -- -- -- -- --                (commmL* x y z b)
-- -- -- -- -- -- --                (commmR* y x z b)
                  

-- -- -- -- -- -- --      trunc* : (xs : FMSet2 A) → isGroupoid (B xs)

-- -- -- -- -- -- --     f : (xs : FMSet2 A) → B xs
-- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- -- -- -- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- -- -- -- -- --     f (comm-inv x y xs i j) =
-- -- -- -- -- -- --        comm-inv* x y (f xs) i j
-- -- -- -- -- -- --     f (commmL x y z xs i) = commmL* x y z (f xs) i
-- -- -- -- -- -- --     f (commmR x y z xs i) = commmR* x y z (f xs) i
-- -- -- -- -- -- --     f (commpL x y z xs i j) = commpL* x y z (f xs) i j 
-- -- -- -- -- -- --     f (commpR x y z xs i j) = commpR* x y z (f xs) i j 
-- -- -- -- -- -- --     f (hex x y z xs i j) = hex* x y z (f xs) i j 
-- -- -- -- -- -- --     f (trunc xs ys p q r s i j k) =
-- -- -- -- -- -- --       isOfHLevel→isOfHLevelDep 3 (λ a → trunc* a)
-- -- -- -- -- -- --          _ _ _ _
-- -- -- -- -- -- --          (λ j k → f (r j k)) (λ j k → f (s j k)) 
-- -- -- -- -- -- --            (trunc xs ys p q r s) i j k


-- -- -- -- -- -- --   -- record RElim' {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- --   --   no-eta-equality
-- -- -- -- -- -- --   --   field
-- -- -- -- -- -- --   --    []* : B []
-- -- -- -- -- -- --   --    _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
-- -- -- -- -- -- --   --    comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- --   --          → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
-- -- -- -- -- -- --   --    comm-inv* : ∀ x y {xs} (b : B xs) → SquareP (λ i j → B (comm-inv x y xs i j))
-- -- -- -- -- -- --   --                       (comm* x y b ) (symP (comm* y x b))
-- -- -- -- -- -- --   --                       refl refl                  

-- -- -- -- -- -- --   --    trunc* : (xs : FMSet2 A) → isGroupoid (B xs)

-- -- -- -- -- -- --   --   fR : RElim (λ z → B z)
-- -- -- -- -- -- --   --   RElim.[]* fR = []*
-- -- -- -- -- -- --   --   RElim._∷*_ fR = _∷*_
-- -- -- -- -- -- --   --   RElim.comm* fR = comm*
-- -- -- -- -- -- --   --   RElim.comm-inv* fR = comm-inv*
-- -- -- -- -- -- --   --   RElim.commmL* fR = {!!}
-- -- -- -- -- -- --   --   RElim.commmR* fR = {!!}
-- -- -- -- -- -- --   --   RElim.commpL* fR = {!!}
-- -- -- -- -- -- --   --   RElim.commpR* fR = {!!}
-- -- -- -- -- -- --   --   RElim.hex* fR = {!!}
-- -- -- -- -- -- --   --   RElim.trunc* fR = {!!}

-- -- -- -- -- -- --   --   f : (xs : FMSet2 A) → B xs
-- -- -- -- -- -- --   --   f = RElim.f fR

-- -- -- -- -- -- --   record RRec {ℓ'} {B : Type ℓ'} (BType : isGroupoid B) : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- --     no-eta-equality
-- -- -- -- -- -- --     field
-- -- -- -- -- -- --      []* : B
-- -- -- -- -- -- --      _∷*_ : A → B → B
-- -- -- -- -- -- --      comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b)
-- -- -- -- -- -- --      comm-inv* : ∀ x y b → comm* x y b ≡ sym (comm* y x b) 
-- -- -- -- -- -- --      commmL* : (x y z : A) → ∀ b
-- -- -- -- -- -- --            → (x ∷* (y ∷* (z ∷* b))) ≡  (z ∷* (x ∷* (y ∷* b)))
-- -- -- -- -- -- --      commmR* : (x y z : A) → ∀ b
-- -- -- -- -- -- --            → (x ∷* (y ∷* (z ∷* b))) ≡ (z ∷* (x ∷* (y ∷* b)))

-- -- -- -- -- -- --      commpL* : ∀ x y z → ∀ b → 
-- -- -- -- -- -- --                Square
-- -- -- -- -- -- --                  (cong (x ∷*_) (comm* y z b))
-- -- -- -- -- -- --                  (comm* x y (z ∷* b))
-- -- -- -- -- -- --                  refl
-- -- -- -- -- -- --                  (commmL* x z y b)
-- -- -- -- -- -- --      commpR* : ∀ x y z → ∀ b →
-- -- -- -- -- -- --                Square 
-- -- -- -- -- -- --                (cong (x ∷*_) (comm* _ _ _))
-- -- -- -- -- -- --                (comm* z x (y ∷* b))
-- -- -- -- -- -- --                (commmR* x y z b)
-- -- -- -- -- -- --                refl
-- -- -- -- -- -- --      hex* : ∀ x y z → ∀ b →
-- -- -- -- -- -- --                Square
-- -- -- -- -- -- --                (comm* x y (z ∷* b))
-- -- -- -- -- -- --                (cong (z ∷*_) (comm* _ _ _))
-- -- -- -- -- -- --                (commmL* x y z b)
-- -- -- -- -- -- --                (commmR* y x z b)


-- -- -- -- -- -- --     f : FMSet2 A → B
-- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- --     f (x ∷2 x₁) = x ∷* f x₁
-- -- -- -- -- -- --     f (comm x y x₁ i) = comm* x y (f x₁) i
-- -- -- -- -- -- --     f (comm-inv x y x₁ i i₁) = comm-inv* x y (f x₁) i i₁
-- -- -- -- -- -- --     f (commmL x y z xs i) = commmL* x y z (f xs) i
-- -- -- -- -- -- --     f (commmR x y z xs i) = commmR* x y z (f xs) i
-- -- -- -- -- -- --     f (commpL x y z xs i j) = commpL* x y z (f xs) i j 
-- -- -- -- -- -- --     f (commpR x y z xs i j) = commpR* x y z (f xs) i j 
-- -- -- -- -- -- --     f (hex x y z xs i j) = hex* x y z (f xs) i j     
-- -- -- -- -- -- --     f (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
-- -- -- -- -- -- --        BType _ _ _ _
-- -- -- -- -- -- --         (cong (cong f) x₃)
-- -- -- -- -- -- --         (cong  (cong f) y₁) i i₁ x₄


-- -- -- -- -- -- --   record RElimSet' {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- --     no-eta-equality
-- -- -- -- -- -- --     field
-- -- -- -- -- -- --      []* : B []
-- -- -- -- -- -- --      _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
-- -- -- -- -- -- --      comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
-- -- -- -- -- -- --      trunc* : (xs : FMSet2 A) → isSet (B xs)

-- -- -- -- -- -- --     fR : RElim B
-- -- -- -- -- -- --     RElim.[]* fR = []*
-- -- -- -- -- -- --     RElim._∷*_ fR = _∷*_
-- -- -- -- -- -- --     RElim.comm* fR = comm*
-- -- -- -- -- -- --     RElim.comm-inv* fR x y b =
-- -- -- -- -- -- --       isSet→SquareP (λ _ _  → trunc* _) _ _ _ _
-- -- -- -- -- -- --     RElim.commmL* fR x y z {xs} b i =
-- -- -- -- -- -- --       comp (λ l → B (commpL x z y xs i l))
-- -- -- -- -- -- --        (λ l → λ { (i = i0) → x ∷* comm* z y b l
-- -- -- -- -- -- --                 ; (i = i1) → comm* x z (y ∷* b) l
-- -- -- -- -- -- --                 })
-- -- -- -- -- -- --        (x ∷* (z ∷* (y ∷* b)))
-- -- -- -- -- -- --     RElim.commmR* fR x y z {xs} b i =
-- -- -- -- -- -- --        comp (λ l → B (commpR x y z xs i (~ l)))
-- -- -- -- -- -- --        (λ l → λ { (i = i0) → x ∷* comm* y z b (~ l)
-- -- -- -- -- -- --                 ; (i = i1) → comm* z x (y ∷* b) (~ l)
-- -- -- -- -- -- --                 })
-- -- -- -- -- -- --        (x ∷* (z ∷* (y ∷* b)))
-- -- -- -- -- -- --     RElim.commpL* fR x y z b =
-- -- -- -- -- -- --       isSet→SquareP (λ _ _  → trunc* _) _ _ _ _
-- -- -- -- -- -- --     RElim.commpR* fR x y z b =
-- -- -- -- -- -- --       isSet→SquareP (λ _ _  → trunc* _) _ _ _ _
-- -- -- -- -- -- --     RElim.hex* fR x y z b =
-- -- -- -- -- -- --       isSet→SquareP (λ _ _  → trunc* _) _ _ _ _
-- -- -- -- -- -- --     RElim.trunc* fR = isSet→isGroupoid ∘ trunc*

-- -- -- -- -- -- --     f : ∀ xs → B xs
-- -- -- -- -- -- --     f = RElim.f fR

-- -- -- -- -- -- --     -- f : ∀ xs → B xs
-- -- -- -- -- -- --     -- f [] = []*
-- -- -- -- -- -- --     -- f (x ∷2 xs) = x ∷* f xs
-- -- -- -- -- -- --     -- f (comm x y xs i) = comm* x y (f xs) i
-- -- -- -- -- -- --     -- f (comm-inv x y xs i j) =
-- -- -- -- -- -- --     --    isOfHLevel→isOfHLevelDep 2 trunc*
-- -- -- -- -- -- --     --        (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
-- -- -- -- -- -- --     --        (comm* x y (f xs)) (symP (comm* y x (f xs)))
-- -- -- -- -- -- --     --        (comm-inv x y xs) i j
-- -- -- -- -- -- --     -- f (commmL x y z xs i) =
-- -- -- -- -- -- --     --   comp (λ l → B (commpL x z y xs i l))
-- -- -- -- -- -- --     --    (λ l → λ { (i = i0) → x ∷* comm* z y (f xs) l
-- -- -- -- -- -- --     --             ; (i = i1) → comm* x z (y ∷* (f xs)) l
-- -- -- -- -- -- --     --             })
-- -- -- -- -- -- --     --    (x ∷* (z ∷* (y ∷* f xs)))
-- -- -- -- -- -- --     -- f (commmR x y z xs i) =
-- -- -- -- -- -- --     --    comp (λ l → B (commpR x y z xs i (~ l)))
-- -- -- -- -- -- --     --    (λ l → λ { (i = i0) → x ∷* comm* y z (f xs) (~ l)
-- -- -- -- -- -- --     --             ; (i = i1) → comm* z x (y ∷* (f xs)) (~ l)
-- -- -- -- -- -- --     --             })
-- -- -- -- -- -- --     --    (x ∷* (z ∷* (y ∷* f xs)))
-- -- -- -- -- -- --     -- f (commpL x y z xs i j) =
-- -- -- -- -- -- --     --   {!isOfHLevel→isOfHLevelDep 2 trunc*
-- -- -- -- -- -- --     --        ? ? ? ?
-- -- -- -- -- -- --     --        (commpL x y z xs) i j!}
-- -- -- -- -- -- --     -- f (commpR x y z xs i i₁) = {!!}
-- -- -- -- -- -- --     -- f (hex x y z xs i i₁) = {!!}
-- -- -- -- -- -- --     -- f (trunc xs xs₁ x y x₁ y₁ i i₁ x₂) = {!!}

-- -- -- -- -- -- -- --     hexDiag* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- --            → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b)))
-- -- -- -- -- -- -- --     hexDiag* x y z {xs} b i =
-- -- -- -- -- -- -- --       comp (λ j → B (hexU x y z xs j i))
-- -- -- -- -- -- -- --         (λ j →
-- -- -- -- -- -- -- --           λ { (i = i0) → comm* y x {(z ∷2 xs)} (z ∷* b) j
-- -- -- -- -- -- -- --             ; (i = i1) → comm* y z (x ∷* b) j
-- -- -- -- -- -- -- --             }) (y ∷* comm* x z b i) 

-- -- -- -- -- -- -- --     f : (xs : FMSet2 A) → B xs
-- -- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- -- -- -- -- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- -- -- -- -- -- --     f (comm-inv x y xs i j) =
-- -- -- -- -- -- -- --        isOfHLevel→isOfHLevelDep 2 trunc*
-- -- -- -- -- -- -- --            (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
-- -- -- -- -- -- -- --            (comm* x y (f xs)) (symP (comm* y x (f xs)))
-- -- -- -- -- -- -- --            (comm-inv x y xs) i j
-- -- -- -- -- -- -- --     f (hexDiag x y z xs i) = 
-- -- -- -- -- -- -- --        hexDiag* x y z (f xs) i
-- -- -- -- -- -- -- --     f (hexU x y z xs i j) = 
-- -- -- -- -- -- -- --       isSet→SquareP 
-- -- -- -- -- -- -- --          (λ i j → trunc* (hexU x y z xs i j))
-- -- -- -- -- -- -- --          (λ j → y ∷* comm* x z (f xs) j)
-- -- -- -- -- -- -- --          (hexDiag* x y z (f xs))
-- -- -- -- -- -- -- --          (comm* y x (z ∷* f xs))
-- -- -- -- -- -- -- --          (comm* y z (x ∷* f xs)) i j
-- -- -- -- -- -- -- --     f (hexL x y z xs i j) = 
-- -- -- -- -- -- -- --          isSet→SquareP 
-- -- -- -- -- -- -- --          (λ i j → trunc* (hexL x y z xs i j))
-- -- -- -- -- -- -- --          (hexDiag* x y z (f xs))
-- -- -- -- -- -- -- --          (comm* x z (y ∷* f xs))
-- -- -- -- -- -- -- --          (λ i₁ → x ∷* comm* y z (f xs) i₁)
-- -- -- -- -- -- -- --          (λ i₁ → z ∷* comm* y x (f xs) i₁) i j
-- -- -- -- -- -- -- --     f (trunc xs zs p q r s i j k) =
-- -- -- -- -- -- -- --         isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
-- -- -- -- -- -- -- --             _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k


-- -- -- -- -- -- -- --     f : (xs : FMSet2 A B xs
-- -- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- -- -- -- -- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- -- -- -- -- -- --     f (comm-inv x y xs i j) =
-- -- -- -- -- -- -- --        comm-inv* x y (f xs) i j
-- -- -- -- -- -- -- --     f (commmL x y z xs i) = commmL* x y z (f xs) i
-- -- -- -- -- -- -- --     f (commmR x y z xs i) = commmR* x y z (f xs) i
-- -- -- -- -- -- -- --     f (commpL x y z xs i j) = commpL* x y z (f xs) i j 
-- -- -- -- -- -- -- --     f (commpR x y z xs i j) = commpR* x y z (f xs) i j 
-- -- -- -- -- -- -- --     f (hex x y z xs i j) = hex* x y z (f xs) i j 
-- -- -- -- -- -- -- --     f (trunc xs ys p q r s i j k) = ?
-- -- -- -- -- -- -- --       -- isOfHLevel→isOfHLevelDep 3 (λ a → trunc* a)
-- -- -- -- -- -- -- --       --    _ _ _ _
-- -- -- -- -- -- -- --       --    (λ j k → f (r j k)) (λ j k → f (s j k)) 
-- -- -- -- -- -- -- --       --      (trunc xs ys p q r s) i j k



-- -- -- -- -- -- -- --   -- module ElimSet {ℓ'} {B : FMSet2 A → Type ℓ'}
-- -- -- -- -- -- -- --   --   ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs))
-- -- -- -- -- -- -- --   --   (comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- --   --          → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
-- -- -- -- -- -- -- --   --        comm-inv* : ∀ x y {xs} (b : B xs) → SquareP (λ i j → B (comm-inv x y xs i j))
-- -- -- -- -- -- -- --   --                       (comm* x y b ) (symP (comm* y x b))
-- -- -- -- -- -- -- --   --                       refl refl 
-- -- -- -- -- -- -- --   --   (commmL* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- --   --          → PathP (λ i → B (commmL x y z xs i))
-- -- -- -- -- -- -- --   --             (x ∷* (y ∷* (z ∷* b)))
-- -- -- -- -- -- -- --   --             (z ∷* (x ∷* (y ∷* b))))
-- -- -- -- -- -- -- --   --   (commmR* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- --   --          → PathP (λ i → B (commmR x y z xs i))
-- -- -- -- -- -- -- --   --             (x ∷* (y ∷* (z ∷* b)))
-- -- -- -- -- -- -- --   --             (z ∷* (x ∷* (y ∷* b))))
-- -- -- -- -- -- -- --   --   (trunc* : (xs : FMSet2 A) → isSet (B xs)) where

-- -- -- -- -- -- -- --   --   f : (xs : FMSet2 A) → B xs
-- -- -- -- -- -- -- --   --   f [] = []*
-- -- -- -- -- -- -- --   --   f (x ∷2 xs) = x ∷* f xs
-- -- -- -- -- -- -- --   --   f (comm x y xs i) = comm* x y (f xs) i
-- -- -- -- -- -- -- --   --   f (comm-inv x y xs i j) = {!!}
-- -- -- -- -- -- -- --   --      -- isOfHLevel→isOfHLevelDep 2 trunc*
-- -- -- -- -- -- -- --   --      --     (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
-- -- -- -- -- -- -- --   --      --     (comm* x y (f xs)) (symP (comm* y x (f xs)))
-- -- -- -- -- -- -- --   --      --     (comm-inv x y xs) i j
-- -- -- -- -- -- -- --   --   f (commmL x y z xs i) = {!!}
-- -- -- -- -- -- -- --   --   f (commmR x y z xs i) = {!!}
-- -- -- -- -- -- -- --   --   f (commpL x y z xs i i₁) = {!!}
-- -- -- -- -- -- -- --   --   f (commpR x y z xs i i₁) = {!!}
-- -- -- -- -- -- -- --   --   f (hex x y z xs i i₁) = {!!}    
-- -- -- -- -- -- -- --   --   f (trunc xs zs p q r s i j k) = {!!}
-- -- -- -- -- -- -- --   --       -- isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
-- -- -- -- -- -- -- --   --       --     _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k

-- -- -- -- -- -- -- -- --   module ElimSet {ℓ'} {B : FMSet2 A → Type ℓ'}
-- -- -- -- -- -- -- -- --     ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs))
-- -- -- -- -- -- -- -- --     (comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- -- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
-- -- -- -- -- -- -- -- --     (commmL* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- -- --            → PathP (λ i → B (commmL x y z xs i))
-- -- -- -- -- -- -- -- --               (x ∷* (y ∷* (z ∷* b)))
-- -- -- -- -- -- -- -- --               (z ∷* (x ∷* (y ∷* b))))
-- -- -- -- -- -- -- -- --     (commmR* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- -- --            → PathP (λ i → B (commmR x y z xs i))
-- -- -- -- -- -- -- -- --               (x ∷* (y ∷* (z ∷* b)))
-- -- -- -- -- -- -- -- --               (z ∷* (x ∷* (y ∷* b))))
-- -- -- -- -- -- -- -- --     (trunc* : (xs : FMSet2 A) → isSet (B xs)) where

-- -- -- -- -- -- -- -- --     f : (xs : FMSet2 A) → B xs
-- -- -- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- -- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- -- -- -- -- -- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- -- -- -- -- -- -- --     f (comm-inv x y xs i j) =
-- -- -- -- -- -- -- -- --        isOfHLevel→isOfHLevelDep 2 trunc*
-- -- -- -- -- -- -- -- --            (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
-- -- -- -- -- -- -- -- --            (comm* x y (f xs)) (symP (comm* y x (f xs)))
-- -- -- -- -- -- -- -- --            (comm-inv x y xs) i j
-- -- -- -- -- -- -- -- --     f (commmL x y z xs i) = {!!}
-- -- -- -- -- -- -- -- --     f (commmR x y z xs i) = {!!}
-- -- -- -- -- -- -- -- --     f (commpL x y z xs i i₁) = {!!}
-- -- -- -- -- -- -- -- --     f (commpR x y z xs i i₁) = {!!}
-- -- -- -- -- -- -- -- --     f (hex x y z xs i i₁) = {!!}    
-- -- -- -- -- -- -- -- --     -- f (hexDiag x y z xs i) = hexDiag* x y z (f xs) i
-- -- -- -- -- -- -- -- --     -- f (hexU x y z xs i j) =
-- -- -- -- -- -- -- -- --     --   isSet→SquareP 
-- -- -- -- -- -- -- -- --     --      (λ i j → trunc* (hexU x y z xs i j))
-- -- -- -- -- -- -- -- --     --      (λ j → y ∷* comm* x z (f xs) j)
-- -- -- -- -- -- -- -- --     --      (hexDiag* x y z (f xs))
-- -- -- -- -- -- -- -- --     --      (comm* y x (z ∷* f xs))
-- -- -- -- -- -- -- -- --     --      (comm* y z (x ∷* f xs)) i j
-- -- -- -- -- -- -- -- --     -- f (hexL x y z xs i j) =
-- -- -- -- -- -- -- -- --     --      isSet→SquareP 
-- -- -- -- -- -- -- -- --     --      (λ i j → trunc* (hexL x y z xs i j))
-- -- -- -- -- -- -- -- --     --      (hexDiag* x y z (f xs))
-- -- -- -- -- -- -- -- --     --      (comm* x z (y ∷* f xs))
-- -- -- -- -- -- -- -- --     --      (λ i₁ → x ∷* comm* y z (f xs) i₁)
-- -- -- -- -- -- -- -- --     --      (λ i₁ → z ∷* comm* y x (f xs) i₁) i j
-- -- -- -- -- -- -- -- --     f (trunc xs zs p q r s i j k) =
-- -- -- -- -- -- -- -- --         isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
-- -- -- -- -- -- -- -- --             _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k


-- -- -- -- -- -- -- -- -- --   record RElimSet {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- -- -- -- --     no-eta-equality
-- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- --      []* : B []
-- -- -- -- -- -- -- -- -- --      _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
-- -- -- -- -- -- -- -- -- --      comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- -- -- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
-- -- -- -- -- -- -- -- -- --      hexDiag* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- -- -- --            → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b)))
-- -- -- -- -- -- -- -- -- --      trunc* : (xs : FMSet2 A) → isSet (B xs)

-- -- -- -- -- -- -- -- -- --     f : (xs : FMSet2 A) → B xs
-- -- -- -- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- -- -- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- -- -- -- -- -- -- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- -- -- -- -- -- -- -- --     f (comm-inv x y xs i j) =
-- -- -- -- -- -- -- -- -- --        isOfHLevel→isOfHLevelDep 2 trunc*
-- -- -- -- -- -- -- -- -- --            (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
-- -- -- -- -- -- -- -- -- --            (comm* x y (f xs)) (symP (comm* y x (f xs)))
-- -- -- -- -- -- -- -- -- --            (comm-inv x y xs) i j
-- -- -- -- -- -- -- -- -- --     f (hexDiag x y z xs i) = hexDiag* x y z (f xs) i
-- -- -- -- -- -- -- -- -- --     f (hexU x y z xs i j) =
-- -- -- -- -- -- -- -- -- --       isSet→SquareP 
-- -- -- -- -- -- -- -- -- --          (λ i j → trunc* (hexU x y z xs i j))
-- -- -- -- -- -- -- -- -- --          (λ j → y ∷* comm* x z (f xs) j)
-- -- -- -- -- -- -- -- -- --          (hexDiag* x y z (f xs))
-- -- -- -- -- -- -- -- -- --          (comm* y x (z ∷* f xs))
-- -- -- -- -- -- -- -- -- --          (comm* y z (x ∷* f xs)) i j
-- -- -- -- -- -- -- -- -- --     f (hexL x y z xs i j) =
-- -- -- -- -- -- -- -- -- --          isSet→SquareP 
-- -- -- -- -- -- -- -- -- --          (λ i j → trunc* (hexL x y z xs i j))
-- -- -- -- -- -- -- -- -- --          (hexDiag* x y z (f xs))
-- -- -- -- -- -- -- -- -- --          (comm* x z (y ∷* f xs))
-- -- -- -- -- -- -- -- -- --          (λ i₁ → x ∷* comm* y z (f xs) i₁)
-- -- -- -- -- -- -- -- -- --          (λ i₁ → z ∷* comm* y x (f xs) i₁) i j
-- -- -- -- -- -- -- -- -- --     f (trunc xs zs p q r s i j k) =
-- -- -- -- -- -- -- -- -- --         isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
-- -- -- -- -- -- -- -- -- --             _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k


-- -- -- -- -- -- -- -- -- --   record RElimSet' {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- -- -- -- --     no-eta-equality
-- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- --      []* : B []
-- -- -- -- -- -- -- -- -- --      _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
-- -- -- -- -- -- -- -- -- --      comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- -- -- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
-- -- -- -- -- -- -- -- -- --      trunc* : (xs : FMSet2 A) → isSet (B xs)

-- -- -- -- -- -- -- -- -- --     hexDiag* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- -- -- --            → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b)))
-- -- -- -- -- -- -- -- -- --     hexDiag* x y z {xs} b i =
-- -- -- -- -- -- -- -- -- --       comp (λ j → B (hexU x y z xs j i))
-- -- -- -- -- -- -- -- -- --         (λ j →
-- -- -- -- -- -- -- -- -- --           λ { (i = i0) → comm* y x {(z ∷2 xs)} (z ∷* b) j
-- -- -- -- -- -- -- -- -- --             ; (i = i1) → comm* y z (x ∷* b) j
-- -- -- -- -- -- -- -- -- --             }) (y ∷* comm* x z b i) 

-- -- -- -- -- -- -- -- -- --     f : (xs : FMSet2 A) → B xs
-- -- -- -- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- -- -- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- -- -- -- -- -- -- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- -- -- -- -- -- -- -- --     f (comm-inv x y xs i j) =
-- -- -- -- -- -- -- -- -- --        isOfHLevel→isOfHLevelDep 2 trunc*
-- -- -- -- -- -- -- -- -- --            (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
-- -- -- -- -- -- -- -- -- --            (comm* x y (f xs)) (symP (comm* y x (f xs)))
-- -- -- -- -- -- -- -- -- --            (comm-inv x y xs) i j
-- -- -- -- -- -- -- -- -- --     f (hexDiag x y z xs i) = 
-- -- -- -- -- -- -- -- -- --        hexDiag* x y z (f xs) i
-- -- -- -- -- -- -- -- -- --     f (hexU x y z xs i j) = 
-- -- -- -- -- -- -- -- -- --       isSet→SquareP 
-- -- -- -- -- -- -- -- -- --          (λ i j → trunc* (hexU x y z xs i j))
-- -- -- -- -- -- -- -- -- --          (λ j → y ∷* comm* x z (f xs) j)
-- -- -- -- -- -- -- -- -- --          (hexDiag* x y z (f xs))
-- -- -- -- -- -- -- -- -- --          (comm* y x (z ∷* f xs))
-- -- -- -- -- -- -- -- -- --          (comm* y z (x ∷* f xs)) i j
-- -- -- -- -- -- -- -- -- --     f (hexL x y z xs i j) = 
-- -- -- -- -- -- -- -- -- --          isSet→SquareP 
-- -- -- -- -- -- -- -- -- --          (λ i j → trunc* (hexL x y z xs i j))
-- -- -- -- -- -- -- -- -- --          (hexDiag* x y z (f xs))
-- -- -- -- -- -- -- -- -- --          (comm* x z (y ∷* f xs))
-- -- -- -- -- -- -- -- -- --          (λ i₁ → x ∷* comm* y z (f xs) i₁)
-- -- -- -- -- -- -- -- -- --          (λ i₁ → z ∷* comm* y x (f xs) i₁) i j
-- -- -- -- -- -- -- -- -- --     f (trunc xs zs p q r s i j k) =
-- -- -- -- -- -- -- -- -- --         isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
-- -- -- -- -- -- -- -- -- --             _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k

-- -- -- -- -- -- -- -- -- --   record RElimProp' {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- -- -- -- --     no-eta-equality
-- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- --      []* : B []
-- -- -- -- -- -- -- -- -- --      _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
-- -- -- -- -- -- -- -- -- --      trunc* : (xs : FMSet2 A) → isProp (B xs)

-- -- -- -- -- -- -- -- -- --     res : RElimSet B
-- -- -- -- -- -- -- -- -- --     RElimSet.[]* res = []*
-- -- -- -- -- -- -- -- -- --     RElimSet._∷*_ res = _∷*_
-- -- -- -- -- -- -- -- -- --     RElimSet.comm* res = (λ x y b → isProp→PathP (λ _ → trunc* _) _ _)
-- -- -- -- -- -- -- -- -- --     RElimSet.hexDiag* res = (λ x y z b → isProp→PathP (λ _ → trunc* _) _ _)
-- -- -- -- -- -- -- -- -- --     RElimSet.trunc* res = isProp→isSet ∘ trunc*

-- -- -- -- -- -- -- -- -- --     f = RElimSet.f res

-- -- -- -- -- -- -- -- -- --   record RElimProp'' {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- -- -- -- --     no-eta-equality
-- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- --      []* : B []
-- -- -- -- -- -- -- -- -- --      _∷*[_]_ : (x : A) (xs : FMSet2 A) → B xs → B (x ∷2 xs)
-- -- -- -- -- -- -- -- -- --      trunc* : (xs : FMSet2 A) → isProp (B xs)

-- -- -- -- -- -- -- -- -- --     res : RElimSet B
-- -- -- -- -- -- -- -- -- --     RElimSet.[]* res = []*
-- -- -- -- -- -- -- -- -- --     (res RElimSet.∷* x) {xs} x₁ = x ∷*[ xs ] x₁ 
-- -- -- -- -- -- -- -- -- --     RElimSet.comm* res = (λ x y b → isProp→PathP (λ _ → trunc* _) _ _)
-- -- -- -- -- -- -- -- -- --     RElimSet.hexDiag* res = (λ x y z b → isProp→PathP (λ _ → trunc* _) _ _)
-- -- -- -- -- -- -- -- -- --     RElimSet.trunc* res = isProp→isSet ∘ trunc*

-- -- -- -- -- -- -- -- -- --     f = RElimSet.f res


-- -- -- -- -- -- -- -- -- --   record RElim {ℓ'} (B : FMSet2 A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- -- -- -- --     no-eta-equality
-- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- --      []* : B []
-- -- -- -- -- -- -- -- -- --      _∷*_ : (x : A) {xs : FMSet2 A} → B xs → B (x ∷2 xs)
-- -- -- -- -- -- -- -- -- --      comm* : (x y : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- -- -- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))
-- -- -- -- -- -- -- -- -- --      comm-inv* : ∀ x y {xs} (b : B xs) → SquareP (λ i j → B (comm-inv x y xs i j))
-- -- -- -- -- -- -- -- -- --                         (comm* x y b ) (symP (comm* y x b))
-- -- -- -- -- -- -- -- -- --                         refl refl 
-- -- -- -- -- -- -- -- -- --      hexDiag* : (x y z : A) {xs : FMSet2 A} (b : B xs)
-- -- -- -- -- -- -- -- -- --            → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b)))
-- -- -- -- -- -- -- -- -- --      hexU* : ∀ x y z {xs : FMSet2 A} (b : B xs) →
-- -- -- -- -- -- -- -- -- --                SquareP
-- -- -- -- -- -- -- -- -- --                ((λ i j → B (hexU x y z xs i j)))
-- -- -- -- -- -- -- -- -- --                  (congP (λ _ → y ∷*_) (comm* x z b))
-- -- -- -- -- -- -- -- -- --                  (hexDiag* x y z b)
-- -- -- -- -- -- -- -- -- --                  (comm* _ _ (z ∷* b))
-- -- -- -- -- -- -- -- -- --                  (comm* _ _ (x ∷* b))
                  
-- -- -- -- -- -- -- -- -- --      hexL* : ∀ x y z {xs : FMSet2 A} (b : B xs)  →
-- -- -- -- -- -- -- -- -- --                SquareP
-- -- -- -- -- -- -- -- -- --                  (λ i j → B (hexL x y z xs i j))
-- -- -- -- -- -- -- -- -- --                  (hexDiag* _ _ _ b)
-- -- -- -- -- -- -- -- -- --                  (comm* _ _ _)
-- -- -- -- -- -- -- -- -- --                  (congP (λ _ → _ ∷*_) (comm* _ _ _))
-- -- -- -- -- -- -- -- -- --                  (congP (λ _ → _ ∷*_) (comm* _ _ _))
                  

-- -- -- -- -- -- -- -- -- --      trunc* : (xs : FMSet2 A) → isGroupoid (B xs)

-- -- -- -- -- -- -- -- -- --     f : (xs : FMSet2 A) → B xs
-- -- -- -- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- -- -- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- -- -- -- -- -- -- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- -- -- -- -- -- -- -- --     f (comm-inv x y xs i j) =
-- -- -- -- -- -- -- -- -- --        comm-inv* x y (f xs) i j
-- -- -- -- -- -- -- -- -- --     f (hexDiag x y z xs i) = hexDiag* x y z (f xs) i
-- -- -- -- -- -- -- -- -- --     f (hexU x y z xs i j) = hexU* x y z (f xs) i j
-- -- -- -- -- -- -- -- -- --     f (hexL x y z xs i j) = hexL* x y z (f xs) i j

-- -- -- -- -- -- -- -- -- --     f (trunc xs ys p q r s i j k) =
-- -- -- -- -- -- -- -- -- --       isOfHLevel→isOfHLevelDep 3 (λ a → trunc* a)
-- -- -- -- -- -- -- -- -- --          _ _ _ _
-- -- -- -- -- -- -- -- -- --          (λ j k → f (r j k)) (λ j k → f (s j k)) 
-- -- -- -- -- -- -- -- -- --            (trunc xs ys p q r s) i j k


-- -- -- -- -- -- -- -- -- --   record RRec {ℓ'} {B : Type ℓ'} (BType : isGroupoid B) : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- -- -- -- --     no-eta-equality
-- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- --       []* : B
-- -- -- -- -- -- -- -- -- --       _∷*_ : A → B → B
-- -- -- -- -- -- -- -- -- --       comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b)
-- -- -- -- -- -- -- -- -- --       comm-inv* : ∀ x y b → comm* x y b ≡ sym (comm* y x b) 
-- -- -- -- -- -- -- -- -- --       hexDiag* : ∀ x y z b → x ∷* (y ∷* (z ∷* b)) ≡ z ∷* (y ∷* (x ∷* b)) 
-- -- -- -- -- -- -- -- -- --       hexU* : ∀ x y z b →
-- -- -- -- -- -- -- -- -- --                Square (cong (_ ∷*_) (comm* _ _ b)) (hexDiag* x y z b)
-- -- -- -- -- -- -- -- -- --                       (comm* _ _ _) (comm* _ _ _)
-- -- -- -- -- -- -- -- -- --       hexL* : ∀ x y z b →
-- -- -- -- -- -- -- -- -- --                Square (hexDiag* x y z b) (comm* _ _ _)
-- -- -- -- -- -- -- -- -- --                       (cong (_ ∷*_) (comm* _ _ b)) (cong (_ ∷*_) (comm* _ _ b))


-- -- -- -- -- -- -- -- -- --     f : FMSet2 A → B
-- -- -- -- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- -- -- -- --     f (x ∷2 x₁) = x ∷* f x₁
-- -- -- -- -- -- -- -- -- --     f (comm x y x₁ i) = comm* x y (f x₁) i
-- -- -- -- -- -- -- -- -- --     f (comm-inv x y x₁ i i₁) = comm-inv* x y (f x₁) i i₁
-- -- -- -- -- -- -- -- -- --     f (hexDiag x y z x₁ i) = hexDiag* x y z (f x₁) i
-- -- -- -- -- -- -- -- -- --     f (hexU x y z x₁ i i₁) = hexU* x y z (f x₁) i i₁
-- -- -- -- -- -- -- -- -- --     f (hexL x y z x₁ i i₁) = hexL* x y z (f x₁) i i₁
-- -- -- -- -- -- -- -- -- --     f (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
-- -- -- -- -- -- -- -- -- --        BType _ _ _ _
-- -- -- -- -- -- -- -- -- --         (cong (cong f) x₃) (cong  (cong f) y₁) i i₁ x₄




-- -- -- -- -- -- --   len2 : FMSet2 A → ℕ
-- -- -- -- -- -- --   len2 [] = zero
-- -- -- -- -- -- --   len2 (x ∷2 x₁) = suc (len2 x₁)
-- -- -- -- -- -- --   len2 (comm x y x₁ i) = suc (suc (len2 x₁))
-- -- -- -- -- -- --   len2 (comm-inv x y x₁ i i₁) = suc (suc (len2 x₁))
-- -- -- -- -- -- --   len2 (commmL x y z x₁ i) = suc (suc (suc (len2 x₁)))
-- -- -- -- -- -- --   len2 (commmR x y z x₁ i) = suc (suc (suc (len2 x₁)))
-- -- -- -- -- -- --   len2 (commpL x y z x₁ i i₁) = suc (suc (suc (len2 x₁)))
-- -- -- -- -- -- --   len2 (commpR x y z x₁ i i₁) = suc (suc (suc (len2 x₁)))
-- -- -- -- -- -- --   len2 (hex x y z x₁ i i₁) = suc (suc (suc (len2 x₁)))
-- -- -- -- -- -- --   len2 (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) = 
-- -- -- -- -- -- --      (isSet→isGroupoid isSetℕ) _ _ _ _
-- -- -- -- -- -- --         (cong (cong len2) x₃) (cong  (cong len2) y₁) i i₁ x₄


-- -- -- -- -- -- -- -- -- -- --   -- paPerm : {xs ys : FMSet2 A} → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- --   --    → EM₁ (SymData (len2 xs))
-- -- -- -- -- -- -- -- -- -- --   -- paPerm {xs} = J (λ ys p → EM₁ (SymData (len2 xs)))
-- -- -- -- -- -- -- -- -- -- --   --    (Elim.f {B = λ xs → EM₁ (SymData (len2 xs))}
-- -- -- -- -- -- -- -- -- -- --   --      embase
-- -- -- -- -- -- -- -- -- -- --   --      (λ _ → gh→em₂→ _ (sucPermFDMorphism _))
-- -- -- -- -- -- -- -- -- -- --   --      (λ x y {xs}
-- -- -- -- -- -- -- -- -- -- --   --        → elimSet (SymData (len2 xs))
-- -- -- -- -- -- -- -- -- -- --   --          (λ _ → emsquash _ _) (emloop swap0and1≃)
-- -- -- -- -- -- -- -- -- -- --   --            λ g → 
-- -- -- -- -- -- -- -- -- -- --   --              ∙≡∙→square
-- -- -- -- -- -- -- -- -- -- --   --              (emloop swap0and1≃)
-- -- -- -- -- -- -- -- -- -- --   --              (emloop (sucPerm (sucPerm g)))                              
-- -- -- -- -- -- -- -- -- -- --   --              (emloop (sucPerm (sucPerm g)))
-- -- -- -- -- -- -- -- -- -- --   --               (emloop swap0and1≃)
-- -- -- -- -- -- -- -- -- -- --   --              {!!}
-- -- -- -- -- -- -- -- -- -- --   --              )

-- -- -- -- -- -- -- -- -- -- --   --      {!!}
-- -- -- -- -- -- -- -- -- -- --   --      {!!}
-- -- -- -- -- -- -- -- -- -- --   --      {!!}
-- -- -- -- -- -- -- -- -- -- --   --      {!!}
-- -- -- -- -- -- -- -- -- -- --   --      (λ _ → emsquash)
-- -- -- -- -- -- -- -- -- -- --   --      xs)

-- -- -- -- -- -- -- -- -- -- -- --   inj∷2 : (xs ys : FMSet2 A) → (x : A)
-- -- -- -- -- -- -- -- -- -- -- --            → x ∷2 xs ≡ x ∷2 ys → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- --   inj∷2 = ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- --     -- (ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- --     --    (λ _ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- --     --    (λ x x₁ x₂ → {!!} ∘ cong len2  )
-- -- -- -- -- -- -- -- -- -- -- --     --    {!!}
-- -- -- -- -- -- -- -- -- -- -- --     --    {!!}
-- -- -- -- -- -- -- -- -- -- -- --     --    λ _ → isSetΠ2 λ _ _ → trunc _ _ )
-- -- -- -- -- -- -- -- -- -- -- --     (λ x {xs} b →
-- -- -- -- -- -- -- -- -- -- -- --       ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- --        {!!}
-- -- -- -- -- -- -- -- -- -- -- --        (λ x' {ys} b' y' p →
-- -- -- -- -- -- -- -- -- -- -- --          {!!})
-- -- -- -- -- -- -- -- -- -- -- --          {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- --         λ _ → isSetΠ2 λ _ _ → trunc _ _)
-- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- --     λ _ → isSetΠ3 λ _ _ _ → trunc _ _ 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Rec.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (isSet→isGroupoid isSetℕ) zero (λ _ → suc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ → refl) (λ _ _ _ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ _ → refl) (λ _ _ _ _ → refl) (λ _ _ _ _ → refl)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RecSet.f isSetℕ zero (λ _ → suc) (λ _ _ _ → refl) (λ _ _ _ _ → refl)

-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- open import Cubical.HITs.EilenbergMacLane1 as EM

-- -- -- -- -- -- -- -- -- -- fm2Map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → FMSet2 A → FMSet2 B 
-- -- -- -- -- -- -- -- -- -- fm2Map f = f'
-- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- --   f' : FMSet2 _ → FMSet2 _ 
-- -- -- -- -- -- -- -- -- --   f' [] = []
-- -- -- -- -- -- -- -- -- --   f' (x ∷2 x₁) = f x ∷2 (f' x₁)
-- -- -- -- -- -- -- -- -- --   f' (comm x y x₁ i) = comm (f x) (f y) (f' x₁) i
-- -- -- -- -- -- -- -- -- --   f' (comm-inv x y x₁ i i₁) = comm-inv (f x) (f y) (f' x₁) i i₁
-- -- -- -- -- -- -- -- -- --   f' (hexDiag x y z x₁ i) = (hexDiag (f x) (f y) (f z) (f' x₁) i)
-- -- -- -- -- -- -- -- -- --   f' (hexU x y z x₁ i i₁) = hexU (f x) (f y) (f z) (f' x₁) i i₁
-- -- -- -- -- -- -- -- -- --   f' (hexL x y z x₁ i i₁) = hexL (f x) (f y) (f z) (f' x₁) i i₁
-- -- -- -- -- -- -- -- -- --   f' (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
-- -- -- -- -- -- -- -- -- --     trunc _ _ _ _ (λ i j → f' (x₃ i j))
-- -- -- -- -- -- -- -- -- --       (λ i j → f' (y₁ i j)) i i₁ x₄

-- -- -- -- -- -- -- -- -- -- module _ (A : Type ℓ) where
-- -- -- -- -- -- -- -- -- --   -- open import Cubical.Data.List.FinData


-- -- -- -- -- -- -- -- -- --   FMSet2OfLen : ℕ → Type ℓ
-- -- -- -- -- -- -- -- -- --   FMSet2OfLen n = Σ (FMSet2 A) λ x → len2 x ≡ n

-- -- -- -- -- -- -- -- -- --   _++2_ : FMSet2 A → FMSet2 A → FMSet2 A
-- -- -- -- -- -- -- -- -- --   [] ++2 ys = ys
-- -- -- -- -- -- -- -- -- --   (x ∷2 xs) ++2 ys = x ∷2 (xs ++2 ys)
-- -- -- -- -- -- -- -- -- --   comm x y xs i ++2 ys = comm x y (xs ++2 ys) i
-- -- -- -- -- -- -- -- -- --   comm-inv x y xs i i₁ ++2 ys = comm-inv x y (xs ++2 ys) i i₁
-- -- -- -- -- -- -- -- -- --   hexDiag x y z xs i ++2 ys = hexDiag x y z (xs ++2 ys) i 
-- -- -- -- -- -- -- -- -- --   hexU x y z xs i i₁ ++2 ys = hexU x y z (xs ++2 ys) i i₁ 
-- -- -- -- -- -- -- -- -- --   hexL x y z xs i i₁ ++2 ys = hexL x y z (xs ++2 ys) i i₁ 
-- -- -- -- -- -- -- -- -- --   trunc _ _ _ _ r s i i₁ i₂ ++2 ys =
-- -- -- -- -- -- -- -- -- --    trunc _ _ _ _ (λ i j → r i j ++2 ys)
-- -- -- -- -- -- -- -- -- --     (λ i j → s i j ++2 ys) i i₁ i₂


-- -- -- -- -- -- -- -- -- --   assoc++ : ∀ xs ys zs → xs ++2 (ys ++2 zs) ≡ (xs ++2 ys) ++2 zs
-- -- -- -- -- -- -- -- -- --   assoc++ = RElimSet.f w
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --      w : RElimSet _
-- -- -- -- -- -- -- -- -- --      RElimSet.[]* w _ _ = refl
-- -- -- -- -- -- -- -- -- --      RElimSet._∷*_ w _ p ys zs = cong (_ ∷2_) (p ys zs)
-- -- -- -- -- -- -- -- -- --      RElimSet.comm* w x y b = funExt₂ λ x' y' → λ i j → comm x y (b x' y' j) i 
-- -- -- -- -- -- -- -- -- --      RElimSet.hexDiag* w x y z b = funExt₂ λ x' y' → λ i j → hexDiag x y z (b x' y' j) i
-- -- -- -- -- -- -- -- -- --      RElimSet.trunc* w _ = isSetΠ2 λ _ _ → trunc _ _


-- -- -- -- -- -- -- -- -- --   rUnit++ : ∀ xs → xs ≡ xs ++2 []
-- -- -- -- -- -- -- -- -- --   rUnit++ = RElimSet.f w
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --      w : RElimSet (λ z → z ≡ (z ++2 []))
-- -- -- -- -- -- -- -- -- --      RElimSet.[]* w = refl
-- -- -- -- -- -- -- -- -- --      RElimSet._∷*_ w a = cong (a ∷2_)
-- -- -- -- -- -- -- -- -- --      RElimSet.comm* w x y b i j = comm x y (b j) i
-- -- -- -- -- -- -- -- -- --      RElimSet.hexDiag* w x y z b i j = hexDiag x y z (b j) i
-- -- -- -- -- -- -- -- -- --      RElimSet.trunc* w _ = trunc _ _

-- -- -- -- -- -- -- -- -- --   -- sym++2 : ∀ xs ys → xs ++2 ys ≡ ys ++2 xs
-- -- -- -- -- -- -- -- -- --   -- sym++2 = RElimSet.f w
-- -- -- -- -- -- -- -- -- --   --   where
-- -- -- -- -- -- -- -- -- --   --     w : RElimSet (λ xs → ∀ ys → (xs ++2 ys) ≡ (ys ++2 xs))
-- -- -- -- -- -- -- -- -- --   --     RElimSet.[]* w = rUnit++
-- -- -- -- -- -- -- -- -- --   --     (w RElimSet.∷* a) {xs} p ys = {!p (a ∷2 [])!}
-- -- -- -- -- -- -- -- -- --   --     -- cong (a ∷2_) (p ys) ∙ 
-- -- -- -- -- -- -- -- -- --   --     --         cong (_++2 xs) {!!} ∙ sym (assoc++ ys (a ∷2 []) xs) 
-- -- -- -- -- -- -- -- -- --   --     RElimSet.comm* w = {!!}
-- -- -- -- -- -- -- -- -- --   --     RElimSet.hexDiag* w = {!!}
-- -- -- -- -- -- -- -- -- --   --     RElimSet.trunc* w _ = isSetΠ λ _ → trunc _ _
-- -- -- -- -- -- -- -- -- --   -- _++2_ = RRec.f w
-- -- -- -- -- -- -- -- -- --   --   where
-- -- -- -- -- -- -- -- -- --   --     w : RRec {B = FMSet2 A → FMSet2 A} {!!}
-- -- -- -- -- -- -- -- -- --   --     w = {!!}

-- -- -- -- -- -- -- -- -- -- module _ {A : Type ℓ} where
-- -- -- -- -- -- -- -- -- --   -- isSetLofLA : ∀ n → isSet (ListOfLen A n)
-- -- -- -- -- -- -- -- -- --   -- isSetLofLA n = isOfHLevelListOfLen 0 isSetA n 

-- -- -- -- -- -- -- -- -- --   FMSet2OfLen≡ : ∀ {n} → {x y : FMSet2OfLen A n} → fst x ≡ fst y → x ≡ y 
-- -- -- -- -- -- -- -- -- --   FMSet2OfLen≡ = Σ≡Prop λ _ → isSetℕ _ _

-- -- -- -- -- -- -- -- -- --   isGroupoidFMSet2OfLen : ∀ n → isGroupoid (FMSet2OfLen A n)
-- -- -- -- -- -- -- -- -- --   isGroupoidFMSet2OfLen n = 
-- -- -- -- -- -- -- -- -- --     (isOfHLevelΣ 3 trunc λ _ → isSet→isGroupoid (isProp→isSet (isSetℕ _ _)))

-- -- -- -- -- -- -- -- -- -- module mkFunTest {CD : hSet ℓ} where

-- -- -- -- -- -- -- -- -- --   hSet≡ : {A B : Type ℓ} {isSetA : isSet A} {isSetB : isSet B} → A ≡ B →
-- -- -- -- -- -- -- -- -- --               Path (hSet ℓ) (A , isSetA) (B , isSetB)  
-- -- -- -- -- -- -- -- -- --   fst (hSet≡ p i) = p i
-- -- -- -- -- -- -- -- -- --   snd (hSet≡  {isSetA = isSetA} {isSetB} p i) =
-- -- -- -- -- -- -- -- -- --     isProp→PathP
-- -- -- -- -- -- -- -- -- --      (λ i → isPropIsSet {A = p i})
-- -- -- -- -- -- -- -- -- --      isSetA
-- -- -- -- -- -- -- -- -- --      isSetB i

-- -- -- -- -- -- -- -- -- --   flipIso : {A B C : Type ℓ} → Iso (A → B → C) (B → A → C) 
-- -- -- -- -- -- -- -- -- --   Iso.fun flipIso = flip
-- -- -- -- -- -- -- -- -- --   Iso.inv flipIso = flip
-- -- -- -- -- -- -- -- -- --   Iso.rightInv flipIso b = refl
-- -- -- -- -- -- -- -- -- --   Iso.leftInv flipIso b = refl


-- -- -- -- -- -- -- -- -- --   flip≃ : {A B C : Type ℓ} → (A → B → C) ≃ (B → A → C) 
-- -- -- -- -- -- -- -- -- --   flip≃ = isoToEquiv flipIso

-- -- -- -- -- -- -- -- -- --   diagIso : {A B C D : Type ℓ} → Iso (A → B → C → D) (C → B → A → D) 
-- -- -- -- -- -- -- -- -- --   Iso.fun diagIso x x₁ x₂ x₃ = x x₃ x₂ x₁
-- -- -- -- -- -- -- -- -- --   Iso.inv diagIso x x₁ x₂ x₃ = x x₃ x₂ x₁
-- -- -- -- -- -- -- -- -- --   Iso.rightInv diagIso b = refl
-- -- -- -- -- -- -- -- -- --   Iso.leftInv diagIso b = refl

-- -- -- -- -- -- -- -- -- --   zzR : RRec {A = Type ℓ} (isGroupoidHSet {ℓ})
-- -- -- -- -- -- -- -- -- --   RRec.[]* zzR = CD
-- -- -- -- -- -- -- -- -- --   RRec._∷*_ zzR A HS = (A → fst HS) , isSet→ (snd HS)
-- -- -- -- -- -- -- -- -- --   RRec.comm* zzR _ _ _ = hSet≡ (ua flip≃) 
-- -- -- -- -- -- -- -- -- --   RRec.comm-inv* zzR _ _ _ =
-- -- -- -- -- -- -- -- -- --     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet)) (isInjectiveTransport refl)
-- -- -- -- -- -- -- -- -- --   RRec.hexDiag* zzR _ _ _ _ = hSet≡ (ua (isoToEquiv diagIso))
-- -- -- -- -- -- -- -- -- --   RRec.hexU* zzR _ _ _ _ =
-- -- -- -- -- -- -- -- -- --    ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport refl))
-- -- -- -- -- -- -- -- -- --   RRec.hexL* zzR _ _ _ _ =
-- -- -- -- -- -- -- -- -- --    ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport refl))
  
-- -- -- -- -- -- -- -- -- --   zz : FMSet2 (Type ℓ) → hSet ℓ
-- -- -- -- -- -- -- -- -- --   zz = RRec.f zzR

-- -- -- -- -- -- -- -- -- -- module mkRecTest (ℓ : Level) where

-- -- -- -- -- -- -- -- -- --   hSet≡ : {A B : Type ℓ} {isSetA : isSet A} {isSetB : isSet B} → A ≡ B →
-- -- -- -- -- -- -- -- -- --               Path (hSet ℓ) (A , isSetA) (B , isSetB)  
-- -- -- -- -- -- -- -- -- --   fst (hSet≡ p i) = p i
-- -- -- -- -- -- -- -- -- --   snd (hSet≡  {isSetA = isSetA} {isSetB} p i) =
-- -- -- -- -- -- -- -- -- --     isProp→PathP
-- -- -- -- -- -- -- -- -- --      (λ i → isPropIsSet {A = p i})
-- -- -- -- -- -- -- -- -- --      isSetA
-- -- -- -- -- -- -- -- -- --      isSetB i

-- -- -- -- -- -- -- -- -- --   swapIso : {A B C : Type ℓ} → Iso (A × B × C) (B × A × C) 
-- -- -- -- -- -- -- -- -- --   Iso.fun swapIso (x , y , z) = y , x , z
-- -- -- -- -- -- -- -- -- --   Iso.inv swapIso (x , y , z) = y , x , z
-- -- -- -- -- -- -- -- -- --   Iso.rightInv swapIso b = refl
-- -- -- -- -- -- -- -- -- --   Iso.leftInv swapIso b = refl

-- -- -- -- -- -- -- -- -- --   diagIso : {A B C D : Type ℓ} → Iso (A × B × C × D) (C × B × A × D) 
-- -- -- -- -- -- -- -- -- --   Iso.fun diagIso (x , y , z , w) = z , y , x , w
-- -- -- -- -- -- -- -- -- --   Iso.inv diagIso (x , y , z , w) = z , y , x , w
-- -- -- -- -- -- -- -- -- --   Iso.rightInv diagIso b = refl
-- -- -- -- -- -- -- -- -- --   Iso.leftInv diagIso b = refl


-- -- -- -- -- -- -- -- -- --   zzR : RRec {A = hSet ℓ} (isGroupoidHSet {ℓ})
-- -- -- -- -- -- -- -- -- --   RRec.[]* zzR = Unit* , isSetUnit*
-- -- -- -- -- -- -- -- -- --   RRec._∷*_ zzR A HS = fst A × (fst HS) , isSet× (snd A) (snd HS)
-- -- -- -- -- -- -- -- -- --   RRec.comm* zzR A B HS = hSet≡ (ua (isoToEquiv swapIso))
-- -- -- -- -- -- -- -- -- --   RRec.comm-inv* zzR A B HS =
-- -- -- -- -- -- -- -- -- --     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet)) (isInjectiveTransport refl)
-- -- -- -- -- -- -- -- -- --   RRec.hexDiag* zzR A B C HS =
-- -- -- -- -- -- -- -- -- --     hSet≡ (ua (isoToEquiv diagIso))
-- -- -- -- -- -- -- -- -- --   RRec.hexU* zzR _ _ _ _ =
-- -- -- -- -- -- -- -- -- --        ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport refl))

-- -- -- -- -- -- -- -- -- --   RRec.hexL* zzR _ _ _ _ =
-- -- -- -- -- -- -- -- -- --        ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport (
-- -- -- -- -- -- -- -- -- --        funExt λ _ → cong₂ _,_ refl (cong₂ _,_ refl (cong₂ _,_ refl refl)))))

-- -- -- -- -- -- -- -- -- -- -- module sum (ℓ : Level) where

-- -- -- -- -- -- -- -- -- -- --   hSet≡ : {A B : Type ℓ} {isSetA : isSet A} {isSetB : isSet B} → A ≡ B →
-- -- -- -- -- -- -- -- -- -- --               Path (hSet ℓ) (A , isSetA) (B , isSetB)  
-- -- -- -- -- -- -- -- -- -- --   fst (hSet≡ p i) = p i
-- -- -- -- -- -- -- -- -- -- --   snd (hSet≡  {isSetA = isSetA} {isSetB} p i) =
-- -- -- -- -- -- -- -- -- -- --     isProp→PathP
-- -- -- -- -- -- -- -- -- -- --      (λ i → isPropIsSet {A = p i})
-- -- -- -- -- -- -- -- -- -- --      isSetA
-- -- -- -- -- -- -- -- -- -- --      isSetB i

-- -- -- -- -- -- -- -- -- -- --   swapIso : {A B C : Type ℓ} → Iso (A × B × C) (B × A × C) 
-- -- -- -- -- -- -- -- -- -- --   Iso.fun swapIso (x , y , z) = y , x , z
-- -- -- -- -- -- -- -- -- -- --   Iso.inv swapIso (x , y , z) = y , x , z
-- -- -- -- -- -- -- -- -- -- --   Iso.rightInv swapIso b = refl
-- -- -- -- -- -- -- -- -- -- --   Iso.leftInv swapIso b = refl

-- -- -- -- -- -- -- -- -- -- --   diagIso : {A B C D : Type ℓ} → Iso (A × B × C × D) (C × B × A × D) 
-- -- -- -- -- -- -- -- -- -- --   Iso.fun diagIso (x , y , z , w) = z , y , x , w
-- -- -- -- -- -- -- -- -- -- --   Iso.inv diagIso (x , y , z , w) = z , y , x , w
-- -- -- -- -- -- -- -- -- -- --   Iso.rightInv diagIso b = refl
-- -- -- -- -- -- -- -- -- -- --   Iso.leftInv diagIso b = refl


-- -- -- -- -- -- -- -- -- -- --   zzR : RRec {A = hSet ℓ} (isGroupoidHSet {ℓ})
-- -- -- -- -- -- -- -- -- -- --   RRec.[]* zzR = Unit* , isSetUnit*
-- -- -- -- -- -- -- -- -- -- --   RRec._∷*_ zzR A HS = fst A × (fst HS) , isSet× (snd A) (snd HS)
-- -- -- -- -- -- -- -- -- -- --   RRec.comm* zzR A B HS = hSet≡ (ua (isoToEquiv swapIso))
-- -- -- -- -- -- -- -- -- -- --   RRec.comm-inv* zzR A B HS =
-- -- -- -- -- -- -- -- -- -- --     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet)) (isInjectiveTransport refl)
-- -- -- -- -- -- -- -- -- -- --   RRec.hexDiag* zzR A B C HS =
-- -- -- -- -- -- -- -- -- -- --     hSet≡ (ua (isoToEquiv diagIso))
-- -- -- -- -- -- -- -- -- -- --   RRec.hexU* zzR _ _ _ _ =
-- -- -- -- -- -- -- -- -- -- --        ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport refl))

-- -- -- -- -- -- -- -- -- -- --   RRec.hexL* zzR _ _ _ _ =
-- -- -- -- -- -- -- -- -- -- --        ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- --     (∙≡∙→square _ _ _ _ (isInjectiveTransport (
-- -- -- -- -- -- -- -- -- -- --        funExt λ _ → cong₂ _,_ refl (cong₂ _,_ refl (cong₂ _,_ refl refl)))))




-- -- -- -- -- -- -- -- -- -- --   zz : FMSet2 (hSet ℓ) → hSet ℓ
-- -- -- -- -- -- -- -- -- -- --   zz = RRec.f zzR

-- -- -- -- -- -- -- -- -- -- --   -- uncR : RElim {A = hSet ℓ} λ S → fst (zz S) → FMSet2 (Σ (Type ℓ) λ X → X) 
-- -- -- -- -- -- -- -- -- -- --   -- RElim.[]* uncR _ = []
-- -- -- -- -- -- -- -- -- -- --   -- (uncR RElim.∷* x) {xs} x₁ (a , r) = (_ , a) ∷2 x₁ r
-- -- -- -- -- -- -- -- -- -- --   -- RElim.comm* uncR x y b i =
-- -- -- -- -- -- -- -- -- -- --   --   (λ b₁ → comm (fst x , fst (snd b₁)) (fst y , fst b₁) (b (snd (snd b₁))) i)
-- -- -- -- -- -- -- -- -- -- --   --     ∘ ua-unglue (isoToEquiv swapIso) i
-- -- -- -- -- -- -- -- -- -- --   -- -- toPathP (funExt λ z i → comm {!!} {!!} {!!} i)
-- -- -- -- -- -- -- -- -- -- --   -- RElim.comm-inv* uncR x y b i j x₁ =
-- -- -- -- -- -- -- -- -- -- --   --  let xx = {!!}
-- -- -- -- -- -- -- -- -- -- --   --  in comm-inv (fst x , {!fst x₁!}) {!!} {!!} i j
-- -- -- -- -- -- -- -- -- -- --   -- RElim.hexDiag* uncR = {!!}
-- -- -- -- -- -- -- -- -- -- --   -- RElim.hexU* uncR = {!!}
-- -- -- -- -- -- -- -- -- -- --   -- RElim.hexL* uncR = {!!}
-- -- -- -- -- -- -- -- -- -- --   -- RElim.trunc* uncR = {!!}

-- -- -- -- -- -- -- -- -- -- --   -- unc : ∀ S → fst (zz S) → FMSet2 (Σ (Type ℓ) λ X → X)
-- -- -- -- -- -- -- -- -- -- --   -- unc = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- module ⊎' where
-- -- -- -- -- -- -- -- -- -- -- --   -- QL : Bool → Type₀
-- -- -- -- -- -- -- -- -- -- -- --   -- QL false = ___+_++{!!}
-- -- -- -- -- -- -- -- -- -- -- --   -- QL true = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   -- QR : Bool → Type₀
-- -- -- -- -- -- -- -- -- -- -- --   -- QR x = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   -- record _⊎'_ {ℓ ℓ'} (A : Type ℓ)(B : Type ℓ') : Type (ℓ-max ℓ ℓ') where 
-- -- -- -- -- -- -- -- -- -- -- --   --   field
-- -- -- -- -- -- -- -- -- -- -- --   --     sw : Bool
-- -- -- -- -- -- -- -- -- -- -- --   --     ll : (Bool→Type sw → A)
-- -- -- -- -- -- -- -- -- -- -- --   --     rr : (Bool→Type (not sw) → B)

-- -- -- -- -- -- -- -- -- -- -- --   _⊎'_ : ∀ {ℓ ℓ'} (A : Type ℓ)(B : Type ℓ') → Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- -- -- -- -- -- --   A ⊎' B = Σ Bool λ sw → (Bool→Type sw → A) × (Bool→Type (not sw) → B)

-- -- -- -- -- -- -- -- -- -- -- --   ⊎-swap-Path : ∀ {ℓ ℓ'} (A : Type ℓ)(B : Type ℓ') → (A ⊎' B) ≡ (B ⊎' A)
-- -- -- -- -- -- -- -- -- -- -- --   ⊎-swap-Path A B i =
-- -- -- -- -- -- -- -- -- -- -- --    Σ (notEq i)
-- -- -- -- -- -- -- -- -- -- -- --      ((λ b → ua (Σ-swap-≃ {A = {!Bool→Type b → A!}} {A' = Bool→Type b → B}) i)
-- -- -- -- -- -- -- -- -- -- -- --        ∘ ua-unglue notEquiv i)

-- -- -- -- -- -- -- -- -- -- -- --   -- ⊎-swap-Iso : ∀ {ℓ ℓ'} (A : Type ℓ)(B : Type ℓ') → Iso (A ⊎' B) (B ⊎' A)
-- -- -- -- -- -- -- -- -- -- -- --   -- Iso.fun (⊎-swap-Iso A B) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   -- Iso.inv (⊎-swap-Iso A B) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   -- Iso.rightInv (⊎-swap-Iso A B) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   -- Iso.leftInv (⊎-swap-Iso A B) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- module ⊎'2 where
-- -- -- -- -- -- -- -- -- -- -- --   -- QL : Bool → Type₀
-- -- -- -- -- -- -- -- -- -- -- --   -- QL false = ___+_++{!!}
-- -- -- -- -- -- -- -- -- -- -- --   -- QL true = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   -- QR : Bool → Type₀
-- -- -- -- -- -- -- -- -- -- -- --   -- QR x = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   record _⊎'_ {ℓ ℓ'} (A : Type ℓ)(B : Type ℓ') : Type (ℓ-max ℓ ℓ') where 
-- -- -- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- -- -- --       sw : Bool
-- -- -- -- -- -- -- -- -- -- -- --       ll : (Bool→Type sw → A)
-- -- -- -- -- -- -- -- -- -- -- --       rr : (Bool→Type (not sw) → B)
