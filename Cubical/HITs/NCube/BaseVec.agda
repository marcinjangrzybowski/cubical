{-# OPTIONS --cubical --safe  #-}
module Cubical.HITs.NCube.BaseVec where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.HITs.Interval
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.IntervalPrim

-- This helper datatype will be injected with
-- boundary of lower dimension and boundaryInj later

data NBoundary' {n} {X : Type₀} (injX : X → NCube (n)) : Type₀ where
   lid : Bool → NCube (n) → NBoundary' injX
   cyl : ∀ x → lid false (injX x) ≡ lid true (injX x)


-- NBoundary and boundaryInj are recursively defined

NBoundary : ℕ → Type₀
boundaryInj : ∀ {n} → NBoundary n → NCube n

NBoundary zero = ⊥
NBoundary (suc n) = NBoundary' {n} (boundaryInj)

boundaryInj {suc n} (lid x x₁) = end x ∷ x₁
boundaryInj {suc n} (cyl x i) = inside i ∷ boundaryInj x

-- flipNBoundaryHead : ∀ {n} → Iso (NBoundary (suc (suc n))) (NBoundary (suc (suc n)))
-- flipNBoundaryHead = iso f f law law
--   where
--     f : _
--     f (lid x (end x₁ , x₂)) = (lid x₁ (end x , x₂))
--     f (lid x (inside i , x₂)) = (cyl (lid x x₂) i)
--     f (cyl (lid x x₁) i) = (lid x (inside i , x₁))
--     f (cyl (cyl x i₁) i) = (cyl (cyl x i) i₁)
    
--     law : _
--     law (lid x (end x₁ , x₂)) = refl
--     law (lid x (inside i , x₂)) = refl
--     law (cyl (lid x x₁) i) = refl
--     law (cyl (cyl x i₁) i) = refl

-- flipNBoundaryHeadF : ∀ {n} → NBoundary (suc (suc n)) → NBoundary (suc (suc n)) 
-- flipNBoundaryHeadF {n} = Iso.fun (flipNBoundaryHead {n})

boundaryEndMap : ∀ {n} → Bool → NBoundary n → NBoundary (suc n)
boundaryEndMap {n} x = lid x ∘ boundaryInj

cyl' : ∀ {n} → (bd : NBoundary (suc n)) →
               boundaryEndMap false bd ≡ boundaryEndMap true bd 
cyl' = cyl

lid' : ∀ {n} → Bool  → NCube n → NBoundary (suc n) 
lid' = lid


cyl'' : ∀ {n} →  Interval' → NBoundary n → NBoundary (suc n)
cyl'' (end x) y = cyl y (Bool→I x)
cyl'' (inside i) y = cyl y i


cylEx : ∀ {n} → boundaryEndMap {n} false ≡ boundaryEndMap true 
cylEx i x = cyl x i

faceInj : ∀ {n}
          → ℕ → Bool
          → NCube n → NBoundary (suc n)  
faceInj {suc n} (suc k) s (end x₂ ∷ x₃) = lid x₂ (boundaryInj (faceInj k s x₃))
faceInj {suc n} (suc k) s (inside i ∷ x₃) = cyl (faceInj k s x₃) i
faceInj  _  = lid

faceMap : ∀ {n}
          → ℕ → Bool
          → NCube n → NCube (suc n)  
faceMap n b = boundaryInj ∘ faceInj n b 

boundaryProj : ∀ {n} → NBoundary (suc n) → NCube n
boundaryProj {zero} _ = []
boundaryProj {suc n} (lid _ x₁) = x₁
boundaryProj {suc n} (cyl x _) = boundaryInj x


boundaryHead : ∀ {n} → NBoundary (suc n) →  Interval'
boundaryHead (lid x x₁) = end x
boundaryHead (cyl x i) = inside i


corner0Bd : ∀ {n} → NBoundary (suc n)
corner0Bd {zero} = lid false []
corner0Bd {suc n} = lid false corner0

corner1Bd : ∀ {n} → NBoundary (suc n)
corner1Bd {zero} = lid true []
corner1Bd {suc n} = lid true corner1

corner0Bd-≡-corner1Bd : ∀ {n} → corner0Bd {n = suc n} ≡ corner1Bd {n = suc n}
corner0Bd-≡-corner1Bd {n} i = ((λ i₁ → cyl (lid false (corner0-≡  corner0 i₁)) i₁)
                             ∙ λ i₁ → lid true (inside i₁ ∷ (corner0-≡-corner1 i₁))) i



NBoundary1-≡-Bool : NBoundary 1 ≡ Bool
NBoundary1-≡-Bool = isoToPath h 
  where

  h : Iso (NBoundary 1) Bool
  Iso.fun h (lid x _) = x
  Iso.inv h x = lid x []
  Iso.rightInv h b = refl
  Iso.leftInv h (lid x []) = refl


Bool≃Susp⊥' : Bool ≃ Susp ⊥
Bool≃Susp⊥' =
  isoToEquiv
    (iso
      (λ {false  → north; true → south})
      (λ {north → false;  south → true})
      (λ {north → refl;  south → refl})
      (λ {true  → refl;  false → refl}))

-- Equality of NBoundary and Sn

NBoundary-≡-S₊ : ∀ {n} → NBoundary (suc n) ≡ S₊ n

NBoundary-≡-S₊ {zero} = NBoundary1-≡-Bool ∙ (ua Bool≃Susp⊥' ) 

NBoundary-≡-S₊ {suc n} = (isoToPath (lem) ) ∙ cong Susp (NBoundary-≡-S₊)
  where

  lem : Iso (NBoundary' {suc n} _) (Susp _)
  Iso.fun (lem) (lid false x₁) = north
  Iso.fun (lem) (lid true x₁) = south
  Iso.fun (lem) (cyl x i) = merid x i
  Iso.inv (lem) north = lid false (corner0)
  Iso.inv (lem) south = lid true (corner1)
  Iso.inv (lem) (merid x i) =   ((cong (lid false) (corner0-≡ (boundaryInj x)))
                              ∙∙ (cyl x)
                              ∙∙ (cong (lid true) (≡-corner1 (boundaryInj x)))) i

  Iso.rightInv (lem) north = refl
  Iso.rightInv (lem) south = refl
  Iso.rightInv (lem) (merid x i₁) i =
          
         doubleCompPath-filler
        (λ _ → north)
        (λ j → doubleCompPath-filler
                (λ i₂ → merid (transp (λ _ → NBoundary (suc n)) ((~ i₂) ∨ i) x) (i₂ ∧ j))
                (λ i₂ → merid (transp ((λ _ → NBoundary (suc n))) i x)  j )
                (λ i₂ → merid (transp (λ _ → NBoundary (suc n)) ((~ i₂) ∧ i) x) (i₂ ∨  j))
                (~ i) j )
        (λ _ → south)
        (~ i) i₁

  Iso.leftInv (lem) (lid false x₁) = cong (lid false) (corner0-≡ _)
  Iso.leftInv (lem) (lid true x₁) = sym (cong (lid true) (≡-corner1 _))
  Iso.leftInv (lem) (cyl x i₁) i =
      doubleCompPath-filler
        (cong (lid false) (corner0-≡ (boundaryInj x)))
        (cyl x)
        (cong (lid true) (≡-corner1 (boundaryInj x)))
        (~ i) i₁

NBoundary-≡-S :  ∀ {n} → NBoundary n ≡ S (-1+ n)
NBoundary-≡-S {zero} = refl
NBoundary-≡-S {suc n} = NBoundary-≡-S₊



-- _isBoundaryOf_ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
--                → (NBoundary n → A) → (NCube n → A)
--                → Type ℓ
-- x isBoundaryOf x₁ = x ≡ x₁ ∘ boundaryInj



InsideOf : ∀ {ℓ} → ∀ {A : Type ℓ}
                  → ∀ {n}
                  → (bd : NBoundary n → A)
                  → Type ℓ

insideOf : ∀ {ℓ} → ∀ {A : Type ℓ}
                  → ∀ {n}
                  → (bc : NCube n → A)                  
                  → InsideOf (bc ∘ boundaryInj)

InsideOf {A = A} {n = zero} bd = A
InsideOf {n = suc n} bd =
                       PathP
                       (λ i → InsideOf (bd ∘ cyl'' (inside i)))
                       (insideOf (bd ∘ lid false))
                       (insideOf (bd ∘ lid true))

insideOf {n = zero} bc = bc [] 
insideOf {n = suc n} bc i = insideOf (λ x₁ → bc (inside i ∷ x₁))


reflⁿ : ∀ {ℓ} → {A : Type ℓ} → ∀ n → (a : A) → InsideOf {n = n} (const a)
reflⁿ zero a = a
reflⁿ (suc n) a = refl

nInside : ∀ n → InsideOf (boundaryInj {n})
nInside n = insideOf (idfun _)

toCubical :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {bd}
             → (InsideOf {A = A} {n = n} bd )
             → NCube n → A 
toCubical {n = zero} {bd} x x₁ = x
toCubical {n = suc n} {bd} x (end x₁ ∷ x₂) = toCubical (x (Bool→I x₁)) x₂
toCubical {n = suc n} {bd} x (inside i ∷ x₂) = toCubical (x i) x₂



NBoundary-rec :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                 → (f : Bool → NCube n → A)
                 → f false ∘ boundaryInj ≡ f true ∘ boundaryInj 
                 → NBoundary (suc n) → A 
NBoundary-rec f x (lid x₁ x₂) = f x₁ x₂
NBoundary-rec f x (cyl x₁ i) = x i x₁


InsideOfω→Cub : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → (bd : Boundaryω A n)
                     → InsideOfω {ℓ} {A} {n} bd
                     → NCube n → A
InsideOfω→Cub {A = A} {n = n} bd x = C→-app {n = n} {A = A} (outSⁿ n (boundaryExpr n) bd x) 

InsideOfω→InsideOf : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → (bd : Boundaryω A n)
                     → InsideOfω {ℓ} {A} {n} bd
                     → Σ _ (InsideOf {A = A} {n = n})
InsideOfω→InsideOf bd x = (InsideOfω→Cub bd x ∘ boundaryInj) , insideOf (InsideOfω→Cub bd x)

InsideOf→InsideOfω-bd : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → (bd : NBoundary n → A)
                     → InsideOf bd
                     → Boundaryω A n
InsideOf→InsideOfω-bd {A = A} {n = n} bd x =
  Partialⁿ-const A n (boundaryExpr n)
   (C→elim {n = n} {A = A} (toCubical x)) 

InsideOf→InsideOfω : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → (bd : NBoundary n → A)
                     → (x : InsideOf bd)
                     → InsideOfω {A = A} {n = n} (InsideOf→InsideOfω-bd bd x)
InsideOf→InsideOfω {A = A} {n = n} bd x =
    inSⁿ n (boundaryExpr n) (C→elim {n = n} {A = A} (toCubical x))


InsideOfω-Path-bd : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → (bd : Boundaryω A (suc n))
                     → InsideOfω {ℓ} {A} {(suc n)} bd
                     → (i : I) → Boundaryω A n
InsideOfω-Path-bd {n = n} bd x i = 
  InsideOf→InsideOfω-bd
    (fst (InsideOfω→InsideOf bd x) ∘ (cyl'' (inside i)))
    ((snd (InsideOfω→InsideOf bd x)) i)

InsideOfω-Path : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → (bd : Boundaryω A (suc n))
                     → (x : InsideOfω {ℓ} {A} {(suc n)} bd)
                     → (i : I)
                     → InsideOfω {A = A} {n = n} ((InsideOfω-Path-bd {A = A} {n = n} bd x) i)
InsideOfω-Path {n = n} bd x i = 
  InsideOf→InsideOfω
    (fst (InsideOfω→InsideOf bd x) ∘ (cyl'' (inside i)))
    ((snd (InsideOfω→InsideOf bd x)) i)


InsideOfω-Path' : ∀ {ℓ} → ∀ (A : Type ℓ) → ∀ n
            → (pa : Partialⁿ A (suc n) (boundaryExpr (suc n)))
            → (s : Subⁿ A (suc n) _ pa)
            → C→-app {n = n} {A} ((outSⁿ (suc n) (boundaryExpr (suc n)) pa s) i0)
              ≡
              C→-app {n = n} {A} ((outSⁿ (suc n) (boundaryExpr (suc n)) pa s) i1)
            
InsideOfω-Path' A n pa s i =
  C→-app (outSⁿ (suc n) (boundaryExpr (suc n)) pa s i)


-- TODO 
-- OnBoundary-test : ∀ n → (∀ c → OnBoundary {n = n} c) → ⊥ 
-- OnBoundary-test zero x = fst (x [])
-- OnBoundary-test (suc n) x = {!!}

-- NBoundary-cyl-Ty : ∀ n → Boundaryω (NBoundary n) n → Typeω  
-- NBoundary-cyl-Ty n bd = PartialPⁿ n (boundaryExpr n)
--                           (Partialⁿ-map {A = NBoundary n} {B = Type₀} n {e = (boundaryExpr n)}
--                             (λ x → lid' false (boundaryInj x) ≡ lid' true (boundaryInj x) )
--                             (bd))
-- NBoundary-cyl : ∀ n → (bd : Boundaryω (NBoundary n) n) → NBoundary-cyl-Ty n bd
-- NBoundary-cyl zero bd ()
-- NBoundary-cyl (suc n) =
--   PartialPⁿ-mapTo {n = suc n}
--     {A = NBoundary (suc n)} 
--     {B = λ bd →  lid false (boundaryInj bd) ≡ lid true (boundaryInj bd)}
--       (λ x i → cyl' x i )


-- _isBoundaryOf_ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
--                → (NBoundary n → A) → (NCube n → A)
--                → Typeω
-- _isBoundaryOf_ {ℓ} {A} {n} x x₁ = {!∀!}


-- NBoundary-cyl :  ∀ n →
--                        Partialⁿ (NBoundary n) n (boundaryExpr n)
--                      → Partialⁿ (NBoundary (suc n)) (suc n)
--                                         (λ _ → boundaryExpr n ) 
-- NBoundary-cyl n x i = Partialⁿ-map {n = n} ((cyl'' (inside i))) (x) 



-- NBoundaryω-intersection : ∀ n → Partialⁿ (NBoundary (suc n)) (suc n)
--                                   (λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr n)
-- NBoundaryω-intersection n i =
--   ⊂'-∧ (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) (boundaryExpr n)
--   (Partial∨ⁿ-ends n i
--     (Partialⁿ-map {A = NCube n} {B = NBoundary (suc n)} n
--       (lid' false) (Partialⁿ-const (NCube n) n _ (nCubeω n)))
--     (Partialⁿ-map {A = NCube n} {B = NBoundary (suc n)} n
--       (lid' true) (Partialⁿ-const (NCube n) n _ (nCubeω n)))
--     )


-- inPartialⁿ-Sub⊂' : ∀ {ℓ} → {A : Type ℓ} → ∀ n → {i j : C→I n}                  
--                   → (pa : Partialⁿ A n i)
--                   → Partialⁿ-Sub A n j i ( ⊂'-∧2 j i pa )
-- inPartialⁿ-Sub⊂' zero pa e=1 = inS {! pa !}
-- inPartialⁿ-Sub⊂' (suc n) pa = {!!}


-- onBoundary-refl : ∀ n → NBoundary n → (Σ _ (OnBoundary {n}))
-- onBoundary-refl n x = (boundaryInj x) , (x , refl)



indω : (x : ℕ → Typeω) → (x 0) → (∀ n → x n → x (suc n)) → ∀ n → x n 
indω x x₁ x₂ zero = x₁
indω x x₁ x₂ (suc n) = x₂ n (indω x x₁ x₂ n)


OnBoundary : ∀ {n} → NCube n → Type₀
OnBoundary c = Σ[ bd ∈ NBoundary _ ] (c ≡ boundaryInj bd)

boundaryω-Σ : ℕ → Typeω
boundaryω-Σ n = PartialPⁿ n (boundaryExpr n)
                (Partialⁿ-const Type₀ n _ (C→elim {n = n} OnBoundary))



PartialP-map-Σ : ∀ {ℓ ℓ' ℓ'' ℓ'''} → ∀ n → {e : C→I n}
                     → {A : Type ℓ} → {A' : Type ℓ'}
                     → {B : NCube n → A → Type ℓ''}
                     → {B' : NCube n → A' → Type ℓ'''}
                     → (f : A → A')
                     → (g : ∀ {c} → ∀ {a} → B c a → B' c (f a))
                     → PartialPⁿ n e
                         (Partialⁿ-const _ n _ (C→elim {n = n} λ c → Σ _ (B c) ))
                     → PartialPⁿ n e
                         ((Partialⁿ-const _ n _ (C→elim {n = n} λ c → Σ _ (B' c) )))
PartialP-map-Σ zero f g x p = (f (fst (x p))) , (g (snd (x p)))
PartialP-map-Σ (suc n) f g x i = PartialP-map-Σ n f g (x i)




Partialⁿ-Sub-ends-split : ∀ {ℓ} → {A : Type ℓ} → ∀ n → {i : I} → {j : C→I (suc n)}
                          → (p : I → Partialⁿ A (suc n) j)
                          → Subⁿ A (suc n) j (p i0)
                          → Subⁿ A (suc n) j (p i1)
                          → Partialⁿ-Sub (A) (suc n)
                             ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) j
                                (⊂'-∧2
                                   ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
                                   j (p i))
Partialⁿ-Sub-ends-split n p l0 l1 i = {!!}



lem1 : ∀ {ℓ} → ∀ {n} → ∀ (i : I) → (j : C→I (suc n))
          → {A : (i₁ : I) → Partialⁿ (Set ℓ) n (j i₁)}
          → PartialPⁿ (suc n) j A
          → PartialPⁿ (suc n) (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ j) {!!}
lem1 = {!!}

NBoundaryω-step : ∀ n → boundaryω-Σ (suc n) → boundaryω-Σ (suc (suc n))
NBoundaryω-step n' prev i = 
   PartialP∨ⁿ n 
       ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr n)       
       intersection
       
       {!!}
       {!!} --(inPartialⁿ-Sub⊂' (suc n) (prev-cyl i))

   where
     n = suc n'

     prev-cyl : (i' : I) → PartialPⁿ n ((boundaryExpr n))
                       ((Partialⁿ-const Type₀ (suc n) (λ _ → boundaryExpr n)
                           (C→elim {n = (suc n)} OnBoundary)) i')
     prev-cyl i' =  PartialP-map-Σ n
                       {B' = λ x x₁ → inside i' ∷ x ≡ boundaryInj x₁}
                        (cyl'' (inside i'))  
                        (cong (inside i' ∷_))
                      (prev)

     iTy0 : {!!}
     iTy0 = {!!}

     intersection0 : PartialPⁿ n
                       (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr n)
                       (⊂'-∧2 ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr n)
                        ( Partialⁿ-const Type₀ (suc n) (λ _ x → boundaryExpr n x)
                           (C→elim {n = suc n} OnBoundary) i))
     intersection0 = ⊂'P-∧2
                     ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
                     (boundaryExpr n)
                      (prev-cyl i)

     iTy : {!!}
     iTy = {!!}

     intersection : PartialPⁿ n (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr n)
                      (⊂'-∧ ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr n)
                       (⊂→⊂' ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
                        (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ boundaryExpr n)
                        (⊂-∨1 ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr n))
                        ( Partialⁿ-const Type₀ (suc n)
                               (λ i′ x → ([ i′ ]Iexpr ∨ⁿ [ ~ i′ ]Iexpr) ∨ⁿ boundaryExpr n x)
                           (C→elim {n = suc n} OnBoundary) i)))
                           
     intersection = {!!}

NBoundaryω1 : boundaryω-Σ 1
NBoundaryω1 i =
  λ { (i = i0) → (lid false []) , refl ;
      (i = i1) → (lid true []) , refl }


NBoundaryω : ∀ n → (boundaryω-Σ n)
NBoundaryω zero ()
NBoundaryω (suc n) =
   indω (λ n → boundaryω-Σ (suc n)) NBoundaryω1
    NBoundaryω-step
    n


-- NBoundaryω : ∀ n → (boundaryω-Σ n)
-- NBoundaryω zero ()
-- NBoundaryω (suc zero) i =
--    λ { (i = i0) → (lid false []) , refl ; (i = i1) → (lid true []) , refl } 
-- NBoundaryω (suc (suc n)) i  = 
--    PartialP∨ⁿ (suc n)
--        ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr (suc n))
--        {Partialⁿ-const Type₀ (suc (suc n)) (boundaryExpr (suc (suc n)))
--             (C→elim {n = suc (suc n)} OnBoundary) i}
--        intersection
       
--        {!!}
--        {!!} --(inPartialⁿ-Sub⊂' (suc n) (prev-cyl i))

--    where

--      prev-cyl : (i' : I) → PartialPⁿ (suc n) ((boundaryExpr (suc n)))
--                        ((Partialⁿ-const Type₀ (suc (suc n)) (λ _ → boundaryExpr (suc n))
--                            (C→elim {n = (suc (suc n))} OnBoundary)) i')
--      prev-cyl i' =  PartialP-map-Σ (suc n)
--                        {A = NBoundary (suc n)} {A' = NBoundary (suc (suc n))}
--                        {B = λ x x₁ → x ≡ boundaryInj x₁}
--                        {B' = λ x x₁ → inside i' ∷ x ≡ boundaryInj x₁}
--                         (cyl'' (inside i'))  
--                         (cong (inside i' ∷_))
--                       (NBoundaryω (suc n))

--      iTy0 : {!!}
--      iTy0 = {!!}

--      intersection0 : PartialPⁿ (suc n)
--                        (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr (suc n))
--                        (⊂'-∧2 ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr (suc n))
--                         ( Partialⁿ-const Type₀ (suc (suc n)) (λ _ → boundaryExpr (suc n))
--                            (C→elim {n = suc (suc n)} OnBoundary) i))
--      intersection0 = ⊂'P-∧2
--                      ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
--                      (boundaryExpr (suc n))
--                       (prev-cyl i)

--      iTy : {!!}
--      iTy = {!!}

--      intersection : PartialPⁿ (suc n) (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr (suc n))
--                        λ i₁ →
--                            ⊂'-∧ ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr (suc n))
--                            (⊂→⊂' ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
--                             (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ boundaryExpr (suc n))
--                             (⊂-∨1 ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr (suc n)))
--                             (Partialⁿ-const Type₀ (suc (suc n)) (boundaryExpr (suc (suc n)))
--                              (C→elim {n = suc (suc n)} OnBoundary) i))
--                            i₁
--      intersection = {!prev-cyl i!}

     -- prev-cyl' : I → Partialⁿ (NBoundary (suc (suc n))) (suc n) (boundaryExpr (suc n))
     -- prev-cyl' i' = Partialⁿ-map (suc n) (cyl'' (inside i')) (NBoundaryω (suc n))

     -- prev-cyl : I → Partialⁿ (NBoundary (suc (suc n))) (suc n) (boundaryExpr (suc n))
     -- prev-cyl i' = Partialⁿ-map (suc n) (
     --                  ( {!!}
     --                   ∙∙ (λ i' → cyl'' (inside i')) ∙∙
     --                   {!!} ) i'
     --                  ) (NBoundaryω (suc n))

     -- intersection : Partialⁿ (NBoundary (suc (suc n))) (suc n)
     --                  (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr (suc n))
     -- intersection = ⊂'-∧2
     --                    ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
     --                    (boundaryExpr (suc n)) (prev-cyl i)

     -- cc : InsideOfω {A = NCube (suc n)} {n = suc n} (
     --            Partialⁿ-map 
     --            (suc n) boundaryInj (NBoundaryω (suc n)))
     -- cc = {!inSⁿ ? ? ?!}

     -- cc2 : {!!}
     -- cc2 = {!!}

     -- c0 : InsideOfω (prev-cyl i0)
     -- c0 = Subⁿ-map (suc n) (lid false ∘ boundaryInj) cc2 

     -- c1 : InsideOfω (prev-cyl i1)
     -- c1 = Subⁿ-map (suc n) (lid true ∘ boundaryInj) cc2

     -- ps : Partialⁿ-Sub (NBoundary (suc (suc n))) (suc n)
     --        ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr (suc n)) intersection
     -- ps = Partialⁿ-Sub-ends-split n prev-cyl
     --        c0
     --        c1
     --   -- let z : {!!}
     --   --     z = 

     --   -- in {!!}


-- -- ↑ clean 
-- -------------------------

-- -- Boundaryω→NBoundary= :  ∀ {ℓ} → ∀ (A : Type ℓ) → ∀ n
-- --             → (pa : Boundaryω A (suc n))
-- --             → Path ((a : NBoundary n) → A) (C→-app
-- --                    (Partialⁿ-IsOne⊂ {ℓ} A n (boundaryExpr (suc n) i0) (pa i0)
-- --                     (1⊂lid n false))
-- --                    ∘ boundaryInj)
                   
-- --                    (C→-app
-- --                    (Partialⁿ-IsOne⊂ A n (boundaryExpr (suc n) i1) (pa i1)
-- --                     (1⊂lid n true))
-- --                    ∘ boundaryInj)

-- -- Boundaryω→NBoundary= = {!!}


-- -- Boundaryω→NBoundary :  ∀ {ℓ} → ∀ (A : Type ℓ) → ∀ n
-- --             → Boundaryω A n
-- --             → NBoundary n → A
-- -- Boundaryω→NBoundary A (suc n) pa =
-- --  let e : Bool → NCube n → A
-- --      e = λ b → C→-app (Partialⁿ-IsOne⊂ _ _ _ (pa (Bool→I b)) (1⊂lid n b))

-- --  in  NBoundary-rec e {!!}



-- NBoundaryω2 : Boundaryω (NBoundary 2) 2
-- NBoundaryω2 i i₁ (i = i1) = lid' true (inside i₁ ∷ [])
-- NBoundaryω2 i i₁ (i = i0) = lid' false (inside i₁ ∷ [])
-- NBoundaryω2 i i₁ (i₁ = i1) = cyl' (lid' true []) i
-- NBoundaryω2 i i₁ (i₁ = i0) = cyl' (lid' false []) i






-- -- NBoundaryωₖ : ∀ n → ∀ k → Partialⁿ (NBoundary (k + n)) (k + n) (liftExpr k (boundaryExpr n))





-- -- NBoundaryω-test : ∀ n → Boundaryω (NBoundary n) n
-- -- NBoundaryω-test = {!!}


-- NBoundaryω-test0' : Boundaryω (NBoundary 3) 3
-- NBoundaryω-test0' i₀ i₁ i₂ =
--   let cu = (nCubeω 3 i₀ i₁ i₂ 1=1)
--   in
--   primPOr i₀ _ (λ _ → lid true (tail cu))
--     (primPOr (~ i₀) _ (λ _ → lid false (tail cu))
--     (primPOr i₁ _ (λ _ → cyl' (lid true (inside i₂ ∷ [])) i₀)
--     (primPOr (~ i₁) _ (λ _ → cyl' ((lid false (inside i₂ ∷ []))) i₀)
--     ((primPOr i₂ _ (λ p → cyl' (cyl' (lid true []) i₁) i₀ ) --NBoundaryω2
--     (primPOr (~ i₂) i0 ((λ p → cyl' (cyl' (lid false []) i₁) i₀ ))
--      empty))))))

-- NBoundaryω-test1' : Boundaryω (NBoundary 3) 3
-- NBoundaryω-test1' i₀ i₁ i₂ =
--   let cu = (nCubeω 3 i₀ i₁ i₂ 1=1)
--   in
--   primPOr i₀ (~ i₀ ∨ i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid true (tail cu))
--     (primPOr (~ i₀) (i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid false (tail cu))
--     λ p →  cyl' (NBoundaryω2 i₁ i₂ p) i₀)

-- NBoundaryω-test2'' : (bd : Boundaryω (NBoundary 2) 2) 
--                    → InsideOfω {A = NCube 2} {n = 2}
--                        ((Partialⁿ-map {A = NBoundary 2} {B = NCube 2} 2 boundaryInj bd))
--                    →  Boundaryω (NBoundary 3) 3
-- NBoundaryω-test2'' bd y i₀ i₁ i₂ = 
--   let x = NBoundary-cyl 2 bd
--       p = snd (InsideOfω→InsideOf
--             (Partialⁿ-map {A = NBoundary 2} {B = NCube 2} 2 boundaryInj bd) y)
--   in
--     primPOr (i₀ ∨ (~ i₀)) (boundaryExpr 2 i₁ i₂)
--       (primPOr i₀  (~ i₀)
--         (λ _ → lid true (p i₁ i₂))
--         (λ _ → lid false (p i₁ i₂))
--         )
--       λ p → (x i₁ i₂ p i₀ )


-- NBoundaryω-test2''' : (bd : Boundaryω (NBoundary 2) 2) 
--                    → InsideOfω {A = NCube 2} {n = 2}
--                        ((Partialⁿ-map {A = NBoundary 2} {B = NCube 2} 2 boundaryInj bd))
--                    →  Boundaryω (NBoundary 3) 3
-- NBoundaryω-test2''' bd y i₀ i₁ i₂ = 
--   let cu = (nCubeω 2 i₁ i₂ 1=1)
      
--       x = NBoundary-cyl 2 bd
--       p = snd (InsideOfω→InsideOf
--             (Partialⁿ-map {A = NBoundary 2} {B = NCube 2} 2 boundaryInj bd) y)

--       x' : .(IsOne (boundaryExpr 2 i₁ i₂)) → Sub (NBoundary 3) ((i₀ ∨ (~ i₀)) ∧ (boundaryExpr 2 i₁ i₂) )
--              (primPOr (i₀ ∧ (boundaryExpr 2 i₁ i₂)) ((~ i₀) ∧ (boundaryExpr 2 i₁ i₂))
--                (⊂'-∧2 ((negIf true i₀)) (boundaryExpr 2 i₁ i₂)
--                (Partialⁿ-map {A = NBoundary 2} 0 (lid true ∘ boundaryInj) (bd i₁ i₂)))
--                (⊂'-∧2 ((negIf false i₀)) (boundaryExpr 2 i₁ i₂)
--                (Partialⁿ-map {A = NBoundary 2} 0 (lid false ∘ boundaryInj) (bd i₁ i₂)))
--                )
--       x' = λ .z → inS ((x i₁ i₂ z i₀ ))

--       p' : Subⁿ (NCube 2) 0 (boundaryExpr 2 i₁ i₂)
--              (Partialⁿ-map 2 boundaryInj bd i₁ i₂)
--       p' = y i₁ i₂
--   in
--     primPOr (i₀ ∨ (~ i₀)) (boundaryExpr 2 i₁ i₂)
--       (primPOr i₀  (~ i₀)
--         (λ _ → lid true (outS p'))
--         (λ _ → lid false (outS p'))
--         )
--       λ p → outS (x' p)

-- -- primPOr i₀ (~ i₀ ∨ i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid true (p i₁ i₂))
-- --     (primPOr (~ i₀) (i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid false (p i₁ i₂))
-- --     λ p → (x i₁ i₂ p i₀ ))


-- -- mkaeBN-step : ∀ {n} {bd : Boundaryω (NBoundary (suc n)) (suc n)}
-- --                  {y : InsideOfω (Partialⁿ-map boundaryInj bd)} {i} →
-- --                PartialPⁿ n (boundaryExpr (suc n) i)
-- --                (Partialⁿ-map
-- --                 (λ x₁ → lid false (boundaryInj x₁) ≡ lid true (boundaryInj x₁))
-- --                 (bd i)) →
-- --                InsideOf
-- --                (λ x₁ →
-- --                   C→-app
-- --                   (outSⁿ n (boundaryExpr (suc n) i) (Partialⁿ-map boundaryInj (bd i))
-- --                    (y i))
-- --                   (boundaryInj x₁)) →
-- --                ∀ i₁ →
-- --                Partialⁿ (NBoundary' boundaryInj) n
-- --                (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ boundaryExpr (suc n) i₁)
-- -- mkaeBN-step = {!!}

-- makeNBoundaryω : ∀ n → (bd : Boundaryω (NBoundary n) n) 
--                    → InsideOfω {A = NCube n} {n = n}
--                        ((Partialⁿ-map {A = NBoundary n} {B = NCube n} n boundaryInj bd))
--                    →  Boundaryω (NBoundary (suc n)) (suc n)
-- makeNBoundaryω zero bd _ i =
--   (primPOr i  (~ i)
--         (λ _ → lid true [])
--         (λ _ → lid false [])
--         )
-- makeNBoundaryω (suc n) bd y i i₁ =
--    let x = NBoundary-cyl (suc n) bd
--        p = snd (InsideOfω→InsideOf
--             (Partialⁿ-map {A = NBoundary (suc n)} {B = NCube (suc n)} (suc n) boundaryInj bd) y)

--        x' : PartialPⁿ n (boundaryExpr (suc n) i)
--               (Partialⁿ-map (suc n)
--                (λ x₁ → lid false (boundaryInj x₁) ≡ lid true (boundaryInj x₁)) bd
--                i)
--        x' = x i
       
--        p' : InsideOf
--               (λ x₁ →
--                  fst (InsideOfω→InsideOf (λ i₂ → Partialⁿ-map (suc n) boundaryInj bd i₂) y)
--                  (cyl'' (inside i) x₁))
--        p' = p i


--        w : Partialⁿ (NBoundary (suc (suc n))) n
--              (boundaryExpr (suc (suc n)) i i₁)
--        w = {!!}

--    in w


-- -- NBoundaryω-test3-test : (i : I) → {!!}
-- -- NBoundaryω-test3-test i = {!NBoundaryω-test3'' _ i i1!}

-- -- NBoundaryω↑ : ∀ n → boundaryω-isOk n
-- --                    →  Boundaryω (NBoundary (suc n)) (suc n)
-- -- NBoundaryω↑ = {!!}


-- -- NBoundaryω-test3'' : boundaryω-isOk 2
-- --                    →  Boundaryω (NBoundary 3) 3
-- -- NBoundaryω-test3'' x i₀ i₁ i₂ =
-- --      let cu = (nCubeω 2 i₁ i₂ 1=1)
-- --      in
-- --      primPOr i₀ (~ i₀ ∨ i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid true cu)
-- --     (primPOr (~ i₀) (i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid false cu)
-- --       λ p →
-- --         ((λ i → lid' false (snd (x i₁ i₂ p) (i)))
-- --         ∙∙
-- --         ((λ i₀ → cyl'  (fst (x i₁ i₂ p)) i₀))
-- --         ∙∙
-- --           λ i → lid' true (snd (x i₁ i₂ p) (~ i)))
-- --            i₀
-- --        )



--   -- let cu = (nCubeω 3 i₀ i₁ i₂ 1=1)
--   --     p = snd (InsideOfω→InsideOf
--   --           (Partialⁿ-map {A = NBoundary 2} {B = NCube 2} {n = 2} boundaryInj bd) y)
--   -- in
--   -- primPOr i₀ (~ i₀ ∨ i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid true (p i₁ i₂))
--   --   (primPOr (~ i₀) (i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid false (p i₁ i₂))
--   --   λ p → (x i₁ i₂ p i₀ ))



-- -- NBoundaryω-test' : InsideOfω {A = ℕ} {n = 3} (Partialⁿ-const ℕ 3 (boundaryExpr 3) (C-const 3 1 ))
-- --                    → Boundaryω ℕ 4
-- -- NBoundaryω-test' x i₀ i₁ i₂ i₃ =
-- --   primPOr i₀ (~ i₀ ∨  (~ i₀) ∨ (boundaryExpr 3 i₁ i₂ i₃)) (λ _ → 1)
-- --     (primPOr (~ i₀) (boundaryExpr 3 i₁ i₂ i₃) (λ _ → 1)
-- --        λ _ → outS (x i₁ i₂ i₃)
-- --        )

-- -- NBoundaryω-test'2 : ∀ {ℓ} → {A : Type ℓ} → (NCube 4 → A)
-- --                    → Boundaryω A 4
-- -- NBoundaryω-test'2 x i₀ i₁ i₂ i₃ =
-- --   primPOr i₀ (~ i₀ ∨  (~ i₀) ∨ (boundaryExpr 3 i₁ i₂ i₃)) (λ _ → (C→elim x i₀ i₁ i₂ i₃ 1=1))
-- --     (primPOr (~ i₀) (boundaryExpr 3 i₁ i₂ i₃) (λ _ → (C→elim x i₀ i₁ i₂ i₃ 1=1))
-- --        λ _ → (C→elim x i₀ i₁ i₂ i₃ 1=1)
-- --        )

-- -- NBoundaryω-test'3 : ∀ {ℓ} → {A : Type ℓ} → A
-- --                    → Boundaryω A 4
-- -- NBoundaryω-test'3 x i₀ i₁ i₂ i₃ =
-- --   primPOr i₀ (~ i₀ ∨  (~ i₀) ∨ (boundaryExpr 3 i₁ i₂ i₃)) (λ _ → x)
-- --     (primPOr (~ i₀) (boundaryExpr 3 i₁ i₂ i₃) (λ _ → x)
-- --        λ _ → x
-- --        )

-- -- -- NBoundaryω-finish' : ∀ {ℓ} → {A : Type ℓ} → A → ∀ n
-- -- --                     → Boundaryω A (suc n)
-- -- -- NBoundaryω-finish' a zero i = primPOr i (~ i) (λ _ → a) λ _ → a
-- -- -- NBoundaryω-finish' a (suc n) i i₁ =
-- -- --   let z : Partialⁿ _ n (boundaryExpr (suc n) i)
-- -- --       z = NBoundaryω-finish' a n i

-- -- --   in {!z!}

-- -- NBoundaryω-finish0 : ∀ {ℓ} → {A : Type ℓ} → (a : A) → (i : I) → (j : I)
-- --                         → (z : Partial j (a ≡ a))
-- --                         → Partial (i ∨ ~ i ∨ j) A  
-- -- NBoundaryω-finish0 a i j z =
-- --       primPOr i (~ i ∨ j) (λ _ → a)
-- --         (primPOr (~ i) (j) (λ _ → a)
-- --          λ p → z p i 
-- --        )

-- -- -- NBoundaryω-finishTy :  ∀ {ℓ} → (A : Type ℓ) → (a : A) → (j : I) → ℕ → Typeω
-- -- -- NBoundaryω-finishTy A a j zero = ∀ i → Partial j (a ≡ a) → Partial (i ∨ ~ i ∨ j) A
-- -- -- NBoundaryω-finishTy A a j (suc n) = ∀ iₖ → NBoundaryω-finishTy A a (j ∨ iₖ ∨ (~ iₖ)) n 

-- -- -- NBoundaryω-finish : ∀ {ℓ} → (A : Type ℓ) → (a : A) → ∀ n
-- -- --                     → NBoundaryω-finishTy A a i0 n
-- -- -- NBoundaryω-finish A a zero i _ =  primPOr i (~ i) (λ _ → a) (λ _ → a)
-- -- -- NBoundaryω-finish A a (suc zero) i j = NBoundaryω-finish0 a j (i ∨ ~ i)
-- -- -- NBoundaryω-finish A a (suc (suc n)) i iₖ = NBoundaryω-finish A a (suc n) ((i ∨ ~ i) ∨ iₖ ∨ ~ iₖ)

-- -- NBoundaryω-finishTy :  ∀ {ℓ} → (m : ℕ) → (j : I) → ℕ → Typeω
-- -- NBoundaryω-finishTy m j zero = ∀ i → {!!}
-- --                                → Partial j (lid' false  {!!} ≡ lid' true {!!})
-- --                                → Partial (i ∨ ~ i ∨ j) (NBoundary m)
-- -- NBoundaryω-finishTy m j (suc n) = {!!}
-- --  -- ∀ iₖ → NBoundaryω-finishTy A a (j ∨ iₖ ∨ (~ iₖ)) n 

-- -- NBoundaryω-finish : ∀ {ℓ} → (A : Type ℓ) → (a : A) → ∀ n
-- --                     → {!!}
-- -- NBoundaryω-finish A a = {!PartialP!}



-- -- NBoundaryω-A4 : ∀ {ℓ} → (A : Type ℓ) → (a : A)
-- --                     → Boundaryω A 4
-- -- NBoundaryω-A4 A a = {!NBoundaryω-finish A a 3 !}

-- -- NBoundaryω-A : ∀ {ℓ} → (A : Type ℓ) → (a : A) → ∀ n
-- --                     → Boundaryω A n
-- -- NBoundaryω-A A a = {!!}

-- -- -- NBoundaryω-↓ : ∀ {ℓ} → {A : Type ℓ} → (j : I) → Partial j A → (n : ℕ) → (k : ℕ)
-- -- --                    →  Partialⁿ A (k + n) ( liftExpr k (boundaryExpr n)) 
-- -- -- NBoundaryω-↓ j x zero zero ()
-- -- -- NBoundaryω-↓ j x (suc n) zero = {!!}
-- -- -- NBoundaryω-↓ j x n (suc k) = {!!}

-- -- -- eatLast : ∀ {ℓ} → {A : Type ℓ} → (a : A) → (n : ℕ) → {!!}
-- -- -- eatLast = {!!}

-- -- -- -- NBoundaryω-finish : ∀ n
-- -- -- --                     → InsideOfω {n = suc n}
-- -- -- --                          (Partialⁿ-const (NCube (suc n)) n (boundaryExpr n) ({!nCubeω n!} ))
-- -- -- --                     → Boundaryω (NBoundary (suc n)) (suc n)
-- -- -- -- NBoundaryω-finish zero x i = primPOr i (~ i) {!!} {!!}
-- -- -- -- NBoundaryω-finish (suc n) x i = {!!}



-- -- -- zzz : {!!}
-- -- -- zzz = {!NBoundaryω-test'!}

-- -- -- -- NBoundaryω : ∀ n → Boundaryω (NBoundary n) n

-- -- -- -- NBoundary-cyl : ∀ n → PartialPⁿ n (boundaryExpr n)
-- -- -- --                           (Partialⁿ-map {A = NBoundary n} {B = Type₀} {n = n} {e = (boundaryExpr n)}
-- -- -- --                             (λ x → lid' false (boundaryInj x) ≡ lid' true (boundaryInj x) )
-- -- -- --                             (NBoundaryω n))


-- -- -- -- sub₁ : ∀ n → Partialⁿ-Sub (NBoundary (suc (suc n))) (suc (suc n))
-- -- -- --              (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (λ _ → boundaryExpr (suc n))
-- -- -- --                (NBoundaryω-intersection (suc n))


-- -- -- -- sub₂ : ∀ n → Partialⁿ-Sub (NBoundary (suc (suc n))) (suc (suc n))
-- -- -- --                (λ _ → boundaryExpr (suc n)) (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
-- -- -- --                (⊂→⊂' {n = suc (suc n)}
-- -- -- --                 ((λ _ → boundaryExpr (suc n)) ∧ⁿ
-- -- -- --                  (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr))
-- -- -- --                 ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ
-- -- -- --                  (λ _ → boundaryExpr (suc n)))
-- -- -- --                 (∧-comm {n = suc (suc n)} (λ _ → boundaryExpr (suc n))
-- -- -- --                  (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr))
-- -- -- --                 (NBoundaryω-intersection (suc n)))


-- -- -- -- -- hhEnds : ∀ n → ∀ i i₁
-- -- -- -- --           →  Partialⁿ (NBoundary (suc n)) n
-- -- -- -- --              (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ boundaryExpr (suc n) i₁)
-- -- -- -- -- hhEnds n i i₁ = {!!}

-- -- -- -- NBoundaryω zero ()
-- -- -- -- NBoundaryω (suc zero) i = primPOr i (~ i) (λ _ → lid false []) λ _ → lid true []
-- -- -- -- NBoundaryω (suc (suc n)) =
-- -- -- --    Partial∨ⁿ (suc (suc n))
-- -- -- --      (λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr))
-- -- -- --      (λ _ → boundaryExpr (suc n))
-- -- -- --      (NBoundaryω-intersection (suc n))
-- -- -- --      (sub₁ n)
-- -- -- --      (sub₂ n)

-- -- -- -- sub₁ zero i i₁ ei=1 = inS {!!}
-- -- -- -- sub₁ (suc n) i i₁ = {!!}


-- -- -- -- sub₂ zero i i₁ ei=1 = {!!}
-- -- -- -- sub₂ (suc n) i i₁ = {!!}

-- -- -- -- -- NBoundaryωₖ zero zero ()
-- -- -- -- -- NBoundaryωₖ (suc zero) zero i = primPOr i (~ i) (λ _ → lid false []) λ _ → lid true []
-- -- -- -- -- NBoundaryωₖ (suc (suc n)) zero = {!!}
-- -- -- -- -- NBoundaryωₖ zero (suc k) _ = Partialⁿ-lift-i0 k
-- -- -- -- -- NBoundaryωₖ (suc n) (suc k) i = 
-- -- -- -- --   Partialⁿ-map 
-- -- -- -- --     {A = NBoundary (k + suc n)}
-- -- -- -- --     {B = (NBoundary (suc k + suc n))} {n = (k + suc n)}
-- -- -- -- --     (cyl'' (inside i)) (NBoundaryωₖ (suc n) k) 


-- -- -- -- NBoundary-cyl zero ()
-- -- -- -- NBoundary-cyl (suc zero) i = {!!}
-- -- -- -- NBoundary-cyl (suc (suc n)) i = {!!}

-- -- -- -- -- Goal: Partialⁿ {ℓ-zero} (NBoundary (suc k + suc n)) (k + suc n)
-- -- -- -- --       (liftExpr {suc n} (suc k) (boundaryExpr (suc n)) i)



-- -- -- -- -- nCubeBoundaryω2' : Partialⁿ (NCube 2) 2 (boundaryExpr 2) 
-- -- -- -- -- nCubeBoundaryω2' i₀ i₁ =
-- -- -- -- --   λ {
-- -- -- -- --       (i₀ = i0) →  inside i₀ ∷ inside i₁ ∷ []
-- -- -- -- --     ; (i₀ = i1) →  inside i₀ ∷ inside i₁ ∷ []
-- -- -- -- --     ; (i₁ = i0) →  inside i₀ ∷ inside i₁ ∷ []
-- -- -- -- --     ; (i₁ = i1) → inside i₀ ∷ inside i₁ ∷ []
-- -- -- -- --    }

-- -- -- -- -- nCubeBoundaryω2'' : Partialⁿ (NCube 2) 2 (boundaryExpr 2) 
-- -- -- -- -- nCubeBoundaryω2'' i₀ i₁ = 
-- -- -- -- --   primPOr (i₀ ∨ ~ i₀) (i₁ ∨ ~ i₁)
-- -- -- -- --     (primPOr i₀ (~ i₀) (λ _ →  inside i₀ ∷ inside i₁ ∷ []) λ _ →  inside i₀ ∷ inside i₁ ∷ [])
-- -- -- -- --     (primPOr i₁ (~ i₁) (λ _ →  inside i₀ ∷ inside i₁ ∷ []) λ _ →  inside i₀ ∷ inside i₁ ∷ [])

-- -- -- -- -- nCubeBoundaryω2''' : Partialⁿ (NCube 2) 2 (boundaryExpr 2) 
-- -- -- -- -- nCubeBoundaryω2''' i₀ i₁ = 
-- -- -- -- --   primPOr i₀ (~ i₀ ∨ i₁ ∨ ~ i₁) (λ _ → inside i₀ ∷ inside i₁ ∷ [])
-- -- -- -- --     (primPOr (~ i₀) (i₁ ∨ ~ i₁) ((λ _ → inside i₀ ∷ inside i₁ ∷ []))
-- -- -- -- --       (primPOr i₁ (~ i₁) ((λ _ → inside i₀ ∷ inside i₁ ∷ [])) (λ _ → inside i₀ ∷ inside i₁ ∷ [])))


-- -- -- -- -- pOrⁿ :  ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n → (a : NCube n → A)
-- -- -- -- --         → Partialⁿ A n (⋁expr n)
-- -- -- -- -- pOrⁿ zero a ()
-- -- -- -- -- pOrⁿ (suc zero) a i = {!!}
-- -- -- -- -- pOrⁿ (suc (suc n)) a = {!!}

-- -- -- -- -- test-POr1 : Partialⁿ (NCube 4) 4 (⋁expr 4)
-- -- -- -- -- test-POr1 i₀ i₁ i₂ i₃ = 
-- -- -- -- --   primPOr i₀ (i₁ ∨ i₂ ∨ i₃) {!!}
-- -- -- -- --     (primPOr i₁ (i₂ ∨ i₃) {!!}
-- -- -- -- --        (primPOr i₂ i₃ {!!}
-- -- -- -- --           {!i₃!}))


-- -- -- -- -- nCubeBoundaryω : ∀ n → NCubeBoundaryω n

-- -- -- -- -- insideOk : ∀ n → InsideOfω {n = n} (nCubeBoundaryω n)

-- -- -- -- -- nCubeBoundaryω zero ()
-- -- -- -- -- nCubeBoundaryω (suc zero) i = primPOr i (~ i) (λ _ → end true ∷ []) λ _ → end false ∷ []
-- -- -- -- -- nCubeBoundaryω (suc (suc n)) i =
-- -- -- -- --    {!!} 

-- -- -- -- -- insideOk = {!!}


-- -- -- -- -- -- λ _ →  inside i₀ ∷ inside i₁ ∷ [])
-- -- -- -- -- --     --(primPOr i₁ (~ i₁) (λ _ →  inside i₀ ∷ inside i₁ ∷ []) λ _ →  inside i₀ ∷ inside i₁ ∷ [])



-- -- -- -- -- -- problem-with-nCubeBoundaryω : (i₀ i₁ : I) → (x : IsOne (boundaryExpr 2 i₀ i₁) )
-- -- -- -- -- --                 →  nCubeBoundaryω2'' i₀ i₁ x ≡ nCubeBoundaryω' 2  i₀ i₁ x
-- -- -- -- -- -- problem-with-nCubeBoundaryω i₀ i₁ x = {!refl!} -- refl do not typecheck here

-- -- -- -- -- -- problem-with-nCubeBoundaryω' : (i₀ i₁ : I) → (x : IsOne (boundaryExpr 2 i₀ i₁) )
-- -- -- -- -- --                 →  nCubeBoundaryω2' i₀ i₁ x ≡ nCubeBoundaryω2''' i₀ i₁ x
-- -- -- -- -- -- problem-with-nCubeBoundaryω' i₀ i₁ x = {!refl!} -- refl do not typecheck here

-- -- -- -- -- -- test-nCubeBoundaryω' : (i₀ i₁ : I) → (x : IsOne (boundaryExpr 2 i₀ i₁) )
-- -- -- -- -- --                 →  nCubeBoundaryω2' i₀ i₁ x ≡ nCubeBoundaryω' 2 i₀ i₁ x
-- -- -- -- -- -- test-nCubeBoundaryω' i₀ i₁ x = {!nCubeBoundaryω' 2  !} 







-- -- -- -- -- -- nCubeBoundaryω : ∀ n → NCubeBoundaryω n

-- -- -- -- -- -- insideOk : ∀ n → InsideOfω {n = n} (nCubeBoundaryω n)

-- -- -- -- -- -- Partialⁿ∨-Ends :    ∀ n
-- -- -- -- -- --                    → ∀ i → ∀ j
-- -- -- -- -- --                    → Partialⁿ (NCube (suc n)) (suc n)
-- -- -- -- -- --                          ((([ i ]Iexpr) ∨ⁿ ([ ~ i ]Iexpr))
-- -- -- -- -- --                                ∨ⁿ j)
-- -- -- -- -- -- Partialⁿ∨-Ends zero i j = {!!}
-- -- -- -- -- -- Partialⁿ∨-Ends (suc n) i j = {!!}

-- -- -- -- -- -- test1 : ∀ (i : I) → Partial (i ∨ ~ i) Interval'
-- -- -- -- -- -- test1 i = primPOr i (~ i) {λ _ → (Interval')} (λ _ → inside i) (λ _ → inside i)

-- -- -- -- -- -- test2 = {!!}


-- -- -- -- -- -- nCubeBoundaryω zero ()
-- -- -- -- -- -- nCubeBoundaryω (suc zero) i = primPOr i (~ i) (λ _ → end true ∷ []) λ _ → end false ∷ []
-- -- -- -- -- -- nCubeBoundaryω (suc (suc n)) i =
-- -- -- -- -- --   let w : {!!}
-- -- -- -- -- --       w = {!!}
-- -- -- -- -- --   in {!!}
-- -- -- -- -- --      -- Partialⁿ∨-Ends (suc n) i (boundaryExpr (suc n))
-- -- -- -- -- --      -- ? ? ? 

-- -- -- -- -- -- insideOk zero = inS []
-- -- -- -- -- -- insideOk (suc zero) i = inS (inside i ∷ [])
-- -- -- -- -- -- insideOk (suc (suc n)) = {!!}








-- -- -- -- -- -- sq-help : ∀ {n} → (bd : NBoundary (suc n))
-- -- -- -- -- --           → Square {A = NBoundary (suc (suc (suc n)))}
-- -- -- -- -- --               (λ i → lid false (boundaryInj (cyl bd i)))
-- -- -- -- -- --               (λ i → lid true (boundaryInj (cyl bd i)))
-- -- -- -- -- --               (λ i → cyl (lid false (boundaryInj bd)) i)
-- -- -- -- -- --               λ i → cyl (lid true (boundaryInj bd)) i
-- -- -- -- -- -- sq-help bd i i₁ = cyl' (cyl' bd i₁) i

-- -- -- -- -- -- sq-Cu-help : ∀ n → (b : Bool) → C→ (NBoundary (suc n)) n 
-- -- -- -- -- -- sq-Cu-help zero b _ = lid' b []
-- -- -- -- -- -- sq-Cu-help (suc n) b i = C→map {n = n} (cyl'' (inside i)) (sq-Cu-help n b)

-- -- -- -- -- -- Cu-help : ∀ n → C→ (NBoundary n) n → C→ (NBoundary (suc n)) (suc n) 
-- -- -- -- -- -- Cu-help zero x x₁ = ⊥-recω (x 1=1)
-- -- -- -- -- -- Cu-help (suc n) x i = C→map {n = suc n} (cyl'' (inside i)) x

-- -- -- -- -- -- nCubeBoundaryω


-- -- -- -- -- ------------




-- -- -- -- -- -- --------------------------




-- -- -- -- -- -- PartialCuTy : ∀ n → (e : C→I n) → Typeω
-- -- -- -- -- -- PartialCuTy n cu = {!!}

-- -- -- -- -- -- ppp∨Ty : ∀ n → NCube n → Typeω
-- -- -- -- -- -- ppp∨Ty n cu = {!  !}

-- -- -- -- -- -- -------------------------

-- -- -- -- -- -- Face-lem :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- --             → ∀ k → ∀ b → ∀ cu
-- -- -- -- -- --             → Σ[ x ∈ NBoundary (suc n) ] faceMap k b cu ≡ boundaryInj x            
-- -- -- -- -- -- Face-lem = {!!}


-- -- -- -- -- -- Partialⁿ-NBoundary-comp :
-- -- -- -- -- --            ∀ n
-- -- -- -- -- --            → Partialⁿ (NBoundary n) n (boundaryExpr n)
-- -- -- -- -- --            → {!!}
-- -- -- -- -- -- Partialⁿ-NBoundary-comp n pa =
-- -- -- -- -- --   {! !}

-- -- -- -- -- -- Partialⁿ-NBoundary-step : ∀ n →
-- -- -- -- -- --                              Partialⁿ (NBoundary n) n (boundaryExpr n)

-- -- -- -- -- --                             → Partialⁿ (NBoundary (suc n)) (suc n) (boundaryExpr (suc n))
-- -- -- -- -- -- Partialⁿ-NBoundary-step zero x i = {!!}
-- -- -- -- -- -- Partialⁿ-NBoundary-step (suc n') x i =
-- -- -- -- -- --   let n = suc n'
-- -- -- -- -- --   in
-- -- -- -- -- --    Partialⁿ-const (NBoundary (suc n)) n (boundaryExpr (suc n) i)
-- -- -- -- -- --     (C→elim {n = n} {A = (NBoundary (suc n))}
-- -- -- -- -- --       λ x₁ →  ((λ j → cyl (lid false {!!}) (i ∧ j))
-- -- -- -- -- --        ∙∙ (λ i₁ → cyl (cyl {!!} i₁) i) ∙∙
-- -- -- -- -- --        (λ j → cyl (lid true {!!}) (i ∨ j))) i)
    

-- -- -- -- -- -- Partialⁿ-NBoundary : ∀ n → Partialⁿ (NBoundary n) n (boundaryExpr n)
-- -- -- -- -- -- Partialⁿ-NBoundary zero ()
-- -- -- -- -- -- Partialⁿ-NBoundary 6 = {!!}
-- -- -- -- -- -- Partialⁿ-NBoundary (suc n) = {!!}








-- -- -- -- -- -- NBoundary→ω : (n : ℕ) → (NBoundary n) → I → NCubeBoundaryω (suc n)
-- -- -- -- -- -- NBoundary→ω = {!!}
 

-- -- -- -- -- -- Partialⁿ-NBoundary : ∀ n → Partialⁿ (NBoundary n) n (boundaryExpr n)


-- -- -- -- -- -- Boundary→ω : ∀ {ℓ} → {A : Type ℓ} → (n : ℕ)
-- -- -- -- -- --         → (NBoundary n → A)
-- -- -- -- -- --         → Boundaryω A n
-- -- -- -- -- -- Boundary→ω n bd = Partialⁿ-map {n = n} bd (Partialⁿ-NBoundary n)

-- -- -- -- -- -- Partialⁿ-NBoundary = {!!}










-- -- -- -- -- -- NBoundary-intersec : ∀ n → ∀ i j → Partialⁿ (NBoundary (suc (suc n))) n
-- -- -- -- -- --                                      (([_]Iexpr n i ∨ⁿ [_]Iexpr n (~ i))
-- -- -- -- -- --                                        ∧ⁿ boundaryExpr (suc n) j)
-- -- -- -- -- -- NBoundary-intersec zero i j =
-- -- -- -- -- --   λ {
-- -- -- -- -- --        (i = i1)(j = i0) → lid true (inside j ∷ [])
-- -- -- -- -- --    ;   (i = i1)(j = i1) → lid true (inside j ∷ [])
-- -- -- -- -- --    ;   (i = i0)(j = i0) → lid false (inside j ∷ [])
-- -- -- -- -- --    ;   (i = i0)(j = i1) → lid false (inside j ∷ [])
-- -- -- -- -- --     }
-- -- -- -- -- -- NBoundary-intersec (suc n) i j i' =
-- -- -- -- -- --  let z = NBoundary-intersec n i i'
-- -- -- -- -- --    in {! !}

-- -- -- -- -- -- 


-- -- -- -- -- -- Partialⁿ-NBoundary zero ()
-- -- -- -- -- -- Partialⁿ-NBoundary (suc zero) i = λ { (i = i0) → lid false [] ; (i = i1) → lid true []  }
-- -- -- -- -- -- -- Partialⁿ-NBoundary (suc (suc zero)) i i₁ = {!!}
-- -- -- -- -- -- Partialⁿ-NBoundary (suc (suc n)) i i₁ =
-- -- -- -- -- --    -- let
-- -- -- -- -- --    --     l :  ∀ n → {!!}
-- -- -- -- -- --    --     l = {!!}

-- -- -- -- -- --    -- in
-- -- -- -- -- --     Partial∨ⁿ n
-- -- -- -- -- --       (([_]Iexpr i ∨ⁿ [_]Iexpr (~ i)))
-- -- -- -- -- --       (boundaryExpr (suc n) i₁)
-- -- -- -- -- --       (NBoundary-intersec n i i₁)
-- -- -- -- -- --       {!!}
-- -- -- -- -- --       {!!} 
-- -- -- -- -- --    -- let z : Partialⁿ (NBoundary (suc (suc n))) (suc (suc n))
-- -- -- -- -- --    --                   λ _  → boundaryExpr (suc n) 
-- -- -- -- -- --    --     z = λ i → Partialⁿ-map {n = suc n} (λ x → cyl' x i) (Partialⁿ-NBoundary (suc n))

-- -- -- -- -- --    --     zz : {!!}
-- -- -- -- -- --    --     zz = {!!}
       
-- -- -- -- -- --    -- in 
-- -- -- -- -- --    --   Partialⁿ-boundaryExpr n i j
-- -- -- -- -- --    --      (C→elim {n = n} {A = NBoundary (suc (suc n))} (λ x → lid false (inside j ∷ x)))
-- -- -- -- -- --    --      (C→elim {n = n} {A = NBoundary (suc (suc n))} (λ x → lid true (inside j ∷ x)))
-- -- -- -- -- --    --      (pse n i j)




-- -- -- -- -- --    -- Partialⁿ-map {n = suc (suc n)}
-- -- -- -- -- --    --    (λ x → cyl'' (head x) {! tail x!})
-- -- -- -- -- --    --    (nCubeBoundaryω (suc (suc n)))
   
-- -- -- -- -- --      --(Partialⁿ-NBoundarySE n i i₁ (Partialⁿ-NBoundary (suc n)))

-- -- -- -- -- -- -- cyl {n = 1} {injX = boundaryInj {1}} (x i₁ j=1) i
-- -- -- -- -- -- -- Partialⁿ-NBoundarySE zero i i₁ x j=1 = {!!}
-- -- -- -- -- -- -- Partialⁿ-NBoundarySE (suc n) i i₁ x = {!!}




  





-- -- -- -- -- -- -- let z = {!ppp n !}
-- -- -- -- -- --  -- in {!!}
 
-- -- -- -- -- -- -- fromBoundaryω : ∀ n → Boundaryω A n →  



-- -- -- -- -- -- -- -- assembleBoundaryFromCubical : ∀ {ℓ} → {A : Type ℓ} → ∀ n
-- -- -- -- -- -- -- --                     → (end0 : NCube n → A)
-- -- -- -- -- -- -- --                     → (end1 : NCube n → A)
-- -- -- -- -- -- -- --                     → (end0 ∘ boundaryInj ≡ end1 ∘ boundaryInj) 
-- -- -- -- -- -- -- --                     → NBoundary (suc n) → A
-- -- -- -- -- -- -- -- assembleBoundaryFromCubical zero end0 end1 x (lid x₁ _) = caseBool end1 end0 x₁ _
-- -- -- -- -- -- -- -- assembleBoundaryFromCubical (suc n) end0 end1 x (lid x₁ x₂) = caseBool end1 end0 x₁ x₂
-- -- -- -- -- -- -- -- assembleBoundaryFromCubical (suc n) end0 end1 x (cyl x₁ i) = x i x₁

-- -- -- -- -- -- -- -- abfc : ∀ {ℓ} → {A : Type ℓ} → ∀ n →
-- -- -- -- -- -- -- --         Iso (Σ ((NCube n) → A) (λ end0 →
-- -- -- -- -- -- -- --              Σ ((NCube n) → A) λ end1 →
-- -- -- -- -- -- -- --              (end0 ∘ boundaryInj ≡ end1 ∘ boundaryInj) ))
-- -- -- -- -- -- -- --           (NBoundary (suc n) → A )
-- -- -- -- -- -- -- -- Iso.fun (abfc zero) x (lid false x₂) = fst x _
-- -- -- -- -- -- -- -- Iso.fun (abfc zero) x (lid true x₂) = fst (snd x) _
-- -- -- -- -- -- -- -- fst (Iso.inv (abfc zero) x) = (const (x (lid false _)))
-- -- -- -- -- -- -- -- fst (snd (Iso.inv (abfc zero) x)) = (const (x (lid true _)))
-- -- -- -- -- -- -- -- snd (snd (Iso.inv (abfc zero) x)) i ()
-- -- -- -- -- -- -- -- Iso.rightInv (abfc zero) b i (lid false x₁) = b (lid false _)
-- -- -- -- -- -- -- -- Iso.rightInv (abfc zero) b i (lid true x₁) = b (lid true _)
-- -- -- -- -- -- -- -- fst (Iso.leftInv (abfc {ℓ} {A} zero) (fst₁ , fst₂ , snd₁) i) x = fst₁ _
-- -- -- -- -- -- -- -- fst (snd (Iso.leftInv (abfc {ℓ} {A} zero) (fst₁ , fst₂ , snd₁) i)) = fst₂
-- -- -- -- -- -- -- -- snd (snd (Iso.leftInv (abfc {ℓ} {A} zero) (fst₁ , fst₂ , snd₁) i)) i₁ ()
-- -- -- -- -- -- -- -- Iso.fun (abfc (suc n)) x = assembleBoundaryFromCubical (suc n) (fst x) (fst (snd x)) (snd (snd x))
-- -- -- -- -- -- -- -- Iso.inv (abfc (suc n)) x = x ∘ (lid false) , (x ∘ (lid true) , λ i a → x (cyl a i))
-- -- -- -- -- -- -- -- Iso.rightInv (abfc (suc n)) b i (lid false x₁) =  b (lid false x₁)
-- -- -- -- -- -- -- -- Iso.rightInv (abfc (suc n)) b i (lid true x₁) =  b (lid true x₁)
-- -- -- -- -- -- -- -- Iso.rightInv (abfc (suc n)) b i (cyl x i₁) = b (cyl x i₁)
-- -- -- -- -- -- -- -- fst (Iso.leftInv (abfc {ℓ} {A} (suc n)) a i) = fst a
-- -- -- -- -- -- -- -- fst (snd (Iso.leftInv (abfc {ℓ} {A} (suc n)) a i)) = fst (snd a)
-- -- -- -- -- -- -- -- snd (snd (Iso.leftInv (abfc {ℓ} {A} (suc n)) a i)) = snd (snd a)



-- -- -- -- -- -- -- -- cubi=-retr : ∀ {ℓ} → (A : Type ℓ) →
-- -- -- -- -- -- -- --          ∀ n → retract {B = Σ (NBoundary n → A) (InsideOf)}
-- -- -- -- -- -- -- --              (λ x → (x ∘ boundaryInj {n}) , (insideOf x))
-- -- -- -- -- -- -- --              (toCubical ∘ snd)
-- -- -- -- -- -- -- -- cubi=-retr A zero a i = a 
-- -- -- -- -- -- -- -- cubi=-retr A (suc n) a i (end false , x₁) = cubi=-retr A n (a ∘ ( inside i0 ,_)) i x₁
-- -- -- -- -- -- -- -- cubi=-retr A (suc n) a i (end true , x₁) = cubi=-retr A n (a ∘ ( inside i1 ,_)) i x₁
-- -- -- -- -- -- -- -- cubi=-retr A (suc n) a i (inside i₁ , x₁) = cubi=-retr A n (a ∘ ( inside i₁ ,_)) i x₁

-- -- -- -- -- -- -- -- cubi=-sec : ∀ {ℓ} → (A : Type ℓ) →
-- -- -- -- -- -- -- --          ∀ n → section {B = Σ (NBoundary (suc n) → A) (InsideOf)}
-- -- -- -- -- -- -- --              (λ x → (x ∘ boundaryInj {(suc n)}) , (insideOf x))
-- -- -- -- -- -- -- --              (λ x → toCubical {bd = fst x } (snd x))


-- -- -- -- -- -- -- -- cubi=0 : ∀ {ℓ} → (A : Type ℓ) →
-- -- -- -- -- -- -- --           ∀ n → Iso (NCube n → A) (Σ (NBoundary n → A) (InsideOf))
-- -- -- -- -- -- -- -- cubi=0 A n = {!!}

-- -- -- -- -- -- -- -- cubi= : ∀ {ℓ} → (A : Type ℓ) →
-- -- -- -- -- -- -- --           ∀ n → Iso (NCube (suc n) → A) (Σ (NBoundary (suc n) → A) (InsideOf))
-- -- -- -- -- -- -- -- cubi= A n = iso
-- -- -- -- -- -- -- --             (λ x → (x ∘ boundaryInj) , (insideOf x))
-- -- -- -- -- -- -- --             (toCubical ∘ snd )
-- -- -- -- -- -- -- --             (cubi=-sec A n)
-- -- -- -- -- -- -- --             (cubi=-retr A (suc n))

-- -- -- -- -- -- -- -- cubiHE : ∀ {ℓ} → (A : Type ℓ) →
-- -- -- -- -- -- -- --           ∀ n → HAEquiv (NCube (suc n) → A) (Σ (NBoundary (suc n) → A) (InsideOf))
-- -- -- -- -- -- -- -- cubiHE A n = iso→HAEquiv (cubi= A n)

-- -- -- -- -- -- -- -- cubi=-sec A zero b = {!!}

-- -- -- -- -- -- -- -- -- cubi=-sec A (suc n) b = {!!}

-- -- -- -- -- -- -- -- cubi=-sec {ℓ} A (suc n) (bd , p) = zz
-- -- -- -- -- -- -- --   where


-- -- -- -- -- -- -- --   pp0 : _,_ {B = InsideOf} (toCubical {bd = λ x → bd (lid false (boundaryInj x))} (p i0) ∘ boundaryInj)
-- -- -- -- -- -- -- --          (insideOf (toCubical {bd = (λ x → bd (lid false (boundaryInj x)))} (p i0))) ≡
-- -- -- -- -- -- -- --           ((λ x → bd (lid false (boundaryInj x))) , p i0)
-- -- -- -- -- -- -- --   pp0 = cubi=-sec A n ((bd ∘ (lid false) ∘  boundaryInj) , p i0)

-- -- -- -- -- -- -- --   pp1 : (toCubical (p i1) ∘ boundaryInj ,
-- -- -- -- -- -- -- --          insideOf (toCubical {bd = (λ x → bd (lid true (boundaryInj x)))} (p i1))) ≡
-- -- -- -- -- -- -- --           ((λ x → bd (lid true (boundaryInj x))) , p i1)
-- -- -- -- -- -- -- --   pp1 = cubi=-sec A n ((bd ∘ (lid true) ∘  boundaryInj) , p i1)

-- -- -- -- -- -- -- --   ppI : (i : I) → (_,_ {B = InsideOf} (toCubical {bd = λ x → bd (cyl'' (inside i) x)} (p i) ∘ boundaryInj)
-- -- -- -- -- -- -- --                    (insideOf {A = A}  (toCubical {bd = (λ x → bd (cyl'' (inside i) x))} (p i)))) ≡
-- -- -- -- -- -- -- --                     ((λ x → bd (cyl'' (inside i) x)) , p i)
-- -- -- -- -- -- -- --   ppI i = cubi=-sec A n ((bd ∘ (cyl'' (inside i))) , p i)



-- -- -- -- -- -- -- --   open Iso


-- -- -- -- -- -- -- --   ssX00 : (cc : NCube n) →
-- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- --                 toCubical (insideOf (λ x → bd (lid false (inside i0 , x)))) cc)
-- -- -- -- -- -- -- --             (λ i → bd (lid false (inside i0 , cc)))
-- -- -- -- -- -- -- --             (λ i → cubi=-retr A n (λ x → bd (lid false (inside i0 , x))) i cc)
-- -- -- -- -- -- -- --             (λ i → fst
-- -- -- -- -- -- -- --                   (cubi=-sec A n ((λ x → bd (lid false (boundaryInj x))) ,
-- -- -- -- -- -- -- --                   (λ i₁ → insideOf (λ x₁ → bd (lid false (inside i₁ , x₁))))
-- -- -- -- -- -- -- --                   ) i)
-- -- -- -- -- -- -- --                   (lid false cc))
-- -- -- -- -- -- -- --   ssX00 cc i i₁ = {!!}

-- -- -- -- -- -- -- --   ssX01 : (cc : NCube n) →
-- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- --                 toCubical (insideOf (λ x → bd (lid false (inside i1 , x)))) cc)
-- -- -- -- -- -- -- --             (λ i → bd (lid false (inside i1 , cc)))
-- -- -- -- -- -- -- --             (λ i → cubi=-retr A n (λ x → bd (lid false (inside i1 , x))) i cc)
-- -- -- -- -- -- -- --             (λ i → fst
-- -- -- -- -- -- -- --                   (cubi=-sec A n ((λ x → bd (lid false (boundaryInj x))) ,
-- -- -- -- -- -- -- --                    λ i₁ → insideOf (λ x₁ → bd (lid false (inside i₁ , x₁)))
-- -- -- -- -- -- -- --                    ) i)
-- -- -- -- -- -- -- --                   (lid true cc))
-- -- -- -- -- -- -- --   ssX01 cc i i₁ = {!!}


-- -- -- -- -- -- -- --   ss0 : (cc : NCube n) →
-- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- --             (λ i → toCubical (p (i0) i) cc)
-- -- -- -- -- -- -- --             (λ i → bd (lid false (inside i , cc)))
-- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- --                 fst
-- -- -- -- -- -- -- --                 (cubi=-sec A n ((λ x → bd (lid false (boundaryInj x))) , p i0) i)
-- -- -- -- -- -- -- --                 (lid false cc))
-- -- -- -- -- -- -- --             λ i →
-- -- -- -- -- -- -- --                 fst
-- -- -- -- -- -- -- --                 (cubi=-sec A n ((λ x → bd (lid false (boundaryInj x))) , p i0) i)
-- -- -- -- -- -- -- --                 (lid true cc)
-- -- -- -- -- -- -- --   ss0 cc i i₁ =
-- -- -- -- -- -- -- --            hcomp {A = A}
-- -- -- -- -- -- -- --            ((λ k → λ {
-- -- -- -- -- -- -- --               (i = i0) → cubi=-retr A n (bd ∘ (lid false) ∘ ( (inside i₁) ,_)) i0 cc
-- -- -- -- -- -- -- --             ; (i = i1) → cubi=-retr A n (bd ∘ (lid false) ∘ ( (inside i₁) ,_)) i1 cc
-- -- -- -- -- -- -- --             ; (i₁ = i0) → ssX00 cc i k
-- -- -- -- -- -- -- --             ; (i₁ = i1) → ssX01 cc i k
-- -- -- -- -- -- -- --            }))
-- -- -- -- -- -- -- --            (cubi=-retr A n (bd ∘ (lid false) ∘ ( (inside i₁) ,_)) i cc)
 


-- -- -- -- -- -- -- --   ssX10 : (cc : NCube n) →
-- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- --                 toCubical (insideOf (λ x → bd (lid true (inside i0 , x)))) cc)
-- -- -- -- -- -- -- --             (λ i → bd (lid true (inside i0 , cc)))
-- -- -- -- -- -- -- --             (λ i → cubi=-retr A n (λ x → bd (lid true (inside i0 , x))) i cc)
-- -- -- -- -- -- -- --             (λ i → fst
-- -- -- -- -- -- -- --                   (cubi=-sec A n ((λ x → bd (lid true (boundaryInj x))) , p i1) i)
-- -- -- -- -- -- -- --                   (lid false cc))
-- -- -- -- -- -- -- --   ssX10 cc i i₁ = {!!}

-- -- -- -- -- -- -- --   ssX11 : (cc : NCube n) →
-- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- --                 toCubical (insideOf (λ x → bd (lid true (inside i1 , x)))) cc)
-- -- -- -- -- -- -- --             (λ i → bd (lid true (inside i1 , cc)))
-- -- -- -- -- -- -- --             (λ i → cubi=-retr A n (λ x → bd (lid true (inside i1 , x))) i cc)
-- -- -- -- -- -- -- --             (λ i → fst
-- -- -- -- -- -- -- --                   (cubi=-sec A n ((λ x → bd (lid true (boundaryInj x))) , p i1) i)
-- -- -- -- -- -- -- --                   (lid true cc))
-- -- -- -- -- -- -- --   ssX11 cc i i₁ = {!!}


-- -- -- -- -- -- -- --   ss1 : (cc : NCube n) →
-- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- --             (λ i → toCubical (p (i1) i) cc)
-- -- -- -- -- -- -- --             (λ i → bd (lid true (inside i , cc)))
-- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- --                 fst
-- -- -- -- -- -- -- --                 (cubi=-sec A n ((λ x → bd (lid true (boundaryInj x))) , p i1) i)
-- -- -- -- -- -- -- --                 (lid false cc))
-- -- -- -- -- -- -- --             λ i →
-- -- -- -- -- -- -- --                 fst
-- -- -- -- -- -- -- --                 (cubi=-sec A n ((λ x → bd (lid true (boundaryInj x))) , p i1) i)
-- -- -- -- -- -- -- --                 (lid true cc)
-- -- -- -- -- -- -- --   ss1 cc i i₁ =
-- -- -- -- -- -- -- --              hcomp {A = A}
-- -- -- -- -- -- -- --            ((λ k → λ {
-- -- -- -- -- -- -- --               (i = i0) → cubi=-retr A n (bd ∘ (lid true) ∘ ( (inside i₁) ,_)) i0 cc
-- -- -- -- -- -- -- --             ; (i = i1) → cubi=-retr A n (bd ∘ (lid true) ∘ ( (inside i₁) ,_)) i1 cc
-- -- -- -- -- -- -- --             ; (i₁ = i0) → ssX10 cc i k
-- -- -- -- -- -- -- --             ; (i₁ = i1) →  ssX11 cc i k
-- -- -- -- -- -- -- --            }))
-- -- -- -- -- -- -- --            (cubi=-retr A n (bd ∘ (lid true) ∘ ( (inside i₁) ,_)) i cc)

-- -- -- -- -- -- -- --   -- sss0 : (k i i₂ : I) → InsideOf (λ x → fst (ppI i0 i) (cyl'' (inside i₂) x))
-- -- -- -- -- -- -- --   -- sss0 k i i₂ = {!!}

-- -- -- -- -- -- -- --   -- sss1 : (k i i₂ : I) → InsideOf (λ x → fst (ppI i1 i) (cyl'' (inside i₂) x))
-- -- -- -- -- -- -- --   -- sss1 k i i₂ = {!!}

-- -- -- -- -- -- -- --   cucu : (cc : NBoundary n) → Cube
-- -- -- -- -- -- -- --          (λ i i₁ → toCubical (p i i₁) (boundaryInj cc))
-- -- -- -- -- -- -- --          (λ i i₁ → bd (cyl (cyl cc i₁) i))
-- -- -- -- -- -- -- --          (ss0 (boundaryInj cc))
-- -- -- -- -- -- -- --          (ss1 (boundaryInj cc))
-- -- -- -- -- -- -- --          (λ i i₁ → fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- --                                    (lid false (boundaryInj cc)))
-- -- -- -- -- -- -- --          λ i i₁ →  fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- --                                     (lid true (boundaryInj cc))
-- -- -- -- -- -- -- --   cucu cc i i₁ i₂ = 
-- -- -- -- -- -- -- --          hcomp {A = A}
-- -- -- -- -- -- -- --            ((λ k → λ {
-- -- -- -- -- -- -- --               (i = i0) →  toCubical (p i₁ i₂) (boundaryInj cc)
-- -- -- -- -- -- -- --             ; (i = i1) → bd (cyl (cyl cc i₂) i₁)
-- -- -- -- -- -- -- --             ; (i₂ = i0) → {!!}
-- -- -- -- -- -- -- --             ; (i₂ = i1) → {!!}
-- -- -- -- -- -- -- --            }))
-- -- -- -- -- -- -- --            ({!!})


-- -- -- -- -- -- -- -- -- i = i0 ⊢ toCubical (p i₁ i₂) (boundaryInj cc)
-- -- -- -- -- -- -- -- -- i = i1 ⊢ bd (cyl (cyl cc i₂) i₁)
-- -- -- -- -- -- -- -- -- i₁ = i0 ⊢ hcomp
-- -- -- -- -- -- -- -- --           (λ { k (i = i0)
-- -- -- -- -- -- -- -- --                  → cubi=-retr A n (λ x → bd (lid false (inside i₂ , x))) i0
-- -- -- -- -- -- -- -- --                    (boundaryInj cc)
-- -- -- -- -- -- -- -- --              ; k (i = i1)
-- -- -- -- -- -- -- -- --                  → cubi=-retr A n (λ x → bd (lid false (inside i₂ , x))) i1
-- -- -- -- -- -- -- -- --                    (boundaryInj cc)
-- -- -- -- -- -- -- -- --              ; k (i₂ = i0) → ssX00 (boundaryInj cc) i k
-- -- -- -- -- -- -- -- --              ; k (i₂ = i1) → ssX01 (boundaryInj cc) i k
-- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- --           (cubi=-retr A n (λ x → bd (lid false (inside i₂ , x))) i
-- -- -- -- -- -- -- -- --            (boundaryInj cc))
-- -- -- -- -- -- -- -- -- i₁ = i1 ⊢ hcomp
-- -- -- -- -- -- -- -- --           (λ { k (i = i0)
-- -- -- -- -- -- -- -- --                  → cubi=-retr A n (λ x → bd (lid true (inside i₂ , x))) i0
-- -- -- -- -- -- -- -- --                    (boundaryInj cc)
-- -- -- -- -- -- -- -- --              ; k (i = i1)
-- -- -- -- -- -- -- -- --                  → cubi=-retr A n (λ x → bd (lid true (inside i₂ , x))) i1
-- -- -- -- -- -- -- -- --                    (boundaryInj cc)
-- -- -- -- -- -- -- -- --              ; k (i₂ = i0) → ssX10 (boundaryInj cc) i k
-- -- -- -- -- -- -- -- --              ; k (i₂ = i1) → ssX11 (boundaryInj cc) i k
-- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- --           (cubi=-retr A n (λ x → bd (lid true (inside i₂ , x))) i
-- -- -- -- -- -- -- -- --            (boundaryInj cc))
-- -- -- -- -- -- -- -- -- i₂ = i0 ⊢ fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- -- --           (lid false (boundaryInj cc))
-- -- -- -- -- -- -- -- -- i₂ = i1 ⊢ fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- -- --           (lid true (boundaryInj cc))

-- -- -- -- -- -- -- --   -- Cucu : Cube
-- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- --   -- Cucu i i₁ i₂ = {!!}



-- -- -- -- -- -- -- --   zz : (toCubical {n = suc (suc n)} p ∘ boundaryInj
-- -- -- -- -- -- -- --         , insideOf {A = A} {n = suc (suc n)} (toCubical {bd = bd} p))
-- -- -- -- -- -- -- --         ≡ (bd , p)
-- -- -- -- -- -- -- --   fst (zz i) (lid false (end false , snd₁)) = fst (pp0 i) (lid false snd₁)
-- -- -- -- -- -- -- --   fst (zz i) (lid false (end true , snd₁)) = fst (pp0 i) (lid true snd₁)
-- -- -- -- -- -- -- --   fst (zz i) (lid false (inside i₁ , snd₁)) = ss0 snd₁ i i₁ 
-- -- -- -- -- -- -- --   fst (zz i) (lid true (end false , snd₁)) = fst (pp1 i) (lid false snd₁)
-- -- -- -- -- -- -- --   fst (zz i) (lid true (end true , snd₁)) =  fst (pp1 i) (lid true snd₁)
-- -- -- -- -- -- -- --   fst (zz i) (lid true (inside i₁ , snd₁)) = ss1 snd₁ i i₁ 
-- -- -- -- -- -- -- --   fst (zz i) (cyl (lid false x₁) i₁) = fst (ppI i₁ i) (lid false x₁)
-- -- -- -- -- -- -- --   fst (zz i) (cyl (lid true x₁) i₁) = fst (ppI i₁ i) (lid true x₁)
-- -- -- -- -- -- -- --   fst (zz i) (cyl (cyl x i₂) i₁) = cucu x i i₁ i₂
-- -- -- -- -- -- -- --   snd (zz i) i₁ i₂ = {!!}
 


-- -- -- -- -- -- -- --     -- hcomp {A = InsideOf (λ x → fst (ppI i₁ i) (cyl'' (inside i₂) x))}
-- -- -- -- -- -- -- --     --        ((λ k → λ {
-- -- -- -- -- -- -- --     --           (i = i0) → insideOf (λ x₁ → toCubical
-- -- -- -- -- -- -- --     --                       {bd = bd ∘ cyl'' (inside i₁) ∘ cyl'' (inside i₂)} (p i₁ i₂) x₁)
-- -- -- -- -- -- -- --     --         ; (i = i1) → p i₁ i₂
-- -- -- -- -- -- -- --     --         ; (i₁ = i0) → sss0 k i i₂ --ss0= k i i₂
-- -- -- -- -- -- -- --     --         ; (i₁ = i1) → sss1 k i i₂ --ss1= k i i₂
-- -- -- -- -- -- -- --     --         ; (i₂ = i0) → insideOf (λ x →
-- -- -- -- -- -- -- --     --                        fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- --     --                          (lid false x))
-- -- -- -- -- -- -- --     --         ; (i₂ = i1) → insideOf (λ x →
-- -- -- -- -- -- -- --     --                        fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- --     --                          (lid true x))
-- -- -- -- -- -- -- --     --        }))
-- -- -- -- -- -- -- --     --        (snd (ppI i₁ i) i₂)




-- -- -- -- -- -- -- --   -- zz : (toCubical {n = suc (suc n)} p ∘ boundaryInj
-- -- -- -- -- -- -- --   --       , insideOf {A = A} {n = suc (suc n)} (toCubical {bd = bd} p))
-- -- -- -- -- -- -- --   --       ≡ (bd , p)
-- -- -- -- -- -- -- --   -- fst (zz i) (lid false (fst₁ , snd₁)) = {!!}
-- -- -- -- -- -- -- --   -- fst (zz i) (lid true (fst₁ , snd₁)) = {!!}
-- -- -- -- -- -- -- --   -- fst (zz i) (cyl x i₁) = fst (ppI i₁ i) x
-- -- -- -- -- -- -- --   -- snd (zz i) i₁ = {!!}
  
-- -- -- -- -- -- -- -- -- i = i0 ⊢ insideOf (toCubical p) i₁
-- -- -- -- -- -- -- -- -- i = i1 ⊢ p i₁
-- -- -- -- -- -- -- -- -- i₁ = i0 ⊢ insideOf (λ x → fst (zz i) (lid false x))
-- -- -- -- -- -- -- -- -- i₁ = i1 ⊢ insideOf (λ x → fst (zz i) (lid true x))


-- -- -- -- -- -- -- -- -- -- -- another definition of n-path , inside Sn

-- -- -- -- -- -- -- -- -- -- Globeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n} → (S (-1+ n) → A) → Type ℓ

-- -- -- -- -- -- -- -- -- -- northGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
-- -- -- -- -- -- -- -- -- --                  → ∀ (bd : (S (-1+ (suc n)) → A))
-- -- -- -- -- -- -- -- -- --                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → north))

-- -- -- -- -- -- -- -- -- -- southGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
-- -- -- -- -- -- -- -- -- --                  → ∀ (bd : (S (-1+ (suc n)) → A))
-- -- -- -- -- -- -- -- -- --                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → south))
                 
-- -- -- -- -- -- -- -- -- -- Globeⁿ {A = A} {n = zero} bd = A 
-- -- -- -- -- -- -- -- -- -- Globeⁿ {A = A} {n = suc n} bd =
-- -- -- -- -- -- -- -- -- --              PathP
-- -- -- -- -- -- -- -- -- --              (λ i → Globeⁿ {n = n} ( bd ∘ (λ x → merid x i)))
-- -- -- -- -- -- -- -- -- --              (northGlobeⁿ {A = A} {n = n} bd)
-- -- -- -- -- -- -- -- -- --              (southGlobeⁿ {A = A} {n = n} bd)


-- -- -- -- -- -- -- -- -- -- north-south-const : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (a : A)
-- -- -- -- -- -- -- -- -- --                      →  (northGlobeⁿ {n = n} (λ _ → a))
-- -- -- -- -- -- -- -- -- --                         ≡ 
-- -- -- -- -- -- -- -- -- --                         (southGlobeⁿ {n = n} (λ _ → a))

-- -- -- -- -- -- -- -- -- -- northGlobeⁿ {n = zero} bd = bd north
-- -- -- -- -- -- -- -- -- -- northGlobeⁿ {ℓ} {A} {suc zero} bd _ = bd north
-- -- -- -- -- -- -- -- -- -- northGlobeⁿ {ℓ} {A} {suc (suc n)} bd = north-south-const (bd north)

-- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = zero} bd = bd south
-- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = suc zero} bd _ = bd south
-- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = suc (suc n)} bd = north-south-const (bd south)

-- -- -- -- -- -- -- -- -- -- north-south-const {n = zero} a = refl
-- -- -- -- -- -- -- -- -- -- north-south-const {n = suc zero} a = refl
-- -- -- -- -- -- -- -- -- -- north-south-const {n = suc (suc n)} a = refl




-- -- -- -- -- -- -- -- -- -- -- glob= : ∀ {ℓ} → (A : Type ℓ) → ∀ n
-- -- -- -- -- -- -- -- -- -- --         → Iso (A) (Σ (_) (Globeⁿ {A = A} {n = n} ))

-- -- -- -- -- -- -- -- -- -- -- fst (Iso.fun (glob= A _) x) = const x 
-- -- -- -- -- -- -- -- -- -- -- snd (Iso.fun (glob= A zero) x) = x
-- -- -- -- -- -- -- -- -- -- -- snd (Iso.fun (glob= A (suc n)) x) = north-south-const x
-- -- -- -- -- -- -- -- -- -- -- Iso.inv (glob= A zero) (fst₁ , snd₁) = snd₁
-- -- -- -- -- -- -- -- -- -- -- Iso.inv (glob= A (suc n)) (fst₁ , snd₁) = fst₁ north
-- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A zero) b i) ()
-- -- -- -- -- -- -- -- -- -- -- snd (Iso.rightInv (glob= A zero) b i) = snd b
-- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc n)) b i) north = fst b north
-- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc zero)) b i) south = snd b i
-- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc (suc n))) b i) south =
-- -- -- -- -- -- -- -- -- -- --   Iso.inv (glob= A _) ((λ x → fst b (merid x i)) , snd b i)  
-- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc (suc n))) b i) (merid north i₁) = fst b (merid north (i ∧ i₁))
-- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc (suc n))) b i) (merid south i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc (suc n))) b i) (merid (merid a i₂) i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- snd (Iso.rightInv (glob= A (suc zero)) b i) i₁ = {!!} --snd b (i ∧ i₁)
-- -- -- -- -- -- -- -- -- -- -- snd (Iso.rightInv (glob= A (suc (suc n))) b i) i₁ = ?

  
-- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (glob= A zero) a = refl
-- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (glob= A (suc n)) a = refl


-- -- -- -- -- -- -- -- -- --   --           (λ x → (x ∘ boundaryInj) , (insideOf x))
-- -- -- -- -- -- -- -- -- --   --           (toCubical ∘ snd)
-- -- -- -- -- -- -- -- -- --   --           (ri _) (li _)
-- -- -- -- -- -- -- -- -- --   -- where

-- -- -- -- -- -- -- -- -- --   -- li : ∀ n → retract {B = Σ (NBoundary n → A) (InsideOf)}
-- -- -- -- -- -- -- -- -- --   --            (λ x → (x ∘ boundaryInj {n}) , (insideOf x))
-- -- -- -- -- -- -- -- -- --   --            (toCubical ∘ snd)
-- -- -- -- -- -- -- -- -- --   -- li = ?


-- -- -- -- -- -- -- -- -- --   -- ri : ∀ n → section {B = Σ (NBoundary n → A) (InsideOf)}
-- -- -- -- -- -- -- -- -- --   --            (λ x → (x ∘ boundaryInj {n}) , (insideOf x))
-- -- -- -- -- -- -- -- -- --   --            (toCubical ∘ snd)
-- -- -- -- -- -- -- -- -- --   -- ri = ?




-- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S relates Paths inside of S and NBoundary 


-- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S₊ : ∀ {n} → NBoundary (suc n) ≡ S₊ n

-- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S₊ {zero} = NBoundary1-≡-Bool ∙ (ua Bool≃Susp⊥' ) 

-- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S₊ {suc n} = (isoToPath (lem) ) ∙ cong Susp (NBoundary-≡-S₊)
-- -- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- -- --   lem : Iso (NBoundary' {suc n} _) (Susp _)
-- -- -- -- -- -- -- -- -- -- --   Iso.fun (lem) (lid false x₁) = north
-- -- -- -- -- -- -- -- -- -- --   Iso.fun (lem) (lid true x₁) = south
-- -- -- -- -- -- -- -- -- -- --   Iso.fun (lem) (cyl x i) = merid x i
-- -- -- -- -- -- -- -- -- -- --   Iso.inv (lem) north = lid false (corner0)
-- -- -- -- -- -- -- -- -- -- --   Iso.inv (lem) south = lid true (corner1)
-- -- -- -- -- -- -- -- -- -- --   Iso.inv (lem) (merid x i) =   ((cong (lid false) (corner0-≡ (boundaryInj x)))
-- -- -- -- -- -- -- -- -- -- --                               ∙∙ (cyl x)
-- -- -- -- -- -- -- -- -- -- --                               ∙∙ (cong (lid true) (≡-corner1 (boundaryInj x)))) i

-- -- -- -- -- -- -- -- -- -- --   Iso.rightInv (lem) north = refl
-- -- -- -- -- -- -- -- -- -- --   Iso.rightInv (lem) south = refl
-- -- -- -- -- -- -- -- -- -- --   Iso.rightInv (lem) (merid x i₁) i =
          
-- -- -- -- -- -- -- -- -- -- --          doubleCompPath-filler
-- -- -- -- -- -- -- -- -- -- --         (λ _ → north)
-- -- -- -- -- -- -- -- -- -- --         (λ j → doubleCompPath-filler
-- -- -- -- -- -- -- -- -- -- --                 (λ i₂ → merid (transp (λ _ → NBoundary (suc n)) ((~ i₂) ∨ i) x) (i₂ ∧ j))
-- -- -- -- -- -- -- -- -- -- --                 (λ i₂ → merid (transp ((λ _ → NBoundary (suc n))) i x)  j )
-- -- -- -- -- -- -- -- -- -- --                 (λ i₂ → merid (transp (λ _ → NBoundary (suc n)) ((~ i₂) ∧ i) x) (i₂ ∨  j))
-- -- -- -- -- -- -- -- -- -- --                 (~ i) j )
-- -- -- -- -- -- -- -- -- -- --         (λ _ → south)
-- -- -- -- -- -- -- -- -- -- --         (~ i) i₁

-- -- -- -- -- -- -- -- -- -- --   Iso.leftInv (lem) (lid false x₁) = cong (lid false) (corner0-≡ _)
-- -- -- -- -- -- -- -- -- -- --   Iso.leftInv (lem) (lid true x₁) = sym (cong (lid true) (≡-corner1 _))
-- -- -- -- -- -- -- -- -- -- --   Iso.leftInv (lem) (cyl x i₁) i =
-- -- -- -- -- -- -- -- -- -- --       doubleCompPath-filler
-- -- -- -- -- -- -- -- -- -- --         (cong (lid false) (corner0-≡ (boundaryInj x)))
-- -- -- -- -- -- -- -- -- -- --         (cyl x)
-- -- -- -- -- -- -- -- -- -- --         (cong (lid true) (≡-corner1 (boundaryInj x)))
-- -- -- -- -- -- -- -- -- -- --         (~ i) i₁

-- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S :  ∀ {n} → NBoundary n ≡ S (-1+ n)
-- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S {zero} = refl
-- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S {suc n} = NBoundary-≡-S₊







-- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n
-- -- -- -- -- -- -- -- -- -- --                   → (Σ _ (InsideOf {A = A} {n})) ≡ (Σ _ (Globeⁿ {A = A} {n})) 
-- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ A zero = {!!}
-- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ A (suc zero) = {!!}
-- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ A (suc (suc n)) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ PathP {ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             PathP {ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- --             (λ i₂ → InsideOf {ℓ} {A} {n} (λ x₁ → x (cyl (cyl x₁ i₂) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- --             (insideOf {ℓ} {A} {n} (λ x₁ → x (cyl (lid false x₁) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- --             (insideOf {ℓ} {A} {n} (λ x₁ → x (cyl (lid true x₁) i₁))))
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             insideOf {ℓ} {A} {n} (λ x₁ → x (lid false (inside i₁ , x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             insideOf {ℓ} {A} {n} (λ x₁ → x (lid true (inside i₁ , x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ PathP {ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             PathP {ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- --             (λ i₂ → Globeⁿ {ℓ} {A} {n} (λ x₁ → x (merid (merid x₁ i₂) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- --             (northGlobeⁿ {ℓ} {A} {n} (λ x₁ → x (merid x₁ i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- --             (southGlobeⁿ {ℓ} {A} {n} (λ x₁ → x (merid x₁ i₁))))
-- -- -- -- -- -- -- -- -- -- -- -- --          (northGlobeⁿ {ℓ} {A} {suc n} x) (southGlobeⁿ {ℓ} {A} {suc n} x)



-- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ PathP
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             PathP (λ i₂ → InsideOf (λ x₁ → x (cyl (cyl x₁ i₂) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- --             (insideOf (λ x₁ → x (cyl (lid false x₁) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- --             (insideOf (λ x₁ → x (cyl (lid true x₁) i₁))))
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ → insideOf (λ x₁ → x (lid false (inside i₁ , x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ → insideOf (λ x₁ → x (lid true (inside i₁ , x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ PathP
-- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- --             PathP (λ i₂ → Globeⁿ (λ x₁ → x (merid (merid x₁ i₂) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- --             (northGlobeⁿ (λ x₁ → x (merid x₁ i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- --             (southGlobeⁿ (λ x₁ → x (merid x₁ i₁))))
-- -- -- -- -- -- -- -- -- -- -- -- --          (northGlobeⁿ x) (southGlobeⁿ x)






-- -- -- -- -- -- -- -- -- -- -- -- -- insideOf↓ : ∀ {ℓ} → ∀ {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- --                   → ∀ n → ∀ {k} → ∀ i'
-- -- -- -- -- -- -- -- -- -- -- -- --                   → (bd :  NCube (suc k) → A)
-- -- -- -- -- -- -- -- -- -- -- -- --                   → (InsideOfₘ n
-- -- -- -- -- -- -- -- -- -- -- -- --                           λ x₁ → bd (i' , (proj₂ (boundaryInj x₁)))) 
-- -- -- -- -- -- -- -- -- -- -- -- --                   → (InsideOfₘ (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- --                           λ x₁ → bd (i' , (boundaryInj x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- insideOf↓ n {k = k} (end b) bd x = x (Bool→I b)
-- -- -- -- -- -- -- -- -- -- -- -- -- insideOf↓ n {k = k} (inside i) bd x = x i


    

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Path of n dimensions

-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (NBoundary n → A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf {ℓ} {A = A} {n} = InsideOfₘ 0 {k = n} 


-- -- -- -- -- -- -- -- -- -- -- -- -- insideOf-faceⁿ : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- --         → (k : ℕ) → (s : Bool) 
-- -- -- -- -- -- -- -- -- -- -- -- --         → (bd : NBoundary (suc n) → A)
-- -- -- -- -- -- -- -- -- -- -- -- --         → InsideOf (bd ∘ (faceInj k s) ∘ boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- insideOf-faceⁿ {n = n} k s bd = insideOf↑ {n = 0} (bd ∘ (faceInj k s))


-- -- -- -- -- -- -- -- -- -- -- -- -- Cubical→InsideOf : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- --                   → (c : NCube n → A)
-- -- -- -- -- -- -- -- -- -- -- -- --                   → InsideOf (c ∘ boundaryInj)  
-- -- -- -- -- -- -- -- -- -- -- -- -- Cubical→InsideOf c =  insideOf↑ {n = 0} λ x₁ → c x₁ 




-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ→Cubical :
-- -- -- -- -- -- -- -- -- -- -- -- --        ∀ {ℓ} → {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- --       → ∀ {n} → ∀ {k}
-- -- -- -- -- -- -- -- -- -- -- -- --       → (bd : NBoundary k → A)          
-- -- -- -- -- -- -- -- -- -- -- -- --       → InsideOfₘ {A = _} n {k = k} bd
-- -- -- -- -- -- -- -- -- -- -- -- --       → NCube k → A
-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ→Cubical {n = n} {zero} _ x _ = x
-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ→Cubical {n = n} {suc k} _ x (end x₁ , x₂) =
-- -- -- -- -- -- -- -- -- -- -- -- --                                    InsideOfₘ→Cubical {n = 0} _ (x (Bool→I x₁)) x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ→Cubical {n = n} {suc k} _ x (inside i , x₂) =
-- -- -- -- -- -- -- -- -- -- -- -- --                                    InsideOfₘ→Cubical {n = 0} _ (x i) x₂



-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf→Cubical : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- --                   → {bd : NBoundary n → A}
-- -- -- -- -- -- -- -- -- -- -- -- --                   → InsideOf bd
-- -- -- -- -- -- -- -- -- -- -- -- --                   → NCube n → A
-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf→Cubical {n = zero} x x₁ = x
-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf→Cubical {A = A} {n = suc n} {bd} x x₁ = InsideOfₘ→Cubical (λ x₃ → bd x₃) x x₁
 

-- -- -- -- -- -- -- -- -- -- -- -- -- insideOfSlice : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- --                   → {bd : NBoundary (suc n) → A}
-- -- -- -- -- -- -- -- -- -- -- -- --                   → InsideOf bd
-- -- -- -- -- -- -- -- -- -- -- -- --                   → (i' : Interval')
-- -- -- -- -- -- -- -- -- -- -- -- --                   → InsideOf (bd ∘ (cyl'' i')) 
-- -- -- -- -- -- -- -- -- -- -- -- -- insideOfSlice x (end x₁) = x (Bool→I x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- insideOfSlice x (inside i) = x i

-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfEquationalₘ : ∀ {ℓ} → ∀ {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- --                       → ∀ {k}
-- -- -- -- -- -- -- -- -- -- -- -- --                       → (bd : NBoundary k → A)
-- -- -- -- -- -- -- -- -- -- -- -- --                       → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfEquationalₘ bd = Σ _ (bd isBoundaryOf_)


-- -- -- -- -- -- -- -- -- -- -- -- -- reflⁿ : ∀ {ℓ} → {A : Type ℓ} → ∀ n → (a : A) → InsideOf {n = n} (const a)
-- -- -- -- -- -- -- -- -- -- -- -- -- reflⁿ zero a = a
-- -- -- -- -- -- -- -- -- -- -- -- -- reflⁿ (suc n) a = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- nInside : ∀ n → InsideOf (boundaryInj {n})
-- -- -- -- -- -- -- -- -- -- -- -- -- nInside n = insideOf↑ {A = NCube n} {n = n} (idfun _)
















-- -- -- -- -- -- -- -- -- -- -- -- -- -- isBd : ∀ {n} → NCube n → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- isBd {n} x = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialTy : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- --               → NCube n → (NCube (suc n) →  A)
-- -- -- -- -- -- -- -- -- -- -- -- -- --               →  A 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialTy c x = iii (brd c) λ x₁ → x (x₁ , c)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialCu : (n : ℕ) → NCube n  → _×_ {ℓ-zero} {ℓ-zero} Interval' (NCube n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialCu n x = mkPartialTy x (idfun (NCube (suc n)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialCuTest : ∀ {ℓ} → {A : Type ℓ} → I → I → ((NCube 3 → A)) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialCuTest i₁ i₂ a = {!mkPartialTy (inside i₁ , inside i₂ , _) a!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- xxx : ∀ n → (c : NCube n) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- xxx = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- ---


-- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n → ∀ k 
-- -- -- -- -- -- -- -- -- -- -- -- -- --           → (c : Interval' → NBoundary (suc k) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- --           → InsideOfₘ n (c (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- --           → NCube (suc k) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all {ℓ} {A} n zero c x cu = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all {ℓ} {A} n (suc zero) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all {ℓ} {A} n (suc k') c x (i' , j' , cu) = hCC i' j'  --hCC

-- -- -- -- -- -- -- -- -- -- -- -- -- --    where
 
-- -- -- -- -- -- -- -- -- -- -- -- -- --    -- k' = suc k''
-- -- -- -- -- -- -- -- -- -- -- -- -- --    k = suc k'

-- -- -- -- -- -- -- -- -- -- -- -- -- --    hC : ∀ i → NCube (suc k') → A
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hC i = hcompⁿ-all
-- -- -- -- -- -- -- -- -- -- -- -- -- --           (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --           k' (λ x₁ x₂ → c x₁ (cyl x₂ i))
-- -- -- -- -- -- -- -- -- -- -- -- -- --           (x i)
          
          
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC : Interval' → Interval' → A   
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC (inside i) (inside j) = hcomp
-- -- -- -- -- -- -- -- -- -- -- -- -- --         ((λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- --             (i = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (i = i1) → {!c (inside l) ?!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (j = i1) → hC i (inside j , cu)
-- -- -- -- -- -- -- -- -- -- -- -- -- --           }))
-- -- -- -- -- -- -- -- -- -- -- -- -- --         {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC i' j' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --    hCub : ∀ i  → NCube (suc (suc k'')) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hCub i = InsideOfₘ→Cubical {n = suc n} {k = k} (λ x₂ → c (end true) (cyl x₂ i)) (hC i)
          
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhTest : (i : I) → (cu : NCube ((suc (suc k'')))) → (φ : I)
-- -- -- -- -- -- -- -- -- -- -- -- -- --               → A
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhTest i cu φ = hcomp {A  = A} (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         (i1 = i1) → hCub i cu --(hC i z) --hCub i z cu
-- -- -- -- -- -- -- -- -- -- -- -- -- --                          })
-- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((hCub i cu ))

-- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC : (i : I) → (cu : NCube ((suc (suc k'')))) → (φ : Interval')
-- -- -- -- -- -- -- -- -- -- -- -- -- --           →  A
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC i cu (end false) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- --                       hcomp {A  = A} (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- --                           (i = i0) → hCub i0 cu --c (inside (z ∧ φ)) (lid false cu) 
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         ; (i = i1) → hCub i1 cu --c (inside (z ∧ φ)) (lid true cu)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                           -- (i1 = i1) → hCub i cu --(hC i z) --hCub i z cu
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         })
-- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((hCub i cu ))
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC i cu (end true) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- --                       hcomp {A  = A} (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- --                           (i1 = i1) → hCub i cu --(hC i z) --hCub i z cu
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         })
-- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((hCub i cu ))
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC i cu (inside φ) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --                       hcomp {A  = A} (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- --                           -- (φ = i0) → hCub i cu
-- -- -- -- -- -- -- -- -- -- -- -- -- --                           (φ = i1) → hCub i cu --(hC i z) --hCub i z cu
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         ; (i = i0) → hCub i0 cu --c (inside (z ∧ φ)) (lid false cu) 
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         ; (i = i1) → hCub i1 cu --c (inside (z ∧ φ)) (lid true cu)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         })
-- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((hCub i cu ))

-- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC' :  (i : Interval') → (cu : NCube ((suc (suc k'')))) →  A
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC' (end false) c = hhhC i0 c (brd c)



-- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC' (end true) c = hhhC i1 c (brd c)


-- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC' (inside i) c =  hhhC i c (brd c)

-- -- -- -- -- -- -- -- -- -- -- -- -- --    -- hhC : Interval' → NCube (suc k) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- --    -- hhC (end b) (x , y) = hhhC (Bool→I b) y x
-- -- -- -- -- -- -- -- -- -- -- -- -- --    -- hhC (inside i) (x , y) = hhhC i y x

   
-- -- -- -- -- -- -- -- -- -- -- -- -- --    -- hCC' : PathP {!!} {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --    -- --InsideOfₘ (suc n) {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --    -- hCC' = insideOf↑ hhC

-- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC0 : InsideOfₘ n {k = suc (suc (suc k''))}
-- -- -- -- -- -- -- -- -- -- -- -- -- --             ((λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁)) ∘ boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC0 = insideOf↑ {n = n} {k = suc k} λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC1 : InsideOfₘ n {k = suc (suc (suc k''))}
-- -- -- -- -- -- -- -- -- -- -- -- -- --             ((λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁)) ∘ boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC1 = (insideOf↑ {n = n} {k = suc k} λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁))

-- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC : InsideOfₘ n {k = suc (suc (suc k''))} (c (end true))
-- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC i i₁ i₂ = {!hCC0 i0 i₁ i₂!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --    -- {!(Cubical→InsideOf (hhC (inside i)))!}  -- (Cubical→InsideOf (hhC (inside i)))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ (suc n) ((c (end true)) ∘ (lid b) ∘ boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hS : ∀ b → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hS b = hcompⁿ-all {!!} {!!} {!!} ( x (Bool→I b))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --insideOf↑ ((c (inside z)) ∘ lid b)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    h : InsideOfₘ (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ → c (inside z) (cyl'' (inside i) (cyl'' (inside i₁) x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    h = hcomp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (i = i0) → {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (i = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (i₁ = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (i₁ = i1) → {!x i i!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              λ _ → {!hC!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         -- hfill
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --  (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --     (i = i0) → {!hS false!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --   ; (i = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --   ; (i₁ = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --   ; (i₁ = i1) → {!x i i!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --   ; (z = i0) → x i i₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --  })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --  (inS ({!hC z!}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --  z
   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- zz : ∀ (i i₁ : I) → (j : I) → Set ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- zz i i₁ j = InsideOfₘ 2 {k'} ((c (inside j))  ∘ (cyl'' (inside i)) ∘ (cyl'' (inside i₁)))
     
   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- h0 : ∀ j → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- h0 j = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       ((hfillⁿ-all k' (λ x₁ x₂ → c x₁ (cyl x₂ i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --           (insideOfSlice {bd = c (end false)} x (inside i)) j)) i₁


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- h2 : InsideOfₘ (suc (suc 0))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --        ((c (inside z)) ∘ (cyl'' (inside i)) ∘  (cyl'' (inside i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- h2 =  hfill
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          (i₁ = i0) → {!h0!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --        ; (i₁ = i1) → {!h!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --        ; (i = i0) → {!h0 z  !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --        ; (i = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       (inS {! h0 !})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       z


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hfillⁿ-all : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → (c : Interval' → NBoundary (suc k) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → InsideOf (c (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → (z : I) → InsideOf (c (inside z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hfillⁿ-all {ℓ} {A} zero c x z i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        hfill
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (i = i0)  → c (inside l) (lid false _)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i1)  → c (inside l) (lid true _)         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (inS (x i )) z

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hfillⁿ-all {ℓ} {A} (suc zero) c x z i i₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       hfill
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (i₁ = i0) → c (inside l) (cyl (lid false _) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i₁ = i1) → c (inside l) (cyl (lid true _) i) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i0)  → c (inside l) (lid false (inside i₁ , _))  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i1)  → c (inside l) (lid true (inside i₁ , _))         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (inS (x i i₁)) z


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hfillⁿ-all {ℓ} {A} (suc (suc k'')) c x z i i₁ = h

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    k' = suc k''
         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    zz : ∀ (i i₁ : I) → (j : I) → Set ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    zz i i₁ j = InsideOfₘ 2 {k'} ((c (inside j))  ∘ (cyl'' (inside i)) ∘ (cyl'' (inside i₁)))
     

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    h : _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    h =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       let cl-i : (b : Bool) → (l : I)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → InsideOfₘ 2 {k'}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       ((c (inside l)) ∘ (lid b) ∘ ( (inside i₁) ,_) ∘ boundaryInj )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           cl-i b l =  insideOf↑ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          ((c (inside l)) ∘ (lid b) ∘ ( (inside i₁) ,_))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           cl-i₁ : (b : Bool) → (l : I)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → InsideOfₘ 2 {k'}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       ((c (inside l)) ∘ ( cyl'' (inside i)) ∘ (lid b) ∘ boundaryInj )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           cl-i₁ b l =  insideOf↑ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          ((c (inside l)) ∘ ( cyl'' (inside i) ) ∘ (lid b))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       in
    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fill (zz i i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (  (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (i₁ = i0) → cl-i₁ false l
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i₁ = i1) → cl-i₁ true l 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i0)  → cl-i false l  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i1)  → cl-i true l        
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           }))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (inS (x i i₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       z




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → (c : Interval' → NBoundary (suc k) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → InsideOf (c (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → InsideOf (c (end true))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all k c x = hfillⁿ-all k c x i1




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type : Cube
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (insideOf-faceⁿ 0 false boundaryInj) (insideOf-faceⁿ 0 true boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (insideOf-faceⁿ 1 false boundaryInj) (insideOf-faceⁿ 1 true boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (insideOf-faceⁿ 2 false boundaryInj) (insideOf-faceⁿ 2 true boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               InsideOf (boundaryInj {3})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type = refl


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-2-Type-holes : Square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     InsideOf (boundaryInj {2})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-2-Type-holes = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-holes : Cube _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     InsideOf (boundaryInj {3})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-holes = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-9-term :  nInside 9
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ≡ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (λ i i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                inside i , inside i₁ , inside i₂ ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                inside i₃ , inside i₄ , inside i₅ ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                inside i₆ , inside i₇ , inside i₈ ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-9-term = refl


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- testXX : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- testXX = {!hcompⁿ-all 2 (const (const tt)) (reflⁿ 3 tt)!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ (suc n) (λ x₁ → c (end true) (cyl x₁ i))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- comp  {!!} {!!} {!!} 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfEquationalₘ-Iso-InsideOfₘ :
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ∀ {ℓ} → ∀ {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → ∀ n → ∀ {k}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → (bd : NBoundary k → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → Iso (InsideOfEquationalₘ bd) (InsideOfₘ n bd)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) (fst₁ , snd₁) = fst₁ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) x) = const x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) x) i ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) b = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) a i) = const (fst a _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) a i) i₁ ()

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc zero} bd) (cu , bd=) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) (cu , bd=) i = ss i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ww* : ∀ i₁ → (x : NCube k) → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ww* i₁ x = cu (inside i₁ , x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss* : ∀ i₁ → InsideOfₘ (suc n) (λ x → cu (inside i₁ , boundaryInj x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss* i₁ = insideOf↑ {n = n} {k = k} (ww* i₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ww : ∀ i₁ → (x : NCube k) → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ww i₁ x = hcomp (λ i₂ → λ {                        
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (i₁ = i0) → bd= (~ i₂) (lid false x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       ; (i₁ = i1) → bd= (~ i₂) (lid true x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     }) (cu (inside i₁ , x))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss : ∀ i₁ → InsideOfₘ (suc n) (λ x → ww i₁ (boundaryInj x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss i₁ = insideOf↑ {n = n} {k = k} (ww i₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              qq : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              qq = {!ss i1!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss' : InsideOfₘ (suc n) (λ x → bd (cyl'' (inside i) x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss' = insideOf↑ {n = n} {k = k} ({!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ww : ∀ i → InsideOfₘ n {k = suc k} (λ x → bd= i0 (cyl x i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ww = λ i → Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} λ x → bd= i0 (cyl x i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  --          ( (λ x → cu (inside i , x)) , λ i₁ x → bd= i₁ (cyl x i)) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- zz : I → I → Type _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- zz i j = InsideOfₘ n (λ x → bd= j (cyl x i))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- sss : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- sss = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ss : ∀ i' → InsideOfₘ (suc n) (λ x₁ → _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ss i' = insideOf↓ n i' (λ x → {!!}) λ i → ww i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ss' : InsideOfₘ n {k = suc (suc k)} bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ss' = coe0→1 {!!} {!!}

             

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) = {!InsideOf→Cubical !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) x = fst x _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) x) _ = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) x) i ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) b = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) a i) x = fst a _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) a i) i₁ ()

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ {ℓ} {A} {n = n} {suc k} c bd) (fst₁ , snd₁) i = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {suc k} c bd) x = {!!}                    

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {suc k} c bd) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {suc k} c bd) = {!!}













-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- another definition of n-path , inside Sn

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Globeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n} → (S (-1+ n) → A) → Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → ∀ (bd : (S (-1+ (suc n)) → A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → north))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → ∀ (bd : (S (-1+ (suc n)) → A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → south))
                 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Globeⁿ {A = A} {n = zero} bd = A 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Globeⁿ {A = A} {n = suc n} bd =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (λ i → Globeⁿ {n = n} ( bd ∘ (λ x → merid x i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (northGlobeⁿ {A = A} {n = n} bd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (southGlobeⁿ {A = A} {n = n} bd)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (a : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      →  (northGlobeⁿ {n = n} (λ _ → a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         ≡ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (southGlobeⁿ {n = n} (λ _ → a))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ {n = zero} bd = bd north
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ {ℓ} {A} {suc zero} bd _ = bd north
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ {ℓ} {A} {suc (suc n)} bd = north-south-const (bd north)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = zero} bd = bd south
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = suc zero} bd _ = bd south
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = suc (suc n)} bd = north-south-const (bd south)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const {n = zero} a = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const {n = suc zero} a = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const {n = suc (suc n)} a = refl



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S relates Paths inside of S and NBoundary 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (λ i → (NBoundary-≡-S {n} i → A) → Type ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     InsideOf Globeⁿ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ A zero = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ {ℓ} A 1 i x =

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     x (coe0→i (λ j → NBoundary-≡-S {n = 1} j) i (lid false _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     x ((coe0→i (λ j → NBoundary-≡-S {n = 1} j) i (lid true _)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ {ℓ} A (suc (suc n)) i x = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}  
                  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     pred= : PathP (λ i₂ → (NBoundary-≡-S {n = suc n} i₂ → A) → Type ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 InsideOf
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 Globeⁿ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     pred= = InsideOf-≡-Globeⁿ {ℓ} A (suc n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ( coei→0 (λ x₁ → NBoundary-≡-S {n = suc n} x₁ → A) i λ x₁ → {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zzz :  ∀ jj → pred= i0 (λ x₁ → x (coe0→i (λ x₂ → NBoundary-≡-S {suc (suc n)} x₂) i (cyl x₁ jj)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ≡ pred= i1 (λ x₁ → x (coe1→i (λ x₂ → NBoundary-≡-S {suc (suc n)} x₂) i (merid x₁ jj)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zzz jj i = pred= i {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zzz' :   I → (xx : ∀ ii → _ → NBoundary-≡-S {n = suc (suc n)} i) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  PathP (λ x₁ → InsideOfₘ {n = suc zero} (inside x₁ , tt)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                           (λ x₂ x₃ → x (xx i0 (cyl x₃ x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (insideOfCubeₘ {n = zero} (λ x₁ x₂ → x (xx i0 (lid false x₂))) (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (insideOfCubeₘ {n = zero} (λ x₁ x₂ → x (xx i0 (lid true x₂))) (end true))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ≡ PathP (λ x₁ → Globeⁿ (λ x₂ → x (xx i1 (merid x₂ x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (northGlobeⁿ (λ x₁ → x (xx i1 x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (southGlobeⁿ (λ x₁ → x (xx i1 x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zzz' jj xx i = pred= i λ x₁ → x (xx i x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     qqq : (jj ii : I) → NBoundary-≡-S₊ ii → NBoundary-≡-S jj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     qqq = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ww : Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ww = PathP (λ x₁ → zzz' x₁ (qqq i) i) {!!} {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- qq0 : (j₀ : I) → NCube 1 → NBoundary (suc n) → NBoundary-≡-S {suc (suc n)} i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- -- 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- qq0 j₀ x x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    qqq1 : {!!} ≡ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    qqq1 = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- qq1 : (j₀ : I) → S (-1+ suc n) → NBoundary-≡-S {n = suc (suc n)} i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- qq1 j₀ z = transport qqq1 (merid z j₀)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    qqq1 : Susp (Susp (S (-1+ n))) ≡ NBoundary-≡-S {n = suc (suc n)} i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    qqq1 i' = {!!}
       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- -- qq1 j₀ x = fill1→i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --            (λ i₁ → NBoundary-≡-S {n = suc (suc n)} i₁)
               
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --            (λ i₁ → λ {                  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --                   (j₀ = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --                 ; (j₀ = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --                })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --           (inS {!!}) i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- ww : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- ww = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- pp : ∀ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        InsideOfₘ {k = suc n} (inside i₁ , tt) (λ x₁ → λ x₂ → x (qq0 i₁ x₁ x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        Globeⁿ (λ x₁ → x (qq1 i₁ x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- pp = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcomp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ { j (i = i0) → NBoundary' boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ; j (i = i1) → Susp (NBoundary-≡-S₊ j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (Agda.Builtin.Cubical.Glue.primGlue (Susp (NBoundary' boundaryInj))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ .x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ { (i = i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → NBoundary' boundaryInj ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    isoToEquiv (Cubical.HITs.NCube.Base.lem n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → Susp (NBoundary' boundaryInj) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    idEquiv (Susp (NBoundary' boundaryInj))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           _ .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ .x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ { (i = i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → NBoundary' boundaryInj ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    isoToEquiv (Cubical.HITs.NCube.Base.lem n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → Susp (NBoundary' boundaryInj) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    idEquiv (Susp (NBoundary' boundaryInj))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           _ .snd))






-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    pp :     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    pp = {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PathP (λ i₁ → Globeⁿ (λ x₁ → x (merid x₁ i₁))) (northGlobeⁿ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (southGlobeⁿ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   = ?0 (i = i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   : Set ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PathP (λ i₁ → InsideOfₘ (inside i₁ , tt) (λ x₁ x₂ → x (cyl x₂ i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (insideOfCubeₘ (λ x₁ x₂ → x (lid false x₂)) (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (insideOfCubeₘ (λ x₁ x₂ → x (lid true x₂)) (end true))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   = ?0 (i = i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   : Set ℓ



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- similar tests for arbitrary types

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical : ∀ {ℓ} → {A : Type ℓ} → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end0 : NCube n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end1 : NCube n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end0 ∘ boundaryInj ≡ end1 ∘ boundaryInj) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → NBoundary (suc n) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical zero end0 end1 x (lid x₁ _) = caseBool end1 end0 x₁ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical (suc n) end0 end1 x (lid x₁ x₂) = caseBool end1 end0 x₁ x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical (suc n) end0 end1 x (cyl x₁ i) = x i x₁



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- boundaryCase : ∀ {ℓ} → {A : Type ℓ} → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → {bd0 bd1 : NBoundary n → A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end0 : InsideOf bd0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end1 : InsideOf bd1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     →    InsideOf→Cubical end0 ∘ boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ≡ InsideOf→Cubical end1 ∘ boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → NBoundary (suc n) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- boundaryCase n end0 end1 cylinder x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        assembleBoundaryFromCubical n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (InsideOf→Cubical end0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (InsideOf→Cubical end1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cylinder) x


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- makeCubeBoundary :
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ∀ {ℓ} → {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     →  NBoundary 3 → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- makeCubeBoundary a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     assembleBoundary 2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         a₀₋₋ a₁₋₋
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         aa
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   aa :   InsideOf→Cubical {bd = makeSquareBoundary _ _ _ _} a₀₋₋ ∘ boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ≡ InsideOf→Cubical {bd = makeSquareBoundary _ _ _ _} a₁₋₋ ∘ boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   aa i (lid x x₁) = {!x!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   aa i (cyl x i₁) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTest :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (InsideOf (makeCubeBoundary  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTest a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTestHoles :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (bd : NBoundaryIn A 3) →   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (Cube _ _ _ _ _ _) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (InsideOf {A = A} {n = 3} bd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTestHoles bd = refl



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTest' :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (Cube {A = A} a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (InsideOf {A = A} {3} (makeCubeBoundary  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTest' a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl










-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ : ∀ {ℓ} → (A : Type ℓ) → ℕ → Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record BoundaryIn' {ℓ} {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (X : A → Type ℓ) : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    constructor bdi

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    coinductive

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {lid0Bd lid1Bd} : A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      cylIn : lid0Bd ≡ lid1Bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      lid0 : X lid0Bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      lid1 : X lid1Bd

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ins : Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ins = PathP (λ x → X (cylIn x)) lid0 lid1

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn : ∀ {ℓ} {A : Type ℓ} → ∀ {n} → Boundaryⁿ A n → Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ A zero = Lift Unit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ A (suc zero) = A × A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ A (suc (suc n)) = BoundaryIn' {A = Boundaryⁿ A (suc n)} (λ x → PPn x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --BoundaryIn' {A = Boundaryⁿ A n} (λ x → PPn x)
                                     

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- boundaryⁿ-Of = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn {A = A} {n = zero} x = A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn {A = A} {n = suc zero} x = proj₁ x ≡ proj₂ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn {A = A} {n = suc (suc n)} x = BoundaryIn'.ins x


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn-look : ∀ {ℓ} {A : Type ℓ} → ∀ {n} → ∀ {bd}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → PPn {A = A} {n} bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → NCube n → A



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make : ∀ {ℓ} → {A : Type ℓ} → {n : ℕ} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (NBoundary n → A) → Boundaryⁿ A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = zero} x = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = suc zero} x = (x (lid false _)) , (x (lid true _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = suc (suc zero)} x = bdi (λ i → Boundaryⁿ-make λ x₁ → x (cyl x₁ i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                         (λ i → x (lid false (inside i , _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                        (λ i → x (lid true (inside i , _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = suc (suc (suc n))} x = bdi ((λ i → Boundaryⁿ-make λ x₁ → x (cyl x₁ i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                             (λ i → Cubical→InsideOf (λ x₁ → {!!}) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                             λ i → {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look : ∀ {ℓ} → {A : Type ℓ} → {n : ℕ} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      Boundaryⁿ A n → NBoundary n → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = zero} x ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc zero} (x , _) (lid false _) = x 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc zero} (_ , x) (lid true _) = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc (suc n)} x (lid x₁ y) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc (suc n)} x (cyl x₁ i) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn-look {n = zero} x _ = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn-look {n = suc zero} x (xx , _) = Iapp x xx
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn-look {n = suc (suc n)} x (end x₁ , x₂) = PPn-look (x (Bool→I x₁)) x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn-look {n = suc (suc n)} x (inside i , x₂) = (PPn-look (x i)) x₂ 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- eeeww :  ∀ {ℓ} {A : Type ℓ} → ∀ {n} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            Iso (NBoundary n → A) (Boundaryⁿ A n) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lower (Iso.fun (eeeww {n = zero}) x) = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = zero}) x ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = zero}) (lift lower₁) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = zero}) a i ()

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (eeeww {n = suc zero}) x = (x (lid false _)) , (x (lid true _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc zero}) x (lid x₁ x₂) = caseBool (proj₂ x) (proj₁ x) x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = suc zero}) (x , x₁) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc zero}) a i (lid false x₁) = a (lid false tt)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc zero}) a i (lid true x₁) = a (lid true tt)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (eeeww {n = suc (suc zero)}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc (suc zero)}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = suc (suc zero)}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc (suc zero)}) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (eeeww {n = suc (suc (suc n))}) x = bdi {!!} {!!} {!!} {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc (suc (suc n))}) x (lid x₁ x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc (suc (suc n))}) x (cyl x₁ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = suc (suc (suc n))}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc (suc (suc n))}) = {!!}





-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-holes-PP : ∀ {ℓ} {A : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (bd : Boundaryⁿ A 3) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      Cube _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        PPn {n = 3} bd
                       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-holes-PP bd = refl


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-PP : 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ∀ {ℓ} → {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PPn {n = 3} ({!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-PP a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl






-- -- -- -- -- -- -- -- -- -- -- -- -- -- self∨ : I → I
-- -- -- -- -- -- -- -- -- -- -- -- -- -- self∨ x = x ∨ (~ x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- self∨' : Interval' → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- self∨' (end x) = end true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- self∨' (inside i) = inside (i ∨ ~ i)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- _∨'_ : Interval' → Interval' → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∨' end false = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∨' end true = end true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- end true ∨' _ = end true 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∨' inside i = inside i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- inside i ∨' end false = inside i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- inside i ∨' end true = end true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- _∨'_ (inside i) (inside i₁) = inside (i ∨ i₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- _∧'_ : Interval' → Interval' → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∧' end false = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∧' end true = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- end true ∧' end false = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- end true ∧' end true = end true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∧' inside i = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- end true ∧' inside i = inside i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- inside i ∧' end false = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- inside i ∧' end true = inside i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- _∧'_ (inside i) (inside i₁) = inside (i ∧ i₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- ⋁ : ∀ {n} → NCube n → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ⋁ {zero} x = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ⋁ {suc n} (z , x₁) = z ∨' ⋁ x₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼' : Interval' → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼' (end x) = end (not x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼' (inside i) = inside (~ i)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼'' : ∀ {n} → NCube n → NCube n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼'' {zero} tt = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼'' {suc n} (x , x₁) = ∼' x ,  (∼'' x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd : ∀ {n} → NCube n → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd x = (⋁ x) ∨' ⋁ (∼'' x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd : ∀ {n} → NCube n → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd {zero} tt = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd {suc n} (z , x₁) = ((∼' z) ∨' z) ∨' brd x₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- brd : ∀ {n} → NCube n → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- brd {zero} x = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- brd {suc n} (end x , x₁) = end true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- brd {suc n} (inside i , x₁) = (inside (self∨ i)) ∨' (brd x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- hcomp' : ∀ {ℓ} → {A : Type ℓ} → (i' : Interval') → (Interval' → A) → A 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- hcomp' (end false) x = hcomp (λ i → empty) (x (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- hcomp' (end true) x = x (end true)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- hcomp' (inside i) x = hcomp (λ j → λ {(i = i1) → x (inside j) }) (x (end false))