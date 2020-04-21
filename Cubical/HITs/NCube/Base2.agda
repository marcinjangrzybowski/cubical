{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.Base2 where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (elim to elimℕ)
open import Cubical.Data.Prod
open import Cubical.Data.List

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


data Interval' : Type₀ where
   end : Bool → Interval'
   inside : end false ≡ end true 



data NCube (n : ℕ) : Type₀ where
  nc : (ℕ → Interval') → NCube n 

ncF : ∀ {n} → NCube (n) → ℕ → Interval'
ncF (nc x) x₁ = x x₁

_,□_ : ∀ {n} → Interval' → NCube n → NCube (suc n)
_,□_ {n} x y = nc (h x (ncF y))
  where
    h : Interval' → (ℕ → Interval') → (ℕ → Interval') 
    h x _ zero = x
    h _ x₁ (suc x₂) = x₁ x₂


data NBoundary' {n} {X : Type₀} (injX : X → NCube (n)) : Type₀ where
   lid : Bool → NCube (n) → NBoundary' injX
   cyl : ∀ x → lid false (injX x) ≡ lid true (injX x)

NBoundary : ℕ → Type₀

boundaryMap : ∀ {n} → NBoundary n → NCube n


NBoundary zero = ⊥
NBoundary (suc n) = NBoundary' {n} (boundaryMap)

boundaryMap {suc n} (lid x x₁) = ((end x) ,□ x₁)
boundaryMap {suc n} (cyl x i) = (inside i) ,□ boundaryMap x

bundaryHead : ∀ {n} → NBoundary (suc n) →  Interval'
bundaryHead (lid x x₁) = end x
bundaryHead (cyl x i) = inside i



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

-- lid' : ∀ {n} → Bool  → NCube n → NBoundary (suc n) 
-- lid' = lid

-- boundaryEndMap : ∀ {n} → Bool → NBoundary n → NBoundary (suc n)
-- boundaryEndMap {n} x = lid x ∘ boundaryMap

-- cyl' : ∀ {n} → (bd : NBoundary (suc n)) →
--                           boundaryEndMap false bd ≡ boundaryEndMap true bd 
-- cyl' = cyl

-- cylEx : ∀ {n} → boundaryEndMap {n} false ≡ boundaryEndMap true 
-- cylEx i x = cyl x i

-- faceMap : ∀ {n}
--           → ℕ → Bool
--           → NCube n → NBoundary (suc n)  
-- faceMap {suc n} (suc k) s (end x₂ , x₃) = lid x₂ (boundaryMap (faceMap k s x₃))
-- faceMap {suc n} (suc k) s (inside i , x₃) = cyl (faceMap k s x₃) i
-- faceMap  _  = lid

isContr-Inrerval' : isContr Interval'
fst isContr-Inrerval' = end false
snd isContr-Inrerval' (end false) = refl
snd isContr-Inrerval' (end true) = inside
snd isContr-Inrerval' (inside i) j = inside (i ∧ j) 

isProp-Inrerval' = isContr→isProp isContr-Inrerval'

corner0 : ∀ {n} → NCube n
corner0 = nc (const (end false))

corner1 : ∀ {n} → NCube n
corner1 = nc (const (end true))


corner0Bd : ∀ {n} → NBoundary (suc n)
corner0Bd = lid false corner0

corner1Bd : ∀ {n} → NBoundary (suc n)
corner1Bd = lid true corner1

corner0-≡ : ∀ {n} → ∀ (a : NCube n) → _≡_ {A = NCube n} (corner0) a  
corner0-≡ (nc x) i = nc λ x₁ → isProp-Inrerval' (end false) (x x₁) i

≡-corner1 : ∀ {n} → ∀ (a : NCube n) → _≡_ {A = NCube n} a (corner1) 
≡-corner1 (nc x) i = nc λ x₁ → isProp-Inrerval' (x x₁) (end true)  i

-- corner0-≡-corner1 : ∀ {n} → _≡_ {A = NCube n}  corner0 corner1  
-- corner0-≡-corner1 {zero} = refl
-- corner0-≡-corner1 {suc n} i = (inside i) , corner0-≡-corner1 i

-- corner0Bd-≡-corner1Bd : ∀ {n} → corner0Bd {n = suc n} ≡ corner1Bd {n = suc n}
-- corner0Bd-≡-corner1Bd {n} i = ((λ i₁ → cyl (lid false (corner0-≡  corner0 i₁)) i₁)
--                              ∙ λ i₁ → lid true (inside i₁ , (corner0-≡-corner1 i₁))) i


Bool→I : Bool → I
Bool→I false = i0
Bool→I true = i1


isPropCube : ∀ {n} → isProp (NCube n)
isPropCube (nc x) (nc y) i = nc λ x₁ → isProp-Inrerval' (x x₁) (y x₁)  i



NBoundary1-≡-Bool : NBoundary 1 ≡ Bool
NBoundary1-≡-Bool = isoToPath h 
  where

  h : Iso (NBoundary 1) Bool
  Iso.fun h (lid x _) = x
  Iso.inv h x = lid x corner0
  Iso.rightInv h b = refl
  Iso.leftInv h (lid x x₁) i = lid x (isPropCube corner0 x₁ i)



-- Globeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n} → (S (-1+ n) → A) → Type ℓ

-- northGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
--                  → ∀ (bd : (S (-1+ (suc n)) → A))
--                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → north))

-- southGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
--                  → ∀ (bd : (S (-1+ (suc n)) → A))
--                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → south))
                 
-- Globeⁿ {A = A} {n = zero} bd = A 
-- Globeⁿ {A = A} {n = suc n} bd =
--              PathP
--              (λ i → Globeⁿ {n = n} ( bd ∘ (λ x → merid x i)))
--              (northGlobeⁿ {A = A} {n = n} bd)
--              (southGlobeⁿ {A = A} {n = n} bd)


-- north-south-const : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (a : A)
--                      →  (northGlobeⁿ {n = n} (λ _ → a))
--                         ≡ 
--                         (southGlobeⁿ {n = n} (λ _ → a))

-- northGlobeⁿ {n = zero} bd = bd north
-- northGlobeⁿ {ℓ} {A} {suc zero} bd _ = bd north
-- northGlobeⁿ {ℓ} {A} {suc (suc n)} bd = north-south-const (bd north)

-- southGlobeⁿ {n = zero} bd = bd south
-- southGlobeⁿ {n = suc zero} bd _ = bd south
-- southGlobeⁿ {n = suc (suc n)} bd = north-south-const (bd south)

-- north-south-const {n = zero} a = refl
-- north-south-const {n = suc zero} a = refl
-- north-south-const {n = suc (suc n)} a = refl






-- -- this version of Bool≃Susp⊥' is consistent with convention in merid (i0=false,i1=true)

Bool≃Susp⊥' : Bool ≃ Susp ⊥
Bool≃Susp⊥' =
  isoToEquiv
    (iso
      (λ {false  → north; true → south})
      (λ {north → false;  south → true})
      (λ {north → refl;  south → refl})
      (λ {true  → refl;  false → refl}))

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
  Iso.inv (lem) (merid x i) =   ((cong (lid false) (corner0-≡ (boundaryMap x)))
                              ∙∙ (cyl x)
                              ∙∙ (cong (lid true) (≡-corner1 (boundaryMap x)))) i

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
        (cong (lid false) (corner0-≡ (boundaryMap x)))
        (cyl x)
        (cong (lid true) (≡-corner1 (boundaryMap x)))
        (~ i) i₁

NBoundary-≡-S :  ∀ {n} → NBoundary n ≡ S (-1+ n)
NBoundary-≡-S {zero} = refl
NBoundary-≡-S {suc n} = NBoundary-≡-S₊


-- cyl2 : ∀ {n} → Interval' → NBoundary n → NBoundary (suc n)
-- cyl2 (end x) x₁ = cyl x₁ (Bool→I x)
-- cyl2 (inside i) x₁ = cyl x₁ i


GG : ∀ n → ℕ → NCube n → Type₀

gg : ∀ n → ∀ k → (cu : NCube n) → GG n k cu

GG n zero _ = NCube n
GG (n) (suc k) cu = PathP (λ j → GG (suc n) k (inside j ,□ cu) )
                       (gg (suc n) k (end false ,□ cu))
                       (gg (suc n) k (end true ,□ cu))

gg zero zero cu = corner0
gg zero (suc k) cu j = gg 1 k (inside j ,□ cu)
gg (suc n) zero cu = cu
gg (suc n) (suc k) cu j = gg (suc (suc n)) k (inside j ,□ cu)

NInside : ℕ → Type₀
NInside n = GG 0 n corner0

nInside : ∀ n → NInside n
nInside n = gg 0 n _

test : {!!}
test = {!(nInside 3)!} 

-- fix-+ : ∀ {n k} → NBoundary (n + (suc k)) → NBoundary (suc n + k)
-- fix-+ {n} {k} = subst {A = ℕ} NBoundary (+-suc _ _)

-- -- cubeLast : ∀ {n} → NCube (m) → NCube (suc n) → Σ (NCube n + ) (λ _ → Interval')  
-- -- cubeLast {zero} (x , x₁) = {!!}
-- -- cubeLast {suc n} = {!!}


-- bInj : ∀ {n k} → NCube n → NBoundary k → NBoundary (n + k) 
-- bInj {zero} {k} _ y = y
-- bInj {suc n} {k} (x , x₁) y = fix-+ (bInj x₁ (cyl2 x y))






-- -- BB : ∀ {ℓ} → ∀ (n k : ℕ) → (A : Type ℓ) → Type ℓ



-- -- EE : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n → ∀ k → (BB n k A) →  NCube n → Type ℓ


-- -- BB↓ : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n → ∀ k → (BB n (suc k) A) → (BB (suc n) k A)



-- -- EEside : 

-- --      ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n → ∀ k → ∀ (bd : BB (suc n) k A) → Bool → ∀ cu
-- --         → EE {A = A} (suc n) k bd cu


-- -- -- bb : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n → ∀ k → ∀ bd → ∀ b → ∀ cu 
-- -- --      →  PathP (λ i → EE {A = A} (suc (suc n)) k (BB↓ (suc n) k (BB↓ n (suc k) bd))
-- -- --                         (inside i , (end b , cu)))
-- -- --         (BBside (suc n) k false (BB↓ n (suc k) bd) (end b , cu))
-- -- --         (BBside (suc n) k true (BB↓ n (suc k) bd) (end b , cu))
        
-- -- EE {A = A} n zero bd _ = NCube n → A
-- -- EE {A = A} (n) (suc k) bd cu =
-- --           PathP (λ j → EE {A = A} (suc n) k (BB↓ {A = A} n k bd) (inside j , cu))
-- --                         (EEside (n) k (BB↓ {A = A} n k bd) false (end false , cu))
-- --                         (EEside (n) k (BB↓ {A = A} n k bd) true (end true , cu))



-- -- BB n k A = Σ (NBoundary n → NCube k → A) (λ _ → (NCube n → NBoundary k → A))

-- -- -- BBside  = {!!}

-- -- EEside n zero (bd , _) b (_ , x₁) _ = bd (lid b x₁) _
-- -- EEside n (suc k) bd b cu j = {!!}

-- -- -- bb zero zero bd false cu i _ = {!!}
-- -- -- bb zero zero bd true cu i _ = {!!}
-- -- -- bb zero (suc k) bd b cu i = {!!}
-- -- -- bb (suc n) zero bd b cu i = {!!}
-- -- -- bb (suc n) (suc k) bd b cu i = {!!}




-- -- BB↓ zero zero (_ , x₁) = (( λ x₂ _ → x₁ _ x₂) , λ x₂ → λ ())
-- -- fst (BB↓ zero (suc k) (_ , x)) (lid x₁ _) x₂ = x _ (lid x₁ x₂)
-- -- snd (BB↓ zero (suc k) (_ , x)) (x₁ , _) z = x _ (cyl2 x₁ z)
-- -- fst (BB↓ (suc n) k (_ , x)) (lid x₁ x₃) x₂ =  x x₃ (lid x₁ x₂)
-- -- fst (BB↓ (suc n) zero (_ , x)) (cyl x₁ i) x₂ = x {!!} {!!}
-- -- fst (BB↓ (suc n) (suc k) (_ , x)) (cyl x₁ i) (x₂ , x₃) = x {!!} {!!}
-- -- snd (BB↓ (suc n) k x) = {!!}

-- -- -- BB↓ n k x (end x₁ , x₂) x₃ = x x₂ (cyl x₃ (Bool→I x₁))
-- -- -- BB↓ n k x (inside i , x₂) x₃ = x x₂ (cyl x₃ i)


-- -- -- BB↓ (suc n) k x x₁ x₂ = {!!}

-- -- -- ee zero zero cu = tt
-- -- -- ee zero (suc k) cu j = ee 1 k (inside j , cu)
-- -- -- ee (suc n) zero cu = cu
-- -- -- ee (suc n) (suc k) cu j = ee (suc (suc n)) k (inside j , cu)

-- -- -- NInside : ℕ → Type₀
-- -- -- NInside n = GG 0 n _

-- -- -- nInside : ∀ n → NInside n
-- -- -- nInside n = gg 0 n _
