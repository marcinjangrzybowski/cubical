{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.Base where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
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

NCube : ℕ -> Type₀
NCube zero = Unit
NCube (suc n) = Interval' × (NCube n)


data NBoundary' {n} {X : Type₀} (injX : X → NCube (n)) : Type₀ where
   lid : Bool → NCube (n) → NBoundary' injX
   cyl : ∀ x → lid false (injX x) ≡ lid true (injX x)

NBoundary : ℕ → Type₀

boundaryMap : ∀ {n} → NBoundary n → NCube n


NBoundary zero = ⊥
NBoundary (suc n) = NBoundary' {n} (boundaryMap)


boundaryMap {zero} ()
boundaryMap {suc _} (lid x₁ x) = (end x₁) , x
boundaryMap {suc _} (cyl x i) = inside i ,  boundaryMap x


flipNBoundaryHead : ∀ {n} → Iso (NBoundary (suc (suc n))) (NBoundary (suc (suc n)))
flipNBoundaryHead = iso f f law law
  where
    f : _
    f (lid x (end x₁ , x₂)) = (lid x₁ (end x , x₂))
    f (lid x (inside i , x₂)) = (cyl (lid x x₂) i)
    f (cyl (lid x x₁) i) = (lid x (inside i , x₁))
    f (cyl (cyl x i₁) i) = (cyl (cyl x i) i₁)
    
    law : _
    law (lid x (end x₁ , x₂)) = refl
    law (lid x (inside i , x₂)) = refl
    law (cyl (lid x x₁) i) = refl
    law (cyl (cyl x i₁) i) = refl

lid' : ∀ {n} → Bool  → NCube n → NBoundary (suc n) 
lid' = lid

boundaryEndMap : ∀ {n} → Bool → NBoundary n → NBoundary (suc n)
boundaryEndMap {n} x = lid x ∘ boundaryMap

cyl' : ∀ {n} → (bd : NBoundary (suc n)) →
                          boundaryEndMap false bd ≡ boundaryEndMap true bd 
cyl' = cyl

Bool→I : Bool → I
Bool→I false = i0
Bool→I true = i1

cyl'' : ∀ {n} → NBoundary n → Interval' → NBoundary (suc n)
cyl'' y (end x) = cyl y (Bool→I x)
cyl'' y (inside i) = cyl y i


cylEx : ∀ {n} → boundaryEndMap {n} false ≡ boundaryEndMap true 
cylEx i x = cyl x i

faceMap : ∀ {n}
          → ℕ → Bool
          → NCube n → NBoundary (suc n)  
faceMap {suc n} (suc k) s (end x₂ , x₃) = lid x₂ (boundaryMap (faceMap k s x₃))
faceMap {suc n} (suc k) s (inside i , x₃) = cyl (faceMap k s x₃) i
faceMap  _  = lid


bundaryHead : ∀ {n} → NBoundary (suc n) →  Interval'
bundaryHead (lid x x₁) = end x
bundaryHead (cyl x i) = inside i

corner0 : ∀ {n} → NCube n
corner0 {zero} = _
corner0 {suc n} =  end false , corner0

corner1 : ∀ {n} → NCube n
corner1 {zero} = _
corner1 {suc n} =  end true , corner1

corner0Bd : ∀ {n} → NBoundary (suc n)
corner0Bd {zero} = lid false _
corner0Bd {suc n} = lid false corner0

corner1Bd : ∀ {n} → NBoundary (suc n)
corner1Bd {zero} = lid true _
corner1Bd {suc n} = lid true corner1


corner0-≡ : ∀ {n} → ∀ (a : NCube n) → _≡_ {A = NCube n} (corner0) a  
corner0-≡ {zero} a = refl
corner0-≡ {suc n} (end false , x₁) i = end false , corner0-≡ x₁ i
corner0-≡ {suc n} (end true , x₁) i = inside i , corner0-≡ x₁ i
corner0-≡ {suc n} (inside i , x₁) j = inside (i ∧ j) , corner0-≡ x₁ j

≡-corner1 : ∀ {n} → ∀ (a : NCube n) → _≡_ {A = NCube n}  a (corner1)  
≡-corner1 {zero} a = refl
≡-corner1 {suc n} (end true , x₁) i = end true , ≡-corner1 x₁ i
≡-corner1 {suc n} (end false , x₁) i = inside i , ≡-corner1 x₁ i
≡-corner1 {suc n} (inside i , x₁) j = inside (i ∨ j) , ≡-corner1 x₁ j

corner0-≡-corner1 : ∀ {n} → _≡_ {A = NCube n}  corner0 corner1  
corner0-≡-corner1 {zero} = refl
corner0-≡-corner1 {suc n} i = (inside i) , corner0-≡-corner1 i

corner0Bd-≡-corner1Bd : ∀ {n} → corner0Bd {n = suc n} ≡ corner1Bd {n = suc n}
corner0Bd-≡-corner1Bd {n} i = ((λ i₁ → cyl (lid false (corner0-≡  corner0 i₁)) i₁)
                             ∙ λ i₁ → lid true (inside i₁ , (corner0-≡-corner1 i₁))) i





isContr-Inrerval' : isContr Interval'
fst isContr-Inrerval' = end false
snd isContr-Inrerval' (end false) = refl
snd isContr-Inrerval' (end true) = inside
snd isContr-Inrerval' (inside i) j = inside (i ∧ j) 


isPropCube : ∀ {n} → isProp (NCube n)
isPropCube {zero} x y i = _
isPropCube {suc n} (x , x₁) (x₂ , x₃) i = (isContr→isProp isContr-Inrerval') x x₂ i , (isPropCube x₁ x₃ i)



NBoundary1-≡-Bool : NBoundary 1 ≡ Bool
NBoundary1-≡-Bool = isoToPath h 
  where

  h : Iso (NBoundary 1) Bool
  Iso.fun h (lid x _) = x
  Iso.inv h x = lid x _
  Iso.rightInv h b = refl
  Iso.leftInv h (lid x x₁) = refl











Globeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n} → (S (-1+ n) → A) → Type ℓ

northGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
                 → ∀ (bd : (S (-1+ (suc n)) → A))
                 → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → north))

southGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
                 → ∀ (bd : (S (-1+ (suc n)) → A))
                 → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → south))
                 
Globeⁿ {A = A} {n = zero} bd = A 
Globeⁿ {A = A} {n = suc n} bd =
             PathP
             (λ i → Globeⁿ {n = n} ( bd ∘ (λ x → merid x i)))
             (northGlobeⁿ {A = A} {n = n} bd)
             (southGlobeⁿ {A = A} {n = n} bd)


north-south-const : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (a : A)
                     →  (northGlobeⁿ {n = n} (λ _ → a))
                        ≡ 
                        (southGlobeⁿ {n = n} (λ _ → a))

northGlobeⁿ {n = zero} bd = bd north
northGlobeⁿ {ℓ} {A} {suc zero} bd _ = bd north
northGlobeⁿ {ℓ} {A} {suc (suc n)} bd = north-south-const (bd north)

southGlobeⁿ {n = zero} bd = bd south
southGlobeⁿ {n = suc zero} bd _ = bd south
southGlobeⁿ {n = suc (suc n)} bd = north-south-const (bd south)

north-south-const {n = zero} a = refl
north-south-const {n = suc zero} a = refl
north-south-const {n = suc (suc n)} a = refl




-- this version of Bool≃Susp⊥' is consistent with convention of Interval' and  merid
--                (i0=false,i1=true)

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









Pathⁿ : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (NBoundary n → A) → Type ℓ
Pathⁿ {ℓ} {A = A} {n-final} bd-final = Pathⁿ-typeBuilder 0 n-final (λ _ → bd-final) _ 


   where

   Pathⁿ-typeBuilder : ∀ n → ∀ k
                     → (bd : NCube n → NBoundary k → A)
                     → (c : NCube n) → Type ℓ

   facePathⁿ-Builder : ∀ n → ∀ k
                     → (bc : NCube n → NCube k → A)
                     → (c : NCube n)
                     → (i' : Interval')
                     → Pathⁿ-typeBuilder (suc n) k (λ x x₁ → bc c (boundaryMap x₁) ) (i' , c)



   Pathⁿ-typeBuilder n zero bd c = A
   Pathⁿ-typeBuilder n (suc k) bd c = PathP
                          (λ i → Pathⁿ-typeBuilder
                                 (suc n) k (λ x x₁ → bd c (cyl x₁ i)) (inside i , c))
                          (facePathⁿ-Builder n k (λ x x₁ → bd x (lid false x₁ )) c (end false))
                          (facePathⁿ-Builder n k (λ x x₁ → bd x (lid true x₁ )) c (end true))



   facePathⁿ-Builder n zero bc c i' = bc c _
   facePathⁿ-Builder n (suc k) bc c i' i = facePathⁿ-Builder (suc n) k (λ x x₁ → bc c (inside i , x₁))
                                     (i' , c) (inside i)



nInside : ∀ n → Pathⁿ (boundaryMap {n})
nInside zero = corner0
nInside (suc n') i = nInside-hlp 0 (suc n') _ (inside i) i

  where

  nInside-Hlp : ∀ n → ℕ → NCube n → Type₀ 


  nInside-hlp : ∀ n → ∀ k → ∀ c → (i' : Interval') → nInside-Hlp n k c

  nInside-Hlp zero k _ = Pathⁿ {n = k} (boundaryMap {k})
  nInside-Hlp (suc n) zero _ = NCube (suc n)
  nInside-Hlp (suc n) (suc k) c =
    PathP (λ i → nInside-Hlp (suc (suc n)) k (inside i , c))
      (nInside-hlp (suc (suc n)) k (end false , c) (end false))
      (nInside-hlp (suc (suc n)) k (end true , c) (end true))


  nInside-hlp (suc n) zero c i' = c

  nInside-hlp zero zero _ i' = _
  nInside-hlp zero (suc k) c (i') i = {!(nInside-hlp (suc zero) k (inside i , c) (inside i))!}
  -- (λ x x₁ → inside i , {!nInside-hlp zero k!}) _ (inside i)
  nInside-hlp (suc n) (suc k) c i' i = (nInside-hlp (suc (suc n)) k (inside i , c) (inside i))

-- -- GG : ∀ n → ℕ → NCube n → Type₀

-- -- gg : ∀ n → ∀ k → (cu : NCube n) → GG n k cu

-- -- GG n zero _ = NCube n
-- -- GG (n) (suc k) cu = PathP (λ j → GG (suc n) k (inside j , cu) )
-- --                        (gg (suc n) k (end false , cu))
-- --                        (gg (suc n) k (end true , cu))

-- -- gg zero zero cu = tt
-- -- gg zero (suc k) cu j = gg 1 k (inside j , cu)
-- -- gg (suc n) zero cu = cu
-- -- gg (suc n) (suc k) cu j = gg (suc (suc n)) k (inside j , cu)

-- -- NInside : ℕ → Type₀
-- -- NInside n = GG 0 n _

-- -- nInside : ∀ n → NInside n
-- -- nInside n = gg 0 n _



-- Pathⁿ-≡-Globeⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n
--                   → PathP (λ i → (NBoundary-≡-S {n} i → A) → Type ℓ)
--                           Pathⁿ Globeⁿ

-- Pathⁿ-≡-Globeⁿ A zero = refl
-- Pathⁿ-≡-Globeⁿ {ℓ} A (suc zero) i x = {! !}
-- Pathⁿ-≡-Globeⁿ {ℓ} A (suc (suc n)) i x = {!!}
