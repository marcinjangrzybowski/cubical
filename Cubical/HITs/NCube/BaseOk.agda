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
open import Cubical.Foundations.CartesianKanOps


-- this version of Interval will let us handle both ends in single case
-- the convention of i0 ↔ false , i1 ↔ true is used everywhere in this module

data Interval' : Type₀ where
   end : Bool → Interval'
   inside : end false ≡ end true 

Bool→I : Bool → I
Bool→I false = i0
Bool→I true = i1

-- I did not check how it would behave, but (Vec n Interval') , or (Fin n → Interval')
-- should also work here

NCube : ℕ -> Type₀
NCube zero = Unit
NCube (suc n) = Interval' × (NCube n)

Iapp : ∀ {ℓ} → {A : Type ℓ} → {a₀ a₁ : A}
         → a₀ ≡ a₁ → Interval' → A
Iapp {a₀ = a₀} {a₁} x (end x₁) = caseBool a₁ a₀ x₁ 
Iapp x (inside i) = x i

IappP : ∀ {ℓ} → {A : I → Type ℓ} → {a₀ : A i0} → {a₁ : A i1}
      → PathP (λ i → A i) a₀ a₁ 
      → ∀ i' →  Iapp (λ i → A i) i'
IappP {a₀ = a₀} x (end false) = a₀
IappP {a₁ = a₁} x (end true) = a₁
IappP x (inside i) = x i

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

boundaryInj {zero} ()
boundaryInj {suc _} (lid x₁ x) = (end x₁) , x
boundaryInj {suc _} (cyl x i) = inside i ,  boundaryInj x




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

flipNBoundaryHeadF : ∀ {n} → NBoundary (suc (suc n)) → NBoundary (suc (suc n)) 
flipNBoundaryHeadF {n} = Iso.fun (flipNBoundaryHead {n})

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
faceInj {suc n} (suc k) s (end x₂ , x₃) = lid x₂ (boundaryInj (faceInj k s x₃))
faceInj {suc n} (suc k) s (inside i , x₃) = cyl (faceInj k s x₃) i
faceInj  _  = lid

faceMap : ∀ {n}
          → ℕ → Bool
          → NCube n → NCube (suc n)  
faceMap n b = boundaryInj ∘ faceInj n b 


boundaryProj : ∀ {n} → NBoundary (suc n) → NCube n
boundaryProj {zero} _ = _
boundaryProj {suc n} (lid _ x₂) = x₂
boundaryProj {suc n} (cyl x₁ _) = boundaryInj x₁


boundaryHead : ∀ {n} → NBoundary (suc n) →  Interval'
boundaryHead (lid x x₁) = end x
boundaryHead (cyl x i) = inside i


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
isPropCube {suc n} (x , x₁) (x₂ , x₃) i =
    (isContr→isProp isContr-Inrerval') x x₂ i , (isPropCube x₁ x₃ i)



NBoundary1-≡-Bool : NBoundary 1 ≡ Bool
NBoundary1-≡-Bool = isoToPath h 
  where

  h : Iso (NBoundary 1) Bool
  Iso.fun h (lid x _) = x
  Iso.inv h x = lid x _
  Iso.rightInv h b = refl
  Iso.leftInv h (lid x x₁) = refl


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



_isBoundaryOf_ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
               → (NBoundary n → A) → (NCube n → A)
               → Type ℓ
x isBoundaryOf x₁ = x ≡ x₁ ∘ boundaryInj

-- InsideOfₘ and insideOf↑  are recursively defined helpers for
-- constructing InsideOf Type, they should nevel "leak out" from InsideOf for
-- finite dimension , but they will leak out during handling terms of unknown
-- dimension (not evaluated into some constant ℕ).
-- To deal with them in such scenerio there are helper functions
--
-- insideOf↓ - is forgetting informations from PathP
-- insideOf↑ - is encoding information inside PathP

-- InsideOf can be thought as Type of paths of arbitrary dimension, it is more complicated
-- than more obvious definition, but i find it more usefull when interacting with NBoundary HIT
--
--


InsideOfₘ : ∀ {ℓ} → ∀ {A : Type ℓ}
                  → ℕ → ∀ {k}
                  → (bd : NBoundary k → A)
                  → Type ℓ

insideOf↑ : ∀ {ℓ} → ∀ {A : Type ℓ}
                  →  ∀ {n} → ∀ {k}
                  → (bc : NCube k → A)                  
                  → InsideOfₘ n (bc ∘ boundaryInj)

InsideOfₘ {A = A} _ {zero} bd = A
InsideOfₘ n {suc k} bd =
                       PathP
                       (λ i → InsideOfₘ (suc n) (bd ∘ cyl'' (inside i)))
                       (insideOf↑ (bd ∘ lid false)) (insideOf↑ (bd ∘ lid true))

insideOf↑ {n = n} {zero} bc = bc _ 
insideOf↑ {n = n} {suc k} bc i = insideOf↑ (λ x₁ → bc (inside i , x₁))


insideOf↓ : ∀ {ℓ} → ∀ {A : Type ℓ}
                  → ∀ n → ∀ {k} → ∀ i'
                  → (bd :  NCube (suc k) → A)
                  → (InsideOfₘ n
                          λ x₁ → bd (i' , (proj₂ (boundaryInj x₁)))) 
                  → (InsideOfₘ (suc n)
                          λ x₁ → bd (i' , (boundaryInj x₁)))
insideOf↓ n {k = k} (end b) bd x = x (Bool→I b)
insideOf↓ n {k = k} (inside i) bd x = x i


    

-- -- Path of n dimensions

InsideOf : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (NBoundary n → A) → Type ℓ
InsideOf {ℓ} {A = A} {n} = InsideOfₘ 0 {k = n} 


insideOf-faceⁿ : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n}
        → (k : ℕ) → (s : Bool) 
        → (bd : NBoundary (suc n) → A)
        → InsideOf (bd ∘ (faceInj k s) ∘ boundaryInj)
insideOf-faceⁿ {n = n} k s bd = insideOf↑ {n = 0} (bd ∘ (faceInj k s))


Cubical→InsideOf : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                  → (c : NCube n → A)
                  → InsideOf (c ∘ boundaryInj)  
Cubical→InsideOf c =  insideOf↑ {n = 0} λ x₁ → c x₁ 




InsideOfₘ→Cubical :
       ∀ {ℓ} → {A : Type ℓ}
      → ∀ {n} → ∀ {k}
      → (bd : NBoundary k → A)          
      → InsideOfₘ {A = _} n {k = k} bd
      → NCube k → A
InsideOfₘ→Cubical {n = n} {zero} _ x _ = x
InsideOfₘ→Cubical {n = n} {suc k} _ x (end x₁ , x₂) =
                                   InsideOfₘ→Cubical {n = 0} _ (x (Bool→I x₁)) x₂
InsideOfₘ→Cubical {n = n} {suc k} _ x (inside i , x₂) =
                                   InsideOfₘ→Cubical {n = 0} _ (x i) x₂



InsideOf→Cubical : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                  → {bd : NBoundary n → A}
                  → InsideOf bd
                  → NCube n → A
InsideOf→Cubical {n = zero} x x₁ = x
InsideOf→Cubical {A = A} {n = suc n} {bd} x x₁ = InsideOfₘ→Cubical (λ x₃ → bd x₃) x x₁
 

insideOfSlice : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                  → {bd : NBoundary (suc n) → A}
                  → InsideOf bd
                  → (i' : Interval')
                  → InsideOf (bd ∘ (cyl'' i')) 
insideOfSlice x (end x₁) = x (Bool→I x₁)
insideOfSlice x (inside i) = x i

InsideOfEquationalₘ : ∀ {ℓ} → ∀ {A : Type ℓ}
                      → ∀ {k}
                      → (bd : NBoundary k → A)
                      → Type ℓ
InsideOfEquationalₘ bd = Σ _ (bd isBoundaryOf_)


reflⁿ : ∀ {ℓ} → {A : Type ℓ} → ∀ n → (a : A) → InsideOf {n = n} (const a)
reflⁿ zero a = a
reflⁿ (suc n) a = refl

nInside : ∀ n → InsideOf (boundaryInj {n})
nInside n = insideOf↑ {A = NCube n} {n = n} (idfun _)
















-- isBd : ∀ {n} → NCube n → {!!}
-- isBd {n} x = {!!}


-- mkPartialTy : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
--               → NCube n → (NCube (suc n) →  A)
--               →  A 
-- mkPartialTy c x = iii (brd c) λ x₁ → x (x₁ , c)

-- mkPartialCu : (n : ℕ) → NCube n  → _×_ {ℓ-zero} {ℓ-zero} Interval' (NCube n)
-- mkPartialCu n x = mkPartialTy x (idfun (NCube (suc n)))

-- mkPartialCuTest : ∀ {ℓ} → {A : Type ℓ} → I → I → ((NCube 3 → A)) → {!!}
-- mkPartialCuTest i₁ i₂ a = {!mkPartialTy (inside i₁ , inside i₂ , _) a!}

-- xxx : ∀ n → (c : NCube n) → {!!}
-- xxx = {!!}

---


-- hcompⁿ-all : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n → ∀ k 
--           → (c : Interval' → NBoundary (suc k) → A)
--           → InsideOfₘ n (c (end false))
--           → NCube (suc k) → A
-- hcompⁿ-all {ℓ} {A} n zero c x cu = {!!}

-- -- hcompⁿ-all {ℓ} {A} n (suc zero) = {!!}

-- hcompⁿ-all {ℓ} {A} n (suc k') c x (i' , j' , cu) = hCC i' j'  --hCC

--    where
 
--    -- k' = suc k''
--    k = suc k'

--    hC : ∀ i → NCube (suc k') → A
--    hC i = hcompⁿ-all
--           (suc n)
--           k' (λ x₁ x₂ → c x₁ (cyl x₂ i))
--           (x i)
          
          
--    hCC : Interval' → Interval' → A   
--    hCC (inside i) (inside j) = hcomp
--         ((λ l → λ {
--             (i = i0) → {!!}
--           ; (i = i1) → {!c (inside l) ?!}
--           ; (j = i1) → hC i (inside j , cu)
--           }))
--         {!!}
--    hCC i' j' = {!!}

--    hCub : ∀ i  → NCube (suc (suc k'')) → A
--    hCub i = InsideOfₘ→Cubical {n = suc n} {k = k} (λ x₂ → c (end true) (cyl x₂ i)) (hC i)
          
--    hhhTest : (i : I) → (cu : NCube ((suc (suc k'')))) → (φ : I)
--               → A
--    hhhTest i cu φ = hcomp {A  = A} (λ l → λ {
--                         (i1 = i1) → hCub i cu --(hC i z) --hCub i z cu
--                          })
--                        ((hCub i cu ))

--    hhhC : (i : I) → (cu : NCube ((suc (suc k'')))) → (φ : Interval')
--           →  A
--    hhhC i cu (end false) = 
--                       hcomp {A  = A} (λ l → λ {
--                           (i = i0) → hCub i0 cu --c (inside (z ∧ φ)) (lid false cu) 
--                         ; (i = i1) → hCub i1 cu --c (inside (z ∧ φ)) (lid true cu)
--                           -- (i1 = i1) → hCub i cu --(hC i z) --hCub i z cu
--                         })
--                        ((hCub i cu ))
--    hhhC i cu (end true) = 
--                       hcomp {A  = A} (λ l → λ {
--                           (i1 = i1) → hCub i cu --(hC i z) --hCub i z cu
--                         })
--                        ((hCub i cu ))
--    hhhC i cu (inside φ) =
--                       hcomp {A  = A} (λ l → λ {
--                           -- (φ = i0) → hCub i cu
--                           (φ = i1) → hCub i cu --(hC i z) --hCub i z cu
--                         ; (i = i0) → hCub i0 cu --c (inside (z ∧ φ)) (lid false cu) 
--                         ; (i = i1) → hCub i1 cu --c (inside (z ∧ φ)) (lid true cu)
--                         })
--                        ((hCub i cu ))

--    hhhC' :  (i : Interval') → (cu : NCube ((suc (suc k'')))) →  A
--    hhhC' (end false) c = hhhC i0 c (brd c)



--    hhhC' (end true) c = hhhC i1 c (brd c)


--    hhhC' (inside i) c =  hhhC i c (brd c)

--    -- hhC : Interval' → NCube (suc k) → A
--    -- hhC (end b) (x , y) = hhhC (Bool→I b) y x
--    -- hhC (inside i) (x , y) = hhhC i y x

   
--    -- hCC' : PathP {!!} {!!} {!!}
--    -- --InsideOfₘ (suc n) {!!}
--    -- hCC' = insideOf↑ hhC

--    hCC0 : InsideOfₘ n {k = suc (suc (suc k''))}
--             ((λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁)) ∘ boundaryInj)
--    hCC0 = insideOf↑ {n = n} {k = suc k} λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁)

--    hCC1 : InsideOfₘ n {k = suc (suc (suc k''))}
--             ((λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁)) ∘ boundaryInj)
--    hCC1 = (insideOf↑ {n = n} {k = suc k} λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁))

--    hCC : InsideOfₘ n {k = suc (suc (suc k''))} (c (end true))
--    hCC i i₁ i₂ = {!hCC0 i0 i₁ i₂!}
--    -- {!(Cubical→InsideOf (hhC (inside i)))!}  -- (Cubical→InsideOf (hhC (inside i)))


-- -- -- InsideOfₘ (suc n) ((c (end true)) ∘ (lid b) ∘ boundaryInj)
-- --    hS : ∀ b → {!!}
-- --    hS b = hcompⁿ-all {!!} {!!} {!!} ( x (Bool→I b))


-- --    --insideOf↑ ((c (inside z)) ∘ lid b)


-- --    h : InsideOfₘ (suc (suc n))
-- --          (λ x₁ → c (inside z) (cyl'' (inside i) (cyl'' (inside i₁) x₁)))
-- --    h = hcomp
-- --          (λ l → λ {
-- --             (i = i0) → {!!} 
-- --           ; (i = i1) → {!!}
-- --           ; (i₁ = i0) → {!!}
-- --           ; (i₁ = i1) → {!x i i!}
-- --          })
-- --              λ _ → {!hC!}
-- --         -- hfill
-- --         --  (λ l → λ {
-- --         --     (i = i0) → {!hS false!} 
-- --         --   ; (i = i1) → {!!}
-- --         --   ; (i₁ = i0) → {!!}
-- --         --   ; (i₁ = i1) → {!x i i!}
-- --         --   ; (z = i0) → x i i₁
-- --         --  })
-- --         --  (inS ({!hC z!}))
-- --         --  z
   
-- --    -- zz : ∀ (i i₁ : I) → (j : I) → Set ℓ
-- --    -- zz i i₁ j = InsideOfₘ 2 {k'} ((c (inside j))  ∘ (cyl'' (inside i)) ∘ (cyl'' (inside i₁)))
     
   
-- --    -- h0 : ∀ j → {!!}
-- --    -- h0 j = 
-- --    --       ((hfillⁿ-all k' (λ x₁ x₂ → c x₁ (cyl x₂ i))
-- --    --           (insideOfSlice {bd = c (end false)} x (inside i)) j)) i₁


-- --    -- h2 : InsideOfₘ (suc (suc 0))
-- --    --        ((c (inside z)) ∘ (cyl'' (inside i)) ∘  (cyl'' (inside i₁)))
-- --    -- h2 =  hfill
-- --    --       (λ l → λ {
-- --    --          (i₁ = i0) → {!h0!}
-- --    --        ; (i₁ = i1) → {!h!}
-- --    --        ; (i = i0) → {!h0 z  !}
-- --    --        ; (i = i1) → {!!}
-- --    --       })
-- --    --       (inS {! h0 !})
-- --    --       z


-- -- -- hfillⁿ-all : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ k
-- -- --           → (c : Interval' → NBoundary (suc k) → A)
-- -- --           → InsideOf (c (end false))
-- -- --           → (z : I) → InsideOf (c (inside z))
-- -- -- hfillⁿ-all {ℓ} {A} zero c x z i =
-- -- --        hfill
-- -- --        (λ l → λ {
-- -- --                (i = i0)  → c (inside l) (lid false _)  
-- -- --              ; (i = i1)  → c (inside l) (lid true _)         
-- -- --           })
-- -- --       (inS (x i )) z

-- -- -- hfillⁿ-all {ℓ} {A} (suc zero) c x z i i₁ =
-- -- --       hfill
-- -- --        (λ l → λ {
-- -- --                (i₁ = i0) → c (inside l) (cyl (lid false _) i)
-- -- --              ; (i₁ = i1) → c (inside l) (cyl (lid true _) i) 
-- -- --              ; (i = i0)  → c (inside l) (lid false (inside i₁ , _))  
-- -- --              ; (i = i1)  → c (inside l) (lid true (inside i₁ , _))         
-- -- --           })
-- -- --       (inS (x i i₁)) z


-- -- -- hfillⁿ-all {ℓ} {A} (suc (suc k'')) c x z i i₁ = h

-- -- --    where

-- -- --    k' = suc k''
         
-- -- --    zz : ∀ (i i₁ : I) → (j : I) → Set ℓ
-- -- --    zz i i₁ j = InsideOfₘ 2 {k'} ((c (inside j))  ∘ (cyl'' (inside i)) ∘ (cyl'' (inside i₁)))
     

-- -- --    h : _

-- -- --    h =
-- -- --       let cl-i : (b : Bool) → (l : I)
-- -- --                     → InsideOfₘ 2 {k'}
-- -- --                       ((c (inside l)) ∘ (lid b) ∘ ( (inside i₁) ,_) ∘ boundaryInj )
-- -- --           cl-i b l =  insideOf↑ 
-- -- --                          ((c (inside l)) ∘ (lid b) ∘ ( (inside i₁) ,_))

-- -- --           cl-i₁ : (b : Bool) → (l : I)
-- -- --                     → InsideOfₘ 2 {k'}
-- -- --                       ((c (inside l)) ∘ ( cyl'' (inside i)) ∘ (lid b) ∘ boundaryInj )
-- -- --           cl-i₁ b l =  insideOf↑ 
-- -- --                          ((c (inside l)) ∘ ( cyl'' (inside i) ) ∘ (lid b))

-- -- --       in
    
-- -- --       fill (zz i i₁)
-- -- --       (  (λ l → λ {
-- -- --                (i₁ = i0) → cl-i₁ false l
-- -- --              ; (i₁ = i1) → cl-i₁ true l 
-- -- --              ; (i = i0)  → cl-i false l  
-- -- --              ; (i = i1)  → cl-i true l        
-- -- --           }))
-- -- --       (inS (x i i₁))
-- -- --       z




-- -- -- hcompⁿ-all : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ k
-- -- --           → (c : Interval' → NBoundary (suc k) → A)
-- -- --           → InsideOf (c (end false))
-- -- --           → InsideOf (c (end true))
-- -- -- hcompⁿ-all k c x = hfillⁿ-all k c x i1




-- -- -- test-3-Type : Cube
-- -- --               (insideOf-faceⁿ 0 false boundaryInj) (insideOf-faceⁿ 0 true boundaryInj)
-- -- --               (insideOf-faceⁿ 1 false boundaryInj) (insideOf-faceⁿ 1 true boundaryInj)
-- -- --               (insideOf-faceⁿ 2 false boundaryInj) (insideOf-faceⁿ 2 true boundaryInj)
-- -- --               ≡
-- -- --               InsideOf (boundaryInj {3})
-- -- -- test-3-Type = refl


-- -- -- test-2-Type-holes : Square _ _ _ _
-- -- --                     ≡
-- -- --                     InsideOf (boundaryInj {2})
-- -- -- test-2-Type-holes = refl

-- -- -- test-3-Type-holes : Cube _ _ _ _ _ _
-- -- --                     ≡
-- -- --                     InsideOf (boundaryInj {3})
-- -- -- test-3-Type-holes = refl

-- -- -- test-9-term :  nInside 9
-- -- --                ≡ 
-- -- --                (λ i i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ →
-- -- --                inside i , inside i₁ , inside i₂ ,
-- -- --                inside i₃ , inside i₄ , inside i₅ ,
-- -- --                inside i₆ , inside i₇ , inside i₈ ,
-- -- --                _)
-- -- -- test-9-term = refl


-- -- -- testXX : {!!}
-- -- -- testXX = {!hcompⁿ-all 2 (const (const tt)) (reflⁿ 3 tt)!}


-- -- -- -- InsideOfₘ (suc n) (λ x₁ → c (end true) (cyl x₁ i))

-- -- --     -- comp  {!!} {!!} {!!} 

-- -- -- -- InsideOfEquationalₘ-Iso-InsideOfₘ :
-- -- -- --                   ∀ {ℓ} → ∀ {A : Type ℓ}
-- -- -- --                   → ∀ n → ∀ {k}
-- -- -- --                   → (bd : NBoundary k → A)
-- -- -- --                   → Iso (InsideOfEquationalₘ bd) (InsideOfₘ n bd)

-- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) (fst₁ , snd₁) = fst₁ _
-- -- -- -- fst (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) x) = const x
-- -- -- -- snd (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) x) i ()
-- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) b = refl
-- -- -- -- fst (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) a i) = const (fst a _)
-- -- -- -- snd (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) a i) i₁ ()

-- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc zero} bd) (cu , bd=) = {!!}

-- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) (cu , bd=) i = ss i

-- -- -- --          where

-- -- -- --              ww* : ∀ i₁ → (x : NCube k) → _
-- -- -- --              ww* i₁ x = cu (inside i₁ , x)

-- -- -- --              ss* : ∀ i₁ → InsideOfₘ (suc n) (λ x → cu (inside i₁ , boundaryInj x))
-- -- -- --              ss* i₁ = insideOf↑ {n = n} {k = k} (ww* i₁)

-- -- -- --              ww : ∀ i₁ → (x : NCube k) → _
-- -- -- --              ww i₁ x = hcomp (λ i₂ → λ {                        
-- -- -- --                         (i₁ = i0) → bd= (~ i₂) (lid false x)
-- -- -- --                       ; (i₁ = i1) → bd= (~ i₂) (lid true x)
-- -- -- --                     }) (cu (inside i₁ , x))

-- -- -- --              ss : ∀ i₁ → InsideOfₘ (suc n) (λ x → ww i₁ (boundaryInj x))
-- -- -- --              ss i₁ = insideOf↑ {n = n} {k = k} (ww i₁)

-- -- -- --              qq : {!!}
-- -- -- --              qq = {!ss i1!}

-- -- -- --              ss' : InsideOfₘ (suc n) (λ x → bd (cyl'' (inside i) x))
-- -- -- --              ss' = insideOf↑ {n = n} {k = k} ({!!})

-- -- -- --                  -- ww : ∀ i → InsideOfₘ n {k = suc k} (λ x → bd= i0 (cyl x i))
-- -- -- --                  -- ww = λ i → Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} λ x → bd= i0 (cyl x i))
-- -- -- --                  --          ( (λ x → cu (inside i , x)) , λ i₁ x → bd= i₁ (cyl x i)) 

-- -- -- --                  -- zz : I → I → Type _
-- -- -- --                  -- zz i j = InsideOfₘ n (λ x → bd= j (cyl x i))

-- -- -- --                  -- sss : {!!}
-- -- -- --                  -- sss = {!!}

-- -- -- --                  -- ss : ∀ i' → InsideOfₘ (suc n) (λ x₁ → _)
-- -- -- --                  -- ss i' = insideOf↓ n i' (λ x → {!!}) λ i → ww i

-- -- -- --                  -- ss' : InsideOfₘ n {k = suc (suc k)} bd
-- -- -- --                  -- ss' = coe0→1 {!!} {!!}

             

-- -- -- -- Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) = {!!}

-- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) = {!!}
-- -- -- -- Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) = {!!}


-- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) = {!InsideOf→Cubical !}
-- -- -- -- -- -- -- Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) x = {!!}
-- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) = {!!}
-- -- -- -- -- -- -- Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) = {!!}

-- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) x = fst x _
-- -- -- -- -- -- -- -- fst (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) x) _ = x
-- -- -- -- -- -- -- -- snd (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) x) i ()
-- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) b = refl
-- -- -- -- -- -- -- -- fst (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) a i) x = fst a _
-- -- -- -- -- -- -- -- snd (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) a i) i₁ ()

-- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ {ℓ} {A} {n = n} {suc k} c bd) (fst₁ , snd₁) i = {!!}

-- -- -- -- -- -- -- -- Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {suc k} c bd) x = {!!}                    

-- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {suc k} c bd) = {!!}
-- -- -- -- -- -- -- -- Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {suc k} c bd) = {!!}













-- -- -- -- -- -- -- -- -- another definition of n-path , inside Sn

-- -- -- -- -- -- -- -- Globeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n} → (S (-1+ n) → A) → Type ℓ

-- -- -- -- -- -- -- -- northGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
-- -- -- -- -- -- -- --                  → ∀ (bd : (S (-1+ (suc n)) → A))
-- -- -- -- -- -- -- --                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → north))

-- -- -- -- -- -- -- -- southGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
-- -- -- -- -- -- -- --                  → ∀ (bd : (S (-1+ (suc n)) → A))
-- -- -- -- -- -- -- --                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → south))
                 
-- -- -- -- -- -- -- -- Globeⁿ {A = A} {n = zero} bd = A 
-- -- -- -- -- -- -- -- Globeⁿ {A = A} {n = suc n} bd =
-- -- -- -- -- -- -- --              PathP
-- -- -- -- -- -- -- --              (λ i → Globeⁿ {n = n} ( bd ∘ (λ x → merid x i)))
-- -- -- -- -- -- -- --              (northGlobeⁿ {A = A} {n = n} bd)
-- -- -- -- -- -- -- --              (southGlobeⁿ {A = A} {n = n} bd)


-- -- -- -- -- -- -- -- north-south-const : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (a : A)
-- -- -- -- -- -- -- --                      →  (northGlobeⁿ {n = n} (λ _ → a))
-- -- -- -- -- -- -- --                         ≡ 
-- -- -- -- -- -- -- --                         (southGlobeⁿ {n = n} (λ _ → a))

-- -- -- -- -- -- -- -- northGlobeⁿ {n = zero} bd = bd north
-- -- -- -- -- -- -- -- northGlobeⁿ {ℓ} {A} {suc zero} bd _ = bd north
-- -- -- -- -- -- -- -- northGlobeⁿ {ℓ} {A} {suc (suc n)} bd = north-south-const (bd north)

-- -- -- -- -- -- -- -- southGlobeⁿ {n = zero} bd = bd south
-- -- -- -- -- -- -- -- southGlobeⁿ {n = suc zero} bd _ = bd south
-- -- -- -- -- -- -- -- southGlobeⁿ {n = suc (suc n)} bd = north-south-const (bd south)

-- -- -- -- -- -- -- -- north-south-const {n = zero} a = refl
-- -- -- -- -- -- -- -- north-south-const {n = suc zero} a = refl
-- -- -- -- -- -- -- -- north-south-const {n = suc (suc n)} a = refl



-- -- -- -- -- -- -- -- -- NBoundary-≡-S relates Paths inside of S and NBoundary 

-- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n
-- -- -- -- -- -- -- -- --                   → PathP
-- -- -- -- -- -- -- -- --                     (λ i → (NBoundary-≡-S {n} i → A) → Type ℓ)
-- -- -- -- -- -- -- -- --                     InsideOf Globeⁿ

-- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ A zero = refl
-- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ {ℓ} A 1 i x =

-- -- -- -- -- -- -- -- --     x (coe0→i (λ j → NBoundary-≡-S {n = 1} j) i (lid false _))
-- -- -- -- -- -- -- -- --     ≡
-- -- -- -- -- -- -- -- --     x ((coe0→i (λ j → NBoundary-≡-S {n = 1} j) i (lid true _)))

-- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ {ℓ} A (suc (suc n)) i x = {!!}
 
-- -- -- -- -- -- -- -- --   {!!}  
                  
-- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- --     pred= : PathP (λ i₂ → (NBoundary-≡-S {n = suc n} i₂ → A) → Type ℓ)
-- -- -- -- -- -- -- -- --                 InsideOf
-- -- -- -- -- -- -- -- --                 Globeⁿ
-- -- -- -- -- -- -- -- --     pred= = InsideOf-≡-Globeⁿ {ℓ} A (suc n)

-- -- -- -- -- -- -- -- -- -- ( coei→0 (λ x₁ → NBoundary-≡-S {n = suc n} x₁ → A) i λ x₁ → {!!})

-- -- -- -- -- -- -- -- --     zzz :  ∀ jj → pred= i0 (λ x₁ → x (coe0→i (λ x₂ → NBoundary-≡-S {suc (suc n)} x₂) i (cyl x₁ jj)))
-- -- -- -- -- -- -- -- --                ≡ pred= i1 (λ x₁ → x (coe1→i (λ x₂ → NBoundary-≡-S {suc (suc n)} x₂) i (merid x₁ jj)))
-- -- -- -- -- -- -- -- --     zzz jj i = pred= i {!!}

-- -- -- -- -- -- -- -- --     zzz' :   I → (xx : ∀ ii → _ → NBoundary-≡-S {n = suc (suc n)} i) →
-- -- -- -- -- -- -- -- --                  PathP (λ x₁ → InsideOfₘ {n = suc zero} (inside x₁ , tt)
-- -- -- -- -- -- -- -- --                                           (λ x₂ x₃ → x (xx i0 (cyl x₃ x₁))))
-- -- -- -- -- -- -- -- --                   (insideOfCubeₘ {n = zero} (λ x₁ x₂ → x (xx i0 (lid false x₂))) (end false))
-- -- -- -- -- -- -- -- --                   (insideOfCubeₘ {n = zero} (λ x₁ x₂ → x (xx i0 (lid true x₂))) (end true))
-- -- -- -- -- -- -- -- --                ≡ PathP (λ x₁ → Globeⁿ (λ x₂ → x (xx i1 (merid x₂ x₁))))
-- -- -- -- -- -- -- -- --                    (northGlobeⁿ (λ x₁ → x (xx i1 x₁)))
-- -- -- -- -- -- -- -- --                    (southGlobeⁿ (λ x₁ → x (xx i1 x₁)))
-- -- -- -- -- -- -- -- --     zzz' jj xx i = pred= i λ x₁ → x (xx i x₁)

-- -- -- -- -- -- -- -- --     qqq : (jj ii : I) → NBoundary-≡-S₊ ii → NBoundary-≡-S jj
-- -- -- -- -- -- -- -- --     qqq = {!!}

-- -- -- -- -- -- -- -- --     ww : Type ℓ
-- -- -- -- -- -- -- -- --     ww = PathP (λ x₁ → zzz' x₁ (qqq i) i) {!!} {!!}

-- -- -- -- -- -- -- --     -- qq0 : (j₀ : I) → NCube 1 → NBoundary (suc n) → NBoundary-≡-S {suc (suc n)} i
-- -- -- -- -- -- -- --     -- -- 
-- -- -- -- -- -- -- --     -- qq0 j₀ x x₁ = {!!}

-- -- -- -- -- -- -- --     --    where

-- -- -- -- -- -- -- --     --    qqq1 : {!!} ≡ {!!}
-- -- -- -- -- -- -- --     --    qqq1 = {!!}

-- -- -- -- -- -- -- --     -- qq1 : (j₀ : I) → S (-1+ suc n) → NBoundary-≡-S {n = suc (suc n)} i
-- -- -- -- -- -- -- --     -- qq1 j₀ z = transport qqq1 (merid z j₀)

-- -- -- -- -- -- -- --     --    where

-- -- -- -- -- -- -- --     --    qqq1 : Susp (Susp (S (-1+ n))) ≡ NBoundary-≡-S {n = suc (suc n)} i
-- -- -- -- -- -- -- --     --    qqq1 i' = {!!}
       
-- -- -- -- -- -- -- --     -- -- qq1 j₀ x = fill1→i
-- -- -- -- -- -- -- --     -- --            (λ i₁ → NBoundary-≡-S {n = suc (suc n)} i₁)
               
-- -- -- -- -- -- -- --     -- --            (λ i₁ → λ {                  
-- -- -- -- -- -- -- --     -- --                   (j₀ = i0) → {!!}
-- -- -- -- -- -- -- --     -- --                 ; (j₀ = i1) → {!!}
-- -- -- -- -- -- -- --     -- --                })
-- -- -- -- -- -- -- --     -- --           (inS {!!}) i

-- -- -- -- -- -- -- --     -- ww : {!!}
-- -- -- -- -- -- -- --     -- ww = {!!}

-- -- -- -- -- -- -- --     -- pp : ∀ i₁ →
-- -- -- -- -- -- -- --     --        InsideOfₘ {k = suc n} (inside i₁ , tt) (λ x₁ → λ x₂ → x (qq0 i₁ x₁ x₂))
-- -- -- -- -- -- -- --     --        ≡
-- -- -- -- -- -- -- --     --        Globeⁿ (λ x₁ → x (qq1 i₁ x₁))
-- -- -- -- -- -- -- --     -- pp = {!!}

-- -- -- -- -- -- -- -- -- hcomp
-- -- -- -- -- -- -- -- --       (λ { j (i = i0) → NBoundary' boundaryInj
-- -- -- -- -- -- -- -- --          ; j (i = i1) → Susp (NBoundary-≡-S₊ j)
-- -- -- -- -- -- -- -- --          })
-- -- -- -- -- -- -- -- --       (Agda.Builtin.Cubical.Glue.primGlue (Susp (NBoundary' boundaryInj))
-- -- -- -- -- -- -- -- --        (λ .x₂ →
-- -- -- -- -- -- -- -- --           (λ { (i = i0)
-- -- -- -- -- -- -- -- --                  → NBoundary' boundaryInj ,
-- -- -- -- -- -- -- -- --                    isoToEquiv (Cubical.HITs.NCube.Base.lem n)
-- -- -- -- -- -- -- -- --              ; (i = i1)
-- -- -- -- -- -- -- -- --                  → Susp (NBoundary' boundaryInj) ,
-- -- -- -- -- -- -- -- --                    idEquiv (Susp (NBoundary' boundaryInj))
-- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- --           _ .fst)
-- -- -- -- -- -- -- -- --        (λ .x₂ →
-- -- -- -- -- -- -- -- --           (λ { (i = i0)
-- -- -- -- -- -- -- -- --                  → NBoundary' boundaryInj ,
-- -- -- -- -- -- -- -- --                    isoToEquiv (Cubical.HITs.NCube.Base.lem n)
-- -- -- -- -- -- -- -- --              ; (i = i1)
-- -- -- -- -- -- -- -- --                  → Susp (NBoundary' boundaryInj) ,
-- -- -- -- -- -- -- -- --                    idEquiv (Susp (NBoundary' boundaryInj))
-- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- --           _ .snd))






-- -- -- -- -- -- -- --   --    pp :     {!!}
-- -- -- -- -- -- -- --   --            ≡
-- -- -- -- -- -- -- --   --            {!!}
  
-- -- -- -- -- -- -- --   --    pp = {!!}
  
-- -- -- -- -- -- -- -- -- PathP (λ i₁ → Globeⁿ (λ x₁ → x (merid x₁ i₁))) (northGlobeⁿ x)
-- -- -- -- -- -- -- -- -- (southGlobeⁿ x)
-- -- -- -- -- -- -- -- --   = ?0 (i = i1)
-- -- -- -- -- -- -- -- --   : Set ℓ
-- -- -- -- -- -- -- -- -- PathP (λ i₁ → InsideOfₘ (inside i₁ , tt) (λ x₁ x₂ → x (cyl x₂ i₁)))
-- -- -- -- -- -- -- -- -- (insideOfCubeₘ (λ x₁ x₂ → x (lid false x₂)) (end false))
-- -- -- -- -- -- -- -- -- (insideOfCubeₘ (λ x₁ x₂ → x (lid true x₂)) (end true))
-- -- -- -- -- -- -- -- --   = ?0 (i = i0)
-- -- -- -- -- -- -- -- --   : Set ℓ



-- -- -- -- -- -- -- -- -- similar tests for arbitrary types

-- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical : ∀ {ℓ} → {A : Type ℓ} → ∀ n
-- -- -- -- -- -- -- -- --                     → (end0 : NCube n → A)
-- -- -- -- -- -- -- -- --                     → (end1 : NCube n → A)
-- -- -- -- -- -- -- -- --                     → (end0 ∘ boundaryInj ≡ end1 ∘ boundaryInj) 
-- -- -- -- -- -- -- -- --                     → NBoundary (suc n) → A
-- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical zero end0 end1 x (lid x₁ _) = caseBool end1 end0 x₁ _
-- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical (suc n) end0 end1 x (lid x₁ x₂) = caseBool end1 end0 x₁ x₂
-- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical (suc n) end0 end1 x (cyl x₁ i) = x i x₁



-- -- -- -- -- -- -- -- -- boundaryCase : ∀ {ℓ} → {A : Type ℓ} → ∀ n
-- -- -- -- -- -- -- -- --                     → {bd0 bd1 : NBoundary n → A}
-- -- -- -- -- -- -- -- --                     → (end0 : InsideOf bd0)
-- -- -- -- -- -- -- -- --                     → (end1 : InsideOf bd1)
-- -- -- -- -- -- -- -- --                     →    InsideOf→Cubical end0 ∘ boundaryInj
-- -- -- -- -- -- -- -- --                        ≡ InsideOf→Cubical end1 ∘ boundaryInj
-- -- -- -- -- -- -- -- --                     → NBoundary (suc n) → A
-- -- -- -- -- -- -- -- -- boundaryCase n end0 end1 cylinder x =
-- -- -- -- -- -- -- -- --        assembleBoundaryFromCubical n
-- -- -- -- -- -- -- -- --         (InsideOf→Cubical end0)
-- -- -- -- -- -- -- -- --         (InsideOf→Cubical end1)
-- -- -- -- -- -- -- -- --         (cylinder) x


-- -- -- -- -- -- -- -- -- makeCubeBoundary :
-- -- -- -- -- -- -- -- --     ∀ {ℓ} → {A : Type ℓ} →
-- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- --     →  NBoundary 3 → A
-- -- -- -- -- -- -- -- -- makeCubeBoundary a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
-- -- -- -- -- -- -- -- --     assembleBoundary 2
-- -- -- -- -- -- -- -- --         a₀₋₋ a₁₋₋
-- -- -- -- -- -- -- -- --         aa
-- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- --   aa :   InsideOf→Cubical {bd = makeSquareBoundary _ _ _ _} a₀₋₋ ∘ boundaryInj
-- -- -- -- -- -- -- -- --        ≡ InsideOf→Cubical {bd = makeSquareBoundary _ _ _ _} a₁₋₋ ∘ boundaryInj
-- -- -- -- -- -- -- -- --   aa i (lid x x₁) = {!x!}
-- -- -- -- -- -- -- -- --   aa i (cyl x i₁) = {!!}


-- -- -- -- -- -- -- -- -- -- cubeTest :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- -- --      → 
-- -- -- -- -- -- -- -- -- --        (Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) ≡
-- -- -- -- -- -- -- -- -- --        (InsideOf (makeCubeBoundary  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁))
-- -- -- -- -- -- -- -- -- -- cubeTest a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl

-- -- -- -- -- -- -- -- -- -- cubeTestHoles :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- --           (bd : NBoundaryIn A 3) →   
-- -- -- -- -- -- -- -- -- --           (Cube _ _ _ _ _ _) ≡
-- -- -- -- -- -- -- -- -- --           (InsideOf {A = A} {n = 3} bd)
-- -- -- -- -- -- -- -- -- -- cubeTestHoles bd = refl



-- -- -- -- -- -- -- -- -- -- cubeTest' :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- -- --      → 
-- -- -- -- -- -- -- -- -- --        (Cube {A = A} a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) ≡
-- -- -- -- -- -- -- -- -- --        (InsideOf {A = A} {3} (makeCubeBoundary  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁))
-- -- -- -- -- -- -- -- -- -- cubeTest' a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl










-- -- -- -- -- -- -- -- -- -- Boundaryⁿ : ∀ {ℓ} → (A : Type ℓ) → ℕ → Type ℓ

-- -- -- -- -- -- -- -- -- -- record BoundaryIn' {ℓ} {A : Type ℓ}
-- -- -- -- -- -- -- -- -- --         (X : A → Type ℓ) : Type ℓ where
-- -- -- -- -- -- -- -- -- --    constructor bdi

-- -- -- -- -- -- -- -- -- --    coinductive

-- -- -- -- -- -- -- -- -- --    field
-- -- -- -- -- -- -- -- -- --      {lid0Bd lid1Bd} : A
-- -- -- -- -- -- -- -- -- --      cylIn : lid0Bd ≡ lid1Bd
-- -- -- -- -- -- -- -- -- --      lid0 : X lid0Bd
-- -- -- -- -- -- -- -- -- --      lid1 : X lid1Bd

-- -- -- -- -- -- -- -- -- --    ins : Type ℓ
-- -- -- -- -- -- -- -- -- --    ins = PathP (λ x → X (cylIn x)) lid0 lid1

-- -- -- -- -- -- -- -- -- -- PPn : ∀ {ℓ} {A : Type ℓ} → ∀ {n} → Boundaryⁿ A n → Type ℓ

-- -- -- -- -- -- -- -- -- -- Boundaryⁿ A zero = Lift Unit
-- -- -- -- -- -- -- -- -- -- Boundaryⁿ A (suc zero) = A × A
-- -- -- -- -- -- -- -- -- -- Boundaryⁿ A (suc (suc n)) = BoundaryIn' {A = Boundaryⁿ A (suc n)} (λ x → PPn x)
-- -- -- -- -- -- -- -- -- -- --BoundaryIn' {A = Boundaryⁿ A n} (λ x → PPn x)
                                     

-- -- -- -- -- -- -- -- -- -- -- boundaryⁿ-Of = {!!}

-- -- -- -- -- -- -- -- -- -- PPn {A = A} {n = zero} x = A
-- -- -- -- -- -- -- -- -- -- PPn {A = A} {n = suc zero} x = proj₁ x ≡ proj₂ x
-- -- -- -- -- -- -- -- -- -- PPn {A = A} {n = suc (suc n)} x = BoundaryIn'.ins x


-- -- -- -- -- -- -- -- -- -- PPn-look : ∀ {ℓ} {A : Type ℓ} → ∀ {n} → ∀ {bd}
-- -- -- -- -- -- -- -- -- --            → PPn {A = A} {n} bd
-- -- -- -- -- -- -- -- -- --            → NCube n → A



-- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make : ∀ {ℓ} → {A : Type ℓ} → {n : ℕ} 
-- -- -- -- -- -- -- -- -- --                     → (NBoundary n → A) → Boundaryⁿ A n
-- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = zero} x = _
-- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = suc zero} x = (x (lid false _)) , (x (lid true _))
-- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = suc (suc zero)} x = bdi (λ i → Boundaryⁿ-make λ x₁ → x (cyl x₁ i))
-- -- -- -- -- -- -- -- -- --                                         (λ i → x (lid false (inside i , _)))
-- -- -- -- -- -- -- -- -- --                                        (λ i → x (lid true (inside i , _)))
-- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = suc (suc (suc n))} x = bdi ((λ i → Boundaryⁿ-make λ x₁ → x (cyl x₁ i)))
-- -- -- -- -- -- -- -- -- --                                             (λ i → Cubical→InsideOf (λ x₁ → {!!}) i)
-- -- -- -- -- -- -- -- -- --                                             λ i → {!!}


-- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look : ∀ {ℓ} → {A : Type ℓ} → {n : ℕ} → 
-- -- -- -- -- -- -- -- -- --                      Boundaryⁿ A n → NBoundary n → A
-- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = zero} x ()
-- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc zero} (x , _) (lid false _) = x 
-- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc zero} (_ , x) (lid true _) = x
-- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc (suc n)} x (lid x₁ y) = {!!}
-- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc (suc n)} x (cyl x₁ i) = {!!}


-- -- -- -- -- -- -- -- -- -- PPn-look {n = zero} x _ = x
-- -- -- -- -- -- -- -- -- -- PPn-look {n = suc zero} x (xx , _) = Iapp x xx
-- -- -- -- -- -- -- -- -- -- PPn-look {n = suc (suc n)} x (end x₁ , x₂) = PPn-look (x (Bool→I x₁)) x₂
-- -- -- -- -- -- -- -- -- -- PPn-look {n = suc (suc n)} x (inside i , x₂) = (PPn-look (x i)) x₂ 


-- -- -- -- -- -- -- -- -- -- -- -- eeeww :  ∀ {ℓ} {A : Type ℓ} → ∀ {n} →
-- -- -- -- -- -- -- -- -- -- -- --            Iso (NBoundary n → A) (Boundaryⁿ A n) 

-- -- -- -- -- -- -- -- -- -- -- -- lower (Iso.fun (eeeww {n = zero}) x) = _
-- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = zero}) x ()
-- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = zero}) (lift lower₁) = refl
-- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = zero}) a i ()

-- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (eeeww {n = suc zero}) x = (x (lid false _)) , (x (lid true _))
-- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc zero}) x (lid x₁ x₂) = caseBool (proj₂ x) (proj₁ x) x₁
-- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = suc zero}) (x , x₁) = refl
-- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc zero}) a i (lid false x₁) = a (lid false tt)
-- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc zero}) a i (lid true x₁) = a (lid true tt)

-- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (eeeww {n = suc (suc zero)}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc (suc zero)}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = suc (suc zero)}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc (suc zero)}) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (eeeww {n = suc (suc (suc n))}) x = bdi {!!} {!!} {!!} {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc (suc (suc n))}) x (lid x₁ x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc (suc (suc n))}) x (cyl x₁ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = suc (suc (suc n))}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc (suc (suc n))}) = {!!}





-- -- -- -- -- -- -- -- -- -- -- test-3-Type-holes-PP : ∀ {ℓ} {A : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- --                     (bd : Boundaryⁿ A 3) → 
-- -- -- -- -- -- -- -- -- -- --                      Cube _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- --                      ≡
-- -- -- -- -- -- -- -- -- -- --                        PPn {n = 3} bd
                       
-- -- -- -- -- -- -- -- -- -- -- test-3-Type-holes-PP bd = refl


-- -- -- -- -- -- -- -- -- -- -- test-3-Type-PP : 
-- -- -- -- -- -- -- -- -- -- --     ∀ {ℓ} → {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- --     → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
-- -- -- -- -- -- -- -- -- -- --       ≡
-- -- -- -- -- -- -- -- -- -- --       PPn {n = 3} ({!!})
-- -- -- -- -- -- -- -- -- -- -- test-3-Type-PP a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl






-- self∨ : I → I
-- self∨ x = x ∨ (~ x)

-- self∨' : Interval' → Interval'
-- self∨' (end x) = end true
-- self∨' (inside i) = inside (i ∨ ~ i)


-- _∨'_ : Interval' → Interval' → Interval'
-- end false ∨' end false = end false
-- end false ∨' end true = end true
-- end true ∨' _ = end true 
-- end false ∨' inside i = inside i
-- inside i ∨' end false = inside i
-- inside i ∨' end true = end true
-- _∨'_ (inside i) (inside i₁) = inside (i ∨ i₁)

-- _∧'_ : Interval' → Interval' → Interval'
-- end false ∧' end false = end false
-- end false ∧' end true = end false
-- end true ∧' end false = end false
-- end true ∧' end true = end true
-- end false ∧' inside i = end false
-- end true ∧' inside i = inside i
-- inside i ∧' end false = end false
-- inside i ∧' end true = inside i
-- _∧'_ (inside i) (inside i₁) = inside (i ∧ i₁)

-- ⋁ : ∀ {n} → NCube n → Interval'
-- ⋁ {zero} x = end false
-- ⋁ {suc n} (z , x₁) = z ∨' ⋁ x₁

-- ∼' : Interval' → Interval'
-- ∼' (end x) = end (not x)
-- ∼' (inside i) = inside (~ i)

-- ∼'' : ∀ {n} → NCube n → NCube n
-- ∼'' {zero} tt = _
-- ∼'' {suc n} (x , x₁) = ∼' x ,  (∼'' x₁)

-- -- brd : ∀ {n} → NCube n → Interval'
-- -- brd x = (⋁ x) ∨' ⋁ (∼'' x)

-- -- brd : ∀ {n} → NCube n → Interval'
-- -- brd {zero} tt = end false
-- -- brd {suc n} (z , x₁) = ((∼' z) ∨' z) ∨' brd x₁

-- brd : ∀ {n} → NCube n → Interval'
-- brd {zero} x = end false
-- brd {suc n} (end x , x₁) = end true
-- brd {suc n} (inside i , x₁) = (inside (self∨ i)) ∨' (brd x₁)

-- hcomp' : ∀ {ℓ} → {A : Type ℓ} → (i' : Interval') → (Interval' → A) → A 
-- hcomp' (end false) x = hcomp (λ i → empty) (x (end false))
-- hcomp' (end true) x = x (end true)
-- hcomp' (inside i) x = hcomp (λ j → λ {(i = i1) → x (inside j) }) (x (end false))
