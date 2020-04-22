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


boundaryEndMap : ∀ {n} → Bool → NBoundary n → NBoundary (suc n)
boundaryEndMap {n} x = lid x ∘ boundaryInj

cyl' : ∀ {n} → (bd : NBoundary (suc n)) →
               boundaryEndMap false bd ≡ boundaryEndMap true bd 
cyl' = cyl

lid' : ∀ {n} → Bool  → NCube n → NBoundary (suc n) 
lid' = lid


cyl'' : ∀ {n} → NBoundary n → Interval' → NBoundary (suc n)
cyl'' y (end x) = cyl y (Bool→I x)
cyl'' y (inside i) = cyl y i


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






-- Pathⁿ-typeBuilder and facePathⁿ-Builder  are recursively defined helpers for
-- constructing Pathⁿ Type, they should nevel "leak out" from Pathⁿ for
-- finite dimension , but facePathⁿ-Builder can be usefull for proving things for
-- arbitrary dimension of Paths

-- i could not convince agda to accept simplier definition of something like
-- Pathⁿ {n = suc n} bd = PathP (λ i → Pathⁿ {n} (λ (bd (cyl _ i)) ))
--                                  (bd ∘ lid false)
--                                  (bd ∘ lid true)
-- it worked for any finite dimension , but not for general case


Pathⁿ-typeBuilder : ∀ {ℓ} → ∀ {A : Type ℓ}
                  → ∀ {n} → ∀ {k}
                  → (c : NCube n)
                  → (bd : NCube n → NBoundary k → A)
                  → Type ℓ

facePathⁿ-Builder : ∀ {ℓ} → ∀ {A : Type ℓ}
                  →  ∀ {n} → ∀ {k}
                  → {c : NCube n}
                  → (bc : NCube n → NCube k → A)                  
                  → (i' : Interval')
                  → Pathⁿ-typeBuilder {n = suc n} {k} (i' , c) (λ x x₁ → bc c (boundaryInj x₁) )



Pathⁿ-typeBuilder {A = A} {n} {zero} c bd = A
Pathⁿ-typeBuilder {n = n} {suc k} c bd = PathP
                       (λ i → Pathⁿ-typeBuilder
                              {n = suc n} {k} (inside i , c) (λ x x₁ → bd c (cyl x₁ i)))
                       (facePathⁿ-Builder {c = c} (λ x x₁ → bd x (lid false x₁ )) (end false))
                       (facePathⁿ-Builder {c = c} (λ x x₁ → bd x (lid true x₁ )) (end true))



facePathⁿ-Builder {n = n} {zero} {c} bc i' = bc c _
facePathⁿ-Builder {n = n} {suc k} {c} bc i' i =
                        facePathⁿ-Builder {n = suc n} {k} {c = (i' , c)}
                         (λ x x₁ → bc c (inside i , x₁))
                         (inside i)




Pathⁿ : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (NBoundary n → A) → Type ℓ
Pathⁿ {ℓ} {A = A} {n-final} bd-final = Pathⁿ-typeBuilder {n = 0} {k = n-final} _ (λ _ → bd-final) 



faceⁿ : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n}
        → (k : ℕ) → (s : Bool) 
        → (bd : NBoundary (suc n) → A)
        → Pathⁿ (bd ∘ (faceInj k s) ∘ boundaryInj)
faceⁿ {n = zero} k s bd = bd (lid s _)
faceⁿ {n = suc n} k s bd i =
         facePathⁿ-Builder
         (λ x x₁ → bd (faceInj k s (inside i , x₁))) (inside i)

Cubical→Pathⁿ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                  → (c : NCube n → A)
                  → Pathⁿ (c ∘ boundaryInj)  
Cubical→Pathⁿ {n = zero} c = c _
Cubical→Pathⁿ {n = suc n} c i =
                  facePathⁿ-Builder
                  (λ x x₁ → (c (inside i , x₁))) (inside i)


Pathⁿ-typeBuilder→Cubi :
       ∀ {ℓ} → {A : Type ℓ}
      → ∀ {n} → ∀ {k}
      → (bd : NCube n → NBoundary k → A)          
      → {c : NCube n} → Pathⁿ-typeBuilder {A = _} {n = n} {k = k} (c) bd
      → NCube k → A
Pathⁿ-typeBuilder→Cubi {n = n} {zero} bd x x₁ = x
Pathⁿ-typeBuilder→Cubi {n = n} {suc k} bd x (end x₁ , x₂) =
                                   Pathⁿ-typeBuilder→Cubi _ (x (Bool→I x₁)) x₂
Pathⁿ-typeBuilder→Cubi {n = n} {suc k} bd x (inside i , x₂) =
                                   Pathⁿ-typeBuilder→Cubi _ (x i) x₂

Pathⁿ→Cubical : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                  → {bd : NBoundary n → A}
                  → Pathⁿ bd
                  → NCube n → A
Pathⁿ→Cubical {n = zero} x x₁ = x
Pathⁿ→Cubical {A = A} {n = suc n} {bd} x x₁ = Pathⁿ-typeBuilder→Cubi (λ _ x₃ → bd x₃) x x₁
 
    



nInside : ∀ n → Pathⁿ (boundaryInj {n})
nInside zero = _
nInside (suc n) i = facePathⁿ-Builder {n = 0} {k = n}
                             (λ x x₁ → inside i , x₁) (inside i)


-- those tests shows that Pathⁿ computes 'nicely'

test-3-Type : Cube
              (faceⁿ 0 false boundaryInj) (faceⁿ 0 true boundaryInj)
              (faceⁿ 1 false boundaryInj) (faceⁿ 1 true boundaryInj)
              (faceⁿ 2 false boundaryInj) (faceⁿ 2 true boundaryInj)
              ≡
              Pathⁿ (boundaryInj {3})
test-3-Type = refl

-- arguments for Cube and Square can be also infered

test-2-Type-holes : Square _ _ _ _
                    ≡
                    Pathⁿ (boundaryInj {2})
test-2-Type-holes = refl

test-3-Type-holes : Cube _ _ _ _ _ _
                    ≡
                    Pathⁿ (boundaryInj {3})
test-3-Type-holes = refl

test-6-term :  nInside 6
               ≡ 
               (λ i i₁ i₂ i₃ i₄ i₅ →
               inside i , inside i₁ , inside i₂ ,
               inside i₃ , inside i₄ , inside i₅ ,
               _)
test-6-term = refl


-- similar tests for arbitrary types

assembleBoundaryFromCubical : ∀ {ℓ} → {A : Type ℓ} → ∀ n
                    → (end0 : NCube n → A)
                    → (end1 : NCube n → A)
                    → (end0 ∘ boundaryInj ≡ end1 ∘ boundaryInj) 
                    → NBoundary (suc n) → A
assembleBoundaryFromCubical zero end0 end1 x (lid x₁ _) = caseBool end1 end0 x₁ _
assembleBoundaryFromCubical (suc n) end0 end1 x (lid x₁ x₂) = caseBool end1 end0 x₁ x₂
assembleBoundaryFromCubical (suc n) end0 end1 x (cyl x₁ i) = x i x₁



assembleBoundary : ∀ {ℓ} → {A : Type ℓ} → ∀ n
                    → {bd0 bd1 : NBoundary n → A}
                    → (end0 : Pathⁿ bd0)
                    → (end1 : Pathⁿ bd1)
                    →    Pathⁿ→Cubical end0 ∘ boundaryInj
                       ≡ Pathⁿ→Cubical end1 ∘ boundaryInj
                    → NBoundary (suc n) → A
assembleBoundary n end0 end1 cylinder x =
       assembleBoundaryFromCubical n
        (Pathⁿ→Cubical end0)
        (Pathⁿ→Cubical end1)
        (cylinder) x


makePathBoundary : ∀ {ℓ} → {A : Type ℓ}
                   → A → A
                   → NBoundary 1 → A
makePathBoundary x x₁ (lid x₂ x₃) = caseBool x₁ x x₂

makeSquareBoundary :
   ∀ {ℓ} → {A : Type ℓ} →
   {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
   {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
   (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → NBoundary 2 → A
makeSquareBoundary a₀₋ a₁₋ a₋₀ a₋₁ =
   assembleBoundary 1
      a₀₋ a₁₋
      aa
  where

  aa :    Pathⁿ→Cubical {bd = makePathBoundary _ _} a₀₋ ∘ boundaryInj
        ≡ Pathⁿ→Cubical {bd = makePathBoundary _ _} a₁₋ ∘ boundaryInj
  aa i (lid false x₁) = a₋₀ i
  aa i (lid true x₁) = a₋₁ i


-- makeCubeBoundary :
--     ∀ {ℓ} → {A : Type ℓ} →
--     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
--     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
--     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
--     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
--     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
--     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
--     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
--     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
--     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--     →  NBoundary 3 → A
-- makeCubeBoundary a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
--     assembleBoundary 2
--         a₀₋₋ a₁₋₋
--         aa
--   where

--   aa :   Pathⁿ→Cubical {bd = makeSquareBoundary _ _ _ _} a₀₋₋ ∘ boundaryInj
--        ≡ Pathⁿ→Cubical {bd = makeSquareBoundary _ _ _ _} a₁₋₋ ∘ boundaryInj
--   aa i (lid x x₁) = {!x!}
--   aa i (cyl x i₁) = {!!}


-- -- cubeTest :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- --      → 
-- --        (Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) ≡
-- --        (InsideOf (makeCubeBoundary  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁))
-- -- cubeTest a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl

-- -- cubeTestHoles :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- --           (bd : NBoundaryIn A 3) →   
-- --           (Cube _ _ _ _ _ _) ≡
-- --           (InsideOf {A = A} {n = 3} bd)
-- -- cubeTestHoles bd = refl



-- -- cubeTest' :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- --      → 
-- --        (Cube {A = A} a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) ≡
-- --        (Pathⁿ {A = A} {3} (makeCubeBoundary  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁))
-- -- cubeTest' a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl


-- this version of (Bool ≃ Susp ⊥) is consistent with convention of Interval' and  merid
-- (i0=false,i1=true)

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


-- another definition of n-path , inside Sn

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


-- Pathⁿ-≡-Globeⁿ {ℓ} A (suc (suc n)) i x = {!!}

-- Pathⁿ-≡-Globeⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n
--                   → PathP (λ i → (NBoundary-≡-S {n} i → A) → Type ℓ)
--                           Pathⁿ Globeⁿ

-- Pathⁿ-≡-Globeⁿ A zero = refl
-- Pathⁿ-≡-Globeⁿ {ℓ} A 1 i x = x {!!} ≡ x {!!}
-- Pathⁿ-≡-Globeⁿ {ℓ} A (suc (suc n)) i x =
--        PathP (λ j → {!Pathⁿ-≡-Globeⁿ A n i ?!})
--              {!!}
--              {!!}



