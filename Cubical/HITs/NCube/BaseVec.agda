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
open import Cubical.HITs.S1

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


-- this version of Bool≃Susp⊥' is consistent with convention in Interval'

Bool≃Susp⊥' : Bool ≃ Susp ⊥
Bool≃Susp⊥' =
  isoToEquiv
    (iso
      (λ {false  → north; true → south})
      (λ {north → false;  south → true})
      (λ {north → refl;  south → refl})
      (λ {true  → refl;  false → refl}))



-- Equality of NBoundary and Sn



-- NBoundary-≡-S₊ : ∀ {n} → NBoundary (suc n) ≡ S₊ n

-- NBoundary-≡-S₊-hlp : ∀ n →  Susp (NBoundary (suc n)) ≡ S₊ (suc n)
-- NBoundary-≡-S₊-hlp zero =
--    cong Susp NBoundary1-≡-Bool
--  ∙ isoToPath w
--   where
--     w : Iso (Susp Bool) (S₊ 1)
--     Iso.fun w north = base
--     Iso.fun w south = base
--     Iso.fun w (merid false i) = base
--     Iso.fun w (merid true i) = loop i
--     Iso.inv w base = north
--     Iso.inv w (loop i) = ((merid true) ∙ sym (merid false)) i 
--     Iso.rightInv w base = refl
--     Iso.rightInv w (loop i) i₁ = {!!}
--     Iso.leftInv w = {!!}
    
-- NBoundary-≡-S₊-hlp (suc n) = cong Susp NBoundary-≡-S₊ 

-- NBoundary-≡-S₊ {zero} = NBoundary1-≡-Bool 

-- NBoundary-≡-S₊ {suc n} = (isoToPath (lem) ) ∙ NBoundary-≡-S₊-hlp n 
--   where

--   lem : Iso (NBoundary' {suc n} _) (Susp _)
--   Iso.fun (lem) (lid false x₁) = north
--   Iso.fun (lem) (lid true x₁) = south
--   Iso.fun (lem) (cyl x i) = merid x i
--   Iso.inv (lem) north = lid false (corner0)
--   Iso.inv (lem) south = lid true (corner1)
--   Iso.inv (lem) (merid x i) =   ((cong (lid false) (corner0-≡ (boundaryInj x)))
--                               ∙∙ (cyl x)
--                               ∙∙ (cong (lid true) (≡-corner1 (boundaryInj x)))) i

--   Iso.rightInv (lem) north = refl
--   Iso.rightInv (lem) south = refl
--   Iso.rightInv (lem) (merid x i₁) i =
          
--          doubleCompPath-filler
--         (λ _ → north)
--         (λ j → doubleCompPath-filler
--                 (λ i₂ → merid (transp (λ _ → NBoundary (suc n)) ((~ i₂) ∨ i) x) (i₂ ∧ j))
--                 (λ i₂ → merid (transp ((λ _ → NBoundary (suc n))) i x)  j )
--                 (λ i₂ → merid (transp (λ _ → NBoundary (suc n)) ((~ i₂) ∧ i) x) (i₂ ∨  j))
--                 (~ i) j )
--         (λ _ → south)
--         (~ i) i₁

--   Iso.leftInv (lem) (lid false x₁) = cong (lid false) (corner0-≡ _)
--   Iso.leftInv (lem) (lid true x₁) = sym (cong (lid true) (≡-corner1 _))
--   Iso.leftInv (lem) (cyl x i₁) i =
--       doubleCompPath-filler
--         (cong (lid false) (corner0-≡ (boundaryInj x)))
--         (cyl x)
--         (cong (lid true) (≡-corner1 (boundaryInj x)))
--         (~ i) i₁

-- NBoundary-≡-S :  ∀ {n} → NBoundary n ≡ S (-1+ n)
-- NBoundary-≡-S {zero} = refl
-- NBoundary-≡-S {suc zero} = NBoundary-≡-S₊ ∙ {!!}
-- NBoundary-≡-S {suc (suc n)} = {!!}


--- equivalence parametrised by point on face

-- S₊-→-NBoundary-≡- : ∀ {n} → NCube n → S₊ n → NBoundary (suc n)
-- S₊-→-NBoundary-≡- x north = lid false x
-- S₊-→-NBoundary-≡- x south = lid true x
-- S₊-→-NBoundary-≡- x (merid a i) = {!!}
----





InsideOf : ∀ {ℓ}  → ∀ {n} → ∀ {A : Type ℓ}
                  → (bd : NBoundary n → A)
                  → Type ℓ

insideOf : ∀ {ℓ} → ∀ {n} → ∀ {A : Type ℓ}                  
                  → (bc : NCube n → A)                  
                  → InsideOf (bc ∘ boundaryInj)

InsideOf {n = zero} {A = A} bd = A
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

toCubical :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → ∀ {bd}
             → (InsideOf {n = n} {A = A} bd )
             → NCube n → A 
toCubical {n = zero} {bd} x x₁ = x
toCubical {n = suc n} {bd} x (end x₁ ∷ x₂) = toCubical (x (Bool→I x₁)) x₂
toCubical {n = suc n} {bd} x (inside i ∷ x₂) = toCubical (x i) x₂

NBoundary-rec :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
                 → (x0 x1 : NCube n → A)
                 → x0 ∘ boundaryInj ≡ x1 ∘ boundaryInj 
                 → NBoundary (suc n) → A 
NBoundary-rec x0 x1 x (lid x₁ x₂) = (caseBool x1 x0) x₁ x₂
NBoundary-rec x0 x1 x (cyl x₁ i) = x i x₁

NBoundary-elim :  ∀ {ℓ} → ∀ {n} → {A : NBoundary (suc n) → Type ℓ}
                 → (f : (b : Bool) → (c : NCube n) → A (lid b c))
                 → PathP (λ i → (bd : NBoundary n) → A (cyl bd i))
                       (f false ∘ boundaryInj)
                       (f true ∘ boundaryInj) 
                 → (bd : NBoundary (suc n)) → A bd 
NBoundary-elim f x (lid x₁ x₂) = f x₁ x₂
NBoundary-elim f x (cyl x₁ i) = x i x₁


NBoundary-app-Interval :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} →
                     (NBoundary (suc n) → A)
                   → (Σ (Interval' → (NBoundary n → A)) λ a → InsideOf (a (end false)) × InsideOf (a (end true))  )
NBoundary-app-Interval {n = zero} x =  (λ x₁ ()) , (x (lid false [])) , (x (lid true []))
NBoundary-app-Interval {n = suc n} x = (λ i →  x ∘ cyl'' i ) , (insideOf (x ∘ lid false )) , insideOf (x ∘ lid true )

NBoundary-rec-inv :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} →
                     (NBoundary (suc n) → A)
                   → (Σ ((NCube n → A) × (NCube n → A)) λ x0x1 → (fst x0x1) ∘ boundaryInj ≡ (snd x0x1) ∘ boundaryInj   )
NBoundary-rec-inv {n = zero} x = ((const (x (lid false []))) , (const (x (lid true [])))) , (funExt λ () )
NBoundary-rec-inv {n = suc n} x = ((x ∘ lid false) , (x ∘ lid true)) , funExt λ x₁ → (λ i → x (cyl x₁ i))



NBoundary-rec-Iso :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} →
                    Iso (NBoundary (suc n) → A)
                        (Σ ((NCube n → A) × (NCube n → A)) λ x0x1 → (fst x0x1) ∘ boundaryInj ≡ (snd x0x1) ∘ boundaryInj   )
Iso.fun NBoundary-rec-Iso = NBoundary-rec-inv
Iso.inv NBoundary-rec-Iso ((x0 , x1) , p) = NBoundary-rec x0 x1 p
fst (fst (Iso.rightInv (NBoundary-rec-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i)) [] = fst₁ []
snd (fst (Iso.rightInv (NBoundary-rec-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i)) [] = snd₂ []
snd (Iso.rightInv (NBoundary-rec-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i) i₁ ()


Iso.leftInv (NBoundary-rec-Iso {n = zero}) a i (lid false []) =  a (lid false [])
Iso.leftInv (NBoundary-rec-Iso {n = zero}) a i (lid true []) =  a (lid true [])

Iso.rightInv (NBoundary-rec-Iso {n = suc n}) b = refl

Iso.leftInv (NBoundary-rec-Iso {n = suc n}) a i (lid false x₁) = a (lid false x₁)
Iso.leftInv (NBoundary-rec-Iso {n = suc n}) a i (lid true x₁) = a (lid true x₁)
Iso.leftInv (NBoundary-rec-Iso {n = suc n}) a i (cyl x i₁) = a (cyl x i₁)



InsideOfP : ∀ {ℓ} → ∀ {n}
                  → (A : NCube n → Type ℓ)                  
                  → ((x : NBoundary n) → A (boundaryInj x))
                  → Type ℓ

insideOfP : ∀ {ℓ} → ∀ {n} →                   
                    {A : NCube n → Type ℓ}                  
                  → (x : ∀ c → A c)                  
                  → InsideOfP A (x ∘ boundaryInj)

InsideOfP {ℓ} {zero} A _ = A []
InsideOfP {ℓ} {suc n} A bd =
                      PathP
                       (λ i → InsideOfP (A i∷ i) (bd ∘ cylEx i))
                       (insideOfP (bd ∘ (lid false)) )
                       (insideOfP (bd ∘ (lid true)) )


insideOfP {n = zero} x = x []
insideOfP {n = suc n} x i = insideOfP (x i∷ i )


toCubicalP :  ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ} → ∀ {bd}
             → (InsideOfP {n = n} A bd )
             → (c : NCube n) → A c 
toCubicalP {n = zero} {bd} x [] = x
toCubicalP {n = suc n} {bd} x (end false ∷ x₂) = toCubicalP (x i0) x₂
toCubicalP {n = suc n} {bd} x (end true ∷ x₂) = toCubicalP (x i1) x₂
toCubicalP {n = suc n} {bd} x (inside i ∷ x₂) = toCubicalP (x i) x₂


NBoundaryP-rec :  ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ}
                 → (x0 : ∀ x → A (end false ∷ x))
                 → (x1 : ∀ x → A (end true ∷ x))
                 → PathP (λ i → ∀ x → A (inside i ∷ boundaryInj x)) (x0 ∘ boundaryInj) (x1 ∘ boundaryInj) 
                 → ∀ x → A (boundaryInj x) 
NBoundaryP-rec x0 x1 x (lid false x₂) = x0 x₂
NBoundaryP-rec x0 x1 x (lid true x₂) = x1 x₂
NBoundaryP-rec x0 x1 x (cyl x₁ i) = x i x₁

NBoundaryP-rec-inv :  ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ} →
                     ( ∀ x → A (boundaryInj x) )
                   → (Σ (( ∀ x → A (end false ∷ x)) × ( ∀ x → A (end true ∷ x)))
                           λ x0x1 → PathP (λ i →  ∀ x → A (inside i ∷ boundaryInj x)) ((fst x0x1) ∘ boundaryInj) ((snd x0x1) ∘ boundaryInj)   )
fst (fst (NBoundaryP-rec-inv {n = zero} x)) [] = x (lid false [])
snd (fst (NBoundaryP-rec-inv {n = zero} x)) [] = x (lid true [])
snd (NBoundaryP-rec-inv {n = zero} x) i ()
NBoundaryP-rec-inv {n = suc n} x = ((x ∘ lid false) , (x ∘ lid true)) , funExt λ x₁ → (λ i → x (cyl x₁ i))


NBoundaryP-rec-Iso :  ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ} →
                    Iso ( ∀ x → A (boundaryInj x) )
                        (Σ (( ∀ x → A (end false ∷ x)) × ( ∀ x → A (end true ∷ x)))
                           λ x0x1 → PathP (λ i →  ∀ x → A (inside i ∷ boundaryInj x))
                            ((fst x0x1) ∘ boundaryInj) ((snd x0x1) ∘ boundaryInj)   )
Iso.fun (NBoundaryP-rec-Iso {n = n} {A}) = NBoundaryP-rec-inv {n = n} {A = A}
Iso.inv (NBoundaryP-rec-Iso {n = n} {A}) ((x0 , x1) , p) = NBoundaryP-rec {n = n} {A = A} x0 x1 p

fst (fst (Iso.rightInv (NBoundaryP-rec-Iso {n = zero} {A}) (fst₁ , snd₁) i)) [] = fst fst₁ []
snd (fst (Iso.rightInv (NBoundaryP-rec-Iso {n = zero} {A}) (fst₁ , snd₁) i)) [] = snd fst₁ []
snd (Iso.rightInv (NBoundaryP-rec-Iso {n = zero} {A}) b i) i₁ ()

fst (fst (Iso.rightInv (NBoundaryP-rec-Iso {n = suc n} {A}) (fst₁ , snd₁) i)) = fst fst₁
snd (fst (Iso.rightInv (NBoundaryP-rec-Iso {n = suc n} {A}) (fst₁ , snd₁) i)) = snd fst₁
snd (Iso.rightInv (NBoundaryP-rec-Iso {n = suc n} {A}) (fst₁ , snd₁) i) i₁ = snd₁ i₁ 

Iso.leftInv (NBoundaryP-rec-Iso {n = zero} {A}) a i (lid false []) = a (lid false [])
Iso.leftInv (NBoundaryP-rec-Iso {n = zero} {A}) a i (lid true []) = a (lid true [])

Iso.leftInv (NBoundaryP-rec-Iso {n = suc n} {A}) a = funExt z

  where
    z : _
    z (lid false x₁) = refl
    z (lid true x₁) = refl
    z (cyl x i) = refl




NInsideP-map : ∀ {ℓ} → ∀ n → {A : NCube n → Type ℓ} → {B : NCube n → Type ℓ}
                      → (f : ∀ cu → A cu → B cu)
                      → (bd : ∀ x → A (boundaryInj x))
                      → InsideOfP A bd
                      → Σ ((x : NBoundary n) → B (boundaryInj x)) (InsideOfP B )
NInsideP-map zero f bd x = (λ ()) , f [] x
-- NInsideP-map (suc zero) {A = A} {B} f bd x = {!!}
NInsideP-map (suc n) {A = A} {B} f bd x = 
  let  z : (i : I) → Σ ((x₁ : NBoundary n) → B (inside i ∷ boundaryInj x₁))
                       (InsideOfP (λ z → B (inside i ∷ z)))
       z i = NInsideP-map n {A = A i∷ i} (λ cu₁ x₁ → f (inside i ∷ cu₁) x₁) (λ x₁ → bd (cylEx i x₁)) (x i)  

  in -- NBoundaryP-rec  {A = B} {! !} {!!} (λ i x₁ → fst (z i) x₁)  , (λ i → snd (z i))
      NBoundaryP-rec  {A = B} (toCubicalP (snd (z i0))) (toCubicalP (snd (z i1))) (λ i x₁ → {!fst (z i) x₁!}) , {!!}





-- NInsideP-rec-Iso : ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ}
--                   → (bd : ∀ x → A (boundaryInj x))
--                   → Iso
--                      (InsideOfP A bd)
--                      (PathP {!!} {!!} {!!})
-- NInsideP-rec-Iso = {!!}

-- -- OnBoundary : ∀ {n} → NCube n → Type₀
-- -- OnBoundary c = Σ[ bd ∈ NBoundary _ ] (c ≡ boundaryInj bd)


-- -- OnBoundary-property : ∀ {n} → (x : ∀ c → (OnBoundary {n} c))
-- --                             → {!∀ y →  !} → ⊥
-- -- OnBoundary-property = {!!}

-- -- -- zz : (c : NCube 1) → (OnBoundary {1} c)
-- -- -- zz (end false ∷ []) = (lid false []) , refl
-- -- -- zz (end true ∷ []) = lid false [] , λ i → (inside (~ i) ∷ [])
-- -- -- zz (inside i ∷ []) = (lid false []) , λ i₁ → inside {!!} ∷ []

-- -- OnBoundary-property1 : (x : ∀ (c : NCube 1) → (OnBoundary {1} c))
-- --                          → (∀ y → (fst ∘ x ∘ boundaryInj) y ≡ y ) → ⊥
-- -- OnBoundary-property1 x z = 
-- --   let zz : (fst ∘ x ∘ boundaryInj) (lid false [])  ≡ lid false []
-- --       zz = (z (lid false []))

-- --       zz1 : {!!}
-- --       zz1 = {!!}
-- --   in {!!}


-- slice : ∀ {ℓ} → ∀ {n k}
--         → {A : NCube (k + n) → Type ℓ}
--         → ∀ bd
--         → InsideOfP A bd 
--          → (y : NCube k)
--          → Σ ((x : NBoundary n) → A (y ++ boundaryInj x))
--              (InsideOfP ( A ∘ (y ++_))) 
-- slice {k = zero} bd x [] = bd , x
-- slice {k = suc k} bd x (end false ∷ y) = slice {k = k} (bd ∘ cylEx i0) (x i0) y
-- slice {k = suc k} bd x (end true ∷ y) = slice {k = k} (bd ∘ cylEx i1) (x i1) y
-- slice {k = suc k} bd x (inside i ∷ y) = slice {k = k} (bd ∘ cylEx i) (x i) y
  

-- sliceInside : ∀ {ℓ} → ∀ {n k}
--         → (A : NCube (k + n) → Type ℓ)
--         → ∀ bd → (x : InsideOfP A bd)
--         → InsideOfP {n = k}
--            (λ y → Σ ((x : NBoundary n) → A (y ++ boundaryInj x))
--              (InsideOfP ( A ∘ (y ++_))))
--                ((slice bd x) ∘ boundaryInj)
-- sliceInside {n = n} {k = k} A bd x =
--    insideOfP
--      {A = λ y → Σ ((x : NBoundary n) → A (y ++ (boundaryInj x)))
--              (InsideOfP ( A ∘ (y ++_)))}
--      (slice bd x)


-- -- InsideOfω→Cub : ∀ {ℓ} → ∀ {n} → {A : T[ CType ℓ n ]}
-- --                      → (bd : T[ Boundaryω n A ])
-- --                      → T[ InsideOfω n bd ]
-- --                      → (c : NCube n)
-- --                      → CType-ev n A c
-- -- InsideOfω→Cub {n = n} bd x = from-cu (outSⁿ n x)


-- -- InsideOfω→InsideOf : ∀ {ℓ} → ∀ {n} → {A : T[ CType ℓ n ]}
-- --                      → (bd : T[ Boundaryω n A ])
-- --                      → T[ InsideOfω n bd ]
-- --                      → Σ _ (InsideOfP (CType-ev n A))
-- -- InsideOfω→InsideOf {n = n} bd x =
-- --    (InsideOfω→Cub bd x ∘ boundaryInj)
-- --  , insideOfP (InsideOfω→Cub {n = n} bd x)


-- cubePΣ-Ty : ℕ → Typeω 
-- cubePΣ-Ty n = 
--            Σω T[ Boundaryω n Ct[ n , const (NCube n) ] ]
--                 λ x → T[ InsideOfω n x ]
                



-- -- cubePΣ : ∀ n → cubePΣ-Ty n
-- -- fstω (cubePΣ zero) ()
-- -- sndω (cubePΣ zero) = inS []
-- -- fstω (cubePΣ (suc zero)) i =
-- --    λ { (i = i0) → end false ∷  [] ;
-- --        (i = i1) → end true ∷  [] }
-- -- sndω (cubePΣ (suc zero)) i = inS (inside i ∷ [])
-- -- cubePΣ (suc (suc n'')) = cubeP-step n'' (cubePΣ (suc n''))
-- --   where

-- --   cubeP-step : ∀ n' → (cubePΣ-Ty (suc n')) → (cubePΣ-Ty (suc (suc n'))) 
-- --   cubeP-step n' prev =
-- --      (Partialⁿ-attach-Ends' n
-- --        (λ j → Partialⁿ-map→ n (paⁿ n (cu→[ n , const (inside j ∷_) ])) (fstω prev))
-- --        s)
-- --      ,ω
-- --       Subⁿ-attach-Ends n _ s

-- --      where
-- --        n = suc n'

-- --        s : _
-- --        s j = Subⁿ-map' n (const (inside j ∷_)) (fstω prev) (sndω prev)


-- -- cubeP : ∀ n → T[ Boundaryω n Ct[ n , const (NCube n) ] ]
-- -- cubeP n = fstω (cubePΣ n)

-- -- Snω : ∀ n → ωType
-- -- Snω n = Boundaryω n Ct[ n , const (S (-1+ n)) ]


-- -- snω : ∀ n → T[ Snω n ]
-- -- snω zero ()
-- -- snω (suc zero) i = 
-- --      λ { (i = i0) → north ;
-- --          (i = i1) → south }
-- -- snω (suc (suc n')) = Snω-step n' (snω (suc n'))

-- --   where

-- --     Snω-step : ∀ n → T[ Snω (suc n) ]
-- --                           → T[ Snω (suc (suc n)) ] 
-- --     Snω-step n' prev = 
-- --        Partialⁿ-attach-Ends n prev-cyl (end0) (end1) 

-- --        where
-- --          n = suc n'

-- --          prev-cyl : (j : I) →
-- --                       T[
-- --                       Partialⁿ n (boundaryExpr n)
-- --                       (λ z → Ct[ suc n , const (S (-1+ (suc n))) ] j z)
-- --                       ]
-- --          prev-cyl i = Partialⁿ-map→ n ((paⁿ n (cu→[ n , f ]))) prev
-- --             where

-- --             f : (c : NCube n) → (S (-1+ n)) → (S (-1+ (suc n)))
-- --             f _ x = merid x i 

-- --          end0 : T[ Subⁿ n (λ z → boundaryExpr n z) (prev-cyl i0) ]
-- --          end0 = inSⁿ→-const n (boundaryExpr n)
-- --                       (const (S (-1+ n))) (λ v → Susp (S (ℕ→ℕ₋₁ n'))) (prev) (const north)

-- --          end1 : T[ Subⁿ n (λ z → boundaryExpr n z) (prev-cyl i1) ]
-- --          end1 = inSⁿ→-const n (boundaryExpr n)
-- --                       (const (S (-1+ n))) (λ v → Susp (S (ℕ→ℕ₋₁ n'))) (prev) (const south)


-- -- -- nBoundaryω : ∀ n → T[ NBoundaryω n ]
-- -- -- nBoundaryω zero ()
-- -- -- nBoundaryω (suc n) =
-- -- --   Partialⁿ-map→ (suc n)
-- -- --       (paⁿ (suc n) cu→[ (suc n) , const (transport (sym NBoundary-≡-S₊)) ]) (snω (suc n))

-- -- NBoundaryω : ∀ n → ωType
-- -- NBoundaryω n = Boundaryω n Ct[ n , const (NBoundary n) ]


-- -- NBoundaryωΣ : ∀ n → Typeω
-- -- NBoundaryωΣ n =    Σω T[ NBoundaryω n ]
-- --                 λ x → T[ InsideOfω n (Partialⁿ-map→ n (paⁿ n cu→[ n , const boundaryInj ]) x) ]


-- -- NBoundaryω-step : ∀ n → (i' : I) → T[ NBoundaryω (suc n) ]
-- --                       → T[ NBoundaryω (suc (suc n)) ] 
-- -- NBoundaryω-step n' i' prev = 
-- --    Partialⁿ-attach-Ends n (prev-cyl i') (end0 i') (end1 i') 

-- --    where
-- --      n = suc n'


-- --      -- i' = 1 - cylinder is pretty
-- --      prev-cyl : I → (j : I) →
-- --                   T[
-- --                   Partialⁿ n (boundaryExpr n)
-- --                   (λ z → Ct[ suc n , const (NBoundary (suc n)) ] j z)
-- --                   ]
-- --      prev-cyl i' i = Partialⁿ-map→ n ((paⁿ n (cu→[ n , f ]))) prev
-- --         where

-- --         f : (c : NCube n) → NBoundary n → NBoundary (suc n)
-- --         f c = doubleCompPath-filler
-- --                   ((λ i₁ x →  lid false (isPropCube c (boundaryInj x) i₁)))
-- --                   cylEx
-- --                   (λ i₁ x → lid true (isPropCube (boundaryInj x) c i₁))
-- --                   (~ i')
-- --                   i
        
-- --      ends : (b : Bool) →  T[ InsideOfω n _ ]
-- --      ends b = inSⁿ→-const n (boundaryExpr (suc n'))
-- --               (const (NBoundary n))
-- --               (const (NBoundary (suc n)))
-- --                prev (lid' b)

-- --      -- i' = 0 - lids are pretty
-- --      end0 : (i' : I) → T[ Subⁿ n (boundaryExpr n) (prev-cyl i' i0) ]
-- --      end0 i' = hfillⁿ n s=' (ends false) (i')

-- --        where
-- --          s=' : (j : I) → T[
-- --                           Partialⁿ n (boundaryExpr n)
-- --                           (Ct[ n , const (NBoundary (suc n)) ])
-- --                           ]
-- --          s=' j =
-- --                   Partialⁿ-map→ n
-- --                         (paⁿ n (cu→[ n , (λ c x → lid' false ((isPropCube c (boundaryInj x) j)) ) ]))
-- --                         prev

-- --      end1 : (i' : I) → T[ Subⁿ n (boundaryExpr n) (prev-cyl i' i1) ]
-- --      end1 i' = hfillⁿ n s=' (ends true) (i')

-- --        where
-- --          s=' : (j : I) → T[
-- --                           Partialⁿ n (boundaryExpr n)
-- --                           (Ct[ n , const (NBoundary (suc n)) ])
-- --                           ]
-- --          s=' j = Partialⁿ-map→ n
-- --                 (paⁿ n cu→[ n , (λ c x → lid' true ((isPropCube (boundaryInj x) c (~ j)))) ])
-- --                 prev


-- -- nBoundaryω : ∀ n → T[ NBoundaryω n ]
-- -- nBoundaryω zero ()
-- -- nBoundaryω (suc zero) i =
-- --   λ { (i = i0) → lid false [] ;
-- --       (i = i1) → lid true [] }
-- -- nBoundaryω (suc (suc n)) i =
-- --   NBoundaryω-step n
-- --   i0
-- --   (nBoundaryω (suc n)) i

-- -- nBoundaryω-coh : ∀ n → ℕ → Bool → (NCube n) → Type₀
-- -- nBoundaryω-coh n k b c = 
-- --                      from-cu' {n = n} (Boundaryω-getFace' n k b (nBoundaryω (suc n))) c
-- --                        ≡
-- --                      faceInj k b c



-- -- -- problemWith-nBoundaryω : ∀ i₀ i₁ i₂ i₃ →
-- -- --                           nBoundaryω-coh 4 2 false
-- -- --                             (inside i₀  ∷ inside i₁ ∷ inside i₂ ∷ inside i₃  ∷ [] )
-- -- -- problemWith-nBoundaryω i₀ i₁ i₂ i₃ = {!refl!}

-- -- nBoundaryω'-Ty : ℕ → ωType
-- -- nBoundaryω'-Ty zero = NBoundaryω zero
-- -- nBoundaryω'-Ty (suc n) = Cuω (NBoundaryω (suc n)) n 


-- -- nBoundaryω' : ∀ n → T[ nBoundaryω'-Ty n ]
-- -- nBoundaryω' zero ()
-- -- nBoundaryω' (suc zero) = nBoundaryω 1
-- -- nBoundaryω' (suc (suc n)) i =
-- --    map-Cuω (NBoundaryω-step n i) n (nBoundaryω' (suc n))


-- -- nBoundaryω-coh-test : ∀ i₀ i₁ i₂ i₃ →
-- --                           nBoundaryω-coh 4 2 false
-- --                             (inside i₀  ∷ inside i₁ ∷ inside i₂ ∷ inside i₃  ∷ [] )
-- -- nBoundaryω-coh-test i₀ i₁ i₂ i₃ i =
-- --    let c =  (inside i₀  ∷ inside i₁ ∷ inside i₂ ∷ inside i₃  ∷ [] )
-- --        y = nBoundaryω' 5 i i i0 i0
-- --    in 
-- --       from-cu' (Boundaryω-getFace' 4 2 false y) c 



-- -- from-Boundaryω : ∀ {ℓ} → ∀ n → (A : T[ CType ℓ n ])
-- --            → T[ Boundaryω n A ]
-- --            → (bd : NBoundary n)
-- --            → CType-ev n A (boundaryInj bd)  
-- -- from-Boundaryω (suc zero) A x (lid false x₂) = x i0 1=1
-- -- from-Boundaryω (suc zero) A x (lid true x₂) = x i1 1=1
-- -- from-Boundaryω (suc (suc n)) A x =
-- --   NBoundary-elim
-- --    (λ b → from-cu (Boundaryω-getLid (suc n) b A x))
-- --    λ i bd → let zz = from-Boundaryω (suc n) _ (Boundaryω-getCyl (suc n) x) bd

-- --              in CType-ev-elim (suc n)
-- --                          {A = (λ c →
-- --                                  PathP (λ x₁ → CType-ev (suc (suc n)) A (inside x₁ ∷ c))
-- --                                  (from-cu (Boundaryω-getLid (suc n) false A x) c)
-- --                                  (from-cu (Boundaryω-getLid (suc n) true A x) c))}
-- --                          (boundaryInj bd) zz i 


-- -- NBoundaryω-Iso-Ty : ∀ n → Typeω
-- -- NBoundaryω-Iso-Ty n = ∀ {ℓ} → (A : NCube n → Type ℓ)
-- --                         → Isoω ((bd : NBoundary n) → (A ∘ boundaryInj) bd )
-- --                                (Boundaryω n Ct[ n , A ])

-- -- -- NBoundaryω-Iso : ∀ n → NBoundaryω-Iso-Ty n
-- -- -- Isoω.to (NBoundaryω-Iso n A) x =
-- -- --   Partialⁿ-map→ n (paⁿ n cu→[ n , (λ c x₁ → subst A (isPropCube _ _) (x x₁)) ]) (nBoundaryω n)

-- -- -- Isoω.from (NBoundaryω-Iso n A) x bd = CType-ev-elim n _ (from-Boundaryω n Ct[ n , A ] x bd)

-- -- -- Isoω.sec (NBoundaryω-Iso n A) = {!!}

-- -- -- Isoω.ret (NBoundaryω-Iso n A) = {!!}


-- -- from-Boundaryω' : ∀ {ℓ} → ∀ n → {A : NCube n → Type ℓ}
-- --                         → ((bd : NBoundary n) → (A ∘ boundaryInj) bd )
-- --                         → T[ (Boundaryω n Ct[ n , A ]) ]
-- -- from-Boundaryω' n {A = A} x =
-- --  Partialⁿ-map→ n (paⁿ n cu→[ n , (λ c x₁ → subst A (isPropCube _ _) (x x₁)) ]) (nBoundaryω n) 

-- -- to-Boundaryω : ∀ {ℓ} → ∀ n → {A : NCube n → Type ℓ}
-- --                        → T[ (Boundaryω n Ct[ n , A ]) ]
-- --                        → ((bd : NBoundary n) → (A ∘ boundaryInj) bd )
                        
-- -- to-Boundaryω  n {A = A} x bd = CType-ev-elim n _ (from-Boundaryω n Ct[ n , A ] x bd)



-- -- CC : Level → ℕ → ωType
-- -- T[_] (CC ℓ n) = Σω T[ CType ℓ n ] λ A → Σω T[ Boundaryω n A  ] λ bd → T[ InsideOfω n bd ]
-- -- (CC ℓ n ωType.≡ω x₁) x₂ =
-- --    Liftω (Σ[ A= ∈ CType-ev n (fstω x₁) ≡ CType-ev n (fstω x₂) ]
-- --           Σ[ bd= ∈ {!!} ]
-- --           {!!} ) 
-- -- ωType.symω (CC ℓ n) = {!!}
-- -- ωType._transω_ (CC ℓ n) = {!!}

-- -- IsoIns : ∀ n → ∀ {ℓ} →
-- --                Isoω
-- --                 (Σ[ A ∈ (NCube n → Type ℓ) ] Σ[ bd ∈ (∀ x → (A ∘ boundaryInj) x ) ] InsideOfP A bd )
-- --                 (CC ℓ n)  
-- -- IsoIns zero = {!!}
-- -- IsoIns (suc n) = {!!}

-- -- -- InsideOf→InsideOfω : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ}
-- -- --                      → (bd : ∀ x → (A ∘ boundaryInj) x )
-- -- --                      → (InsideOfP A bd)
-- -- --                      → T[ InsideOfω n (from-Boundaryω' n {A = A} bd) ]
-- -- -- InsideOf→InsideOfω {n = zero} bd x = inS x
-- -- -- InsideOf→InsideOfω {n = suc zero} {A = A} bd x i = {!!}

-- -- -- InsideOf→InsideOfω {n = suc (suc n)} bd x i = {!x!}



-- -- -- InsideOfω→InsideOf : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ}
-- -- --                      → (bd : ∀ x → (A ∘ boundaryInj) x )
-- -- --                      → T[ InsideOfω n (from-Boundaryω' n {A = A} bd) ]
-- -- --                      → (InsideOfP A bd)
-- -- -- InsideOfω→InsideOf {n = zero} bd x = outS x
-- -- -- InsideOfω→InsideOf {n = suc zero} {A = A} bd x i = {!x i!}


-- -- -- InsideOfω→InsideOf {n = suc (suc n)} bd x i =
-- -- --   let zz = InsideOfω→InsideOf (bd ∘ cylEx i) {!sidesPath-Sub ? ? x i !}

-- -- --       z = {!sidesPath-Sub (suc n) ? !}
-- -- --   in InsideOfω→InsideOf {n = (suc n)} (bd ∘ cylEx i) z



-- -- -- hcompIns : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ}
-- -- --            → (sides : I → (x : NBoundary n) → (A ∘ boundaryInj) x)
-- -- --            → InsideOfP A (sides i0)
-- -- --            → InsideOfP A (sides i1)
-- -- -- hcompIns {n = n} sides x =
-- -- --   let z = hcompⁿ n (λ j → from-Boundaryω' n (sides j)) (InsideOf→InsideOfω (sides i0) x)
-- -- --   in InsideOfω→InsideOf (sides i1) z

-- -- -- hfillIns : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ}
-- -- --            → (sides : I → (x : NBoundary n) → (A ∘ boundaryInj) x)
-- -- --            → InsideOfP A (sides i0)
-- -- --            → (i : I) → InsideOfP A (sides i)
-- -- -- hfillIns {n = n} sides x i =
-- -- --   let z = hfillⁿ n (λ j → from-Boundaryω' n (sides j)) (InsideOf→InsideOfω (sides i0) x) i
-- -- --   in InsideOfω→InsideOf (sides i) z


-- -- -- lem1 : ∀ {n} → ∀ {ℓ} → {A : NCube n → Type ℓ}
-- -- --            → (bd : ∀ x →  (A ∘ boundaryInj) x)
-- -- --            → (x : InsideOfP A bd)
-- -- --            → (toCubicalP x) ∘ boundaryInj ≡ bd
-- -- -- lem1 {zero} bd x i ()
-- -- -- lem1 {1} bd x i (lid false []) = bd (lid false [])
-- -- -- lem1 {1} bd x i (lid true []) = bd (lid true [])
-- -- -- lem1 {suc (suc n)} {A = A} bd x = funExt h 

-- -- --   where

-- -- --     h0 : (b : Bool) (c : NCube (suc n)) →
-- -- --            (toCubicalP {A = A} {bd = bd} x ∘ boundaryInj) (lid' b c) ≡ bd (lid' b c)
-- -- --     h0 = {!!}
    
-- -- --     h1 : {!!}
-- -- --     h1 = {!!}

-- -- --     h : (x₁ : NBoundary (suc (suc n))) →
-- -- --           (toCubicalP x ∘ boundaryInj) x₁ ≡ bd x₁
-- -- --     h = NBoundary-elim h0 h1

-- -- --   -- NBoundary-elim {A = {!!}}
-- -- --   --  {!!} --(λ b → toCubicalP {A = A ∘ (end b ∷} (x (Bool→I b)))
-- -- --   --  {!!} --(λ i₁ bd₁ → (toCubicalP {A = A i∷ i₁} (x i₁)) (boundaryInj bd₁))
-- -- --   --  y

-- -- -- ISO-INS : ∀ n → ∀ {ℓ} → (A : NCube n → Type ℓ)
-- -- --            → (bd : ∀ x → (A ∘ boundaryInj) x)
-- -- --            → Iso (InsideOfP A bd) (Σ[ cu ∈ (∀ x → A x) ] cu ∘ boundaryInj ≡ bd) 
-- -- -- Iso.fun (ISO-INS n A bd) x = (toCubicalP x) , {!!}

-- -- -- Iso.inv (ISO-INS n A bd) x = hcompIns (λ j → snd x j) (insideOfP {A = A} (fst x))

-- -- -- Iso.rightInv (ISO-INS n A bd) = {!!}
-- -- -- Iso.leftInv (ISO-INS n A bd) = {!!}



   
-- -- -- -- -- --





-- -- -- -- -- dcpp : ∀ {ℓ} → (A : I → Type ℓ) → (A0 A1 : Type ℓ)
-- -- -- -- --             → (A0= : A i0 ≡ A0) → (A1= : A i1 ≡ A1)
-- -- -- -- --             → (a0 : A i0) → (a1 : A i1) → (a00 : A0) → (a11 : A1)
-- -- -- -- --             → PathP (λ x → A0= x) a0 a00
-- -- -- -- --             → PathP A a0 a1
-- -- -- -- --             → PathP ((λ x → A1= x)) a1 a11
-- -- -- -- --             → PathP
-- -- -- -- --                 (λ x → (sym A0= ∙∙ (λ i → A i) ∙∙ A1=) x)
-- -- -- -- --                   a00 a11
-- -- -- -- -- dcpp A A0 A1 A0= A1= a0 a1 a00 a11 x x₁ x₂ i =
-- -- -- -- --   comp (λ i₁ → doubleCompPath-filler (sym A0=) (λ i → A i) A1= i₁ i )
-- -- -- -- --   (λ k → λ { (i = i0) → x k ; (i = i1) → x₂ k })
-- -- -- -- --   (x₁ i)

-- -- -- -- -- dcpp' : ∀ {ℓ} → {A : I → Type ℓ}
-- -- -- -- --             → {a0 : A i0} → {a1 : A i1} → {a00 : A i0} → {a11 : A i1}
-- -- -- -- --             → a0 ≡ a00
-- -- -- -- --             → PathP A a0 a1
-- -- -- -- --             → a1 ≡ a11
-- -- -- -- --             → PathP
-- -- -- -- --                 (λ x → A x)
-- -- -- -- --                   a00 a11
-- -- -- -- -- dcpp'  x x₁ x₂ i =
-- -- -- -- --  hcomp (λ k → λ {
-- -- -- -- --       (i = i0) → x k
-- -- -- -- --     ; (i = i1) → x₂ k
-- -- -- -- --     }) (x₁ i) 





-- -- -- -- -- -- -- -- injBack : ∀ n → T[ injBackTy n ]
-- -- -- -- -- -- -- -- injBack zero () _
-- -- -- -- -- -- -- -- injBack (suc zero) i =
-- -- -- -- -- -- -- --   λ { (i = i0) → lid false ∘ tail ;
-- -- -- -- -- -- -- --       (i = i1) → lid true ∘ tail }
-- -- -- -- -- -- -- -- injBack (suc (suc n)) i = {!!}

-- -- -- -- -- -- -- -- NBoundaryωΣ-step : ∀ n → NBoundaryωΣ (suc n)
-- -- -- -- -- -- -- --                        → NBoundaryωΣ (suc (suc n)) 
-- -- -- -- -- -- -- -- NBoundaryωΣ-step n' prev =
-- -- -- -- -- -- -- --     Partialⁿ-attach-Ends' n prevP prevS
-- -- -- -- -- -- -- --    ,ω (Subⁿ-map' (suc n)
-- -- -- -- -- -- -- --           (const boundaryInj) _
-- -- -- -- -- -- -- --            (Subⁿ-attach-Ends n {e = boundaryExpr n} prevP prevS))
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --     n = suc n'

-- -- -- -- -- -- -- --     -- prev-cyl : (j : I) →
-- -- -- -- -- -- -- --     --              T[
-- -- -- -- -- -- -- --     --              Partialⁿ n (boundaryExpr n)
-- -- -- -- -- -- -- --     --              (λ z → Ct[ suc n , const (NBoundary (suc n)) ] j z)
-- -- -- -- -- -- -- --     --              ]
-- -- -- -- -- -- -- --     -- prev-cyl i = Partialⁿ-map→ n ((paⁿ n (cu→[ n , f ]))) (fstω prev)
-- -- -- -- -- -- -- --     --    where

-- -- -- -- -- -- -- --     --    f : (c : NCube n) → NBoundary n → NBoundary (suc n)
-- -- -- -- -- -- -- --     --    f _ = cylEx i

-- -- -- -- -- -- -- --     prevP : (j : I) →
-- -- -- -- -- -- -- --               T[
-- -- -- -- -- -- -- --               Partialⁿ n (boundaryExpr (suc n'))
-- -- -- -- -- -- -- --               (Ct[ suc (suc n') , (λ _ → NBoundary (suc (suc n'))) ] j)
-- -- -- -- -- -- -- --               ]
-- -- -- -- -- -- -- --     prevP j =  Partialⁿ-map→ n ((paⁿ n (cu→[ n , (const (cylEx j)) ]))) (fstω prev)



-- -- -- -- -- -- -- --     prevS' : (j : I) → T[ Subⁿ n (boundaryExpr (suc n')) (prevP j) ]
-- -- -- -- -- -- -- --     prevS' j = {!!}


-- -- -- -- -- -- -- --     prevS : (j : I) → T[ Subⁿ n (boundaryExpr (suc n')) (prevP j) ]
-- -- -- -- -- -- -- --     prevS j = {!sndω prev!}


-- -- -- -- -- -- -- -- nBoundaryωΣ : ∀ n → NBoundaryωΣ n
-- -- -- -- -- -- -- -- Σω.fstω (nBoundaryωΣ zero) ()
-- -- -- -- -- -- -- -- Σω.sndω (nBoundaryωΣ zero) = inSⁿ→i0 0 (λ _ → [])
-- -- -- -- -- -- -- -- Σω.fstω (nBoundaryωΣ (suc zero)) i = 
-- -- -- -- -- -- -- --   λ { (i = i0) → lid false [] ;
-- -- -- -- -- -- -- --       (i = i1) → lid true [] }
-- -- -- -- -- -- -- -- Σω.sndω (nBoundaryωΣ (suc zero)) = inSⁿ 1 (boundaryExpr 1) λ i x → inside i ∷ []
-- -- -- -- -- -- -- -- nBoundaryωΣ (suc (suc n'')) = NBoundaryωΣ-step n'' (nBoundaryωΣ (suc n''))



-- -- -- -- -- -- -- -- sbpTest : I → I → {!!}
-- -- -- -- -- -- -- -- sbpTest i₁ i₂ = {!fstω (cubeP 7)!}

-- -- -- -- -- -- -- -- record NBoundaryω-↔ (n : ℕ) : Typeω where
-- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- --     isom : NBoundaryω-Iso-Ty n
-- -- -- -- -- -- -- --     ins= : ωType._≡ω_ (Partialⁿ n (boundaryExpr n) Ct[ n , const (NCube n) ])
-- -- -- -- -- -- -- --                (paⁿ n ct[ n , (λ c → c) ])
-- -- -- -- -- -- -- --                (Isoω.to (isom (const (NCube n))) boundaryInj)
                 


-- -- -- -- -- -- -- -- NBoundaryω-↔-step : ∀ n → NBoundaryω-↔ (suc n)
-- -- -- -- -- -- -- --                         → NBoundaryω-↔ (suc (suc n))
-- -- -- -- -- -- -- -- NBoundaryω-↔-step n' prev =
-- -- -- -- -- -- -- --    record {
-- -- -- -- -- -- -- --           isom = ism
-- -- -- -- -- -- -- --         ; ins= = ins=
-- -- -- -- -- -- -- --         }
-- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- --     open NBoundaryω-↔ prev using () renaming (isom to isom-pred ; ins= to ins=-pred)

-- -- -- -- -- -- -- --     n = suc n'

-- -- -- -- -- -- -- --     ism : ∀ {ℓ} → (A : NCube (suc n) → Type ℓ ) → Isoω _ _
-- -- -- -- -- -- -- --     ism A = record { to = t ; from = f ; sec = s ; ret = r } 

-- -- -- -- -- -- -- --       where

-- -- -- -- -- -- -- --       t : _
-- -- -- -- -- -- -- --       t x = Partialⁿ-attach-Ends n cy e0 e1

-- -- -- -- -- -- -- --         where

-- -- -- -- -- -- -- --         cy : _
-- -- -- -- -- -- -- --         cy i = to (x ∘ cylEx i)

-- -- -- -- -- -- -- --           where
-- -- -- -- -- -- -- --           open Isoω (isom-pred (A i∷ i))



-- -- -- -- -- -- -- --         e0 : T[ InsideOfω n (λ i → _) ]
-- -- -- -- -- -- -- --         e0 = hcompⁿ n (λ j i' → {!ins=-pred i'!})
-- -- -- -- -- -- -- --                (inSⁿ n (boundaryExpr n) ct[ n , x ∘ lid' false ])

-- -- -- -- -- -- -- --         e1 : {!!}
-- -- -- -- -- -- -- --         e1 = {!!}

-- -- -- -- -- -- -- --       f : {!!}
-- -- -- -- -- -- -- --       f = {!!}

-- -- -- -- -- -- -- --       s : {!!}
-- -- -- -- -- -- -- --       s = {!!}

-- -- -- -- -- -- -- --       r : {!!}
-- -- -- -- -- -- -- --       r = {!!}

-- -- -- -- -- -- -- --     ins= : (Partialⁿ (suc (suc n')) (boundaryExpr (suc (suc n')))
-- -- -- -- -- -- -- --               Ct[ suc (suc n') , const (NCube (suc (suc n'))) ]
-- -- -- -- -- -- -- --               ωType.≡ω paⁿ (suc (suc n')) ct[ suc (suc n') , (λ c → c) ])
-- -- -- -- -- -- -- --              (Isoω.to (ism (const (NCube (suc (suc n'))))) boundaryInj)
-- -- -- -- -- -- -- --     ins= i i₁ = {!!}


-- -- -- -- -- -- -- -- -- NBoundaryω-Iso-2 : NBoundaryω-Iso-Ty 2 
-- -- -- -- -- -- -- -- -- Isoω.to (NBoundaryω-Iso-2 A) x i i₁ =
-- -- -- -- -- -- -- -- --  λ {
-- -- -- -- -- -- -- -- --       (i = i1) → x (lid true (inside i₁ ∷ []))
-- -- -- -- -- -- -- -- --     ; (i = i0) → x (lid false (inside i₁ ∷ []))
-- -- -- -- -- -- -- -- --     ; (i₁ = i1) → x (cyl (lid true []) i)
-- -- -- -- -- -- -- -- --     ; (i₁ = i0) → x (cyl (lid false []) i)
-- -- -- -- -- -- -- -- --    }
  
-- -- -- -- -- -- -- -- -- Isoω.from (NBoundaryω-Iso-2 A) x (lid false (end false ∷ [])) = x i0 i0 1=1
-- -- -- -- -- -- -- -- -- Isoω.from (NBoundaryω-Iso-2 A) x (lid false (end true ∷ [])) = x i0 i1 1=1
-- -- -- -- -- -- -- -- -- Isoω.from (NBoundaryω-Iso-2 A) x (lid true (end false ∷ [])) = x i1 i0 1=1
-- -- -- -- -- -- -- -- -- Isoω.from (NBoundaryω-Iso-2 A) x (lid true (end true ∷ [])) = x i1 i1 1=1
-- -- -- -- -- -- -- -- -- Isoω.from (NBoundaryω-Iso-2 A) x (lid false (inside i ∷ [])) = x i0 i 1=1
-- -- -- -- -- -- -- -- -- Isoω.from (NBoundaryω-Iso-2 A) x (lid true (inside i ∷ [])) = x i1 i 1=1
-- -- -- -- -- -- -- -- -- Isoω.from (NBoundaryω-Iso-2 A) x (cyl (lid false []) i) = x i i0 1=1
-- -- -- -- -- -- -- -- -- Isoω.from (NBoundaryω-Iso-2 A) x (cyl (lid true []) i) = x i i1 1=1

-- -- -- -- -- -- -- -- -- Isoω.sec (NBoundaryω-Iso-2 A) b i (lid false (end false ∷ [])) = b (lid false (inside i0 ∷ []))
-- -- -- -- -- -- -- -- -- Isoω.sec (NBoundaryω-Iso-2 A) b i (lid false (end true ∷ [])) = b (lid false (end true ∷ []))
-- -- -- -- -- -- -- -- -- Isoω.sec (NBoundaryω-Iso-2 A) b i (lid false (inside i₁ ∷ [])) = b ((lid false (inside i₁ ∷ [])))
-- -- -- -- -- -- -- -- -- Isoω.sec (NBoundaryω-Iso-2 A) b i (lid true (end false ∷ [])) = b ((lid true (end false ∷ []))) 
-- -- -- -- -- -- -- -- -- Isoω.sec (NBoundaryω-Iso-2 A) b i (lid true (end true ∷ [])) = b ((lid true (end true ∷ [])))
-- -- -- -- -- -- -- -- -- Isoω.sec (NBoundaryω-Iso-2 A) b i (lid true (inside i₁ ∷ [])) = b ((lid true (inside i₁ ∷ [])))
-- -- -- -- -- -- -- -- -- Isoω.sec (NBoundaryω-Iso-2 A) b i (cyl (lid false []) i₁) = b ((cyl (lid false []) i₁))
-- -- -- -- -- -- -- -- -- Isoω.sec (NBoundaryω-Iso-2 A) b i (cyl (lid true []) i₁) = b ((cyl (lid true []) i₁))

-- -- -- -- -- -- -- -- -- Isoω.ret (NBoundaryω-Iso-2 A) a i i₁ = 
-- -- -- -- -- -- -- -- --    λ {
-- -- -- -- -- -- -- -- --       (i = i1) → λ _ →  a i1 i₁ 1=1
-- -- -- -- -- -- -- -- --     ; (i = i0) → λ _ →  a i0 i₁ 1=1
-- -- -- -- -- -- -- -- --     ; (i₁ = i1) → λ _ →  a i i1 1=1
-- -- -- -- -- -- -- -- --     ; (i₁ = i0) → λ _ →  a i i0 1=1
-- -- -- -- -- -- -- -- --    }



-- -- -- -- -- -- -- -- -- NBoundaryω-Iso-step : ∀ n → NBoundaryω-Iso-Ty (suc n) → NBoundaryω-Iso-Ty (suc (suc n))
-- -- -- -- -- -- -- -- -- NBoundaryω-Iso-step n' prev A = record { to = t ; from = f ; sec = s ; ret = r }
-- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- --   n = suc n'

  


-- -- -- -- -- -- -- -- --   t : ((bd : NBoundary (suc n)) → (A ∘ boundaryInj) bd) →
-- -- -- -- -- -- -- -- --         T[ Boundaryω (suc n) Ct[ suc n , A ] ]
-- -- -- -- -- -- -- -- --   t x = Partialⁿ-attach-Ends n cy e0 e1
-- -- -- -- -- -- -- -- --     where

-- -- -- -- -- -- -- -- --       cy : (i : I) → T[ Partialⁿ n (boundaryExpr n) Ct[ n , A i∷ i ] ]
-- -- -- -- -- -- -- -- --       cy i = to (x ∘ cylEx i)

-- -- -- -- -- -- -- -- --         where
-- -- -- -- -- -- -- -- --         open Isoω (prev (A i∷ i))

-- -- -- -- -- -- -- -- --       e0 : T[ Subⁿ n {A = Ct[ n , A i∷ i0 ]} (boundaryExpr n) (cy i0) ]
-- -- -- -- -- -- -- -- --       e0 = hcompⁿ n (λ j → f j) e0''
-- -- -- -- -- -- -- -- --         where
-- -- -- -- -- -- -- -- --         open Isoω (prev (A i∷ i0))

-- -- -- -- -- -- -- -- --         e0'' : T[ Subⁿ n {A = Ct[ n , (A i∷ i0) ]}
-- -- -- -- -- -- -- -- --                     (boundaryExpr n) (paⁿ n ct[ n , x ∘ lid false ]) ]
-- -- -- -- -- -- -- -- --         e0'' = inSⁿ n (boundaryExpr n) ct[ n , x ∘ lid' false ]

-- -- -- -- -- -- -- -- --         rr : (i : I) →
-- -- -- -- -- -- -- -- --                (Partialⁿ n' (boundaryExpr (suc n') i)
-- -- -- -- -- -- -- -- --                 (Ct[ suc n' , (λ x₁ → A (inside i0 ∷ x₁)) ] i)
-- -- -- -- -- -- -- -- --                 ωType.≡ω to (from (cy i0)) i)
-- -- -- -- -- -- -- -- --                (cy i0 i)
-- -- -- -- -- -- -- -- --         rr = (ret (cy i0))

-- -- -- -- -- -- -- -- --         ss : from (to (λ x₁ → x (lid false (boundaryInj x₁)))) ≡
-- -- -- -- -- -- -- -- --                       (λ x₁ → x (lid false (boundaryInj x₁)))
-- -- -- -- -- -- -- -- --         ss = sec (x ∘ lid' false ∘ boundaryInj)

-- -- -- -- -- -- -- -- --         f : (j : I) → T[ Partialⁿ n (boundaryExpr n) (Ct[ n , A i∷ i0 ])
-- -- -- -- -- -- -- -- --                         ]
-- -- -- -- -- -- -- -- --         f j i = 
-- -- -- -- -- -- -- -- --            let zz : _
-- -- -- -- -- -- -- -- --                zz = lem11 n prev A x i

-- -- -- -- -- -- -- -- --            in {!zz!}

-- -- -- -- -- -- -- -- -- -- ?2 i1 i
-- -- -- -- -- -- -- -- -- --   = Isoω.to (prev (λ x₁ → A (end false ∷ x₁)))
-- -- -- -- -- -- -- -- -- --     (λ x₁ → x (lid false (boundaryInj x₁))) i
-- -- -- -- -- -- -- -- -- --   : T[
-- -- -- -- -- -- -- -- -- --     Partialⁿ n' (boundaryExpr (suc n') i)
-- -- -- -- -- -- -- -- -- --     Ct[ n' , (λ x₁ → A (end false ∷ inside i ∷ x₁)) ]
-- -- -- -- -- -- -- -- -- --     ]
-- -- -- -- -- -- -- -- -- -- paⁿ n' ct[ n' , (λ x₁ → x (lid false (inside i ∷ x₁))) ] = ?2 i0 i
-- -- -- -- -- -- -- -- -- --   : T[
-- -- -- -- -- -- -- -- -- --     Partialⁿ n' (boundaryExpr (suc n') i)
-- -- -- -- -- -- -- -- -- --     Ct[ n' , (λ x₁ → A (end false ∷ inside i ∷ x₁)) ]
-- -- -- -- -- -- -- -- -- --     ]

-- -- -- -- -- -- -- -- --         -- -- s= : {!!} ≡ {!!}
-- -- -- -- -- -- -- -- --         -- -- s= = {!!}

-- -- -- -- -- -- -- -- --         -- e0' : {!hcompⁿ!}
-- -- -- -- -- -- -- -- --         -- e0' = hcompⁿ n {boundaryExpr n}
-- -- -- -- -- -- -- -- --         --  -- (λ j →  paⁿ n ct[ n , (λ c → sec (x ∘ lid' false ∘ boundaryInj) j {!lid' false c!}) ])
-- -- -- -- -- -- -- -- --         --          (λ j → Partialⁿ-map→ n (f j)
-- -- -- -- -- -- -- -- --         --             (paⁿ n ct[ n , x  ∘ (lid' false) ]))
-- -- -- -- -- -- -- -- --         --          {!!}

-- -- -- -- -- -- -- -- --         --   where
-- -- -- -- -- -- -- -- --         --     f' : (j : I) → T[ Partialⁿ n (boundaryExpr n) _ ]
-- -- -- -- -- -- -- -- --         --     f' j = Isoω.to (prev {!sec!}) {!!}

-- -- -- -- -- -- -- -- --         --     f : (j : I) → T[ Partialⁿ n (boundaryExpr n) _ ]
-- -- -- -- -- -- -- -- --         --     f j = {!Isoω.to (prev ?) ?!}

-- -- -- -- -- -- -- -- --       e1 : T[ Subⁿ n (λ z → boundaryExpr n z) (cy i1) ]
-- -- -- -- -- -- -- -- --       e1 = hcompⁿ n {A = {!!}} {!!} {!!}
      



-- -- -- -- -- -- -- -- --   f : T[ Boundaryω (suc n) Ct[ suc n , A ] ] →
-- -- -- -- -- -- -- -- --         (bd : NBoundary (suc n)) → (A ∘ boundaryInj) bd
-- -- -- -- -- -- -- -- --   f = {!!}

-- -- -- -- -- -- -- -- --   s : {!!}
-- -- -- -- -- -- -- -- --   s = {!!}

-- -- -- -- -- -- -- -- --   r : {!!}
-- -- -- -- -- -- -- -- --   r = {!!}


-- -- -- -- -- -- -- -- -- -- lem1 : ∀ {ℓ} → ∀ n → {A A' : Type ℓ}
-- -- -- -- -- -- -- -- -- --        → (bd : T[ Boundaryω n Ct[ n , const A ] ])
-- -- -- -- -- -- -- -- -- --        → (f : A → NCube n)
-- -- -- -- -- -- -- -- -- --        → (f' : NCube n → A')
-- -- -- -- -- -- -- -- -- --        → T[ InsideOfω n
-- -- -- -- -- -- -- -- -- --              (Partialⁿ-map→ n (paⁿ n cu→[ n , (λ _ → f' ∘ f) ]) bd) ]
-- -- -- -- -- -- -- -- -- -- lem1 zero bd f f' = inS (f' [])
-- -- -- -- -- -- -- -- -- -- lem1 (suc zero) bd f f' i = {!!}
-- -- -- -- -- -- -- -- -- -- lem1 (suc (suc n)) bd f f' i = {!!}




-- -- -- -- -- -- -- -- -- -- NBoundaryω-step' : ∀ n → T[ NBoundaryω (suc n) ]
-- -- -- -- -- -- -- -- -- --                       → T[ NBoundaryω (suc (suc n)) ] 
-- -- -- -- -- -- -- -- -- -- NBoundaryω-step' n' prev = 
-- -- -- -- -- -- -- -- -- --    Partialⁿ-attach-Ends n prev-cyl (end0) (end1) 

-- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- --      n = suc n'

-- -- -- -- -- -- -- -- -- --      prev-cyl : (j : I) →
-- -- -- -- -- -- -- -- -- --                   T[
-- -- -- -- -- -- -- -- -- --                   Partialⁿ n (boundaryExpr n)
-- -- -- -- -- -- -- -- -- --                   (λ z → Ct[ suc n , const (NBoundary (suc n)) ] j z)
-- -- -- -- -- -- -- -- -- --                   ]
-- -- -- -- -- -- -- -- -- --      prev-cyl i = Partialⁿ-map→ n ((paⁿ n (cu→[ n , f ]))) prev
-- -- -- -- -- -- -- -- -- --         where

-- -- -- -- -- -- -- -- -- --         f : (c : NCube n) → NBoundary n → NBoundary (suc n)
-- -- -- -- -- -- -- -- -- --         f c = cylEx i

-- -- -- -- -- -- -- -- -- --      ends : (b : Bool) → T[ InsideOfω n _ ]
-- -- -- -- -- -- -- -- -- --      ends b = inSⁿ→-const n (boundaryExpr (suc n'))
-- -- -- -- -- -- -- -- -- --               (const (NBoundary n))
-- -- -- -- -- -- -- -- -- --               (const (NBoundary (suc n)))
-- -- -- -- -- -- -- -- -- --                prev (lid' b)

-- -- -- -- -- -- -- -- -- --      end0 : T[ Subⁿ n (λ z → boundaryExpr n z) (prev-cyl i0) ]
-- -- -- -- -- -- -- -- -- --      end0 = lem1 n prev boundaryInj (lid' false)

-- -- -- -- -- -- -- -- -- --      end1 : _
-- -- -- -- -- -- -- -- -- --      end1 = lem1 n prev boundaryInj (lid' true)


-- -- -- -- -- -- -- -- -- -- nBoundaryω : ∀ n → T[ NBoundaryω n ]
-- -- -- -- -- -- -- -- -- -- nBoundaryω zero ()
-- -- -- -- -- -- -- -- -- -- nBoundaryω (suc zero) i =
-- -- -- -- -- -- -- -- -- --   λ { (i = i0) → lid false [] ;
-- -- -- -- -- -- -- -- -- --       (i = i1) → lid true [] }
-- -- -- -- -- -- -- -- -- -- nBoundaryω (suc (suc n'')) = NBoundaryω-step n'' (nBoundaryω (suc n''))

-- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- --    -- whithout this additional definition termination checker is complaining
-- -- -- -- -- -- -- -- -- --    NBoundaryω-step : ∀ n → T[ NBoundaryω (suc n) ]
-- -- -- -- -- -- -- -- -- --                          → T[ NBoundaryω (suc (suc n)) ] 
-- -- -- -- -- -- -- -- -- --    NBoundaryω-step n' prev = 
-- -- -- -- -- -- -- -- -- --       Partialⁿ-attach-Ends n prev-cyl (ends false) (ends true) 

-- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- --         n = suc n'

-- -- -- -- -- -- -- -- -- --         prev-cyl : (j : I) →
-- -- -- -- -- -- -- -- -- --                      T[
-- -- -- -- -- -- -- -- -- --                      Partialⁿ n (boundaryExpr n)
-- -- -- -- -- -- -- -- -- --                      (λ z → Ct[ suc n , const (NBoundary (suc n)) ] j z)
-- -- -- -- -- -- -- -- -- --                      ]
-- -- -- -- -- -- -- -- -- --         prev-cyl i = Partialⁿ-map→ n ((paⁿ n (cu→[ n , f ]))) prev
-- -- -- -- -- -- -- -- -- --            where

-- -- -- -- -- -- -- -- -- --            f : (c : NCube n) → NBoundary n → NBoundary (suc n)
-- -- -- -- -- -- -- -- -- --            f c = ((λ i₁ x →  lid false (isPropCube c (boundaryInj x) i₁))
-- -- -- -- -- -- -- -- -- --                      ∙∙ cylEx ∙∙
-- -- -- -- -- -- -- -- -- --                      λ i₁ x → lid true (isPropCube (boundaryInj x) c i₁))
-- -- -- -- -- -- -- -- -- --                      i

-- -- -- -- -- -- -- -- -- --         ends : (b : Bool) → T[ InsideOfω n _ ]
-- -- -- -- -- -- -- -- -- --         ends b = inSⁿ→-const n (boundaryExpr (suc n'))
-- -- -- -- -- -- -- -- -- --                  (const (NBoundary n))
-- -- -- -- -- -- -- -- -- --                  (const (NBoundary (suc n)))
-- -- -- -- -- -- -- -- -- --                   prev (lid' b)



-- -- -- -- -- -- -- -- -- -- toBoundaryω : ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
-- -- -- -- -- -- -- -- -- --               → (NBoundary n → A)
-- -- -- -- -- -- -- -- -- --               → T[ Boundaryω n Ct[ n , const A ] ]
-- -- -- -- -- -- -- -- -- -- toBoundaryω {n = n} bd = Partialⁿ-map→ n (paⁿ n cu→[ n , const bd ]) (nBoundaryω n) 

-- -- -- -- -- -- -- -- -- -- -- fromBoundaryω : ∀ {ℓ} → ∀ {n} → {A : Type ℓ}              
-- -- -- -- -- -- -- -- -- -- --               → T[ Boundaryω n Ct[ n , const A ] ]
-- -- -- -- -- -- -- -- -- -- --               → (NBoundary n → A)
-- -- -- -- -- -- -- -- -- -- -- fromBoundaryω {n = zero} x ()
-- -- -- -- -- -- -- -- -- -- -- fromBoundaryω {n = 1} x = {!!}
-- -- -- -- -- -- -- -- -- -- -- fromBoundaryω {n = 2} x = {!!}
-- -- -- -- -- -- -- -- -- -- -- fromBoundaryω {n = suc (suc (suc n'))} x (lid x₁ x₂) =
-- -- -- -- -- -- -- -- -- -- --   let n = (suc n')
-- -- -- -- -- -- -- -- -- -- --       z : T[ Partialⁿ (suc n) i1ⁿ (λ z → Ct[ suc (suc n) , const _ ] (Bool→I x₁) z) ]
-- -- -- -- -- -- -- -- -- -- --       z = ⊆I→⊆'I (suc n) (⊆I-trans (suc n) (⊂-∨~B (suc n) x₁)
-- -- -- -- -- -- -- -- -- -- --                          ((⊆I-∨1 (([ (Bool→I x₁) ]Iexpr ∨ⁿ [ ~ (Bool→I x₁) ]Iexpr))
-- -- -- -- -- -- -- -- -- -- --                           ((boundaryExpr (suc n))))))
-- -- -- -- -- -- -- -- -- -- --                              ((x (Bool→I x₁))) 
-- -- -- -- -- -- -- -- -- -- -- -- (x (Bool→I x₁))
-- -- -- -- -- -- -- -- -- -- --   in from-cu' (Partialⁿ-i1-elim (suc n) z) x₂  
-- -- -- -- -- -- -- -- -- -- -- -- ⊂-∨~B
-- -- -- -- -- -- -- -- -- -- -- fromBoundaryω {n = suc (suc (suc n'))} {A} x (cyl x₁ i) =
-- -- -- -- -- -- -- -- -- -- --   let n = (suc n')
-- -- -- -- -- -- -- -- -- -- --       cy = λ (i : I) →  ⊆I→⊆'I (suc n) (⊆I-∨2 _ (boundaryExpr (suc n))) (x i)

-- -- -- -- -- -- -- -- -- -- --       cc :  fromBoundaryω (⊆I→⊆'I (suc (suc n')) _ (x i0)) x₁
-- -- -- -- -- -- -- -- -- -- --             ≡ fromBoundaryω (⊆I→⊆'I (suc (suc n')) _ (x i1)) x₁
-- -- -- -- -- -- -- -- -- -- --       cc = λ i → fromBoundaryω {n = suc n} (cy i) x₁

-- -- -- -- -- -- -- -- -- -- --       s0 : ∀ i₁ i₂ → ⊆I i1ⁿ (boundaryExpr (suc (suc (suc n'))) i0 i₁ i₂)
-- -- -- -- -- -- -- -- -- -- --       s0 = λ i₁ i₂ → {!!}

-- -- -- -- -- -- -- -- -- -- --       s1 : ∀ i₁ i₂ → ⊆I i1ⁿ (boundaryExpr (suc (suc (suc n'))) i1 i₁ i₂)
-- -- -- -- -- -- -- -- -- -- --       s1 = λ i₁ i₂ → {!!}

-- -- -- -- -- -- -- -- -- -- --       lhs : from-cu' (λ i₁ i₂ → Partialⁿ-i1-elim n' (⊆I→⊆'I n' _ (x i0 i₁ i₂)))
-- -- -- -- -- -- -- -- -- -- --               (boundaryInj x₁)
-- -- -- -- -- -- -- -- -- -- --               ≡ fromBoundaryω (⊆I→⊆'I (suc (suc n')) _ (x i0)) x₁
-- -- -- -- -- -- -- -- -- -- --       lhs = λ i₁ → {!!}

-- -- -- -- -- -- -- -- -- -- --       w : from-cu'
-- -- -- -- -- -- -- -- -- -- --            (λ i₁ i₂ → Partialⁿ-i1-elim n' (⊆I→⊆'I n' (s0 i₁ i₂) (x i0 i₁ i₂)))
-- -- -- -- -- -- -- -- -- -- --            (boundaryInj x₁)
-- -- -- -- -- -- -- -- -- -- --           ≡
-- -- -- -- -- -- -- -- -- -- --           from-cu'
-- -- -- -- -- -- -- -- -- -- --          (λ i₁ i₂ → Partialⁿ-i1-elim n' (⊆I→⊆'I n' (s1 i₁ i₂) (x i1 i₁ i₂)))
-- -- -- -- -- -- -- -- -- -- --          (boundaryInj x₁)
-- -- -- -- -- -- -- -- -- -- --       w = lhs ∙∙ cc ∙∙ {!!}

-- -- -- -- -- -- -- -- -- -- --   in w i

-- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ from-cu'
-- -- -- -- -- -- -- -- -- -- --          (λ i₁ i₂ → Partialⁿ-i1-elim n' (⊆I→⊆'I n' _ (x i0 i₁ i₂)))
-- -- -- -- -- -- -- -- -- -- --          (boundaryInj x₁)
-- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ from-cu'
-- -- -- -- -- -- -- -- -- -- --          (λ i₁ i₂ → Partialⁿ-i1-elim n' (⊆I→⊆'I n' _ (x i1 i₁ i₂)))
-- -- -- -- -- -- -- -- -- -- --          (boundaryInj x₁)
   

-- -- -- -- -- -- -- -- -- -- -- InsideOf→InsideOfω-bd : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- --                      → (bd : NBoundary n → A)
-- -- -- -- -- -- -- -- -- -- --                      → InsideOf bd
-- -- -- -- -- -- -- -- -- -- --                      → T[ Boundaryω n Ct[ n , const A ] ]
-- -- -- -- -- -- -- -- -- -- -- InsideOf→InsideOfω-bd {A = A} {n = n} bd x = paⁿ n {!cu[ n , ? ]!}
-- -- -- -- -- -- -- -- -- -- --   -- Partialⁿ-const A n (boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- --   --  (C→elim {n = n} {A = A} (toCubical x)) 

-- -- -- -- -- -- -- -- -- -- -- InsideOf→InsideOfω : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- --                      → (bd : NBoundary n → A)
-- -- -- -- -- -- -- -- -- -- --                      → (x : InsideOf bd)
-- -- -- -- -- -- -- -- -- -- --                      → InsideOfω {A = A} {n = n} (InsideOf→InsideOfω-bd bd x)
-- -- -- -- -- -- -- -- -- -- -- InsideOf→InsideOfω {A = A} {n = n} bd x =
-- -- -- -- -- -- -- -- -- -- --     inSⁿ n (boundaryExpr n) (C→elim {n = n} {A = A} (toCubical x))


-- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path-bd : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- --                      → (bd : Boundaryω A (suc n))
-- -- -- -- -- -- -- -- -- -- --                      → InsideOfω {ℓ} {A} {(suc n)} bd
-- -- -- -- -- -- -- -- -- -- --                      → (i : I) → Boundaryω A n
-- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path-bd {n = n} bd x i = 
-- -- -- -- -- -- -- -- -- -- --   InsideOf→InsideOfω-bd
-- -- -- -- -- -- -- -- -- -- --     (fst (InsideOfω→InsideOf bd x) ∘ (cyl'' (inside i)))
-- -- -- -- -- -- -- -- -- -- --     ((snd (InsideOfω→InsideOf bd x)) i)

-- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- --                      → (bd : Boundaryω A (suc n))
-- -- -- -- -- -- -- -- -- -- --                      → (x : InsideOfω {ℓ} {A} {(suc n)} bd)
-- -- -- -- -- -- -- -- -- -- --                      → (i : I)
-- -- -- -- -- -- -- -- -- -- --                      → InsideOfω {A = A} {n = n} ((InsideOfω-Path-bd {A = A} {n = n} bd x) i)
-- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path {n = n} bd x i = 
-- -- -- -- -- -- -- -- -- -- --   InsideOf→InsideOfω
-- -- -- -- -- -- -- -- -- -- --     (fst (InsideOfω→InsideOf bd x) ∘ (cyl'' (inside i)))
-- -- -- -- -- -- -- -- -- -- --     ((snd (InsideOfω→InsideOf bd x)) i)


-- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path' : ∀ {ℓ} → ∀ (A : Type ℓ) → ∀ n
-- -- -- -- -- -- -- -- -- -- --             → (pa : Partialⁿ A (suc n) (boundaryExpr (suc n)))
-- -- -- -- -- -- -- -- -- -- --             → (s : Subⁿ A (suc n) _ pa)
-- -- -- -- -- -- -- -- -- -- --             → C→-app {n = n} {A} ((outSⁿ (suc n) (boundaryExpr (suc n)) pa s) i0)
-- -- -- -- -- -- -- -- -- -- --               ≡
-- -- -- -- -- -- -- -- -- -- --               C→-app {n = n} {A} ((outSⁿ (suc n) (boundaryExpr (suc n)) pa s) i1)
            
-- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path' A n pa s i =
-- -- -- -- -- -- -- -- -- -- --   C→-app (outSⁿ (suc n) (boundaryExpr (suc n)) pa s i)



-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-comp : ∀ {ℓ} → ∀ {n} → ∀ {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- --                 → (bd : I → NBoundary n → A)
-- -- -- -- -- -- -- -- -- -- -- -- --                 → InsideOf (bd i0)
-- -- -- -- -- -- -- -- -- -- -- -- --                 → InsideOf (bd i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-comp = {!!}




-- -- -- -- -- -- -- -- -- -- -- -- -- boundaryω-Σ : ℕ → ωType
-- -- -- -- -- -- -- -- -- -- -- -- -- boundaryω-Σ n = Partialⁿ n (boundaryExpr n) Ct[ n , OnBoundary ]

-- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-step : ∀ n → T[ boundaryω-Σ (suc n) ] → T[ boundaryω-Σ (suc (suc n)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-step n' prev = 
-- -- -- -- -- -- -- -- -- -- -- -- --    Partialⁿ-attach-Ends n
-- -- -- -- -- -- -- -- -- -- -- -- --      prev-cyl e0 e1 

-- -- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- -- --      n = suc n'

-- -- -- -- -- -- -- -- -- -- -- -- --      prev-cyl : T[
-- -- -- -- -- -- -- -- -- -- -- -- --                   Partialⁿ (suc n) (λ _ → boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- --                   (Ct[ suc n , OnBoundary ])
-- -- -- -- -- -- -- -- -- -- -- -- --                   ]
-- -- -- -- -- -- -- -- -- -- -- -- --      prev-cyl i = Partialⁿ-map→ n (λ i' → (paⁿ n' (cu→[ n' , (f i') ]))) prev 
-- -- -- -- -- -- -- -- -- -- -- -- --        where
-- -- -- -- -- -- -- -- -- -- -- -- --          f : (i' : I) → (c : NCube n')
-- -- -- -- -- -- -- -- -- -- -- -- --                 → OnBoundary (inside i' ∷ c)
-- -- -- -- -- -- -- -- -- -- -- -- --                 → OnBoundary (inside i ∷ inside i' ∷ c)
-- -- -- -- -- -- -- -- -- -- -- -- --          f i' c x = cyl (fst x) i , (cong (inside i ∷_) (snd x))

-- -- -- -- -- -- -- -- -- -- -- -- --      e0 : T[ InsideOfω n (prev-cyl i0) ]
-- -- -- -- -- -- -- -- -- -- -- -- --      e0 = {!inSⁿ ?!}
     
-- -- -- -- -- -- -- -- -- -- -- -- --      e1 : T[ InsideOfω n (prev-cyl i1) ]
-- -- -- -- -- -- -- -- -- -- -- -- --      e1 = {!!}

-- -- -- -- -- -- -- -- -- -- -- --      -- intersection : T[
-- -- -- -- -- -- -- -- -- -- -- --      --                  Partialⁿ (suc n)
-- -- -- -- -- -- -- -- -- -- -- --      --                  ((λ z → ([ z ]Iexpr ∨ⁿ [ ~ z ]Iexpr)) ∧ⁿ
-- -- -- -- -- -- -- -- -- -- -- --      --                   (λ _ → boundaryExpr n))
-- -- -- -- -- -- -- -- -- -- -- --      --                  (Ct[ suc n , OnBoundary ])
-- -- -- -- -- -- -- -- -- -- -- --      --                  ]
-- -- -- -- -- -- -- -- -- -- -- --      -- intersection =  ⊆'2-∧ {n = suc n} _ _ prev-cyl

-- -- -- -- -- -- -- -- -- -- -- --      -- e0 : T[ InsideOfω n (prev-cyl i0) ]
-- -- -- -- -- -- -- -- -- -- -- --      -- e0 i = {!inSⁿ n' ? ?!}

-- -- -- -- -- -- -- -- -- -- -- --      -- e1 : T[ InsideOfω n (prev-cyl i1) ]
-- -- -- -- -- -- -- -- -- -- -- --      -- e1 = {!!}

-- -- -- -- -- -- -- -- -- -- -- --      -- s1 : T[ Partialⁿ-Sub (suc n) intersection ]
-- -- -- -- -- -- -- -- -- -- -- --      -- s1 = Partialⁿ-Sub-Ends n prev-cyl e0 e1 

-- -- -- -- -- -- -- -- -- -- -- --      -- s2 : T[ Partialⁿ-Sub (suc n) (⊆I→⊆'I (suc n) _ intersection) ]
-- -- -- -- -- -- -- -- -- -- -- --      -- s2 = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --      intersection : T[
-- -- -- -- -- -- -- -- -- -- -- -- --                       Partialⁿ n
-- -- -- -- -- -- -- -- -- -- -- -- --                       ((λ z → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) z) ∧ⁿ
-- -- -- -- -- -- -- -- -- -- -- -- --                                                   (λ _ → boundaryExpr n i))
-- -- -- -- -- -- -- -- -- -- -- -- --                       (Ct[ suc n , OnBoundary ] i)
-- -- -- -- -- -- -- -- -- -- -- -- --                       ]
-- -- -- -- -- -- -- -- -- -- -- -- --      intersection = ⊆'2-∧ {n = n} _ _ (prev-cyl i)

-- -- -- -- -- -- -- -- -- -- -- -- --      e0 : T[ Subⁿ n (λ _ → boundaryExpr n i) (prev-cyl i) ]
-- -- -- -- -- -- -- -- -- -- -- -- --      e0 = {!!}
     
-- -- -- -- -- -- -- -- -- -- -- -- --      e1 : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --      e1 = {!!}
     
-- -- -- -- -- -- -- -- -- -- -- -- --      s1 : T[ Partialⁿ-Sub n intersection ]
-- -- -- -- -- -- -- -- -- -- -- -- --      s1 = Partialⁿ-Sub-Ends n (λ j i₁ → prev-cyl i i₁) e0 e1 i

-- -- -- -- -- -- -- -- -- -- -- -- --      s2 : T[ Partialⁿ-Sub n (⊆I→⊆'I n _ intersection) ]
-- -- -- -- -- -- -- -- -- -- -- -- --      s2 = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- Type₀ n _ (C→elim {n = n} OnBoundary)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfω→Cub : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (bd : Boundaryω A n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → InsideOfω {ℓ} {A} {n} bd
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → NCube n → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfω→Cub {A = A} {n = n} bd x = C→-app {n = n} {A = A} (outSⁿ n (boundaryExpr n) bd x) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfω→InsideOf : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (bd : Boundaryω A n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → InsideOfω {ℓ} {A} {n} bd
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → Σ _ (InsideOf {A = A} {n = n})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfω→InsideOf bd x = (InsideOfω→Cub bd x ∘ boundaryInj) , insideOf (InsideOfω→Cub bd x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf→InsideOfω-bd : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (bd : NBoundary n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → InsideOf bd
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → Boundaryω A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf→InsideOfω-bd {A = A} {n = n} bd x =
-- -- -- -- -- -- -- -- -- -- -- -- -- --   Partialⁿ-const A n (boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --    (C→elim {n = n} {A = A} (toCubical x)) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf→InsideOfω : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (bd : NBoundary n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (x : InsideOf bd)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → InsideOfω {A = A} {n = n} (InsideOf→InsideOfω-bd bd x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf→InsideOfω {A = A} {n = n} bd x =
-- -- -- -- -- -- -- -- -- -- -- -- -- --     inSⁿ n (boundaryExpr n) (C→elim {n = n} {A = A} (toCubical x))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path-bd : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (bd : Boundaryω A (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → InsideOfω {ℓ} {A} {(suc n)} bd
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (i : I) → Boundaryω A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path-bd {n = n} bd x i = 
-- -- -- -- -- -- -- -- -- -- -- -- -- --   InsideOf→InsideOfω-bd
-- -- -- -- -- -- -- -- -- -- -- -- -- --     (fst (InsideOfω→InsideOf bd x) ∘ (cyl'' (inside i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --     ((snd (InsideOfω→InsideOf bd x)) i)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (bd : Boundaryω A (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (x : InsideOfω {ℓ} {A} {(suc n)} bd)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (i : I)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → InsideOfω {A = A} {n = n} ((InsideOfω-Path-bd {A = A} {n = n} bd x) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path {n = n} bd x i = 
-- -- -- -- -- -- -- -- -- -- -- -- -- --   InsideOf→InsideOfω
-- -- -- -- -- -- -- -- -- -- -- -- -- --     (fst (InsideOfω→InsideOf bd x) ∘ (cyl'' (inside i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --     ((snd (InsideOfω→InsideOf bd x)) i)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path' : ∀ {ℓ} → ∀ (A : Type ℓ) → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- --             → (pa : Partialⁿ A (suc n) (boundaryExpr (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --             → (s : Subⁿ A (suc n) _ pa)
-- -- -- -- -- -- -- -- -- -- -- -- -- --             → C→-app {n = n} {A} ((outSⁿ (suc n) (boundaryExpr (suc n)) pa s) i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- --               ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- --               C→-app {n = n} {A} ((outSⁿ (suc n) (boundaryExpr (suc n)) pa s) i1)
            
-- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfω-Path' A n pa s i =
-- -- -- -- -- -- -- -- -- -- -- -- -- --   C→-app (outSⁿ (suc n) (boundaryExpr (suc n)) pa s i)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- TODO 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- OnBoundary-test : ∀ n → (∀ c → OnBoundary {n = n} c) → ⊥ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- OnBoundary-test zero x = fst (x [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- OnBoundary-test (suc n) x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-cyl-Ty : ∀ n → Boundaryω (NBoundary n) n → Typeω  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-cyl-Ty n bd = PartialPⁿ n (boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           (Partialⁿ-map {A = NBoundary n} {B = Type₀} n {e = (boundaryExpr n)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (λ x → lid' false (boundaryInj x) ≡ lid' true (boundaryInj x) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (bd))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-cyl : ∀ n → (bd : Boundaryω (NBoundary n) n) → NBoundary-cyl-Ty n bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-cyl zero bd ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-cyl (suc n) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PartialPⁿ-mapTo {n = suc n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {A = NBoundary (suc n)} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {B = λ bd →  lid false (boundaryInj bd) ≡ lid true (boundaryInj bd)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ x i → cyl' x i )


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _isBoundaryOf_ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                → (NBoundary n → A) → (NCube n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                → Typeω
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _isBoundaryOf_ {ℓ} {A} {n} x x₁ = {!∀!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-cyl :  ∀ n →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        Partialⁿ (NBoundary n) n (boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      → Partialⁿ (NBoundary (suc n)) (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                         (λ _ → boundaryExpr n ) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-cyl n x i = Partialⁿ-map {n = n} ((cyl'' (inside i))) (x) 



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-intersection : ∀ n → Partialⁿ (NBoundary (suc n)) (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                   (λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-intersection n i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⊂'-∧ (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) (boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (Partial∨ⁿ-ends n i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (Partialⁿ-map {A = NCube n} {B = NBoundary (suc n)} n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (lid' false) (Partialⁿ-const (NCube n) n _ (nCubeω n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (Partialⁿ-map {A = NCube n} {B = NBoundary (suc n)} n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (lid' true) (Partialⁿ-const (NCube n) n _ (nCubeω n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     )


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- inPartialⁿ-Sub⊂' : ∀ {ℓ} → {A : Type ℓ} → ∀ n → {i j : C→I n}                  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → (pa : Partialⁿ A n i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → Partialⁿ-Sub A n j i ( ⊂'-∧2 j i pa )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- inPartialⁿ-Sub⊂' zero pa e=1 = inS {! pa !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- inPartialⁿ-Sub⊂' (suc n) pa = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onBoundary-refl : ∀ n → NBoundary n → (Σ _ (OnBoundary {n}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onBoundary-refl n x = (boundaryInj x) , (x , refl)









-- -- -- -- -- -- -- -- -- -- -- -- -- -- PartialP-map-Σ : ∀ {ℓ ℓ' ℓ'' ℓ'''} → ∀ n → {e : C→I n}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → {A : Type ℓ} → {A' : Type ℓ'}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → {B : NCube n → A → Type ℓ''}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → {B' : NCube n → A' → Type ℓ'''}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (f : A → A')
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → (g : ∀ {c} → ∀ {a} → B c a → B' c (f a))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → PartialPⁿ n e
-- -- -- -- -- -- -- -- -- -- -- -- -- --                          (Partialⁿ-const _ n _ (C→elim {n = n} λ c → Σ _ (B c) ))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      → PartialPⁿ n e
-- -- -- -- -- -- -- -- -- -- -- -- -- --                          ((Partialⁿ-const _ n _ (C→elim {n = n} λ c → Σ _ (B' c) )))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- PartialP-map-Σ zero f g x p = (f (fst (x p))) , (g (snd (x p)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- PartialP-map-Σ (suc n) f g x i = PartialP-map-Σ n f g (x i)




-- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-Sub-ends-split : ∀ {ℓ} → {A : Type ℓ} → ∀ n → {i : I} → {j : C→I (suc n)}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                           → (p : I → Partialⁿ A (suc n) j)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                           → Subⁿ A (suc n) j (p i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                           → Subⁿ A (suc n) j (p i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                           → Partialⁿ-Sub (A) (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                              ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) j
-- -- -- -- -- -- -- -- -- -- -- -- -- --                                 (⊂'-∧2
-- -- -- -- -- -- -- -- -- -- -- -- -- --                                    ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                                    j (p i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-Sub-ends-split n p l0 l1 i = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- lem1 : ∀ {ℓ} → ∀ {n} → ∀ (i : I) → (j : C→I (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --           → {A : (i₁ : I) → Partialⁿ (Set ℓ) n (j i₁)}
-- -- -- -- -- -- -- -- -- -- -- -- -- --           → PartialPⁿ (suc n) j A
-- -- -- -- -- -- -- -- -- -- -- -- -- --           → PartialPⁿ (suc n) (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ j) {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- lem1 = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-step : ∀ n → boundaryω-Σ (suc n) → boundaryω-Σ (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-step n' prev i = 
-- -- -- -- -- -- -- -- -- -- -- -- -- --    PartialP∨ⁿ n 
-- -- -- -- -- -- -- -- -- -- -- -- -- --        ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr n)       
-- -- -- -- -- -- -- -- -- -- -- -- -- --        intersection
       
-- -- -- -- -- -- -- -- -- -- -- -- -- --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --        {!!} --(inPartialⁿ-Sub⊂' (suc n) (prev-cyl i))

-- -- -- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- -- -- --      n = suc n'

-- -- -- -- -- -- -- -- -- -- -- -- -- --      prev-cyl : (i' : I) → PartialPⁿ n ((boundaryExpr n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((Partialⁿ-const Type₀ (suc n) (λ _ → boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                            (C→elim {n = (suc n)} OnBoundary)) i')
-- -- -- -- -- -- -- -- -- -- -- -- -- --      prev-cyl i' =  PartialP-map-Σ n
-- -- -- -- -- -- -- -- -- -- -- -- -- --                        {B' = λ x x₁ → inside i' ∷ x ≡ boundaryInj x₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         (cyl'' (inside i'))  
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         (cong (inside i' ∷_))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                       (prev)

-- -- -- -- -- -- -- -- -- -- -- -- -- --      iTy0 : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --      iTy0 = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --      intersection0 : PartialPⁿ n
-- -- -- -- -- -- -- -- -- -- -- -- -- --                        (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                        (⊂'-∧2 ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         ( Partialⁿ-const Type₀ (suc n) (λ _ x → boundaryExpr n x)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                            (C→elim {n = suc n} OnBoundary) i))
-- -- -- -- -- -- -- -- -- -- -- -- -- --      intersection0 = ⊂'P-∧2
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                      (boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                       (prev-cyl i)

-- -- -- -- -- -- -- -- -- -- -- -- -- --      iTy : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --      iTy = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --      intersection : PartialPⁿ n (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                       (⊂'-∧ ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                        (⊂→⊂' ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         (⊂-∨1 ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                         ( Partialⁿ-const Type₀ (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                                (λ i′ x → ([ i′ ]Iexpr ∨ⁿ [ ~ i′ ]Iexpr) ∨ⁿ boundaryExpr n x)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                            (C→elim {n = suc n} OnBoundary) i)))
                           
-- -- -- -- -- -- -- -- -- -- -- -- -- --      intersection = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω1 : boundaryω-Σ 1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω1 i =
-- -- -- -- -- -- -- -- -- -- -- -- -- --   λ { (i = i0) → (lid false []) , refl ;
-- -- -- -- -- -- -- -- -- -- -- -- -- --       (i = i1) → (lid true []) , refl }


-- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω : ∀ n → (boundaryω-Σ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω zero ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω (suc n) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --    indω (λ n → boundaryω-Σ (suc n)) NBoundaryω1
-- -- -- -- -- -- -- -- -- -- -- -- -- --     NBoundaryω-step
-- -- -- -- -- -- -- -- -- -- -- -- -- --     n


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω : ∀ n → (boundaryω-Σ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω zero ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω (suc zero) i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    λ { (i = i0) → (lid false []) , refl ; (i = i1) → (lid true []) , refl } 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω (suc (suc n)) i  = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    PartialP∨ⁿ (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {Partialⁿ-const Type₀ (suc (suc n)) (boundaryExpr (suc (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (C→elim {n = suc (suc n)} OnBoundary) i}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        intersection
       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {!!} --(inPartialⁿ-Sub⊂' (suc n) (prev-cyl i))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      prev-cyl : (i' : I) → PartialPⁿ (suc n) ((boundaryExpr (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((Partialⁿ-const Type₀ (suc (suc n)) (λ _ → boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            (C→elim {n = (suc (suc n))} OnBoundary)) i')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      prev-cyl i' =  PartialP-map-Σ (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        {A = NBoundary (suc n)} {A' = NBoundary (suc (suc n))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        {B = λ x x₁ → x ≡ boundaryInj x₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        {B' = λ x x₁ → inside i' ∷ x ≡ boundaryInj x₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (cyl'' (inside i'))  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (cong (inside i' ∷_))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       (NBoundaryω (suc n))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      iTy0 : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      iTy0 = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      intersection0 : PartialPⁿ (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        (⊂'-∧2 ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         ( Partialⁿ-const Type₀ (suc (suc n)) (λ _ → boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            (C→elim {n = suc (suc n)} OnBoundary) i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      intersection0 = ⊂'P-∧2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       (prev-cyl i)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      iTy : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      iTy = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      intersection : PartialPⁿ (suc n) (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            ⊂'-∧ ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            (⊂→⊂' ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (⊂-∨1 ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (Partialⁿ-const Type₀ (suc (suc n)) (boundaryExpr (suc (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              (C→elim {n = suc (suc n)} OnBoundary) i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            i₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      intersection = {!prev-cyl i!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- prev-cyl' : I → Partialⁿ (NBoundary (suc (suc n))) (suc n) (boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- prev-cyl' i' = Partialⁿ-map (suc n) (cyl'' (inside i')) (NBoundaryω (suc n))

-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- prev-cyl : I → Partialⁿ (NBoundary (suc (suc n))) (suc n) (boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- prev-cyl i' = Partialⁿ-map (suc n) (
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --                  ( {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --                   ∙∙ (λ i' → cyl'' (inside i')) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --                   {!!} ) i'
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --                  ) (NBoundaryω (suc n))

-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- intersection : Partialⁿ (NBoundary (suc (suc n))) (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --                  (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- intersection = ⊂'-∧2
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --                    ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --                    (boundaryExpr (suc n)) (prev-cyl i)

-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- cc : InsideOfω {A = NCube (suc n)} {n = suc n} (
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --            Partialⁿ-map 
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --            (suc n) boundaryInj (NBoundaryω (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- cc = {!inSⁿ ? ? ?!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- cc2 : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- cc2 = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- c0 : InsideOfω (prev-cyl i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- c0 = Subⁿ-map (suc n) (lid false ∘ boundaryInj) cc2 

-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- c1 : InsideOfω (prev-cyl i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- c1 = Subⁿ-map (suc n) (lid true ∘ boundaryInj) cc2

-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- ps : Partialⁿ-Sub (NBoundary (suc (suc n))) (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --        ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (boundaryExpr (suc n)) intersection
-- -- -- -- -- -- -- -- -- -- -- -- -- --      -- ps = Partialⁿ-Sub-ends-split n prev-cyl
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --        c0
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --        c1
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --   -- let z : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --      --   --     z = 

-- -- -- -- -- -- -- -- -- -- -- -- -- --      --   -- in {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↑ clean 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -------------------------

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryω→NBoundary= :  ∀ {ℓ} → ∀ (A : Type ℓ) → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → (pa : Boundaryω A (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → Path ((a : NBoundary n) → A) (C→-app
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (Partialⁿ-IsOne⊂ {ℓ} A n (boundaryExpr (suc n) i0) (pa i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (1⊂lid n false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    ∘ boundaryInj)
                   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (C→-app
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (Partialⁿ-IsOne⊂ A n (boundaryExpr (suc n) i1) (pa i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (1⊂lid n true))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    ∘ boundaryInj)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryω→NBoundary= = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryω→NBoundary :  ∀ {ℓ} → ∀ (A : Type ℓ) → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → Boundaryω A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → NBoundary n → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryω→NBoundary A (suc n) pa =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let e : Bool → NCube n → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      e = λ b → C→-app (Partialⁿ-IsOne⊂ _ _ _ (pa (Bool→I b)) (1⊂lid n b))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in  NBoundary-rec e {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω2 : Boundaryω (NBoundary 2) 2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω2 i i₁ (i = i1) = lid' true (inside i₁ ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω2 i i₁ (i = i0) = lid' false (inside i₁ ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω2 i i₁ (i₁ = i1) = cyl' (lid' true []) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω2 i i₁ (i₁ = i0) = cyl' (lid' false []) i






-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryωₖ : ∀ n → ∀ k → Partialⁿ (NBoundary (k + n)) (k + n) (liftExpr k (boundaryExpr n))





-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test : ∀ n → Boundaryω (NBoundary n) n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test0' : Boundaryω (NBoundary 3) 3
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test0' i₀ i₁ i₂ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let cu = (nCubeω 3 i₀ i₁ i₂ 1=1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   primPOr i₀ _ (λ _ → lid true (tail cu))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr (~ i₀) _ (λ _ → lid false (tail cu))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr i₁ _ (λ _ → cyl' (lid true (inside i₂ ∷ [])) i₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr (~ i₁) _ (λ _ → cyl' ((lid false (inside i₂ ∷ []))) i₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ((primPOr i₂ _ (λ p → cyl' (cyl' (lid true []) i₁) i₀ ) --NBoundaryω2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr (~ i₂) i0 ((λ p → cyl' (cyl' (lid false []) i₁) i₀ ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      empty))))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test1' : Boundaryω (NBoundary 3) 3
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test1' i₀ i₁ i₂ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let cu = (nCubeω 3 i₀ i₁ i₂ 1=1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   primPOr i₀ (~ i₀ ∨ i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid true (tail cu))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr (~ i₀) (i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid false (tail cu))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ p →  cyl' (NBoundaryω2 i₁ i₂ p) i₀)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test2'' : (bd : Boundaryω (NBoundary 2) 2) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    → InsideOfω {A = NCube 2} {n = 2}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((Partialⁿ-map {A = NBoundary 2} {B = NCube 2} 2 boundaryInj bd))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    →  Boundaryω (NBoundary 3) 3
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test2'' bd y i₀ i₁ i₂ = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let x = NBoundary-cyl 2 bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p = snd (InsideOfω→InsideOf
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (Partialⁿ-map {A = NBoundary 2} {B = NCube 2} 2 boundaryInj bd) y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     primPOr (i₀ ∨ (~ i₀)) (boundaryExpr 2 i₁ i₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (primPOr i₀  (~ i₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ _ → lid true (p i₁ i₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ _ → lid false (p i₁ i₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ p → (x i₁ i₂ p i₀ )


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test2''' : (bd : Boundaryω (NBoundary 2) 2) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    → InsideOfω {A = NCube 2} {n = 2}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((Partialⁿ-map {A = NBoundary 2} {B = NCube 2} 2 boundaryInj bd))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    →  Boundaryω (NBoundary 3) 3
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test2''' bd y i₀ i₁ i₂ = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let cu = (nCubeω 2 i₁ i₂ 1=1)
      
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       x = NBoundary-cyl 2 bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p = snd (InsideOfω→InsideOf
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (Partialⁿ-map {A = NBoundary 2} {B = NCube 2} 2 boundaryInj bd) y)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       x' : .(IsOne (boundaryExpr 2 i₁ i₂)) → Sub (NBoundary 3) ((i₀ ∨ (~ i₀)) ∧ (boundaryExpr 2 i₁ i₂) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (primPOr (i₀ ∧ (boundaryExpr 2 i₁ i₂)) ((~ i₀) ∧ (boundaryExpr 2 i₁ i₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (⊂'-∧2 ((negIf true i₀)) (boundaryExpr 2 i₁ i₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (Partialⁿ-map {A = NBoundary 2} 0 (lid true ∘ boundaryInj) (bd i₁ i₂)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (⊂'-∧2 ((negIf false i₀)) (boundaryExpr 2 i₁ i₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (Partialⁿ-map {A = NBoundary 2} 0 (lid false ∘ boundaryInj) (bd i₁ i₂)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       x' = λ .z → inS ((x i₁ i₂ z i₀ ))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p' : Subⁿ (NCube 2) 0 (boundaryExpr 2 i₁ i₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (Partialⁿ-map 2 boundaryInj bd i₁ i₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p' = y i₁ i₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     primPOr (i₀ ∨ (~ i₀)) (boundaryExpr 2 i₁ i₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (primPOr i₀  (~ i₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ _ → lid true (outS p'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ _ → lid false (outS p'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ p → outS (x' p)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- primPOr i₀ (~ i₀ ∨ i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid true (p i₁ i₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr (~ i₀) (i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid false (p i₁ i₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ p → (x i₁ i₂ p i₀ ))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkaeBN-step : ∀ {n} {bd : Boundaryω (NBoundary (suc n)) (suc n)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  {y : InsideOfω (Partialⁿ-map boundaryInj bd)} {i} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                PartialPⁿ n (boundaryExpr (suc n) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (Partialⁿ-map
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (λ x₁ → lid false (boundaryInj x₁) ≡ lid true (boundaryInj x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (bd i)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                InsideOf
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   C→-app
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (outSⁿ n (boundaryExpr (suc n) i) (Partialⁿ-map boundaryInj (bd i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (y i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (boundaryInj x₁)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ∀ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                Partialⁿ (NBoundary' boundaryInj) n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ boundaryExpr (suc n) i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkaeBN-step = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- makeNBoundaryω : ∀ n → (bd : Boundaryω (NBoundary n) n) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    → InsideOfω {A = NCube n} {n = n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((Partialⁿ-map {A = NBoundary n} {B = NCube n} n boundaryInj bd))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    →  Boundaryω (NBoundary (suc n)) (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- makeNBoundaryω zero bd _ i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (primPOr i  (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ _ → lid true [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ _ → lid false [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- makeNBoundaryω (suc n) bd y i i₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    let x = NBoundary-cyl (suc n) bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        p = snd (InsideOfω→InsideOf
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (Partialⁿ-map {A = NBoundary (suc n)} {B = NCube (suc n)} (suc n) boundaryInj bd) y)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        x' : PartialPⁿ n (boundaryExpr (suc n) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (Partialⁿ-map (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (λ x₁ → lid false (boundaryInj x₁) ≡ lid true (boundaryInj x₁)) bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        x' = x i
       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        p' : InsideOf
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  fst (InsideOfω→InsideOf (λ i₂ → Partialⁿ-map (suc n) boundaryInj bd i₂) y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (cyl'' (inside i) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        p' = p i


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        w : Partialⁿ (NBoundary (suc (suc n))) n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (boundaryExpr (suc (suc n)) i i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        w = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    in w


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test3-test : (i : I) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test3-test i = {!NBoundaryω-test3'' _ i i1!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω↑ : ∀ n → boundaryω-isOk n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    →  Boundaryω (NBoundary (suc n)) (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω↑ = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test3'' : boundaryω-isOk 2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    →  Boundaryω (NBoundary 3) 3
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test3'' x i₀ i₁ i₂ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      let cu = (nCubeω 2 i₁ i₂ 1=1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      primPOr i₀ (~ i₀ ∨ i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid true cu)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr (~ i₀) (i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid false cu)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ p →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ((λ i → lid' false (snd (x i₁ i₂ p) (i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ((λ i₀ → cyl'  (fst (x i₁ i₂ p)) i₀))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           λ i → lid' true (snd (x i₁ i₂ p) (~ i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            i₀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        )



-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- let cu = (nCubeω 3 i₀ i₁ i₂ 1=1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     p = snd (InsideOfω→InsideOf
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           (Partialⁿ-map {A = NBoundary 2} {B = NCube 2} {n = 2} boundaryInj bd) y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- primPOr i₀ (~ i₀ ∨ i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid true (p i₁ i₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   (primPOr (~ i₀) (i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂ ∨ i0) (λ _ → lid false (p i₁ i₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   λ p → (x i₁ i₂ p i₀ ))



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test' : InsideOfω {A = ℕ} {n = 3} (Partialⁿ-const ℕ 3 (boundaryExpr 3) (C-const 3 1 ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    → Boundaryω ℕ 4
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test' x i₀ i₁ i₂ i₃ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   primPOr i₀ (~ i₀ ∨  (~ i₀) ∨ (boundaryExpr 3 i₁ i₂ i₃)) (λ _ → 1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr (~ i₀) (boundaryExpr 3 i₁ i₂ i₃) (λ _ → 1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        λ _ → outS (x i₁ i₂ i₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        )

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test'2 : ∀ {ℓ} → {A : Type ℓ} → (NCube 4 → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    → Boundaryω A 4
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test'2 x i₀ i₁ i₂ i₃ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   primPOr i₀ (~ i₀ ∨  (~ i₀) ∨ (boundaryExpr 3 i₁ i₂ i₃)) (λ _ → (C→elim x i₀ i₁ i₂ i₃ 1=1))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr (~ i₀) (boundaryExpr 3 i₁ i₂ i₃) (λ _ → (C→elim x i₀ i₁ i₂ i₃ 1=1))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        λ _ → (C→elim x i₀ i₁ i₂ i₃ 1=1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        )

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test'3 : ∀ {ℓ} → {A : Type ℓ} → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    → Boundaryω A 4
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-test'3 x i₀ i₁ i₂ i₃ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   primPOr i₀ (~ i₀ ∨  (~ i₀) ∨ (boundaryExpr 3 i₁ i₂ i₃)) (λ _ → x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr (~ i₀) (boundaryExpr 3 i₁ i₂ i₃) (λ _ → x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        λ _ → x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        )

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish' : ∀ {ℓ} → {A : Type ℓ} → A → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → Boundaryω A (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish' a zero i = primPOr i (~ i) (λ _ → a) λ _ → a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish' a (suc n) i i₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let z : Partialⁿ _ n (boundaryExpr (suc n) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       z = NBoundaryω-finish' a n i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in {!z!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish0 : ∀ {ℓ} → {A : Type ℓ} → (a : A) → (i : I) → (j : I)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         → (z : Partial j (a ≡ a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         → Partial (i ∨ ~ i ∨ j) A  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish0 a i j z =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       primPOr i (~ i ∨ j) (λ _ → a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (primPOr (~ i) (j) (λ _ → a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          λ p → z p i 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        )

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finishTy :  ∀ {ℓ} → (A : Type ℓ) → (a : A) → (j : I) → ℕ → Typeω
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finishTy A a j zero = ∀ i → Partial j (a ≡ a) → Partial (i ∨ ~ i ∨ j) A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finishTy A a j (suc n) = ∀ iₖ → NBoundaryω-finishTy A a (j ∨ iₖ ∨ (~ iₖ)) n 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish : ∀ {ℓ} → (A : Type ℓ) → (a : A) → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → NBoundaryω-finishTy A a i0 n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish A a zero i _ =  primPOr i (~ i) (λ _ → a) (λ _ → a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish A a (suc zero) i j = NBoundaryω-finish0 a j (i ∨ ~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish A a (suc (suc n)) i iₖ = NBoundaryω-finish A a (suc n) ((i ∨ ~ i) ∨ iₖ ∨ ~ iₖ)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finishTy :  ∀ {ℓ} → (m : ℕ) → (j : I) → ℕ → Typeω
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finishTy m j zero = ∀ i → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                → Partial j (lid' false  {!!} ≡ lid' true {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                → Partial (i ∨ ~ i ∨ j) (NBoundary m)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finishTy m j (suc n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ∀ iₖ → NBoundaryω-finishTy A a (j ∨ iₖ ∨ (~ iₖ)) n 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish : ∀ {ℓ} → (A : Type ℓ) → (a : A) → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish A a = {!PartialP!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-A4 : ∀ {ℓ} → (A : Type ℓ) → (a : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → Boundaryω A 4
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-A4 A a = {!NBoundaryω-finish A a 3 !}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-A : ∀ {ℓ} → (A : Type ℓ) → (a : A) → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → Boundaryω A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-A A a = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-↓ : ∀ {ℓ} → {A : Type ℓ} → (j : I) → Partial j A → (n : ℕ) → (k : ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    →  Partialⁿ A (k + n) ( liftExpr k (boundaryExpr n)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-↓ j x zero zero ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-↓ j x (suc n) zero = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-↓ j x n (suc k) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- eatLast : ∀ {ℓ} → {A : Type ℓ} → (a : A) → (n : ℕ) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- eatLast = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish : ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → InsideOfω {n = suc n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          (Partialⁿ-const (NCube (suc n)) n (boundaryExpr n) ({!nCubeω n!} ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → Boundaryω (NBoundary (suc n)) (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish zero x i = primPOr i (~ i) {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω-finish (suc n) x i = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- zzz : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- zzz = {!NBoundaryω-test'!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω : ∀ n → Boundaryω (NBoundary n) n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-cyl : ∀ n → PartialPⁿ n (boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           (Partialⁿ-map {A = NBoundary n} {B = Type₀} {n = n} {e = (boundaryExpr n)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (λ x → lid' false (boundaryInj x) ≡ lid' true (boundaryInj x) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (NBoundaryω n))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sub₁ : ∀ n → Partialⁿ-Sub (NBoundary (suc (suc n))) (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (λ _ → boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (NBoundaryω-intersection (suc n))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sub₂ : ∀ n → Partialⁿ-Sub (NBoundary (suc (suc n))) (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (λ _ → boundaryExpr (suc n)) (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (⊂→⊂' {n = suc (suc n)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ((λ _ → boundaryExpr (suc n)) ∧ⁿ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∧ⁿ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (λ _ → boundaryExpr (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (∧-comm {n = suc (suc n)} (λ _ → boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (NBoundaryω-intersection (suc n)))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hhEnds : ∀ n → ∀ i i₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           →  Partialⁿ (NBoundary (suc n)) n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ boundaryExpr (suc n) i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hhEnds n i i₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω zero ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω (suc zero) i = primPOr i (~ i) (λ _ → lid false []) λ _ → lid true []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryω (suc (suc n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Partial∨ⁿ (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ _ → boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (NBoundaryω-intersection (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (sub₁ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (sub₂ n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sub₁ zero i i₁ ei=1 = inS {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sub₁ (suc n) i i₁ = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sub₂ zero i i₁ ei=1 = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sub₂ (suc n) i i₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryωₖ zero zero ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryωₖ (suc zero) zero i = primPOr i (~ i) (λ _ → lid false []) λ _ → lid true []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryωₖ (suc (suc n)) zero = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryωₖ zero (suc k) _ = Partialⁿ-lift-i0 k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundaryωₖ (suc n) (suc k) i = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Partialⁿ-map 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {A = NBoundary (k + suc n)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {B = (NBoundary (suc k + suc n))} {n = (k + suc n)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (cyl'' (inside i)) (NBoundaryωₖ (suc n) k) 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-cyl zero ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-cyl (suc zero) i = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-cyl (suc (suc n)) i = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Goal: Partialⁿ {ℓ-zero} (NBoundary (suc k + suc n)) (k + suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (liftExpr {suc n} (suc k) (boundaryExpr (suc n)) i)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω2' : Partialⁿ (NCube 2) 2 (boundaryExpr 2) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω2' i₀ i₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (i₀ = i0) →  inside i₀ ∷ inside i₁ ∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ; (i₀ = i1) →  inside i₀ ∷ inside i₁ ∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ; (i₁ = i0) →  inside i₀ ∷ inside i₁ ∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ; (i₁ = i1) → inside i₀ ∷ inside i₁ ∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω2'' : Partialⁿ (NCube 2) 2 (boundaryExpr 2) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω2'' i₀ i₁ = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   primPOr (i₀ ∨ ~ i₀) (i₁ ∨ ~ i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr i₀ (~ i₀) (λ _ →  inside i₀ ∷ inside i₁ ∷ []) λ _ →  inside i₀ ∷ inside i₁ ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr i₁ (~ i₁) (λ _ →  inside i₀ ∷ inside i₁ ∷ []) λ _ →  inside i₀ ∷ inside i₁ ∷ [])

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω2''' : Partialⁿ (NCube 2) 2 (boundaryExpr 2) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω2''' i₀ i₁ = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   primPOr i₀ (~ i₀ ∨ i₁ ∨ ~ i₁) (λ _ → inside i₀ ∷ inside i₁ ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr (~ i₀) (i₁ ∨ ~ i₁) ((λ _ → inside i₀ ∷ inside i₁ ∷ []))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (primPOr i₁ (~ i₁) ((λ _ → inside i₀ ∷ inside i₁ ∷ [])) (λ _ → inside i₀ ∷ inside i₁ ∷ [])))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pOrⁿ :  ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n → (a : NCube n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → Partialⁿ A n (⋁expr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pOrⁿ zero a ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pOrⁿ (suc zero) a i = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pOrⁿ (suc (suc n)) a = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-POr1 : Partialⁿ (NCube 4) 4 (⋁expr 4)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-POr1 i₀ i₁ i₂ i₃ = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   primPOr i₀ (i₁ ∨ i₂ ∨ i₃) {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (primPOr i₁ (i₂ ∨ i₃) {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (primPOr i₂ i₃ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           {!i₃!}))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω : ∀ n → NCubeBoundaryω n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOk : ∀ n → InsideOfω {n = n} (nCubeBoundaryω n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω zero ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω (suc zero) i = primPOr i (~ i) (λ _ → end true ∷ []) λ _ → end false ∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω (suc (suc n)) i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOk = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- λ _ →  inside i₀ ∷ inside i₁ ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --(primPOr i₁ (~ i₁) (λ _ →  inside i₀ ∷ inside i₁ ∷ []) λ _ →  inside i₀ ∷ inside i₁ ∷ [])



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- problem-with-nCubeBoundaryω : (i₀ i₁ : I) → (x : IsOne (boundaryExpr 2 i₀ i₁) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 →  nCubeBoundaryω2'' i₀ i₁ x ≡ nCubeBoundaryω' 2  i₀ i₁ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- problem-with-nCubeBoundaryω i₀ i₁ x = {!refl!} -- refl do not typecheck here

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- problem-with-nCubeBoundaryω' : (i₀ i₁ : I) → (x : IsOne (boundaryExpr 2 i₀ i₁) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 →  nCubeBoundaryω2' i₀ i₁ x ≡ nCubeBoundaryω2''' i₀ i₁ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- problem-with-nCubeBoundaryω' i₀ i₁ x = {!refl!} -- refl do not typecheck here

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-nCubeBoundaryω' : (i₀ i₁ : I) → (x : IsOne (boundaryExpr 2 i₀ i₁) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 →  nCubeBoundaryω2' i₀ i₁ x ≡ nCubeBoundaryω' 2 i₀ i₁ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-nCubeBoundaryω' i₀ i₁ x = {!nCubeBoundaryω' 2  !} 







-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω : ∀ n → NCubeBoundaryω n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOk : ∀ n → InsideOfω {n = n} (nCubeBoundaryω n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ∨-Ends :    ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    → ∀ i → ∀ j
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    → Partialⁿ (NCube (suc n)) (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          ((([ i ]Iexpr) ∨ⁿ ([ ~ i ]Iexpr))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                ∨ⁿ j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ∨-Ends zero i j = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ∨-Ends (suc n) i j = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test1 : ∀ (i : I) → Partial (i ∨ ~ i) Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test1 i = primPOr i (~ i) {λ _ → (Interval')} (λ _ → inside i) (λ _ → inside i)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test2 = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω zero ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω (suc zero) i = primPOr i (~ i) (λ _ → end true ∷ []) λ _ → end false ∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω (suc (suc n)) i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let w : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- Partialⁿ∨-Ends (suc n) i (boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- ? ? ? 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOk zero = inS []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOk (suc zero) i = inS (inside i ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOk (suc (suc n)) = {!!}








-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sq-help : ∀ {n} → (bd : NBoundary (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → Square {A = NBoundary (suc (suc (suc n)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (λ i → lid false (boundaryInj (cyl bd i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (λ i → lid true (boundaryInj (cyl bd i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (λ i → cyl (lid false (boundaryInj bd)) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               λ i → cyl (lid true (boundaryInj bd)) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sq-help bd i i₁ = cyl' (cyl' bd i₁) i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sq-Cu-help : ∀ n → (b : Bool) → C→ (NBoundary (suc n)) n 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sq-Cu-help zero b _ = lid' b []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sq-Cu-help (suc n) b i = C→map {n = n} (cyl'' (inside i)) (sq-Cu-help n b)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Cu-help : ∀ n → C→ (NBoundary n) n → C→ (NBoundary (suc n)) (suc n) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Cu-help zero x x₁ = ⊥-recω (x 1=1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Cu-help (suc n) x i = C→map {n = suc n} (cyl'' (inside i)) x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nCubeBoundaryω


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ------------




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --------------------------




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PartialCuTy : ∀ n → (e : C→I n) → Typeω
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PartialCuTy n cu = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ppp∨Ty : ∀ n → NCube n → Typeω
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ppp∨Ty n cu = {!  !}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -------------------------

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Face-lem :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → ∀ k → ∀ b → ∀ cu
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → Σ[ x ∈ NBoundary (suc n) ] faceMap k b cu ≡ boundaryInj x            
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Face-lem = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary-comp :
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → Partialⁿ (NBoundary n) n (boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary-comp n pa =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {! !}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary-step : ∀ n →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              Partialⁿ (NBoundary n) n (boundaryExpr n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             → Partialⁿ (NBoundary (suc n)) (suc n) (boundaryExpr (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary-step zero x i = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary-step (suc n') x i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let n = suc n'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Partialⁿ-const (NBoundary (suc n)) n (boundaryExpr (suc n) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (C→elim {n = n} {A = (NBoundary (suc n))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ x₁ →  ((λ j → cyl (lid false {!!}) (i ∧ j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∙∙ (λ i₁ → cyl (cyl {!!} i₁) i) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ j → cyl (lid true {!!}) (i ∨ j))) i)
    

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary : ∀ n → Partialⁿ (NBoundary n) n (boundaryExpr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary zero ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary 6 = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary (suc n) = {!!}








-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary→ω : (n : ℕ) → (NBoundary n) → I → NCubeBoundaryω (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary→ω = {!!}
 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary : ∀ n → Partialⁿ (NBoundary n) n (boundaryExpr n)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundary→ω : ∀ {ℓ} → {A : Type ℓ} → (n : ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → (NBoundary n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → Boundaryω A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundary→ω n bd = Partialⁿ-map {n = n} bd (Partialⁿ-NBoundary n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary = {!!}










-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-intersec : ∀ n → ∀ i j → Partialⁿ (NBoundary (suc (suc n))) n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                      (([_]Iexpr n i ∨ⁿ [_]Iexpr n (~ i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                        ∧ⁿ boundaryExpr (suc n) j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-intersec zero i j =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (i = i1)(j = i0) → lid true (inside j ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ;   (i = i1)(j = i1) → lid true (inside j ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ;   (i = i0)(j = i0) → lid false (inside j ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ;   (i = i0)(j = i1) → lid false (inside j ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-intersec (suc n) i j i' =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let z = NBoundary-intersec n i i'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    in {! !}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary zero ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary (suc zero) i = λ { (i = i0) → lid false [] ; (i = i1) → lid true []  }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary (suc (suc zero)) i i₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundary (suc (suc n)) i i₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- let
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --     l :  ∀ n → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --     l = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Partial∨ⁿ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (([_]Iexpr i ∨ⁿ [_]Iexpr (~ i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (boundaryExpr (suc n) i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (NBoundary-intersec n i i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- let z : Partialⁿ (NBoundary (suc (suc n))) (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                   λ _  → boundaryExpr (suc n) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --     z = λ i → Partialⁿ-map {n = suc n} (λ x → cyl' x i) (Partialⁿ-NBoundary (suc n))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --     zz : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --     zz = {!!}
       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- in 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   Partialⁿ-boundaryExpr n i j
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      (C→elim {n = n} {A = NBoundary (suc (suc n))} (λ x → lid false (inside j ∷ x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      (C→elim {n = n} {A = NBoundary (suc (suc n))} (λ x → lid true (inside j ∷ x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      (pse n i j)




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- Partialⁿ-map {n = suc (suc n)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --    (λ x → cyl'' (head x) {! tail x!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --    (nCubeBoundaryω (suc (suc n)))
   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --(Partialⁿ-NBoundarySE n i i₁ (Partialⁿ-NBoundary (suc n)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyl {n = 1} {injX = boundaryInj {1}} (x i₁ j=1) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundarySE zero i i₁ x j=1 = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Partialⁿ-NBoundarySE (suc n) i i₁ x = {!!}




  





-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- let z = {!ppp n !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- in {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fromBoundaryω : ∀ n → Boundaryω A n →  



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical : ∀ {ℓ} → {A : Type ℓ} → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end0 : NCube n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end1 : NCube n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end0 ∘ boundaryInj ≡ end1 ∘ boundaryInj) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → NBoundary (suc n) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical zero end0 end1 x (lid x₁ _) = caseBool end1 end0 x₁ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical (suc n) end0 end1 x (lid x₁ x₂) = caseBool end1 end0 x₁ x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical (suc n) end0 end1 x (cyl x₁ i) = x i x₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- abfc : ∀ {ℓ} → {A : Type ℓ} → ∀ n →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         Iso (Σ ((NCube n) → A) (λ end0 →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              Σ ((NCube n) → A) λ end1 →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (end0 ∘ boundaryInj ≡ end1 ∘ boundaryInj) ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (NBoundary (suc n) → A )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (abfc zero) x (lid false x₂) = fst x _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (abfc zero) x (lid true x₂) = fst (snd x) _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.inv (abfc zero) x) = (const (x (lid false _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (snd (Iso.inv (abfc zero) x)) = (const (x (lid true _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (snd (Iso.inv (abfc zero) x)) i ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (abfc zero) b i (lid false x₁) = b (lid false _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (abfc zero) b i (lid true x₁) = b (lid true _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.leftInv (abfc {ℓ} {A} zero) (fst₁ , fst₂ , snd₁) i) x = fst₁ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (snd (Iso.leftInv (abfc {ℓ} {A} zero) (fst₁ , fst₂ , snd₁) i)) = fst₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (snd (Iso.leftInv (abfc {ℓ} {A} zero) (fst₁ , fst₂ , snd₁) i)) i₁ ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (abfc (suc n)) x = assembleBoundaryFromCubical (suc n) (fst x) (fst (snd x)) (snd (snd x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (abfc (suc n)) x = x ∘ (lid false) , (x ∘ (lid true) , λ i a → x (cyl a i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (abfc (suc n)) b i (lid false x₁) =  b (lid false x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (abfc (suc n)) b i (lid true x₁) =  b (lid true x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (abfc (suc n)) b i (cyl x i₁) = b (cyl x i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.leftInv (abfc {ℓ} {A} (suc n)) a i) = fst a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (snd (Iso.leftInv (abfc {ℓ} {A} (suc n)) a i)) = fst (snd a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (snd (Iso.leftInv (abfc {ℓ} {A} (suc n)) a i)) = snd (snd a)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi=-retr : ∀ {ℓ} → (A : Type ℓ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ∀ n → retract {B = Σ (NBoundary n → A) (InsideOf)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (λ x → (x ∘ boundaryInj {n}) , (insideOf x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (toCubical ∘ snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi=-retr A zero a i = a 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi=-retr A (suc n) a i (end false , x₁) = cubi=-retr A n (a ∘ ( inside i0 ,_)) i x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi=-retr A (suc n) a i (end true , x₁) = cubi=-retr A n (a ∘ ( inside i1 ,_)) i x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi=-retr A (suc n) a i (inside i₁ , x₁) = cubi=-retr A n (a ∘ ( inside i₁ ,_)) i x₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi=-sec : ∀ {ℓ} → (A : Type ℓ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ∀ n → section {B = Σ (NBoundary (suc n) → A) (InsideOf)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (λ x → (x ∘ boundaryInj {(suc n)}) , (insideOf x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (λ x → toCubical {bd = fst x } (snd x))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi=0 : ∀ {ℓ} → (A : Type ℓ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∀ n → Iso (NCube n → A) (Σ (NBoundary n → A) (InsideOf))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi=0 A n = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi= : ∀ {ℓ} → (A : Type ℓ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∀ n → Iso (NCube (suc n) → A) (Σ (NBoundary (suc n) → A) (InsideOf))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi= A n = iso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ x → (x ∘ boundaryInj) , (insideOf x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (toCubical ∘ snd )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (cubi=-sec A n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (cubi=-retr A (suc n))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubiHE : ∀ {ℓ} → (A : Type ℓ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∀ n → HAEquiv (NCube (suc n) → A) (Σ (NBoundary (suc n) → A) (InsideOf))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubiHE A n = iso→HAEquiv (cubi= A n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi=-sec A zero b = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi=-sec A (suc n) b = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubi=-sec {ℓ} A (suc n) (bd , p) = zz
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pp0 : _,_ {B = InsideOf} (toCubical {bd = λ x → bd (lid false (boundaryInj x))} (p i0) ∘ boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (insideOf (toCubical {bd = (λ x → bd (lid false (boundaryInj x)))} (p i0))) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ((λ x → bd (lid false (boundaryInj x))) , p i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pp0 = cubi=-sec A n ((bd ∘ (lid false) ∘  boundaryInj) , p i0)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pp1 : (toCubical (p i1) ∘ boundaryInj ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          insideOf (toCubical {bd = (λ x → bd (lid true (boundaryInj x)))} (p i1))) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ((λ x → bd (lid true (boundaryInj x))) , p i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pp1 = cubi=-sec A n ((bd ∘ (lid true) ∘  boundaryInj) , p i1)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ppI : (i : I) → (_,_ {B = InsideOf} (toCubical {bd = λ x → bd (cyl'' (inside i) x)} (p i) ∘ boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (insideOf {A = A}  (toCubical {bd = (λ x → bd (cyl'' (inside i) x))} (p i)))) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ((λ x → bd (cyl'' (inside i) x)) , p i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ppI i = cubi=-sec A n ((bd ∘ (cyl'' (inside i))) , p i)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Iso


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ssX00 : (cc : NCube n) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 toCubical (insideOf (λ x → bd (lid false (inside i0 , x)))) cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → bd (lid false (inside i0 , cc)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → cubi=-retr A n (λ x → bd (lid false (inside i0 , x))) i cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (cubi=-sec A n ((λ x → bd (lid false (boundaryInj x))) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (λ i₁ → insideOf (λ x₁ → bd (lid false (inside i₁ , x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (lid false cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ssX00 cc i i₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ssX01 : (cc : NCube n) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 toCubical (insideOf (λ x → bd (lid false (inside i1 , x)))) cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → bd (lid false (inside i1 , cc)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → cubi=-retr A n (λ x → bd (lid false (inside i1 , x))) i cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (cubi=-sec A n ((λ x → bd (lid false (boundaryInj x))) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    λ i₁ → insideOf (λ x₁ → bd (lid false (inside i₁ , x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    ) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (lid true cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ssX01 cc i i₁ = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ss0 : (cc : NCube n) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → toCubical (p (i0) i) cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → bd (lid false (inside i , cc)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (cubi=-sec A n ((λ x → bd (lid false (boundaryInj x))) , p i0) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (lid false cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (cubi=-sec A n ((λ x → bd (lid false (boundaryInj x))) , p i0) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (lid true cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ss0 cc i i₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            hcomp {A = A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ((λ k → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (i = i0) → cubi=-retr A n (bd ∘ (lid false) ∘ ( (inside i₁) ,_)) i0 cc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; (i = i1) → cubi=-retr A n (bd ∘ (lid false) ∘ ( (inside i₁) ,_)) i1 cc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; (i₁ = i0) → ssX00 cc i k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; (i₁ = i1) → ssX01 cc i k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            }))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (cubi=-retr A n (bd ∘ (lid false) ∘ ( (inside i₁) ,_)) i cc)
 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ssX10 : (cc : NCube n) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 toCubical (insideOf (λ x → bd (lid true (inside i0 , x)))) cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → bd (lid true (inside i0 , cc)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → cubi=-retr A n (λ x → bd (lid true (inside i0 , x))) i cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (cubi=-sec A n ((λ x → bd (lid true (boundaryInj x))) , p i1) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (lid false cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ssX10 cc i i₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ssX11 : (cc : NCube n) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 toCubical (insideOf (λ x → bd (lid true (inside i1 , x)))) cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → bd (lid true (inside i1 , cc)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → cubi=-retr A n (λ x → bd (lid true (inside i1 , x))) i cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (cubi=-sec A n ((λ x → bd (lid true (boundaryInj x))) , p i1) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (lid true cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ssX11 cc i i₁ = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ss1 : (cc : NCube n) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → toCubical (p (i1) i) cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i → bd (lid true (inside i , cc)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (cubi=-sec A n ((λ x → bd (lid true (boundaryInj x))) , p i1) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (lid false cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (cubi=-sec A n ((λ x → bd (lid true (boundaryInj x))) , p i1) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (lid true cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ss1 cc i i₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              hcomp {A = A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ((λ k → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (i = i0) → cubi=-retr A n (bd ∘ (lid true) ∘ ( (inside i₁) ,_)) i0 cc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; (i = i1) → cubi=-retr A n (bd ∘ (lid true) ∘ ( (inside i₁) ,_)) i1 cc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; (i₁ = i0) → ssX10 cc i k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; (i₁ = i1) →  ssX11 cc i k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            }))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (cubi=-retr A n (bd ∘ (lid true) ∘ ( (inside i₁) ,_)) i cc)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- sss0 : (k i i₂ : I) → InsideOf (λ x → fst (ppI i0 i) (cyl'' (inside i₂) x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- sss0 k i i₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- sss1 : (k i i₂ : I) → InsideOf (λ x → fst (ppI i1 i) (cyl'' (inside i₂) x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- sss1 k i i₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cucu : (cc : NBoundary n) → Cube
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ i i₁ → toCubical (p i i₁) (boundaryInj cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ i i₁ → bd (cyl (cyl cc i₁) i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (ss0 (boundaryInj cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (ss1 (boundaryInj cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ i i₁ → fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                    (lid false (boundaryInj cc)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          λ i i₁ →  fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                     (lid true (boundaryInj cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cucu cc i i₁ i₂ = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          hcomp {A = A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ((λ k → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (i = i0) →  toCubical (p i₁ i₂) (boundaryInj cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; (i = i1) → bd (cyl (cyl cc i₂) i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; (i₂ = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; (i₂ = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            }))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ({!!})


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ toCubical (p i₁ i₂) (boundaryInj cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ bd (cyl (cyl cc i₂) i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i₁ = i0 ⊢ hcomp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ { k (i = i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → cubi=-retr A n (λ x → bd (lid false (inside i₂ , x))) i0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (boundaryInj cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; k (i = i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → cubi=-retr A n (λ x → bd (lid false (inside i₂ , x))) i1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (boundaryInj cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; k (i₂ = i0) → ssX00 (boundaryInj cc) i k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; k (i₂ = i1) → ssX01 (boundaryInj cc) i k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (cubi=-retr A n (λ x → bd (lid false (inside i₂ , x))) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (boundaryInj cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i₁ = i1 ⊢ hcomp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ { k (i = i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → cubi=-retr A n (λ x → bd (lid true (inside i₂ , x))) i0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (boundaryInj cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; k (i = i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → cubi=-retr A n (λ x → bd (lid true (inside i₂ , x))) i1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (boundaryInj cc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; k (i₂ = i0) → ssX10 (boundaryInj cc) i k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; k (i₂ = i1) → ssX11 (boundaryInj cc) i k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (cubi=-retr A n (λ x → bd (lid true (inside i₂ , x))) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (boundaryInj cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i₂ = i0 ⊢ fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (lid false (boundaryInj cc))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i₂ = i1 ⊢ fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (lid true (boundaryInj cc))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Cucu : Cube
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Cucu i i₁ i₂ = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   zz : (toCubical {n = suc (suc n)} p ∘ boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         , insideOf {A = A} {n = suc (suc n)} (toCubical {bd = bd} p))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ≡ (bd , p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (zz i) (lid false (end false , snd₁)) = fst (pp0 i) (lid false snd₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (zz i) (lid false (end true , snd₁)) = fst (pp0 i) (lid true snd₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (zz i) (lid false (inside i₁ , snd₁)) = ss0 snd₁ i i₁ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (zz i) (lid true (end false , snd₁)) = fst (pp1 i) (lid false snd₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (zz i) (lid true (end true , snd₁)) =  fst (pp1 i) (lid true snd₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (zz i) (lid true (inside i₁ , snd₁)) = ss1 snd₁ i i₁ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (zz i) (cyl (lid false x₁) i₁) = fst (ppI i₁ i) (lid false x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (zz i) (cyl (lid true x₁) i₁) = fst (ppI i₁ i) (lid true x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (zz i) (cyl (cyl x i₂) i₁) = cucu x i i₁ i₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   snd (zz i) i₁ i₂ = {!!}
 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- hcomp {A = InsideOf (λ x → fst (ppI i₁ i) (cyl'' (inside i₂) x))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        ((λ k → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --           (i = i0) → insideOf (λ x₁ → toCubical
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --                       {bd = bd ∘ cyl'' (inside i₁) ∘ cyl'' (inside i₂)} (p i₁ i₂) x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --         ; (i = i1) → p i₁ i₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --         ; (i₁ = i0) → sss0 k i i₂ --ss0= k i i₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --         ; (i₁ = i1) → sss1 k i i₂ --ss1= k i i₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --         ; (i₂ = i0) → insideOf (λ x →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --                        fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --                          (lid false x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --         ; (i₂ = i1) → insideOf (λ x →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --                        fst (cubi=-sec A n ((λ x₁ → bd (cyl x₁ i₁)) , p i₁) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --                          (lid true x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        }))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        (snd (ppI i₁ i) i₂)




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- zz : (toCubical {n = suc (suc n)} p ∘ boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       , insideOf {A = A} {n = suc (suc n)} (toCubical {bd = bd} p))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       ≡ (bd , p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- fst (zz i) (lid false (fst₁ , snd₁)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- fst (zz i) (lid true (fst₁ , snd₁)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- fst (zz i) (cyl x i₁) = fst (ppI i₁ i) x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- snd (zz i) i₁ = {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ insideOf (toCubical p) i₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ p i₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i₁ = i0 ⊢ insideOf (λ x → fst (zz i) (lid false x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i₁ = i1 ⊢ insideOf (λ x → fst (zz i) (lid true x))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- another definition of n-path , inside Sn

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Globeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n} → (S (-1+ n) → A) → Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → ∀ (bd : (S (-1+ (suc n)) → A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → north))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → ∀ (bd : (S (-1+ (suc n)) → A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → south))
                 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Globeⁿ {A = A} {n = zero} bd = A 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Globeⁿ {A = A} {n = suc n} bd =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (λ i → Globeⁿ {n = n} ( bd ∘ (λ x → merid x i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (northGlobeⁿ {A = A} {n = n} bd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (southGlobeⁿ {A = A} {n = n} bd)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (a : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      →  (northGlobeⁿ {n = n} (λ _ → a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         ≡ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (southGlobeⁿ {n = n} (λ _ → a))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ {n = zero} bd = bd north
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ {ℓ} {A} {suc zero} bd _ = bd north
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ {ℓ} {A} {suc (suc n)} bd = north-south-const (bd north)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = zero} bd = bd south
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = suc zero} bd _ = bd south
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = suc (suc n)} bd = north-south-const (bd south)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const {n = zero} a = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const {n = suc zero} a = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const {n = suc (suc n)} a = refl




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- glob= : ∀ {ℓ} → (A : Type ℓ) → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → Iso (A) (Σ (_) (Globeⁿ {A = A} {n = n} ))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.fun (glob= A _) x) = const x 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.fun (glob= A zero) x) = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.fun (glob= A (suc n)) x) = north-south-const x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (glob= A zero) (fst₁ , snd₁) = snd₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (glob= A (suc n)) (fst₁ , snd₁) = fst₁ north
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A zero) b i) ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.rightInv (glob= A zero) b i) = snd b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc n)) b i) north = fst b north
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc zero)) b i) south = snd b i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc (suc n))) b i) south =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv (glob= A _) ((λ x → fst b (merid x i)) , snd b i)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc (suc n))) b i) (merid north i₁) = fst b (merid north (i ∧ i₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc (suc n))) b i) (merid south i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.rightInv (glob= A (suc (suc n))) b i) (merid (merid a i₂) i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.rightInv (glob= A (suc zero)) b i) i₁ = {!!} --snd b (i ∧ i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.rightInv (glob= A (suc (suc n))) b i) i₁ = ?

  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (glob= A zero) a = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (glob= A (suc n)) a = refl


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           (λ x → (x ∘ boundaryInj) , (insideOf x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           (toCubical ∘ snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           (ri _) (li _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- li : ∀ n → retract {B = Σ (NBoundary n → A) (InsideOf)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (λ x → (x ∘ boundaryInj {n}) , (insideOf x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (toCubical ∘ snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- li = ?


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ri : ∀ n → section {B = Σ (NBoundary n → A) (InsideOf)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (λ x → (x ∘ boundaryInj {n}) , (insideOf x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (toCubical ∘ snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ri = ?




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S relates Paths inside of S and NBoundary 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S₊ : ∀ {n} → NBoundary (suc n) ≡ S₊ n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S₊ {zero} = NBoundary1-≡-Bool ∙ (ua Bool≃Susp⊥' ) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S₊ {suc n} = (isoToPath (lem) ) ∙ cong Susp (NBoundary-≡-S₊)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   lem : Iso (NBoundary' {suc n} _) (Susp _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.fun (lem) (lid false x₁) = north
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.fun (lem) (lid true x₁) = south
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.fun (lem) (cyl x i) = merid x i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv (lem) north = lid false (corner0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv (lem) south = lid true (corner1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv (lem) (merid x i) =   ((cong (lid false) (corner0-≡ (boundaryInj x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                               ∙∙ (cyl x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                               ∙∙ (cong (lid true) (≡-corner1 (boundaryInj x)))) i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv (lem) north = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv (lem) south = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv (lem) (merid x i₁) i =
          
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          doubleCompPath-filler
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ _ → north)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ j → doubleCompPath-filler
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (λ i₂ → merid (transp (λ _ → NBoundary (suc n)) ((~ i₂) ∨ i) x) (i₂ ∧ j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (λ i₂ → merid (transp ((λ _ → NBoundary (suc n))) i x)  j )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (λ i₂ → merid (transp (λ _ → NBoundary (suc n)) ((~ i₂) ∧ i) x) (i₂ ∨  j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (~ i) j )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ _ → south)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (~ i) i₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv (lem) (lid false x₁) = cong (lid false) (corner0-≡ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv (lem) (lid true x₁) = sym (cong (lid true) (≡-corner1 _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv (lem) (cyl x i₁) i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       doubleCompPath-filler
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong (lid false) (corner0-≡ (boundaryInj x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cyl x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong (lid true) (≡-corner1 (boundaryInj x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (~ i) i₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S :  ∀ {n} → NBoundary n ≡ S (-1+ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S {zero} = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S {suc n} = NBoundary-≡-S₊







-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → (Σ _ (InsideOf {A = A} {n})) ≡ (Σ _ (Globeⁿ {A = A} {n})) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ A zero = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ A (suc zero) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ A (suc (suc n)) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ PathP {ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             PathP {ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i₂ → InsideOf {ℓ} {A} {n} (λ x₁ → x (cyl (cyl x₁ i₂) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (insideOf {ℓ} {A} {n} (λ x₁ → x (cyl (lid false x₁) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (insideOf {ℓ} {A} {n} (λ x₁ → x (cyl (lid true x₁) i₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             insideOf {ℓ} {A} {n} (λ x₁ → x (lid false (inside i₁ , x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             insideOf {ℓ} {A} {n} (λ x₁ → x (lid true (inside i₁ , x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ PathP {ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             PathP {ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ i₂ → Globeⁿ {ℓ} {A} {n} (λ x₁ → x (merid (merid x₁ i₂) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (northGlobeⁿ {ℓ} {A} {n} (λ x₁ → x (merid x₁ i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (southGlobeⁿ {ℓ} {A} {n} (λ x₁ → x (merid x₁ i₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (northGlobeⁿ {ℓ} {A} {suc n} x) (southGlobeⁿ {ℓ} {A} {suc n} x)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             PathP (λ i₂ → InsideOf (λ x₁ → x (cyl (cyl x₁ i₂) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (insideOf (λ x₁ → x (cyl (lid false x₁) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (insideOf (λ x₁ → x (cyl (lid true x₁) i₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ → insideOf (λ x₁ → x (lid false (inside i₁ , x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ → insideOf (λ x₁ → x (lid true (inside i₁ , x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             PathP (λ i₂ → Globeⁿ (λ x₁ → x (merid (merid x₁ i₂) i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (northGlobeⁿ (λ x₁ → x (merid x₁ i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (southGlobeⁿ (λ x₁ → x (merid x₁ i₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (northGlobeⁿ x) (southGlobeⁿ x)






-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOf↓ : ∀ {ℓ} → ∀ {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → ∀ n → ∀ {k} → ∀ i'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → (bd :  NCube (suc k) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → (InsideOfₘ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           λ x₁ → bd (i' , (proj₂ (boundaryInj x₁)))) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → (InsideOfₘ (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           λ x₁ → bd (i' , (boundaryInj x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOf↓ n {k = k} (end b) bd x = x (Bool→I b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOf↓ n {k = k} (inside i) bd x = x i


    

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Path of n dimensions

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (NBoundary n → A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf {ℓ} {A = A} {n} = InsideOfₘ 0 {k = n} 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOf-faceⁿ : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → (k : ℕ) → (s : Bool) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → (bd : NBoundary (suc n) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → InsideOf (bd ∘ (faceInj k s) ∘ boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOf-faceⁿ {n = n} k s bd = insideOf↑ {n = 0} (bd ∘ (faceInj k s))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Cubical→InsideOf : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → (c : NCube n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → InsideOf (c ∘ boundaryInj)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Cubical→InsideOf c =  insideOf↑ {n = 0} λ x₁ → c x₁ 




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ→Cubical :
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∀ {ℓ} → {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → ∀ {n} → ∀ {k}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → (bd : NBoundary k → A)          
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → InsideOfₘ {A = _} n {k = k} bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → NCube k → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ→Cubical {n = n} {zero} _ x _ = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ→Cubical {n = n} {suc k} _ x (end x₁ , x₂) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                    InsideOfₘ→Cubical {n = 0} _ (x (Bool→I x₁)) x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ→Cubical {n = n} {suc k} _ x (inside i , x₂) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                    InsideOfₘ→Cubical {n = 0} _ (x i) x₂



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf→Cubical : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → {bd : NBoundary n → A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → InsideOf bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → NCube n → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf→Cubical {n = zero} x x₁ = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf→Cubical {A = A} {n = suc n} {bd} x x₁ = InsideOfₘ→Cubical (λ x₃ → bd x₃) x x₁
 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOfSlice : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → {bd : NBoundary (suc n) → A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → InsideOf bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → (i' : Interval')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → InsideOf (bd ∘ (cyl'' i')) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOfSlice x (end x₁) = x (Bool→I x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- insideOfSlice x (inside i) = x i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfEquationalₘ : ∀ {ℓ} → ∀ {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       → ∀ {k}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       → (bd : NBoundary k → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfEquationalₘ bd = Σ _ (bd isBoundaryOf_)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- reflⁿ : ∀ {ℓ} → {A : Type ℓ} → ∀ n → (a : A) → InsideOf {n = n} (const a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- reflⁿ zero a = a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- reflⁿ (suc n) a = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nInside : ∀ n → InsideOf (boundaryInj {n})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- nInside n = insideOf↑ {A = NCube n} {n = n} (idfun _)
















-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isBd : ∀ {n} → NCube n → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isBd {n} x = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialTy : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               → NCube n → (NCube (suc n) →  A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               →  A 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialTy c x = iii (brd c) λ x₁ → x (x₁ , c)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialCu : (n : ℕ) → NCube n  → _×_ {ℓ-zero} {ℓ-zero} Interval' (NCube n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialCu n x = mkPartialTy x (idfun (NCube (suc n)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialCuTest : ∀ {ℓ} → {A : Type ℓ} → I → I → ((NCube 3 → A)) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPartialCuTest i₁ i₂ a = {!mkPartialTy (inside i₁ , inside i₂ , _) a!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- xxx : ∀ n → (c : NCube n) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- xxx = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ---


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n → ∀ k 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → (c : Interval' → NBoundary (suc k) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → InsideOfₘ n (c (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → NCube (suc k) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all {ℓ} {A} n zero c x cu = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all {ℓ} {A} n (suc zero) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all {ℓ} {A} n (suc k') c x (i' , j' , cu) = hCC i' j'  --hCC

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- k' = suc k''
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    k = suc k'

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hC : ∀ i → NCube (suc k') → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hC i = hcompⁿ-all
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           k' (λ x₁ x₂ → c x₁ (cyl x₂ i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (x i)
          
          
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC : Interval' → Interval' → A   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC (inside i) (inside j) = hcomp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ((λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (i = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (i = i1) → {!c (inside l) ?!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (j = i1) → hC i (inside j , cu)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           }))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC i' j' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hCub : ∀ i  → NCube (suc (suc k'')) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hCub i = InsideOfₘ→Cubical {n = suc n} {k = k} (λ x₂ → c (end true) (cyl x₂ i)) (hC i)
          
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhTest : (i : I) → (cu : NCube ((suc (suc k'')))) → (φ : I)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhTest i cu φ = hcomp {A  = A} (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (i1 = i1) → hCub i cu --(hC i z) --hCub i z cu
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((hCub i cu ))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC : (i : I) → (cu : NCube ((suc (suc k'')))) → (φ : Interval')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           →  A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC i cu (end false) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       hcomp {A  = A} (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           (i = i0) → hCub i0 cu --c (inside (z ∧ φ)) (lid false cu) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         ; (i = i1) → hCub i1 cu --c (inside (z ∧ φ)) (lid true cu)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           -- (i1 = i1) → hCub i cu --(hC i z) --hCub i z cu
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((hCub i cu ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC i cu (end true) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       hcomp {A  = A} (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           (i1 = i1) → hCub i cu --(hC i z) --hCub i z cu
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((hCub i cu ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC i cu (inside φ) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       hcomp {A  = A} (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           -- (φ = i0) → hCub i cu
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           (φ = i1) → hCub i cu --(hC i z) --hCub i z cu
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         ; (i = i0) → hCub i0 cu --c (inside (z ∧ φ)) (lid false cu) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         ; (i = i1) → hCub i1 cu --c (inside (z ∧ φ)) (lid true cu)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ((hCub i cu ))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC' :  (i : Interval') → (cu : NCube ((suc (suc k'')))) →  A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC' (end false) c = hhhC i0 c (brd c)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC' (end true) c = hhhC i1 c (brd c)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hhhC' (inside i) c =  hhhC i c (brd c)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- hhC : Interval' → NCube (suc k) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- hhC (end b) (x , y) = hhhC (Bool→I b) y x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- hhC (inside i) (x , y) = hhhC i y x

   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- hCC' : PathP {!!} {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- --InsideOfₘ (suc n) {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- hCC' = insideOf↑ hhC

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC0 : InsideOfₘ n {k = suc (suc (suc k''))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ((λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁)) ∘ boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC0 = insideOf↑ {n = n} {k = suc k} λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC1 : InsideOfₘ n {k = suc (suc (suc k''))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ((λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁)) ∘ boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC1 = (insideOf↑ {n = n} {k = suc k} λ x₁ → hhhC' (proj₁ x₁) (proj₂ x₁))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC : InsideOfₘ n {k = suc (suc (suc k''))} (c (end true))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hCC i i₁ i₂ = {!hCC0 i0 i₁ i₂!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- {!(Cubical→InsideOf (hhC (inside i)))!}  -- (Cubical→InsideOf (hhC (inside i)))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ (suc n) ((c (end true)) ∘ (lid b) ∘ boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hS : ∀ b → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hS b = hcompⁿ-all {!!} {!!} {!!} ( x (Bool→I b))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --insideOf↑ ((c (inside z)) ∘ lid b)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    h : InsideOfₘ (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ → c (inside z) (cyl'' (inside i) (cyl'' (inside i₁) x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    h = hcomp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (i = i0) → {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (i = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (i₁ = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (i₁ = i1) → {!x i i!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              λ _ → {!hC!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         -- hfill
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --  (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --     (i = i0) → {!hS false!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --   ; (i = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --   ; (i₁ = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --   ; (i₁ = i1) → {!x i i!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --   ; (z = i0) → x i i₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --  })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --  (inS ({!hC z!}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --  z
   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- zz : ∀ (i i₁ : I) → (j : I) → Set ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- zz i i₁ j = InsideOfₘ 2 {k'} ((c (inside j))  ∘ (cyl'' (inside i)) ∘ (cyl'' (inside i₁)))
     
   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- h0 : ∀ j → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- h0 j = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       ((hfillⁿ-all k' (λ x₁ x₂ → c x₁ (cyl x₂ i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --           (insideOfSlice {bd = c (end false)} x (inside i)) j)) i₁


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- h2 : InsideOfₘ (suc (suc 0))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --        ((c (inside z)) ∘ (cyl'' (inside i)) ∘  (cyl'' (inside i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- h2 =  hfill
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          (i₁ = i0) → {!h0!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --        ; (i₁ = i1) → {!h!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --        ; (i = i0) → {!h0 z  !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --        ; (i = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       (inS {! h0 !})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --       z


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hfillⁿ-all : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → (c : Interval' → NBoundary (suc k) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → InsideOf (c (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → (z : I) → InsideOf (c (inside z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hfillⁿ-all {ℓ} {A} zero c x z i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        hfill
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (i = i0)  → c (inside l) (lid false _)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i1)  → c (inside l) (lid true _)         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (inS (x i )) z

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hfillⁿ-all {ℓ} {A} (suc zero) c x z i i₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       hfill
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (i₁ = i0) → c (inside l) (cyl (lid false _) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i₁ = i1) → c (inside l) (cyl (lid true _) i) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i0)  → c (inside l) (lid false (inside i₁ , _))  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i1)  → c (inside l) (lid true (inside i₁ , _))         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (inS (x i i₁)) z


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hfillⁿ-all {ℓ} {A} (suc (suc k'')) c x z i i₁ = h

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    k' = suc k''
         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    zz : ∀ (i i₁ : I) → (j : I) → Set ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    zz i i₁ j = InsideOfₘ 2 {k'} ((c (inside j))  ∘ (cyl'' (inside i)) ∘ (cyl'' (inside i₁)))
     

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    h : _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    h =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       let cl-i : (b : Bool) → (l : I)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → InsideOfₘ 2 {k'}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       ((c (inside l)) ∘ (lid b) ∘ ( (inside i₁) ,_) ∘ boundaryInj )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           cl-i b l =  insideOf↑ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          ((c (inside l)) ∘ (lid b) ∘ ( (inside i₁) ,_))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           cl-i₁ : (b : Bool) → (l : I)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → InsideOfₘ 2 {k'}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       ((c (inside l)) ∘ ( cyl'' (inside i)) ∘ (lid b) ∘ boundaryInj )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           cl-i₁ b l =  insideOf↑ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          ((c (inside l)) ∘ ( cyl'' (inside i) ) ∘ (lid b))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       in
    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fill (zz i i₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (  (λ l → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (i₁ = i0) → cl-i₁ false l
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i₁ = i1) → cl-i₁ true l 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i0)  → cl-i false l  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i1)  → cl-i true l        
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           }))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (inS (x i i₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       z




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → (c : Interval' → NBoundary (suc k) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → InsideOf (c (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           → InsideOf (c (end true))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcompⁿ-all k c x = hfillⁿ-all k c x i1




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type : Cube
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (insideOf-faceⁿ 0 false boundaryInj) (insideOf-faceⁿ 0 true boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (insideOf-faceⁿ 1 false boundaryInj) (insideOf-faceⁿ 1 true boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (insideOf-faceⁿ 2 false boundaryInj) (insideOf-faceⁿ 2 true boundaryInj)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               InsideOf (boundaryInj {3})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type = refl


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-2-Type-holes : Square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     InsideOf (boundaryInj {2})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-2-Type-holes = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-holes : Cube _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     InsideOf (boundaryInj {3})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-holes = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-9-term :  nInside 9
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ≡ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (λ i i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                inside i , inside i₁ , inside i₂ ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                inside i₃ , inside i₄ , inside i₅ ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                inside i₆ , inside i₇ , inside i₈ ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-9-term = refl


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- testXX : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- testXX = {!hcompⁿ-all 2 (const (const tt)) (reflⁿ 3 tt)!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfₘ (suc n) (λ x₁ → c (end true) (cyl x₁ i))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- comp  {!!} {!!} {!!} 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOfEquationalₘ-Iso-InsideOfₘ :
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ∀ {ℓ} → ∀ {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → ∀ n → ∀ {k}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → (bd : NBoundary k → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → Iso (InsideOfEquationalₘ bd) (InsideOfₘ n bd)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) (fst₁ , snd₁) = fst₁ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) x) = const x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) x) i ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) b = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) a i) = const (fst a _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {zero} bd) a i) i₁ ()

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc zero} bd) (cu , bd=) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) (cu , bd=) i = ss i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ww* : ∀ i₁ → (x : NCube k) → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ww* i₁ x = cu (inside i₁ , x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss* : ∀ i₁ → InsideOfₘ (suc n) (λ x → cu (inside i₁ , boundaryInj x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss* i₁ = insideOf↑ {n = n} {k = k} (ww* i₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ww : ∀ i₁ → (x : NCube k) → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ww i₁ x = hcomp (λ i₂ → λ {                        
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (i₁ = i0) → bd= (~ i₂) (lid false x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       ; (i₁ = i1) → bd= (~ i₂) (lid true x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     }) (cu (inside i₁ , x))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss : ∀ i₁ → InsideOfₘ (suc n) (λ x → ww i₁ (boundaryInj x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss i₁ = insideOf↑ {n = n} {k = k} (ww i₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              qq : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              qq = {!ss i1!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss' : InsideOfₘ (suc n) (λ x → bd (cyl'' (inside i) x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ss' = insideOf↑ {n = n} {k = k} ({!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ww : ∀ i → InsideOfₘ n {k = suc k} (λ x → bd= i0 (cyl x i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ww = λ i → Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} λ x → bd= i0 (cyl x i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  --          ( (λ x → cu (inside i , x)) , λ i₁ x → bd= i₁ (cyl x i)) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- zz : I → I → Type _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- zz i j = InsideOfₘ n (λ x → bd= j (cyl x i))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- sss : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- sss = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ss : ∀ i' → InsideOfₘ (suc n) (λ x₁ → _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ss i' = insideOf↓ n i' (λ x → {!!}) λ i → ww i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ss' : InsideOfₘ n {k = suc (suc k)} bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  -- ss' = coe0→1 {!!} {!!}

             

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ n {suc k} bd) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) = {!InsideOf→Cubical !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ c bd) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) x = fst x _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) x) _ = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) x) i ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) b = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) a i) x = fst a _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {zero} c bd) a i) i₁ ()

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (InsideOfEquationalₘ-Iso-InsideOfₘ {ℓ} {A} {n = n} {suc k} c bd) (fst₁ , snd₁) i = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {suc k} c bd) x = {!!}                    

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {suc k} c bd) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (InsideOfEquationalₘ-Iso-InsideOfₘ {n = n} {suc k} c bd) = {!!}













-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- another definition of n-path , inside Sn

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Globeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n} → (S (-1+ n) → A) → Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → ∀ (bd : (S (-1+ (suc n)) → A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → north))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → ∀ (bd : (S (-1+ (suc n)) → A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → south))
                 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Globeⁿ {A = A} {n = zero} bd = A 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Globeⁿ {A = A} {n = suc n} bd =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (λ i → Globeⁿ {n = n} ( bd ∘ (λ x → merid x i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (northGlobeⁿ {A = A} {n = n} bd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (southGlobeⁿ {A = A} {n = n} bd)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (a : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      →  (northGlobeⁿ {n = n} (λ _ → a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         ≡ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (southGlobeⁿ {n = n} (λ _ → a))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ {n = zero} bd = bd north
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ {ℓ} {A} {suc zero} bd _ = bd north
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- northGlobeⁿ {ℓ} {A} {suc (suc n)} bd = north-south-const (bd north)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = zero} bd = bd south
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = suc zero} bd _ = bd south
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- southGlobeⁿ {n = suc (suc n)} bd = north-south-const (bd south)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const {n = zero} a = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const {n = suc zero} a = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- north-south-const {n = suc (suc n)} a = refl



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- NBoundary-≡-S relates Paths inside of S and NBoundary 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (λ i → (NBoundary-≡-S {n} i → A) → Type ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     InsideOf Globeⁿ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ A zero = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ {ℓ} A 1 i x =

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     x (coe0→i (λ j → NBoundary-≡-S {n = 1} j) i (lid false _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     x ((coe0→i (λ j → NBoundary-≡-S {n = 1} j) i (lid true _)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- InsideOf-≡-Globeⁿ {ℓ} A (suc (suc n)) i x = {!!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}  
                  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     pred= : PathP (λ i₂ → (NBoundary-≡-S {n = suc n} i₂ → A) → Type ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 InsideOf
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 Globeⁿ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     pred= = InsideOf-≡-Globeⁿ {ℓ} A (suc n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ( coei→0 (λ x₁ → NBoundary-≡-S {n = suc n} x₁ → A) i λ x₁ → {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zzz :  ∀ jj → pred= i0 (λ x₁ → x (coe0→i (λ x₂ → NBoundary-≡-S {suc (suc n)} x₂) i (cyl x₁ jj)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ≡ pred= i1 (λ x₁ → x (coe1→i (λ x₂ → NBoundary-≡-S {suc (suc n)} x₂) i (merid x₁ jj)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zzz jj i = pred= i {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zzz' :   I → (xx : ∀ ii → _ → NBoundary-≡-S {n = suc (suc n)} i) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  PathP (λ x₁ → InsideOfₘ {n = suc zero} (inside x₁ , tt)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                           (λ x₂ x₃ → x (xx i0 (cyl x₃ x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (insideOfCubeₘ {n = zero} (λ x₁ x₂ → x (xx i0 (lid false x₂))) (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (insideOfCubeₘ {n = zero} (λ x₁ x₂ → x (xx i0 (lid true x₂))) (end true))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ≡ PathP (λ x₁ → Globeⁿ (λ x₂ → x (xx i1 (merid x₂ x₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (northGlobeⁿ (λ x₁ → x (xx i1 x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (southGlobeⁿ (λ x₁ → x (xx i1 x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zzz' jj xx i = pred= i λ x₁ → x (xx i x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     qqq : (jj ii : I) → NBoundary-≡-S₊ ii → NBoundary-≡-S jj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     qqq = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ww : Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ww = PathP (λ x₁ → zzz' x₁ (qqq i) i) {!!} {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- qq0 : (j₀ : I) → NCube 1 → NBoundary (suc n) → NBoundary-≡-S {suc (suc n)} i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- -- 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- qq0 j₀ x x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    qqq1 : {!!} ≡ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    qqq1 = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- qq1 : (j₀ : I) → S (-1+ suc n) → NBoundary-≡-S {n = suc (suc n)} i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- qq1 j₀ z = transport qqq1 (merid z j₀)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    qqq1 : Susp (Susp (S (-1+ n))) ≡ NBoundary-≡-S {n = suc (suc n)} i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    qqq1 i' = {!!}
       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- -- qq1 j₀ x = fill1→i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --            (λ i₁ → NBoundary-≡-S {n = suc (suc n)} i₁)
               
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --            (λ i₁ → λ {                  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --                   (j₀ = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --                 ; (j₀ = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --                })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- --           (inS {!!}) i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- ww : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- ww = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- pp : ∀ i₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        InsideOfₘ {k = suc n} (inside i₁ , tt) (λ x₁ → λ x₂ → x (qq0 i₁ x₁ x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        Globeⁿ (λ x₁ → x (qq1 i₁ x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- pp = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcomp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ { j (i = i0) → NBoundary' boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ; j (i = i1) → Susp (NBoundary-≡-S₊ j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (Agda.Builtin.Cubical.Glue.primGlue (Susp (NBoundary' boundaryInj))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ .x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ { (i = i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → NBoundary' boundaryInj ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    isoToEquiv (Cubical.HITs.NCube.Base.lem n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → Susp (NBoundary' boundaryInj) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    idEquiv (Susp (NBoundary' boundaryInj))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           _ .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ .x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ { (i = i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → NBoundary' boundaryInj ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    isoToEquiv (Cubical.HITs.NCube.Base.lem n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (i = i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → Susp (NBoundary' boundaryInj) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    idEquiv (Susp (NBoundary' boundaryInj))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           _ .snd))






-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    pp :     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    pp = {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PathP (λ i₁ → Globeⁿ (λ x₁ → x (merid x₁ i₁))) (northGlobeⁿ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (southGlobeⁿ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   = ?0 (i = i1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   : Set ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PathP (λ i₁ → InsideOfₘ (inside i₁ , tt) (λ x₁ x₂ → x (cyl x₂ i₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (insideOfCubeₘ (λ x₁ x₂ → x (lid false x₂)) (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (insideOfCubeₘ (λ x₁ x₂ → x (lid true x₂)) (end true))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   = ?0 (i = i0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   : Set ℓ



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- similar tests for arbitrary types

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical : ∀ {ℓ} → {A : Type ℓ} → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end0 : NCube n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end1 : NCube n → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end0 ∘ boundaryInj ≡ end1 ∘ boundaryInj) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → NBoundary (suc n) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical zero end0 end1 x (lid x₁ _) = caseBool end1 end0 x₁ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical (suc n) end0 end1 x (lid x₁ x₂) = caseBool end1 end0 x₁ x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assembleBoundaryFromCubical (suc n) end0 end1 x (cyl x₁ i) = x i x₁



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- boundaryCase : ∀ {ℓ} → {A : Type ℓ} → ∀ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → {bd0 bd1 : NBoundary n → A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end0 : InsideOf bd0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (end1 : InsideOf bd1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     →    InsideOf→Cubical end0 ∘ boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ≡ InsideOf→Cubical end1 ∘ boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → NBoundary (suc n) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- boundaryCase n end0 end1 cylinder x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        assembleBoundaryFromCubical n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (InsideOf→Cubical end0)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (InsideOf→Cubical end1)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cylinder) x


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- makeCubeBoundary :
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ∀ {ℓ} → {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     →  NBoundary 3 → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- makeCubeBoundary a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     assembleBoundary 2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         a₀₋₋ a₁₋₋
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         aa
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   aa :   InsideOf→Cubical {bd = makeSquareBoundary _ _ _ _} a₀₋₋ ∘ boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ≡ InsideOf→Cubical {bd = makeSquareBoundary _ _ _ _} a₁₋₋ ∘ boundaryInj
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   aa i (lid x x₁) = {!x!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   aa i (cyl x i₁) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTest :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (InsideOf (makeCubeBoundary  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTest a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTestHoles :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (bd : NBoundaryIn A 3) →   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (Cube _ _ _ _ _ _) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (InsideOf {A = A} {n = 3} bd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTestHoles bd = refl



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTest' :  ∀ {ℓ} → ∀ {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (Cube {A = A} a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (InsideOf {A = A} {3} (makeCubeBoundary  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cubeTest' a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl










-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ : ∀ {ℓ} → (A : Type ℓ) → ℕ → Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record BoundaryIn' {ℓ} {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (X : A → Type ℓ) : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    constructor bdi

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    coinductive

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {lid0Bd lid1Bd} : A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      cylIn : lid0Bd ≡ lid1Bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      lid0 : X lid0Bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      lid1 : X lid1Bd

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ins : Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ins = PathP (λ x → X (cylIn x)) lid0 lid1

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn : ∀ {ℓ} {A : Type ℓ} → ∀ {n} → Boundaryⁿ A n → Type ℓ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ A zero = Lift Unit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ A (suc zero) = A × A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ A (suc (suc n)) = BoundaryIn' {A = Boundaryⁿ A (suc n)} (λ x → PPn x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --BoundaryIn' {A = Boundaryⁿ A n} (λ x → PPn x)
                                     

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- boundaryⁿ-Of = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn {A = A} {n = zero} x = A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn {A = A} {n = suc zero} x = proj₁ x ≡ proj₂ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn {A = A} {n = suc (suc n)} x = BoundaryIn'.ins x


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn-look : ∀ {ℓ} {A : Type ℓ} → ∀ {n} → ∀ {bd}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → PPn {A = A} {n} bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → NCube n → A



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make : ∀ {ℓ} → {A : Type ℓ} → {n : ℕ} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → (NBoundary n → A) → Boundaryⁿ A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = zero} x = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = suc zero} x = (x (lid false _)) , (x (lid true _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = suc (suc zero)} x = bdi (λ i → Boundaryⁿ-make λ x₁ → x (cyl x₁ i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                         (λ i → x (lid false (inside i , _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                        (λ i → x (lid true (inside i , _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-make {n = suc (suc (suc n))} x = bdi ((λ i → Boundaryⁿ-make λ x₁ → x (cyl x₁ i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                             (λ i → Cubical→InsideOf (λ x₁ → {!!}) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                             λ i → {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look : ∀ {ℓ} → {A : Type ℓ} → {n : ℕ} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      Boundaryⁿ A n → NBoundary n → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = zero} x ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc zero} (x , _) (lid false _) = x 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc zero} (_ , x) (lid true _) = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc (suc n)} x (lid x₁ y) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Boundaryⁿ-look {n = suc (suc n)} x (cyl x₁ i) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn-look {n = zero} x _ = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn-look {n = suc zero} x (xx , _) = Iapp x xx
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn-look {n = suc (suc n)} x (end x₁ , x₂) = PPn-look (x (Bool→I x₁)) x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PPn-look {n = suc (suc n)} x (inside i , x₂) = (PPn-look (x i)) x₂ 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- eeeww :  ∀ {ℓ} {A : Type ℓ} → ∀ {n} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            Iso (NBoundary n → A) (Boundaryⁿ A n) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lower (Iso.fun (eeeww {n = zero}) x) = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = zero}) x ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = zero}) (lift lower₁) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = zero}) a i ()

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (eeeww {n = suc zero}) x = (x (lid false _)) , (x (lid true _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc zero}) x (lid x₁ x₂) = caseBool (proj₂ x) (proj₁ x) x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = suc zero}) (x , x₁) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc zero}) a i (lid false x₁) = a (lid false tt)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc zero}) a i (lid true x₁) = a (lid true tt)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (eeeww {n = suc (suc zero)}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc (suc zero)}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = suc (suc zero)}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc (suc zero)}) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (eeeww {n = suc (suc (suc n))}) x = bdi {!!} {!!} {!!} {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc (suc (suc n))}) x (lid x₁ x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (eeeww {n = suc (suc (suc n))}) x (cyl x₁ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (eeeww {n = suc (suc (suc n))}) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (eeeww {n = suc (suc (suc n))}) = {!!}





-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-holes-PP : ∀ {ℓ} {A : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (bd : Boundaryⁿ A 3) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      Cube _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        PPn {n = 3} bd
                       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-holes-PP bd = refl


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-PP : 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ∀ {ℓ} → {A : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PPn {n = 3} ({!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test-3-Type-PP a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl






-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- self∨ : I → I
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- self∨ x = x ∨ (~ x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- self∨' : Interval' → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- self∨' (end x) = end true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- self∨' (inside i) = inside (i ∨ ~ i)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∨'_ : Interval' → Interval' → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∨' end false = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∨' end true = end true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- end true ∨' _ = end true 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∨' inside i = inside i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- inside i ∨' end false = inside i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- inside i ∨' end true = end true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∨'_ (inside i) (inside i₁) = inside (i ∨ i₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∧'_ : Interval' → Interval' → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∧' end false = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∧' end true = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- end true ∧' end false = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- end true ∧' end true = end true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- end false ∧' inside i = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- end true ∧' inside i = inside i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- inside i ∧' end false = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- inside i ∧' end true = inside i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∧'_ (inside i) (inside i₁) = inside (i ∧ i₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ⋁ : ∀ {n} → NCube n → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ⋁ {zero} x = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ⋁ {suc n} (z , x₁) = z ∨' ⋁ x₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼' : Interval' → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼' (end x) = end (not x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼' (inside i) = inside (~ i)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼'' : ∀ {n} → NCube n → NCube n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼'' {zero} tt = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∼'' {suc n} (x , x₁) = ∼' x ,  (∼'' x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd : ∀ {n} → NCube n → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd x = (⋁ x) ∨' ⋁ (∼'' x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd : ∀ {n} → NCube n → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd {zero} tt = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd {suc n} (z , x₁) = ((∼' z) ∨' z) ∨' brd x₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd : ∀ {n} → NCube n → Interval'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd {zero} x = end false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd {suc n} (end x , x₁) = end true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- brd {suc n} (inside i , x₁) = (inside (self∨ i)) ∨' (brd x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcomp' : ∀ {ℓ} → {A : Type ℓ} → (i' : Interval') → (Interval' → A) → A 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcomp' (end false) x = hcomp (λ i → empty) (x (end false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcomp' (end true) x = x (end true)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hcomp' (inside i) x = hcomp (λ j → λ {(i = i1) → x (inside j) }) (x (end false))
