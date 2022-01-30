{-# OPTIONS --cubical --safe  #-}
module Cubical.HITs.NCube.BaseVec2Prim where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Data.NatMinusOne.Base

open import Cubical.HITs.Interval
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Susp.Properties


open import Cubical.HITs.S1

open import Cubical.HITs.Join


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

-- NBoundary and boundaryInj are recursively defined


NBoundary : ℕ → Type₀

boundaryInj : ∀ {n} → NBoundary n → NCube n

data NBoundary' {n} : Type₀ where
   lid : Bool → NCube (n) → NBoundary'
   cyl : ∀ x → lid false (boundaryInj x) ≡ lid true (boundaryInj x)

NBoundary zero = ⊥
NBoundary (suc n) = NBoundary' {n}

boundaryInj {suc n} (lid x x₁) = end x ∷ x₁
boundaryInj {suc n} (cyl x i) = inside i ∷ boundaryInj x

boundaryEndMap : ∀ {n} → Bool → NBoundary n → NBoundary (suc n)
boundaryEndMap {n} x = lid x ∘ boundaryInj

cyl' : ∀ {n} → (bd : NBoundary (suc n)) →
               boundaryEndMap false bd ≡ boundaryEndMap true bd 
cyl' = cyl

lid' : ∀ {n} → Bool  → NCube n → NBoundary (suc n) 
lid' = lid

cyl'' : ∀ {n} →  Interval' → NBoundary n → NBoundary (suc n)
cyl'' (end false) y = cyl y i0
cyl'' (end true) y = cyl y i1
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



--Equality of NBoundary and S

NBoundary-≡-S : ∀ {n} → NBoundary n ≡ S (-1+ n)
NBoundary-≡-S {zero} = refl
NBoundary-≡-S {suc zero} = NBoundary1-≡-Bool ∙  ua Bool≃Susp⊥'
NBoundary-≡-S {suc (suc n)} = (isoToPath (lem) ) ∙ cong Susp (NBoundary-≡-S) 
  where

  lem : Iso NBoundary' (Susp NBoundary')
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








InsideOf : ∀ {ℓ}  → ∀ {n} → ∀ {A : Type ℓ}
                  → (bd : NBoundary n → A)
                  → Type ℓ

insideOf : ∀ {ℓ} → ∀ {n} → ∀ {A : Type ℓ}                  
                  → (bc : NCube n → A)                  
                  → InsideOf (bc ∘ boundaryInj)

InsideOf {n = zero} {A = A} bd = A
InsideOf {n = suc n} bd = ?
                       -- PathP
                       -- (λ i → InsideOf (bd ∘ cyl'' (inside i)))
                       -- (insideOf (bd ∘ lid false))
                       -- (insideOf (bd ∘ lid true))

insideOf {n = zero} bc = bc [] 
insideOf {n = suc n} bc i = ?
  --insideOf (λ x₁ → bc (inside i ∷ x₁))



-- reflⁿ : ∀ {ℓ} → {A : Type ℓ} → ∀ n → (a : A) → InsideOf {n = n} (const a)
-- reflⁿ zero a = a
-- reflⁿ (suc n) a = refl

-- nInside : ∀ n → InsideOf (boundaryInj {n})
-- nInside n = insideOf (idfun _)

-- toCubical :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → ∀ {bd}
--              → (InsideOf {n = n} {A = A} bd )
--              → NCube n → A 
-- toCubical {n = zero} {_} x x₁ = x
-- toCubical {n = suc n} {_} x (end false ∷ x₂) = toCubical (x (i0)) x₂
-- toCubical {n = suc n} {_} x (end true ∷ x₂) = toCubical (x (i1)) x₂
-- toCubical {n = suc n} {_} x (inside i ∷ x₂) = toCubical (x i) x₂




-- NBoundary-rec :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
--                  → (x0 x1 : NCube n → A)
--                  → x0 ∘ boundaryInj ≡ x1 ∘ boundaryInj 
--                  → NBoundary (suc n) → A 
-- NBoundary-rec x0 x1 x (lid x₁ x₂) = (caseBool x1 x0) x₁ x₂
-- NBoundary-rec x0 x1 x (cyl x₁ i) = x i x₁

-- NBoundary-elim :  ∀ {ℓ} → ∀ {n} → {A : NBoundary (suc n) → Type ℓ}
--                  → (f : (b : Bool) → (c : NCube n) → A (lid b c))
--                  → PathP (λ i → (bd : NBoundary n) → A (cyl bd i))
--                        (f false ∘ boundaryInj)
--                        (f true ∘ boundaryInj) 
--                  → (bd : NBoundary (suc n)) → A bd 
-- NBoundary-elim f x (lid x₁ x₂) = f x₁ x₂
-- NBoundary-elim f x (cyl x₁ i) = x i x₁


-- NBoundary-app-Interval :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} →
--                      (NBoundary (suc n) → A)
--                    → (Σ (Interval' → (NBoundary n → A)) λ a → InsideOf (a (end false)) × InsideOf (a (end true))  )
-- NBoundary-app-Interval {n = zero} x =  (λ x₁ ()) , (x (lid false [])) , (x (lid true []))
-- NBoundary-app-Interval {n = suc n} x = (λ i →  x ∘ cyl'' i ) , (insideOf (x ∘ lid false )) , insideOf (x ∘ lid true )

-- NBoundary-rec-inv :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} →
--                      (NBoundary (suc n) → A)
--                    → (Σ ((NCube n → A) × (NCube n → A)) λ x0x1 → (fst x0x1) ∘ boundaryInj ≡ (snd x0x1) ∘ boundaryInj   )
-- NBoundary-rec-inv {n = zero} x = ((const (x (lid false []))) , (const (x (lid true [])))) , (funExt λ () )
-- NBoundary-rec-inv {n = suc n} x = ((x ∘ lid false) , (x ∘ lid true)) , funExt λ x₁ → (λ i → x (cyl x₁ i))



-- NBoundary-rec-Iso :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} →
--                     Iso (NBoundary (suc n) → A)
--                         (Σ ((NCube n → A) × (NCube n → A)) λ x0x1 → (fst x0x1) ∘ boundaryInj ≡ (snd x0x1) ∘ boundaryInj   )
-- Iso.fun NBoundary-rec-Iso = NBoundary-rec-inv
-- Iso.inv NBoundary-rec-Iso ((x0 , x1) , p) = NBoundary-rec x0 x1 p
-- fst (fst (Iso.rightInv (NBoundary-rec-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i)) [] = fst₁ []
-- snd (fst (Iso.rightInv (NBoundary-rec-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i)) [] = snd₂ []
-- snd (Iso.rightInv (NBoundary-rec-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i) i₁ ()


-- Iso.leftInv (NBoundary-rec-Iso {n = zero}) a i (lid false []) =  a (lid false [])
-- Iso.leftInv (NBoundary-rec-Iso {n = zero}) a i (lid true []) =  a (lid true [])

-- Iso.rightInv (NBoundary-rec-Iso {n = suc n}) b = refl

-- Iso.leftInv (NBoundary-rec-Iso {n = suc n}) a i (lid false x₁) = a (lid false x₁)
-- Iso.leftInv (NBoundary-rec-Iso {n = suc n}) a i (lid true x₁) = a (lid true x₁)
-- Iso.leftInv (NBoundary-rec-Iso {n = suc n}) a i (cyl x i₁) = a (cyl x i₁)


-- NBoundary-elim-Iso :  ∀ {ℓ} → ∀ {n} → {A : NBoundary (suc n) → Type ℓ} →
--                     Iso (∀ x → A x)
--                         (Σ ((∀ x → (A ∘ lid false) x) × (∀ x → (A ∘ lid true) x))
--                            λ x0x1 → PathP (λ i → (∀ x → (A ∘ cylEx i) x))
--                                 ((fst x0x1) ∘ boundaryInj)
--                                 ((snd x0x1) ∘ boundaryInj)   )
-- Iso.fun NBoundary-elim-Iso x = ((x ∘ lid false) , (x ∘ lid true)) , cong (x ∘_) cylEx
-- Iso.inv NBoundary-elim-Iso ((x0 , x1) , p) = NBoundary-elim (λ { false → x0 ; true → x1 }) p

-- fst (fst (Iso.rightInv (NBoundary-elim-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i)) [] = fst₁ []
-- snd (fst (Iso.rightInv (NBoundary-elim-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i)) [] = snd₂ []
-- snd (Iso.rightInv (NBoundary-elim-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i) i₁ ()


-- Iso.leftInv (NBoundary-elim-Iso {n = zero}) a i (lid false []) =  a (lid false [])
-- Iso.leftInv (NBoundary-elim-Iso {n = zero}) a i (lid true []) =  a (lid true [])

-- Iso.rightInv (NBoundary-elim-Iso {n = suc n}) b = refl

-- Iso.leftInv (NBoundary-elim-Iso {n = suc n}) a i (lid false x₁) = a (lid false x₁)
-- Iso.leftInv (NBoundary-elim-Iso {n = suc n}) a i (lid true x₁) = a (lid true x₁)
-- Iso.leftInv (NBoundary-elim-Iso {n = suc n}) a i (cyl x i₁) = a (cyl x i₁)



-- InsideOfP : ∀ {ℓ} → ∀ {n}
--                   → (A : NCube n → Type ℓ)                  
--                   → ((x : NBoundary n) → A (boundaryInj x))
--                   → Type ℓ

-- insideOfP : ∀ {ℓ} → ∀ {n} →                   
--                     {A : NCube n → Type ℓ}                  
--                   → (x : ∀ c → A c)                  
--                   → InsideOfP A (x ∘ boundaryInj)

-- InsideOfP {ℓ} {zero} A _ = A []
-- InsideOfP {ℓ} {suc n} A bd =
--                       PathP
--                        (λ i → InsideOfP (A i∷ i) (bd ∘ cylEx i))
--                        (insideOfP (bd ∘ (lid false)) )
--                        (insideOfP (bd ∘ (lid true)) )


-- insideOfP {n = zero} x = x []
-- insideOfP {n = suc n} x i = insideOfP (x i∷ i )


-- toCubicalP :  ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ} → ∀ {bd}
--              → (InsideOfP {n = n} A bd )
--              → (c : NCube n) → A c 
-- toCubicalP {n = zero} {bd} x [] = x
-- toCubicalP {n = suc n} {bd} x (end false ∷ x₂) = toCubicalP (x i0) x₂
-- toCubicalP {n = suc n} {bd} x (end true ∷ x₂) = toCubicalP (x i1) x₂
-- toCubicalP {n = suc n} {bd} x (inside i ∷ x₂) = toCubicalP (x i) x₂


-- NBoundaryP-rec :  ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ}
--                  → (x0 : ∀ x → A (end false ∷ x))
--                  → (x1 : ∀ x → A (end true ∷ x))
--                  → PathP (λ i → ∀ x → A (inside i ∷ boundaryInj x)) (x0 ∘ boundaryInj) (x1 ∘ boundaryInj) 
--                  → ∀ x → A (boundaryInj x) 
-- NBoundaryP-rec x0 x1 x (lid false x₂) = x0 x₂
-- NBoundaryP-rec x0 x1 x (lid true x₂) = x1 x₂
-- NBoundaryP-rec x0 x1 x (cyl x₁ i) = x i x₁

-- NBoundaryP-rec-inv :  ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ} →
--                      ( ∀ x → A (boundaryInj x) )
--                    → (Σ (( ∀ x → A (end false ∷ x)) × ( ∀ x → A (end true ∷ x)))
--                            λ x0x1 → PathP (λ i →  ∀ x → A (inside i ∷ boundaryInj x))
--                                   ((fst x0x1) ∘ boundaryInj)
--                                   ((snd x0x1) ∘ boundaryInj)
--                                 )
-- fst (fst (NBoundaryP-rec-inv {n = zero} x)) [] = x (lid false [])
-- snd (fst (NBoundaryP-rec-inv {n = zero} x)) [] = x (lid true [])
-- snd (NBoundaryP-rec-inv {n = zero} x) i ()
-- NBoundaryP-rec-inv {n = suc n} x = ((x ∘ lid false) , (x ∘ lid true)) , funExt λ x₁ → (λ i → x (cyl x₁ i))


-- NBoundaryP-rec-Iso :  ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ} →
--                     Iso ( ∀ x → A (boundaryInj x) )
--                         (Σ (( ∀ x → A (end false ∷ x)) × ( ∀ x → A (end true ∷ x)))
--                            λ x0x1 → PathP (λ i →  ∀ x → A (inside i ∷ boundaryInj x))
--                             ((fst x0x1) ∘ boundaryInj) ((snd x0x1) ∘ boundaryInj)   )
-- Iso.fun (NBoundaryP-rec-Iso {n = n} {A}) = NBoundaryP-rec-inv {n = n} {A = A}
-- Iso.inv (NBoundaryP-rec-Iso {n = n} {A}) ((x0 , x1) , p) = NBoundaryP-rec {n = n} {A = A} x0 x1 p

-- fst (fst (Iso.rightInv (NBoundaryP-rec-Iso {n = zero} {A}) (fst₁ , snd₁) i)) [] = fst fst₁ []
-- snd (fst (Iso.rightInv (NBoundaryP-rec-Iso {n = zero} {A}) (fst₁ , snd₁) i)) [] = snd fst₁ []
-- snd (Iso.rightInv (NBoundaryP-rec-Iso {n = zero} {A}) b i) i₁ ()

-- fst (fst (Iso.rightInv (NBoundaryP-rec-Iso {n = suc n} {A}) (fst₁ , snd₁) i)) = fst fst₁
-- snd (fst (Iso.rightInv (NBoundaryP-rec-Iso {n = suc n} {A}) (fst₁ , snd₁) i)) = snd fst₁
-- snd (Iso.rightInv (NBoundaryP-rec-Iso {n = suc n} {A}) (fst₁ , snd₁) i) i₁ = snd₁ i₁ 

-- Iso.leftInv (NBoundaryP-rec-Iso {n = zero} {A}) a i (lid false []) = a (lid false [])
-- Iso.leftInv (NBoundaryP-rec-Iso {n = zero} {A}) a i (lid true []) = a (lid true [])

-- Iso.leftInv (NBoundaryP-rec-Iso {n = suc n} {A}) a = funExt z

--   where
--     z : _
--     z (lid false x₁) = refl
--     z (lid true x₁) = refl
--     z (cyl x i) = refl


-- NBoundaryP-rec' :  ∀ {ℓ} → ∀ {n} → {A : NBoundary (suc n) → Type ℓ}
--                  → (x0 : ∀ x → A (lid false x))
--                  → (x1 : ∀ x → A (lid true x))
--                  → PathP (λ i → ∀ x → A (cyl x i)) (x0 ∘ boundaryInj) (x1 ∘ boundaryInj) 
--                  → ∀ x → A x 
-- NBoundaryP-rec' x0 x1 x (lid false x₂) = x0 x₂
-- NBoundaryP-rec' x0 x1 x (lid true x₂) = x1 x₂
-- NBoundaryP-rec' x0 x1 x (cyl x₁ i) = x i x₁




-- module bdtest (A : Type) where

--   Bd : ℕ -> Σ Type (λ bd → bd → Type)
--   Bd zero = Unit , const A 
--   Bd (suc n) =
--     let (prev-bd , prev-ins) = Bd n
--     in (Σ (Σ prev-bd prev-ins × Σ prev-bd prev-ins) λ x → fst (fst x) ≡ fst (snd (x))) ,
--        λ x → PathP (λ i → prev-ins (snd x i)) (snd (fst (fst x))) (snd (snd (fst x)))
       

--   Iso-bd : ∀ n → Iso (Σ (fst (Bd n)) (snd (Bd n))) (NCube n -> A)
--   Iso.fun (Iso-bd zero) x x₁ = snd x
--   Iso.inv (Iso-bd zero) x = _ , x []
--   Iso.rightInv (Iso-bd zero) b i [] = b []
--   Iso.leftInv (Iso-bd zero) (tt , snd₁) = refl
  
--   Iso.fun (Iso-bd (suc n)) x (end false ∷ x₂) = Iso.fun (Iso-bd (n)) (_ , (snd x i0)) x₂
--   Iso.fun (Iso-bd (suc n)) x (end true ∷ x₂) = Iso.fun (Iso-bd (n)) (_ , (snd x i1)) x₂
--   Iso.fun (Iso-bd (suc n)) x (inside i ∷ x₂) = Iso.fun (Iso-bd (n)) (_ , (snd x i)) x₂
  
--   Iso.inv (Iso-bd (suc n)) x = _ , λ i → snd (Iso.inv (Iso-bd n) (x i∷ i))
  
--   Iso.rightInv (Iso-bd (suc n)) b i (end false ∷ x₁) = Iso.rightInv (Iso-bd (n)) (b i∷ i0) i x₁
--   Iso.rightInv (Iso-bd (suc n)) b i (end true ∷ x₁) = Iso.rightInv (Iso-bd (n)) (b i∷ i1) i x₁
--   Iso.rightInv (Iso-bd (suc n)) b i (inside i₁ ∷ x₁) = Iso.rightInv (Iso-bd (n)) (b i∷ i₁) i x₁
--   Iso.leftInv (Iso-bd (suc n)) a i =
--     _ , λ i₁ → snd (Iso.leftInv (Iso-bd n) (_ , snd a i₁) i)


-- -- data Lω {ℓ : Level} (A : Type ℓ) : Typeω where
-- --   lω : A → Lω A



-- -- loω : {ℓ : Level} {A : Type ℓ} → Lω A → A
-- -- loω (lω x) = x

-- -- Iⁿ→ : ∀ {ℓ} → (A : Type ℓ) → ℕ → Typeω
-- -- Iⁿ→ A zero = I → A
-- -- Iⁿ→ A (suc x) = I → Iⁿ→ A x


-- -- CuωTy : {ℓ : Level} (A : Type ℓ) → ℕ → Typeω
-- -- CuωTy A zero = Lω A
-- -- CuωTy A (suc n) = (Iⁿ→ A n)


-- -- -- from-cuωS : {ℓ : Level} {A : Type ℓ} → ∀ {n} → CuωTy A (suc n) → (Iⁿ→ A n) 
-- -- -- from-cuωS x = x


-- -- mkCube : ∀ {ℓ} → {A : Type ℓ} → ∀ n → CuωTy A n → NCube n → A
-- -- mkCube zero x _ = loω x
-- -- mkCube (suc zero) x (end false ∷ x₂) = x i0
-- -- mkCube (suc zero) x (end true ∷ x₂) = x i1
-- -- mkCube (suc zero) x (inside i ∷ x₂) = x i
-- -- mkCube (suc (suc n)) x (end false ∷ x₂) = mkCube (suc n) (x i0) x₂
-- -- mkCube (suc (suc n)) x (end true ∷ x₂) = mkCube (suc n) (x i1) x₂
-- -- mkCube (suc (suc n)) x (inside i ∷ x₂) = mkCube (suc n) (x i) x₂

-- -- fromCube : ∀ {ℓ} → {A : Type ℓ} → ∀ n → (NCube n → A) → CuωTy A n
-- -- fromCube zero x = lω (x [])
-- -- fromCube (suc zero) x = λ i → x (inside i ∷ [])
-- -- fromCube (suc (suc n)) x = (λ i → (fromCube _ (x i∷ i)))

-- -- mkCube-fromCube : ∀ {ℓ} → ∀ n → {A : NCube n → Type ℓ} → ∀ x →
-- --                     mkCube n (fromCube n (λ x' → A x')) x
-- --                    → A x
-- -- mkCube-fromCube zero [] a = a
-- -- mkCube-fromCube (suc zero) (end false ∷ []) a = a
-- -- mkCube-fromCube (suc zero) (end true ∷ []) a = a
-- -- mkCube-fromCube (suc zero) (inside i ∷ []) a = a
-- -- mkCube-fromCube (suc (suc n)) {A} (end false ∷ x₁) a = mkCube-fromCube (suc n) {A = A i∷ i0} x₁ a
-- -- mkCube-fromCube (suc (suc n)) {A} (end true ∷ x₁) a = mkCube-fromCube (suc n) {A = A i∷ i1} x₁ a
-- -- mkCube-fromCube (suc (suc n)) {A} (inside i ∷ x₁) a = mkCube-fromCube (suc n) {A = A i∷ i} x₁ a

-- -- -- mkCube-fromCube : ∀ {ℓ} → ∀ n → {A : NCube n → Type ℓ} → ∀ x →
-- -- --                     mkCube n (fromCube n (λ x' → A x')) x
-- -- --                    → A x
-- -- -- mkCube-fromCube = ?


-- -- ∀Iⁿ : ∀ {ℓ} → ∀ n → Iⁿ→ (Type ℓ) n → Typeω
-- -- ∀Iⁿ zero x = (i : I) → x i
-- -- ∀Iⁿ (suc n) x = (i : I) → ∀Iⁿ n (x i)



-- -- CuPωTy : {ℓ : Level} → ∀ n → CuωTy (Type ℓ) n  → Typeω
-- -- CuPωTy zero x = Lω (loω x)
-- -- CuPωTy (suc n) x = ∀Iⁿ _ x

-- -- -- → A → CuPωTy zero (cuω0 A)
-- -- -- CuPωTy : ∀ {n} → ∀ {A} → ∀Iⁿ n A → CuPωTy (suc n) (cuωS A)

-- -- -- from-cuPωS : {ℓ : Level} → ∀ {n} → (A : CuωTy (Type ℓ) (suc n)) → CuPωTy (suc n) A → (∀Iⁿ n (from-cuωS A)) 
-- -- -- from-cuPωS {n = n} .(cuωS _) (cuPωS x) = x


-- -- mkCubeP : ∀ {ℓ} → ∀ {n} → {A : CuωTy (Type ℓ) n} → CuPωTy n A → ∀ x → mkCube n A x
-- -- mkCubeP {n = zero} x x₁ = loω x
-- -- mkCubeP {n = suc zero} x (end false ∷ x₂) = x i0
-- -- mkCubeP {n = suc zero} x (end true ∷ x₂) = x i1
-- -- mkCubeP {n = suc zero} x (inside i ∷ x₂) = x i
-- -- mkCubeP {n = suc (suc n)} x (end false ∷ x₂) = mkCubeP (x i0) x₂
-- -- mkCubeP {n = suc (suc n)} x (end true ∷ x₂) = mkCubeP (x i1) x₂
-- -- mkCubeP {n = suc (suc n)} x (inside i ∷ x₂) = mkCubeP (x i) x₂

-- -- mkCubeP' : ∀ {ℓ} → ∀ {n} → {A : NCube n → (Type ℓ)} → CuPωTy n (fromCube n A) → ∀ x → A x
-- -- mkCubeP' {n = zero} x [] = loω x
-- -- mkCubeP' {n = suc zero} x (end false ∷ []) = x i0
-- -- mkCubeP' {n = suc zero} x (end true ∷ []) = x i1
-- -- mkCubeP' {n = suc zero} x (inside i ∷ []) = x i
-- -- mkCubeP' {n = suc (suc n)} x (end false ∷ x₂) = mkCubeP' (x i0) x₂
-- -- mkCubeP' {n = suc (suc n)} x (end true ∷ x₂) = mkCubeP' (x i1) x₂
-- -- mkCubeP' {n = suc (suc n)} x (inside i ∷ x₂) = mkCubeP' (x i) x₂

-- -- fromCubeP : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ} → (∀ x → A x) → CuPωTy n (fromCube n A) 
-- -- fromCubeP {n = zero} x = lω (x [])
-- -- fromCubeP {n = suc zero} x i = x (inside i ∷ [])
-- -- fromCubeP {n = suc (suc n)} x i = fromCubeP (x i∷ i )

-- -- BdωTy : {ℓ : Level} (A : Type ℓ) → ℕ → Typeω
-- -- BdPωTy : {ℓ : Level} → ∀ n → BdωTy (Type ℓ) n → Typeω



-- -- mkBd : ∀ {ℓ} → {A : Type ℓ} → ∀ n → BdωTy A n → NBoundary n → A


-- -- mkBdP : ∀ {ℓ} → ∀ {n} → {A : BdωTy (Type ℓ) n} → BdPωTy _ A → ∀ x → mkBd _ A x







-- -- record BdωTyS {ℓ : Level} (A : Type ℓ) (n : ℕ) : Typeω where
-- --   constructor bdωS
-- --   field
-- --     lid0 lid1 : Iⁿ→ A n
-- --     pa : ((a : NBoundary') →
-- --             ((mkCube (suc n) lid0 ∘ boundaryInj) a
-- --              ≡
-- --             (mkCube (suc n) lid1 ∘ boundaryInj) a)
-- --             ) 


-- -- BdωTy {ℓ} A zero = Unitω
-- -- BdωTy {ℓ} A (suc zero) = Lω (A × A)
-- -- BdωTy {ℓ} A (suc (suc n)) = BdωTyS A n



-- -- record BdPωTyS {ℓ : Level} (n : ℕ) {A₀ A₁ : NCube (suc n) → Type ℓ}
-- --              (P : (A₀ ∘ boundaryInj ≡ A₁ ∘ boundaryInj) )
-- --               : Typeω where
              
-- --   constructor bdPωS 
-- --   field
-- --     lid0   : ∀Iⁿ _ (fromCube _ A₀)
-- --     lid1   : ∀Iⁿ _ (fromCube _ A₁)
-- --     pa : ((a : NBoundary') → PathP (λ i → P i a )
-- --                    ((mkCubeP' {n =  suc n} lid0 ∘ boundaryInj) a)
-- --                    ((mkCubeP' {n =  suc n} lid1 ∘ boundaryInj) a))






-- -- BdPωTy zero x = Unitω
-- -- BdPωTy (suc zero) x = Lω (fst (loω x) × snd (loω x))
-- -- BdPωTy (suc (suc n)) y =
-- --       BdPωTyS n {A₀ = mkCube _ lid0} {mkCube _ lid1}
-- --                    (funExt pa)
-- --    where
-- --      open BdωTyS y

-- -- mkBd (suc zero) x (lid false x₂) = fst (loω x)
-- -- mkBd (suc zero) x (lid true x₂) = snd (loω x)
-- -- mkBd (suc (suc n)) (y) =
-- --       NBoundary-rec (mkCube (suc n) lid0) (mkCube (suc n) lid1) (funExt pa)
-- --   where
-- --     open BdωTyS y



-- -- mkBdP {n = suc zero} x (lid false x₂) = fst (loω x)
-- -- mkBdP {n = suc zero} x (lid true x₂) = snd (loω x)
-- -- mkBdP {n = suc (suc n)} y = 
-- --   NBoundaryP-rec' (mkCubeP' lid0) (mkCubeP' lid1) (funExt pa)

-- --   where
-- --     open BdPωTyS y



-- -- -- NCubId : NBoundary 5 → NBoundary 5
-- -- -- NCubId = mkBd 5 (bdωS (λ x x₁ x₂ x₃ → {!!})
-- -- --                       (λ x x₁ x₂ x₃ → {!!})
-- -- --                       (funExt (mkBdP {!!})))




-- -- squareLemma : ∀ n → (x : NCube (suc n))
-- --             → Square {A = NBoundary (suc (suc (suc n)))}
-- --                      (λ i → cyl (lid false x) i)
-- --                      (λ i → cyl (lid true x) i)
-- --                      (λ i → lid false (inside i ∷ x))
-- --                      (λ i → lid true (inside i ∷ x))
-- -- squareLemma n (hx ∷ x) i i₁ =  hcomp
-- --     (λ j →
-- --         let p = endF= hx (~ j) in
-- --        λ { (i = i0) → cyl (lid false (p ∷ x)) i₁
-- --              ; (i = i1) → cyl (lid true (p ∷ x)) i₁
-- --              ; (i₁ = i0) → lid false (inside i ∷ p ∷ x)
-- --              ; (i₁ = i1) → lid true (inside i ∷ p ∷ x)
-- --          })
-- --     (cyl (cyl (lid false x) i) i₁)



-- -- fromBd : ∀ {ℓ} → {A : Type ℓ} → ∀ n → (NBoundary n → A) → BdωTy A n

-- -- fromBdPTy : ∀ {ℓ} → ∀ {n} → (A : NBoundary n → Type ℓ) → Typeω
-- -- fromBdPTy A = (∀ x → A x) → BdPωTy _ (fromBd _ A) 



-- -- fromBd zero x = ttω
-- -- fromBd (suc zero) x = lω ((x (lid false [])) , (x (lid true []) ))
-- -- fromBd (suc (suc zero)) x =
-- --   bdωS (fromCube (suc zero) (x ∘ lid false))
-- --      (fromCube (suc zero) (x ∘ lid true))
-- --      w
     
-- --       where
-- --       w : _
-- --       w (lid false x₁) i = x (cyl (lid false []) i)
-- --       w (lid true x₁) i = x (cyl (lid true []) i)


-- -- fromBd (suc (suc (suc n))) x = bdωS (fromCube (suc (suc n)) (x ∘ lid false))
-- --                                     (fromCube (suc (suc n)) (x ∘ lid true))
-- --                                     (w)

-- --   where
-- --     w : _
-- --     w (lid false x₁) i =
-- --         mkCube (suc n)
-- --            (fromCube (suc n) (λ x₂ → x (cyl (lid false x₂) i))) x₁
-- --     w (lid true x₁) i =
-- --         mkCube (suc n)
-- --            (fromCube (suc n) (λ x₂ → x (cyl (lid true x₂) i))) x₁
-- --     w (cyl xx i₁) i =
-- --         mkCube (suc n)
-- --           (fromCube (suc n) (λ x₂ → x (squareLemma n x₂ i₁ i))) (boundaryInj xx)



-- -- record BdP {ℓ} {n} (A : NBoundary (suc n) → Type ℓ) : Typeω where
-- --    constructor bdP
-- --    field
-- --      lid0 : ∀Iⁿ _ (fromCube _ {!A ∘ lid false!})
-- --      lid1 : ∀Iⁿ _ (fromCube _ {!!})
-- --      pa : {!!}








-- -- -- fromCube-mkCube : ∀ {ℓ} → ∀ n → {A : NCube (suc n) → Type ℓ} 
-- -- --                    → ∀Iⁿ (n)
-- -- --                      (fromCube (suc n)
-- -- --                       (mkCube (suc n) ?))
-- -- --                      → CuPωTy (suc n)
-- -- --                            (fromCube (suc n) (λ x → A (lid false x)))

-- -- -- fromCube-mkCube = ?


-- -- -- mkBdP' : ∀ {ℓ} → ∀ {n} → {A : NBoundary n → Type ℓ} → BdPωTy n (fromBd n A) → ∀ x → A x

-- -- -- mkBdP' {n = suc zero} x (lid false []) = fst (loω x)
-- -- -- mkBdP' {n = suc zero} x (lid true []) = snd (loω x)

-- -- -- mkBdP' {n = suc (suc zero)} y =
-- -- --   NBoundaryP-rec' (mkCubeP' lid0) (mkCubeP' lid1)
-- -- --      (funExt (mkBdP' (lω ((pa (lid false [])) , (pa (lid true []))))))

-- -- --   where
-- -- --     open BdPωTyS y

-- -- -- -- mkBdP' {n = suc (suc (suc n))} {A} y = 
-- -- -- --   NBoundaryP-rec' ({!(mkCubeP' {A = A ∘ lid false} )!}) {!!}
-- -- -- --      (funExt {!!})

-- -- -- --   where
-- -- -- --     open BdPωTyS y


-- -- -- mkBdP' {n = suc (suc (suc zero))} {A} y = 
-- -- --   NBoundaryP-rec' (mkCubeP' lid0) (mkCubeP' lid1)
-- -- --      (funExt (mkBdP'
-- -- --        (bdPωS
-- -- --         (λ i → pa (lid false (inside i ∷ [])))
-- -- --         (λ i → pa (lid true (inside i ∷ [])))
-- -- --         (mkBdP' (lω ((λ i x → {!pa (cyl (lid false []) i ) x !})
-- -- --                    , (λ i x → {!pa (cyl (lid true []) i ) x!}))))
-- -- --         )))

-- -- --   where
-- -- --     open BdPωTyS y


-- -- -- mkBdP' {n = suc (suc (suc (suc n)))} {A} y = 
-- -- --   NBoundaryP-rec' ((mkCubeP' {A = A ∘ lid false} {!lid0!})) {!!}
-- -- --      (funExt {!!})

-- -- --   where
-- -- --     open BdPωTyS y




-- -- -- fromBd zero x = ttω
-- -- -- fromBd (suc zero) x = lω ((x (lid false [])) , (x (lid true []) ))
-- -- -- fromBd (suc (suc zero)) x = bdωS (fromCube (suc zero) (x ∘ lid false))
-- -- --                               (fromCube (suc zero) (x ∘ lid true))
-- -- --                                (w)
-- -- --                         where
-- -- --                           w : _
-- -- --                           w i (lid false x₁) = x (cyl (lid false []) i)
-- -- --                           w i (lid true x₁) = x (cyl (lid true []) i)
                               
-- -- -- fromBd (suc (suc (suc n))) x = bdωS (fromCube (suc (suc n)) (x ∘ lid false))
-- -- --                               (fromCube (suc (suc n)) (x ∘ lid true))
-- -- --                                (w)
-- -- --                         where 
-- -- --                           w : _
-- -- --                           w i (lid false x₁) =
-- -- --                              mkCube (suc n)
-- -- --                                (fromCube (suc n) (λ x₂ → x (cyl (lid false x₂) i))) x₁
-- -- --                           w i (lid true x₁) = 
-- -- --                              mkCube (suc n)
-- -- --                                (fromCube (suc n) (λ x₂ → x (cyl (lid true x₂) i))) x₁
-- -- --                           w i (cyl xx i₁) = 
-- -- --                              mkCube (suc n)
-- -- --                                    (fromCube (suc n) (λ x₂ → x (squareLemma n x₂ i₁ i))) (boundaryInj xx)

-- -- -- fromBdP {n = zero} x = ttω
-- -- -- fromBdP {n = suc zero} x = lω (((x (lid false [])) , (x (lid true []) )))
-- -- -- fromBdP {n = suc (suc zero)} x = bdPωS (fromCubeP (x ∘ lid false)) (fromCubeP (x ∘ lid true)) w
-- -- --                        where
-- -- --                           w : _
-- -- --                           w i (lid false x₁) = x (cyl (lid false []) i)
-- -- --                           w i (lid true x₁) = x (cyl (lid true []) i)
                          
-- -- -- fromBdP {n = suc (suc (suc n))} x = bdPωS (fromCubeP (x ∘ lid false)) (fromCubeP (x ∘ lid true)) w
-- -- --                        where
-- -- --                           w : _
-- -- --                           w i (lid false x₁) =
-- -- --                              mkCubeP (fromCubeP (λ x₂ → x (cyl (lid false x₂) i))) x₁
-- -- --                           w i (lid true x₁) = 
-- -- --                              mkCubeP (fromCubeP (λ x₂ → x (cyl (lid true x₂) i))) x₁
-- -- --                           w i (cyl xx i₁) = 
-- -- --                              mkCubeP (fromCubeP (λ x₂ → x (squareLemma n x₂ i₁ i))) (boundaryInj xx)


-- -- -- mkBdP' : ∀ {ℓ} → ∀ {n} → {A : NBoundary n → Type ℓ} → BdPωTy n (fromBd n A) → ∀ x → A x
-- -- -- mkBdP' {n = zero} x ()
-- -- -- mkBdP' {n = suc zero} x (lid false []) = fst (loω x)
-- -- -- mkBdP' {n = suc zero} x (lid true []) = snd (loω x)

-- -- -- mkBdP' {n = suc (suc zero)} {A} (bdPωS lid0 lid1 p) (lid false x₁) = mkCubeP' {A = A ∘ lid false} lid0 x₁
-- -- -- mkBdP' {n = suc (suc zero)} {A} (bdPωS lid0 lid1 p) (lid true x₁) = mkCubeP' {A = A ∘ lid true} lid1 x₁
-- -- -- mkBdP' {n = suc (suc zero)} {A} (bdPωS lid0 lid1 p) (cyl (lid false []) i) = p i (lid false [])
-- -- -- mkBdP' {n = suc (suc zero)} {A} (bdPωS lid0 lid1 p) (cyl (lid true []) i) = p i (lid true [])

-- -- -- mkBdP' {n = suc (suc (suc n))} {A} (bdPωS lid0 lid1 x) (lid false x₂) =
-- -- --                                                 mkCubeP' {A = A ∘ lid false} lid0 x₂
-- -- -- mkBdP' {n = suc (suc (suc n))} {A} (bdPωS lid0 lid1 x) (lid true x₂) =
-- -- --                                                mkCubeP' {A = A ∘ lid true} lid1 x₂
-- -- -- mkBdP' {n = suc (suc (suc n))} {A} (bdPωS lid0 lid1 x) (cyl (lid false x₂) i) = {!!}
-- -- --                                                 -- mkCube-fromCube (suc n) {A = A ∘ cylEx i ∘ lid false}
-- -- --                                                 --   x₂ (x i (lid false x₂)) 
                                                
-- -- -- mkBdP' {n = suc (suc (suc n))} {A} (bdPωS lid0 lid1 x) (cyl (lid true x₂) i) = {!!}
-- -- --                                                 -- mkCube-fromCube (suc n) {A = A ∘ cylEx i ∘ lid true}
-- -- --                                                 --   x₂ (x i (lid true x₂))
-- -- --                                                 -- --mkCubeP' {A = A ∘ cylEx i ∘ lid true} {!x i!} x₂
-- -- -- mkBdP' {n = suc (suc (suc n))} (bdPωS lid0 lid1 x) (cyl (cyl x₁ i₁) i) = {!!}



-- -- -- -- NCubId : NBoundary 5 → NBoundary 5
-- -- -- -- NCubId = mkBd 5 (bdωS (λ x x₁ x₂ x₃ → {!!})
-- -- -- --                       (λ x x₁ x₂ x₃ → {!!})
-- -- -- --                       (funExt (mkBdP' (bdPωS
-- -- -- --                        (λ i i₁ i₂ i₃ → {!!})
-- -- -- --                        (λ i i₁ i₂ i₃ → {!!})
-- -- -- --                        (funExt (mkBdP' (bdPωS
-- -- -- --                        (λ i i₁ x x₁ → {!!})
-- -- -- --                        (λ i i₁ x x₁ → {!!})
-- -- -- --                        (funExt (mkBdP' (bdPωS
-- -- -- --                        (λ i x x₁ x₂ → {!!})
-- -- -- --                        (λ i x x₁ x₂ → {!!})
-- -- -- --                        (funExt {!!})))))))))))
