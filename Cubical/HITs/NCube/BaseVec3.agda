{-# OPTIONS --cubical --safe  #-}
module Cubical.HITs.NCube.BaseVec3 where


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
toCubical {n = zero} {_} x x₁ = x
toCubical {n = suc n} {_} x (end x₁ ∷ x₂) = toCubical (x (Bool→I x₁)) x₂
toCubical {n = suc n} {_} x (inside i ∷ x₂) = toCubical (x i) x₂

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


NBoundary-elim-Iso :  ∀ {ℓ} → ∀ {n} → {A : NBoundary (suc n) → Type ℓ} →
                    Iso (∀ x → A x)
                        (Σ ((∀ x → (A ∘ lid false) x) × (∀ x → (A ∘ lid true) x))
                           λ x0x1 → PathP (λ i → (∀ x → (A ∘ cylEx i) x))
                                ((fst x0x1) ∘ boundaryInj)
                                ((snd x0x1) ∘ boundaryInj)   )
Iso.fun NBoundary-elim-Iso x = ((x ∘ lid false) , (x ∘ lid true)) , cong (x ∘_) cylEx
Iso.inv NBoundary-elim-Iso ((x0 , x1) , p) = NBoundary-elim (λ { false → x0 ; true → x1 }) p

fst (fst (Iso.rightInv (NBoundary-elim-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i)) [] = fst₁ []
snd (fst (Iso.rightInv (NBoundary-elim-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i)) [] = snd₂ []
snd (Iso.rightInv (NBoundary-elim-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i) i₁ ()


Iso.leftInv (NBoundary-elim-Iso {n = zero}) a i (lid false []) =  a (lid false [])
Iso.leftInv (NBoundary-elim-Iso {n = zero}) a i (lid true []) =  a (lid true [])

Iso.rightInv (NBoundary-elim-Iso {n = suc n}) b = refl

Iso.leftInv (NBoundary-elim-Iso {n = suc n}) a i (lid false x₁) = a (lid false x₁)
Iso.leftInv (NBoundary-elim-Iso {n = suc n}) a i (lid true x₁) = a (lid true x₁)
Iso.leftInv (NBoundary-elim-Iso {n = suc n}) a i (cyl x i₁) = a (cyl x i₁)



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
                           λ x0x1 → PathP (λ i →  ∀ x → A (inside i ∷ boundaryInj x))
                                  ((fst x0x1) ∘ boundaryInj)
                                  ((snd x0x1) ∘ boundaryInj)
                                )
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


NBoundaryP-rec' :  ∀ {ℓ} → ∀ {n} → {A : NBoundary (suc n) → Type ℓ}
                 → (x0 : ∀ x → A (lid false x))
                 → (x1 : ∀ x → A (lid true x))
                 → PathP (λ i → ∀ x → A (cyl x i)) (x0 ∘ boundaryInj) (x1 ∘ boundaryInj) 
                 → ∀ x → A x 
NBoundaryP-rec' x0 x1 x (lid false x₂) = x0 x₂
NBoundaryP-rec' x0 x1 x (lid true x₂) = x1 x₂
NBoundaryP-rec' x0 x1 x (cyl x₁ i) = x i x₁




module bdtest (A : Type) where

  Bd : ℕ -> Σ Type (λ bd → bd → Type)
  Bd zero = Unit , const A 
  Bd (suc n) =
    let (prev-bd , prev-ins) = Bd n
    in (Σ (Σ prev-bd prev-ins × Σ prev-bd prev-ins) λ x → fst (fst x) ≡ fst (snd (x))) ,
       λ x → PathP (λ i → prev-ins (snd x i)) (snd (fst (fst x))) (snd (snd (fst x)))
       

  Iso-bd : ∀ n → Iso (Σ (fst (Bd n)) (snd (Bd n))) (NCube n -> A)
  Iso.fun (Iso-bd zero) x x₁ = snd x
  Iso.inv (Iso-bd zero) x = _ , x []
  Iso.rightInv (Iso-bd zero) b i [] = b []
  Iso.leftInv (Iso-bd zero) (tt , snd₁) = refl
  
  Iso.fun (Iso-bd (suc n)) x (end false ∷ x₂) = Iso.fun (Iso-bd (n)) (_ , (snd x i0)) x₂
  Iso.fun (Iso-bd (suc n)) x (end true ∷ x₂) = Iso.fun (Iso-bd (n)) (_ , (snd x i1)) x₂
  Iso.fun (Iso-bd (suc n)) x (inside i ∷ x₂) = Iso.fun (Iso-bd (n)) (_ , (snd x i)) x₂
  
  Iso.inv (Iso-bd (suc n)) x = _ , λ i → snd (Iso.inv (Iso-bd n) (x i∷ i))
  
  Iso.rightInv (Iso-bd (suc n)) b i (end false ∷ x₁) = Iso.rightInv (Iso-bd (n)) (b i∷ i0) i x₁
  Iso.rightInv (Iso-bd (suc n)) b i (end true ∷ x₁) = Iso.rightInv (Iso-bd (n)) (b i∷ i1) i x₁
  Iso.rightInv (Iso-bd (suc n)) b i (inside i₁ ∷ x₁) = Iso.rightInv (Iso-bd (n)) (b i∷ i₁) i x₁
  Iso.leftInv (Iso-bd (suc n)) a i =
    _ , λ i₁ → snd (Iso.leftInv (Iso-bd n) (_ , snd a i₁) i)


record Lω {ℓ : Level} (A : Type ℓ) : Typeω where
  constructor lω
  field
    loω : A

open Lω

Iⁿ→ : ∀ {ℓ} → (A : Type ℓ) → ℕ → Typeω
Iⁿ→ A zero = I → A
Iⁿ→ A (suc x) = I → Iⁿ→ A x


∀Iⁿ : ∀ {ℓ} → ∀ {n} → (NCube n → Type ℓ) → Typeω 
∀Iⁿ {n = zero} x = Lω (x [])
∀Iⁿ {n = suc zero} x = ∀ i → x (inside i ∷ [])
∀Iⁿ {n = suc (suc n)} x = ∀ i → ∀Iⁿ (x i∷ i )

∀Iⁿ-cu : ∀ {ℓ} → ∀ {n} → (A : NCube n → Type ℓ) → ∀Iⁿ A →
                 ∀ x →  A x  
∀Iⁿ-cu {n = zero} A x [] = loω x
∀Iⁿ-cu {n = suc zero} A x (end false ∷ []) = x i0
∀Iⁿ-cu {n = suc zero} A x (end true ∷ []) = x i1
∀Iⁿ-cu {n = suc zero} A x (inside i ∷ []) = x i
∀Iⁿ-cu {n = suc (suc n)} A x (end false ∷ xs) = ∀Iⁿ-cu (A i∷ i0) (x i0) xs
∀Iⁿ-cu {n = suc (suc n)} A x (end true ∷ xs) = ∀Iⁿ-cu (A i∷ i1) (x i1) xs
∀Iⁿ-cu {n = suc (suc n)} A x (inside i ∷ xs) = ∀Iⁿ-cu (A i∷ i) (x i) xs


record BdP {ℓ} {n} (A : NBoundary (suc n) → Type ℓ) : Typeω where
   constructor bdP
   field
     lid0 : ∀Iⁿ (A ∘ lid false)
     lid1 : ∀Iⁿ (A ∘ lid true)
     pa : ∀ bd → PathP (λ i → A (cyl bd i))
             ((∀Iⁿ-cu _ lid0 ∘ boundaryInj) bd)
             ((∀Iⁿ-cu _ lid1 ∘ boundaryInj) bd)  



mkBd : ∀ {ℓ} {n} {A : NBoundary (suc n) → Type ℓ}
           → BdP A
           → ∀ x → A x
mkBd {ℓ} {zero} {A} x (lid false []) = loω (BdP.lid0 x)
mkBd {ℓ} {zero} {A} x (lid true []) = loω (BdP.lid1 x)
mkBd {ℓ} {suc n} {A} x (lid false x₂) = ∀Iⁿ-cu _ (BdP.lid0 x) x₂
mkBd {ℓ} {suc n} {A} x (lid true x₂) = ∀Iⁿ-cu _ (BdP.lid1 x) x₂
mkBd {ℓ} {suc n} {A} x (cyl x₁ i) = BdP.pa x x₁ i



-- NCubId : NBoundary 5 → Unit
-- NCubId = mkBd (bdP (λ i i₁ i₂ i₃ → tt)
--                    (λ i i₁ i₂ i₃ → tt)
--                    (mkBd (bdP
--                    (λ i i₁ i₂ i₃ → tt)
--                    (λ i i₁ i₂ i₃ → tt)
--                    (mkBd (bdP
--                    (λ i i₁ i₂ i₃ → tt)
--                    (λ i i₁ i₂ i₃ → tt)
--                    (mkBd (bdP
--                    {!!}
--                    {!!}
--                    {!!})))))))


-- NCubId : NBoundary 4 → NBoundary 4
-- NCubId = mkBd (bdP
--          (λ i i₁ i₂ → {!!})
--          (λ i i₁ i₂ → {!!})
--          (mkBd (bdP
--          (λ i i₁ i₂ → {!!})
--          (λ i i₁ i₂ → {!!})
--          (mkBd (bdP
--          (λ i i₁ i₂ → {!!})
--          (λ i i₁ i₂ → {!!})
--          (mkBd (bdP
--          (lω λ i i₁ i₂ → {!!})
--          (lω (λ i i₁ i₂ → {!!}))
--          λ () ))))))) 

NCubLem : {!(x : NBoundary 4) → ?!}
NCubLem = {!!}
