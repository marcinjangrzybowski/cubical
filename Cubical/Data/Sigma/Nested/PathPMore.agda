{-

  From (I → Sig ℓ n) we can generate Sig ℓ (n * 3)
  in the two ways by arranging fileds in diferent order
   (this is illustrated in Example.agda)

  Of course for both definitions, the path betwen most nested arguments must be at the end,
  becouse its type depends on all the previous fields.


  In second part of this file, those generated signatures are used to
  define paths of arbitrary dimension (generalization of Path, Square and Cube from Prelude).

  The diferent order of fields results in two diferent (equivalent after uncurring)
  definitions of Pathⁿ.

  Non-primed definition have order of arguments consistent with definitions from Prelude.


-}


{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Sigma.Nested.PathP where

open import Cubical.Data.Nat

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying

open import Cubical.Data.Sigma.Nested.Path

open import Cubical.HITs.NCube.IntervalPrim



Boundaryⁿ'-elim-iso2 : ∀ {ℓ} → {A : Type ℓ} → ∀ n →
               Iso (Boundaryⁿ' (suc n) A)
                   ((Σ (Σ ((Boundaryⁿ' n A) × (Boundaryⁿ' n A)) λ a → (fst a) ≡ (snd a) ))
                     λ x → InsideOfⁿ' {n = n} {A} (fst (fst x)) × InsideOfⁿ' {n = n} {A} (snd (fst x)) )

-- Boundaryⁿ'-elim-iso2 {A = A} zero = {!!}

Boundaryⁿ'-elim-iso2 {A = A} n =
   compIso (Boundaryⁿ'-elim-iso {A = A} n) h 

  where

    module cuIso = Iso (Cubeⁿ'-ΣInsideⁿ'-iso {A = A} n)

    h : Iso
                (Σ (Cubeⁿ' n A × Cubeⁿ' n A)
                  (λ a → cubeBd' n A (fst a) ≡ cubeBd' n A (snd a)))
                (Σ (Σ (Boundaryⁿ' n A × Boundaryⁿ' n A) (λ a → fst a ≡ snd a))
                  (λ x → InsideOfⁿ' {n = n} {A = A} (fst (fst x)) × InsideOfⁿ' {n = n} {A = A} (snd (fst x))))
    Iso.fun h ((c0 , c1) , bp) =
       let (bd0 , ins0) = cuIso.fun c0
           (bd1 , ins1) = cuIso.fun c1
       in  ((bd0 , bd1) , bp) , ins0 , ins1
       
    Iso.inv h (((bd0 , bd1) , bp) , ins0 , ins1) =
       let c0 = cuIso.inv (bd0 , ins0)
           c1 = cuIso.inv (bd1 , ins1)
       in  ((c0 , c1) , (cong fst (cuIso.rightInv _) ∙∙ bp ∙∙ sym (cong fst (cuIso.rightInv _))))

    Iso.rightInv h = {!!}

    Iso.leftInv h = {!!}











NCubePSig' : ∀ {ℓ} → ∀ n → Cubeⁿ' n (Type ℓ) → Sig ℓ (3^ n)
NCubePSig' zero x = x
NCubePSig' (suc n) x = sig-PathP-withEnds' λ i → NCubePSig' n (Cubeⁿ'-elim n x i)

BoundaryPⁿ' :  ∀ {ℓ} → ∀ n → (A : Cubeⁿ' n (Type ℓ)) → Type ℓ
BoundaryPⁿ' n A = NestedΣᵣ (dropLast (NCubePSig' n A))

CubePⁿ' : ∀ {ℓ} → ∀ n → Cubeⁿ' n (Type ℓ) → Type ℓ
CubePⁿ' n A = NestedΣᵣ (NCubePSig' n A)

cubeBdP' : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' n (Type ℓ)) → CubePⁿ' n A → BoundaryPⁿ' n A
cubeBdP' n A = dropLastΣᵣ ( (NCubePSig' n A))


InsideOfPⁿ' : ∀ {ℓ} → ∀ {n} → {A : Cubeⁿ' n (Type ℓ)} → BoundaryPⁿ' n A → Type ℓ
InsideOfPⁿ' {n = n} {A} = lastTy (NCubePSig' n A)

cubePIns' : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' n (Type ℓ)) → (c : CubePⁿ' n A) → InsideOfPⁿ' {n = n} {A} (cubeBdP' n A c)
cubePIns' n A c = getLast ((NCubePSig' n A)) c





BoundaryPⁿ'-elim-iso : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →  
                          Iso (BoundaryPⁿ' (suc n) A) 
                              (Σ ((CubePⁿ' n _) × (CubePⁿ' n _))
                                (λ a → 
                                 PathP (λ i → BoundaryPⁿ' n (Cubeⁿ'-elim n A i))
                                    (cubeBdP' n _ (fst a)) 
                                    (cubeBdP' n _ (snd a)) ))

BoundaryPⁿ'-elim-iso n A = sig-PathP-withEnds'-iso-dropL (λ i → (NCubePSig' n (Cubeⁿ'-elim n A i))) --λ i → (NCubePSig' n ?)
  where open Boundary*-elim-iso-lemmas 


-- -- module debugTransp where

-- --   A = Type

-- --   zz : (Σ ((Cubeⁿ' 4 A) × (Cubeⁿ' 4 A)) λ a → cubeBd' 4 A (fst a) ≡ cubeBd' 4 A (snd a) ) → {!!}
-- --   zz x = {!getLast (dropLast (NCubeSig' 4 A)) (Iso.inv (Boundary'-elim-iso 4) x) !}


CubePⁿ'-elim-iso : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
               Iso (CubePⁿ' (suc n) A)
                   (Σ ((CubePⁿ' n _) × (CubePⁿ' n _))
                                (λ a → PathP (λ i → CubePⁿ' n (Cubeⁿ'-elim n A i))
                                            (fst a) 
                                            (snd a) ))


CubePⁿ'-elim-iso n A = nestedΣᵣ-combine-iso (λ i → NCubePSig' n (Cubeⁿ'-elim n A i))



Boundaryⁿ'-splitBase : ∀ {ℓ} → ℕ → ℕ → (A : Type ℓ) → Type ℓ
Boundaryⁿ'-splitBase n m A = Cubeⁿ' n (Boundaryⁿ' m A)


Boundaryⁿ'-splitTarget : ∀ {ℓ} → ∀ n m → ∀ (A : Type ℓ) → Boundaryⁿ'-splitBase n m A → Type ℓ
Boundaryⁿ'-splitTarget n m A sb = BoundaryPⁿ' n (Cubeⁿ'-map n (InsideOfⁿ' {n = m}) sb) 

Boundaryⁿ'-Split : ∀ {ℓ} → ∀ (A : Type ℓ) → ℕ → ℕ → Type ℓ
Boundaryⁿ'-Split A n m = Σ _ (Boundaryⁿ'-splitTarget n m A)



Cubeⁿ'-Boundaryⁿ'-InsideOfⁿ'-Iso : ∀ {ℓ} → {A : Type ℓ} → ∀ n →
                                      Iso (Cubeⁿ' n A) (Σ _ (InsideOfⁿ' {n = n} {A = A}))
Cubeⁿ'-Boundaryⁿ'-InsideOfⁿ'-Iso n = {!!}

Cubeⁿ'-map2 : ∀ {ℓ ℓb} → {A A' : Type ℓ} → {B : Type ℓb} → ∀ n → (A → A' → B) → Cubeⁿ' n A → Cubeⁿ' n A' → Cubeⁿ' n B
Cubeⁿ'-map2 = {!!}


Cubeⁿ'-unzipΣ-Iso : ∀ {ℓ ℓc} → ∀ n → (A : Type ℓ ) → (C : A → Type ℓc)
                         → Iso (Cubeⁿ' n ((Σ A C)))
                                (Σ (Cubeⁿ' n A ) λ x → CubePⁿ' n (Cubeⁿ'-map n C x))
Cubeⁿ'-unzipΣ-Iso = {!!}


Cubeⁿ'-unzipΣ2-Iso : ∀ {ℓ ℓc} → ∀ n → (A B : Type ℓ ) → (C : A → B → Type ℓc)
                         → Iso (Cubeⁿ' n ((Σ (A × B) λ x → C (fst x) (snd x))))
                                (Σ (Cubeⁿ' n A × Cubeⁿ' n B ) λ x → CubePⁿ' n (Cubeⁿ'-map2 n C (fst x) (snd x)))
Cubeⁿ'-unzipΣ2-Iso = {!!}

Cubeⁿ'-unzipΣ2-Path-Iso : ∀ {ℓ ℓb} → ∀ n → (A : Type ℓ ) → (B : Type ℓb ) → (f : A → B)
                         → Iso (Cubeⁿ' n (Σ (A × A) λ x → f (fst x) ≡ f (snd x)))
                               (Σ (Cubeⁿ' n A × Cubeⁿ' n A)
                                       λ x →    (Cubeⁿ'-map n f (fst x))
                                              ≡ (Cubeⁿ'-map n f (snd x)))
                                -- (Σ (Cubeⁿ' n A × Cubeⁿ' n B ) λ x → CubePⁿ' n (Cubeⁿ'-map2 n C (fst x) (snd x)))
Cubeⁿ'-unzipΣ2-Path-Iso = {!!}

getSplitBd : ∀ {ℓ} → ∀ n m → ∀ (A : Type ℓ) → Cubeⁿ' n (Cubeⁿ' m A ) → Boundaryⁿ'-Split A n m
getSplitBd n m A x = {!!}

Boundary-split-Iso-L :  ∀ {ℓ} → ∀ n m → ∀ (A : Type ℓ)
                          → Iso (Boundaryⁿ'-Split A (suc n) m)
                                (Σ (Cubeⁿ' n (Cubeⁿ' m A ) × (Cubeⁿ' n (Cubeⁿ' m A)))
                                       λ a →  _≡_ {A = Boundaryⁿ'-Split A n m}
                                                   (getSplitBd n m A (fst a))
                                                   (getSplitBd n m A (fst a)) )
Boundary-split-Iso-L = {!!}

Boundary-split-Iso-R :  ∀ {ℓ} → ∀ n m → ∀ (A : Type ℓ)
                          →  Iso (Boundaryⁿ'-Split A n (suc m))
                                (Σ (Cubeⁿ' n (Cubeⁿ' m A ) × (Cubeⁿ' n (Cubeⁿ' m A)))
                                       λ a →  _≡_ {A = Boundaryⁿ'-Split A n m}
                                                   (getSplitBd n m A (fst a))
                                                   (getSplitBd n m A (fst a)) )
Boundary-split-Iso-R = {!!}


Boundary-split-Iso :  ∀ {ℓ} → ∀ n m → ∀ (A : Type ℓ)
                          → Iso (Boundaryⁿ'-Split A (suc n) m)
                                (Boundaryⁿ'-Split A n (suc m))

Boundary-split-Iso n m A = compIso (Boundary-split-Iso-L n m A) (invIso (Boundary-split-Iso-R n m A))


-- Boundary-split-Iso zero zero A = {!!}
-- Boundary-split-Iso zero (suc m) A = {!!}
-- Boundary-split-Iso (suc n) zero A = {!!}

-- Boundary-split-Iso n@(suc nn) m@(suc mm) A = iso fun inv sec ret
--   where
--     module CIsoN = Iso (Cubeⁿ'-elim-iso {A = Boundaryⁿ' m A} n)
--     module BIsoPN sb = Iso (BoundaryPⁿ'-elim-iso n (Cubeⁿ'-map {A = Boundaryⁿ' m A} (suc n) (InsideOfⁿ' {n = m}) sb))
--     module BIsoM = Iso (Boundaryⁿ'-elim-iso {A = A} m)

--     module ZipIsoBM = Iso (Cubeⁿ'-unzipΣ2-Path-Iso n (Cubeⁿ' m A) (Boundaryⁿ' m A) (cubeBd' m A))

--     module CBI-Iso-m = Iso (Cubeⁿ'-Boundaryⁿ'-InsideOfⁿ'-Iso {A = A} m)

--     fun : Boundaryⁿ'-Split A (suc n) m → Boundaryⁿ'-Split A n (suc m)
--     fun (base , trgt) =
--        let ((_ , _) , p) = CIsoN.fun base
--            ((x₀* , x₁*) , p*) = BIsoPN.fun base trgt

--            -- xx0 = Cubeⁿ'-map n (CBI-Iso-m.inv) (Iso.inv (Cubeⁿ'-unzipΣ-Iso n _ _) (x₀ , {!p* i0!}))
--            -- xx1 = Cubeⁿ'-map n (CBI-Iso-m.inv) (Iso.inv (Cubeⁿ'-unzipΣ-Iso n _ _) (x₁ , {!!}))
           
--            pp : I → NestedΣᵣ (NCubeSig' (suc nn) (Cubeⁿ' (suc mm) A))
--            pp = λ i → Cubeⁿ'-map n (CBI-Iso-m.inv) (Iso.inv (Cubeⁿ'-unzipΣ-Iso n _ _) (p i , {!!}))

--            z = {!trgt!}

--            pa1 :  {!!} ≡ {!!}
--            pa1 = {!!}
           
--            fstR : Boundaryⁿ'-splitBase (suc nn) (suc (suc mm)) A
--            fstR = Cubeⁿ'-map n BIsoM.inv (ZipIsoBM.inv (({!!} , {!!}) , {!p!}))




--           -- pierwszy parametr pary ma zyskac dane
--           in {!!}
--            , {!!}

--     inv : Boundaryⁿ'-Split A n (suc m) → Boundaryⁿ'-Split A (suc n) m
--     inv = {!!}

--     sec : section fun inv
--     sec = {!!}

--     ret : retract fun inv
--     ret = {!!}

  


-- Iso.fun (Boundary-split-Iso zero zero A) = (_, _) ∘ snd
-- Iso.inv (Boundary-split-Iso zero zero A) = ((_ , (_ , refl)) ,_) ∘ fst
-- Iso.rightInv (Boundary-split-Iso zero zero A) b = refl
-- Iso.leftInv (Boundary-split-Iso zero zero A) a = refl

-- Boundary-split-Iso zero (suc m) A = {!!}
-- Boundary-split-Iso (suc n) zero A = {!!}
-- Boundary-split-Iso (suc n) (suc m) A = {!!}


Iso-string : ∀ {ℓ} → (A : ℕ → ℕ → Type ℓ) → (∀ n m → Iso (A (suc n) m) (A n (suc m)))
                   → ∀ n → (Iso (A n zero) (A zero n))
Iso-string A x zero = idIso
Iso-string A x (suc n) = compIso (x n zero) (Iso-string (λ n m → A n (suc m)) (λ n' m' → x n' (suc m')) n)

-- InsideOfnot-ω : ∀ {ℓ} → ∀ n → {A : T[ CType ℓ n ]}
--              → (x : T[ Boundaryω n A ]) → Type ℓ
-- InsideOfnot-ω zero {A} x = A 1=1
-- InsideOfnot-ω (suc zero) {A} x = PathP (λ i → A i 1=1) (x i0 1=1) (x i1 1=1)
-- InsideOfnot-ω (suc (suc n)) {A} x = PathP (λ i →  InsideOfnot-ω (suc n) {A = (A i)} {!x i!}) {!(x i0)!} {!!}

-- -- Boundaryⁿ'-Splitω : ∀ {ℓ}  → ∀ n → ∀ m → ∀ (A : T[ CType ℓ (n + m) ]) → Typeω

-- Boundaryⁿ'-Splitω-base : ∀ {ℓ}  → ∀ n → ∀ m → ∀ (A : T[ CType ℓ (n + m) ]) → ωType
-- Boundaryⁿ'-Splitω-base zero m A = Boundaryω m A
-- Boundaryⁿ'-Splitω-base (suc n) m A = ∀I λ i → Boundaryⁿ'-Splitω-base n m (A i)

-- -- Boundaryⁿ'-Splitω-target-Ty : ∀ {ℓ}  → ∀ n → ∀ m → ∀ (A : T[ CType ℓ (n + m) ])
-- --                            → T[ Boundaryⁿ'-Splitω-base n m A ] → T[ CType ℓ n ]
-- -- Boundaryⁿ'-Splitω-target-Ty zero m A x = {!!}
-- -- Boundaryⁿ'-Splitω-target-Ty (suc n) m A x = {!!}

-- Boundaryⁿ'-Splitω-target : ∀ {ℓ}  → ∀ n → ∀ m → ∀ (A : T[ CType ℓ (n + m) ])
--                            → T[ Boundaryⁿ'-Splitω-base n m A ] → ωType
-- Boundaryⁿ'-Splitω-target n m A x = Boundaryω n {!!} 

-- Boundaryⁿ'-splitTarget : ∀ {ℓ} → ∀ n m → ∀ (A : Type ℓ) → Boundaryⁿ'-splitBase n m A → Type ℓ
-- Boundaryⁿ'-splitTarget n m A sb = BoundaryPⁿ' n (Cubeⁿ'-map n (InsideOfⁿ' {n = m}) sb)




-- Boundaryⁿ'-splitTargetω : ∀ {ℓ} → ∀ n m → ∀ (A : Type ℓ) → Boundaryⁿ'-splitBase n m A → ωType
-- Boundaryⁿ'-splitTargetω n m A sb = Boundaryω n (toCType n (Cubeⁿ'-map n (InsideOfⁿ' {n = m}) sb)) 


-- Boundaryⁿ'-splitω-exchange-L-base : ∀ {ℓ} → ∀ n m → ∀ (A : Type ℓ) → (base : Boundaryⁿ'-splitBase (suc n) m A)
--                                        → T[ (Boundaryⁿ'-splitTargetω (suc n) m A base) ]
--                                        → Boundaryⁿ'-splitBase n (suc m) A
-- Boundaryⁿ'-splitω-exchange-L-base = {!!}

-- Boundaryⁿ'-splitω-exchange-L : ∀ {ℓ} → ∀ n m → ∀ (A : Type ℓ) → (base : Boundaryⁿ'-splitBase (suc n) m A)
--                                        → (T1 : T[ (Boundaryⁿ'-splitTargetω (suc n) m A base) ])
--                                        → T[ (Boundaryⁿ'-splitTargetω n (suc m) A (Boundaryⁿ'-splitω-exchange-L-base n m A base T1)) ]
                                       
-- Boundaryⁿ'-splitω-exchange-L = {!!}



-- Boundaryⁿ'-splitω-Iso : {!!}
-- Boundaryⁿ'-splitω-Iso = {!!}



Boundaryω-attachE :  ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
                              (e0 : CubePⁿ' n (Cubeⁿ'-elim n A i0)) → (e1 : CubePⁿ' n (Cubeⁿ'-elim n A i1))
                                → {!!}
                                → {!!}
Boundaryω-attachE = {!!}

Boundaryω-Iso :  ∀ {ℓ} → ∀ n → (A : Cubeⁿ' n (Type ℓ)) → BoundaryPⁿ' n A  → T[ Boundaryω n (toCType n A) ]
Boundaryω-Iso zero A _ ()
Boundaryω-Iso (suc n) A x =
  let ((c0 , c1) , pa) = Iso.fun (BoundaryPⁿ'-elim-iso n A) x
      cl : (i : I) → T[ Partialⁿ n (boundaryExpr n) (toCType n (Cubeⁿ'-elim n A i)) ]
      cl i = Boundaryω-Iso n ((Cubeⁿ'-elim n A) i ) (pa i)
  in {!Boundaryω-attachE n A cl!}
