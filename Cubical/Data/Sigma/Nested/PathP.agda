

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



toCType : ∀ {ℓ} → ∀ n → (Cubeⁿ' n (Type ℓ)) → T[ CType ℓ n ]
toCType zero A _ = A
toCType (suc n) A i = toCType n (Cubeⁿ'-elim n A i)

fromCType : ∀ {ℓ} → ∀ n → T[ CType ℓ n ] → (Cubeⁿ' n (Type ℓ)) 
fromCType zero x = x 1=1
fromCType (suc n) x = Iso.inv (Cubeⁿ'-elim-iso n) (_ , (λ i → fromCType n (x i))) 

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




-- Cubeⁿ'-map-elim-isoP : ∀ {ℓ ℓb} → {A : Type ℓ} → {B : A → Type ℓb} → ∀ n →  (cA : Cubeⁿ' (suc n) A)
--                            →  (i : I) → 
--                            Iso (CubePⁿ' n (Cubeⁿ'-elim n (Cubeⁿ'-map (suc n) B cA) i))
--                                (CubePⁿ' n (Cubeⁿ'-map n B (Cubeⁿ'-elim n cA i)))
-- Cubeⁿ'-map-elim-isoP zero cA i = idIso
-- Cubeⁿ'-map-elim-isoP (suc n) cA i = {!!}

-- Cubeⁿ'-map-dep : ∀ {ℓ ℓb} → {A : Type ℓ} → {B : A → Type ℓb} → ∀ n → ((a : A) → B a) → (cA : Cubeⁿ' n A)
--                              → CubePⁿ' n (Cubeⁿ'-map n B cA)
-- Cubeⁿ'-map-dep zero x cA = x cA
-- Cubeⁿ'-map-dep {B = B} (suc n) x cA =

--    let z : (i : I) → CubePⁿ' n (Cubeⁿ'-map n B (Cubeⁿ'-elim n cA i))
--        z i = Cubeⁿ'-map-dep n x (Cubeⁿ'-elim n cA i)

--    in Iso.inv (CubePⁿ'-elim-iso n (Cubeⁿ'-map (suc n) _ cA)) (_ , (λ i → {!z i!}))
--    -- Iso.inv (CubePⁿ'-elim-iso n (Cubeⁿ'-map (suc n) _ cA))
--    --     (_ , λ i → {!Cubeⁿ'-map-dep n x ?!})


-- -- Cubeⁿ'-map-from-dep : ∀ {ℓ ℓb} → ∀ n → {A : Cubeⁿ' n (Type ℓ)} → {B : Type ℓb} →  (cA : CubePⁿ' n A)
-- --                              → CubePⁿ' n (Cubeⁿ'-map n (λ x → x → B) A)                               
-- --                              → Cubeⁿ' n B
-- -- Cubeⁿ'-map-from-dep = {!!} 


-- -- Cubeⁿ'-unzipΣ2-Path-Iso : ∀ {ℓ} → ∀ n → (A : (Type ℓ)) 
-- --                          → Iso (Cubeⁿ' n (Σ (A × A) λ x → fst x ≡ snd x) )
-- --                                (Σ (Cubeⁿ' n A × Cubeⁿ' n A) λ x → (fst x) ≡ (snd x))
-- -- Cubeⁿ'-unzipΣ2-Path-Iso = {!snd!}


-- -- Cubeⁿ'-unzipΣ2-IsoTy : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ))
-- --                                  → Cubeⁿ' n (Type ℓ)
-- -- Cubeⁿ'-unzipΣ2-IsoTy n A = Cubeⁿ'-map2 n _×_ ((Cubeⁿ'-elim n) A i0) ((Cubeⁿ'-elim n) A i1)

-- -- Cubeⁿ'-unzipΣ2-IsoTyPa : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ))
-- --                                  → CubePⁿ' n (Cubeⁿ'-unzipΣ2-IsoTy n A)
-- --                                  → Cubeⁿ' n (Type ℓ) 
-- -- Cubeⁿ'-unzipΣ2-IsoTyPa n A x = {!!}


-- -- Cubeⁿ'-unzipΣ2-Iso : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
-- --                                Iso (CubePⁿ' n ((Cubeⁿ'-elim n) A i0) × CubePⁿ' n ((Cubeⁿ'-elim n) A i1))
-- --                                    (CubePⁿ' n (Cubeⁿ'-unzipΣ2-IsoTy n A))
-- -- Cubeⁿ'-unzipΣ2-Iso = {!!}


-- -- Cubeⁿ'-unzipΣ2-Iso-mkP : ∀ {ℓ} (n : ℕ)
-- --                            (A : Cubeⁿ' (suc n) (Type ℓ))
-- --                            (c0 : CubePⁿ' n (Cubeⁿ'-elim n A i0))
-- --                            (c1 : CubePⁿ' n (Cubeⁿ'-elim n A i1)) →
-- --                             CubePⁿ' n (Cubeⁿ'-map n (λ x → x → Type ℓ)
-- --                              (Cubeⁿ'-unzipΣ2-IsoTy n A))
-- -- Cubeⁿ'-unzipΣ2-Iso-mkP = {!!}


-- -- CubePⁿ'-unzipΣ2-Path-Iso : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) 
-- --                         → (c0 : CubePⁿ' n ((Cubeⁿ'-elim n) A i0))
-- --                         → (c1 : CubePⁿ' n ((Cubeⁿ'-elim n) A i1))
-- --                         →  Iso (CubePⁿ' n (Cubeⁿ'-map-from-dep n (Iso.fun (Cubeⁿ'-unzipΣ2-Iso n A) (c0 , c1))
-- --                                                                 (Cubeⁿ'-unzipΣ2-Iso-mkP n A c0 c1)))
-- --                                (PathP (λ i → CubePⁿ' n ((Cubeⁿ'-elim n) A i)) c0 c1)

-- -- CubePⁿ'-unzipΣ2-Path-Iso = {!!}



-- -- PathCu : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
-- --                      (c0 : CubePⁿ' n ((Cubeⁿ'-elim n) A i0)) →
-- --                      (c1 : CubePⁿ' n ((Cubeⁿ'-elim n) A i1)) →
-- --                      Cubeⁿ' n (Type ℓ) 
-- -- PathCu n A c0 c1 = {!!}


