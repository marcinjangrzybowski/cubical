

{-# OPTIONS --cubical #-}

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
open import Cubical.Data.Sigma.Nested.PathMore


open import Cubical.HITs.NCube.IntervalPrim

open import Cubical.HITs.NCube.BaseVec

open import Cubical.Foundations.Equiv.HalfAdjoint

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





-- slice-fun : ∀ {ℓ} → ∀ n → {A : Cubeⁿ' (suc n) (Type ℓ)} → {B : Cubeⁿ' (suc n) (Type ℓ)}
--                  → (f : CubePⁿ' (suc n) (Cubeⁿ'-map2 (suc n) (λ x x₁ → x → x₁) A B))
--                  → PathP (λ i → CubePⁿ' n
--                               (Cubeⁿ'-map2 n (λ x x₁ → x → x₁) (Cubeⁿ'-elim n A i)
--                               (Cubeⁿ'-elim n B i)))
--                               {! !}
--                               {!!}
-- slice-fun zero f = {!!}
-- slice-fun (suc n) f = {!!}



CubePⁿ'-elim-iso : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
               Iso (CubePⁿ' (suc n) A)
                   (Σ ((CubePⁿ' n _) × (CubePⁿ' n _))
                                (λ a → PathP (λ i → CubePⁿ' n (Cubeⁿ'-elim n A i))
                                            (fst a) 
                                            (snd a) ))

CubePⁿ'-elim-iso n A = nestedΣᵣ-combine-iso (λ i → NCubePSig' n (Cubeⁿ'-elim n A i))


CubePⁿ'-ΣInsidePⁿ'-iso : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' n (Type ℓ)) →
                         Iso
                          (CubePⁿ' n A)
                          (Σ (BoundaryPⁿ' n A) (InsideOfPⁿ' {n = n} {A}) )
                          
CubePⁿ'-ΣInsidePⁿ'-iso n A = nestedΣᵣ-dropLast.isom-to (3^ n) (NCubePSig' n A)


BoundaryPⁿ'-elim-iso2 : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ))  →
               Iso (BoundaryPⁿ' (suc n) A)
                   ((Σ (Σ ((BoundaryPⁿ' n _) × (BoundaryPⁿ' n _))
                           λ a → PathP (λ i → BoundaryPⁿ' n (Cubeⁿ'-elim n A i)) (fst a) (snd a) ))
                     λ x → InsideOfPⁿ' {n = n} {_} (fst (fst x)) × InsideOfPⁿ' {n = n} {_} (snd (fst x)) )

BoundaryPⁿ'-elim-iso2 n A =
     compIso (BoundaryPⁿ'-elim-iso n A) h 

  where

    cuIso : (i : I) → _
    cuIso = λ i → (isHAEquiv→Iso (snd (iso→HAEquiv (CubePⁿ'-ΣInsidePⁿ'-iso n ((Cubeⁿ'-elim n A i))))))

    h : Iso
                (Σ (CubePⁿ' n _ × CubePⁿ' n _)
                  (λ a → PathP _ (cubeBdP' n _ (fst a)) (cubeBdP' n _ (snd a))))
                (Σ (Σ (BoundaryPⁿ' n _ × BoundaryPⁿ' n _) (λ a → PathP _ (fst a) (snd a)))
                  (λ x → InsideOfPⁿ' {n = n} {A = _} (fst (fst x)) × InsideOfPⁿ' {n = n} {A = _} (snd (fst x))))
    -- h =               
    Iso.fun h ((c0 , c1) , bp) =
       let (bd0 , ins0) = Iso.fun (cuIso i0) c0
           (bd1 , ins1) = Iso.fun (cuIso i1) c1
       in  ((bd0 , bd1) , bp) , ins0 , ins1
       
    Iso.inv h (((bd0 , bd1) , bp) , ins0 , ins1) =
       let c0 = Iso.inv (cuIso i0) (bd0 , ins0)
           c1 = Iso.inv (cuIso i1) (bd1 , ins1)
       in  ((c0 , c1) , λ i → hcomp (λ j →
                                      λ { (i = i0) → cong fst (Iso.rightInv (cuIso i0) (bd0 , ins0)) (~ j)
                                        ; (i = i1) → cong fst (Iso.rightInv (cuIso i1) (bd1 , ins1)) (~ j)}  )
                                        (bp i))

    Iso.rightInv h (((bd0 , bd1) , bp) , ins0 , ins1) i =
       let (bd0' , ins0') = Iso.rightInv (cuIso i0) (bd0 , ins0) i
           (bd1' , ins1') = Iso.rightInv (cuIso i1) (bd1 , ins1) i
       in  ((bd0' , bd1') ,
                λ i₁ → hfill 
                   ((λ j →  λ { (i₁ = i0) → (cong fst (Iso.rightInv (cuIso i0) (bd0 , ins0))) (~ j)
                              ; (i₁ = i1) → (cong fst (Iso.rightInv (cuIso i1) (bd1 , ins1))) (~ j)}  ))
                   (inS (bp i₁))
                   (~ i)
  
                    )
                 , ins0' , ins1'

    Iso.leftInv h ((c0 , c1) , bp) i = {!!}
       -- let c0' = Iso.leftInv cuIso c0 i
       --     c1' = Iso.leftInv cuIso c1 i

       --     ww' : (j : I) → _
       --     ww' j =  doubleCompPath-filler ( cong fst (Iso.rightInv cuIso (Iso.fun cuIso c0))) bp
       --                     (sym (cong fst (Iso.rightInv cuIso (Iso.fun cuIso c1)))) (j)


       --     ww0 : Square
       --                  (λ _ → bp i0)
       --                  (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c0))
       --                  (sym (cong fst (Iso.rightInv cuIso (Iso.fun cuIso c0))))
       --                  (λ _ → bp i0)
       --     ww0 k j =
       --        hcomp
       --          (λ l → λ { (j = i0) → fst ((isHAEquiv.com (snd (iso→HAEquiv (Cubeⁿ'-ΣInsideⁿ'-iso {A = A} n))) c0) l (~ k))
       --                   ; (j = i1) → bp i0
       --                   ; (k = i0) → bp i0
       --                   ; (k = i1) → (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c0)) j
       --              })
       --          ( (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c0)) (j ∨  (~ k)))


       --     ww1 :  Square 
       --                  (λ _ → bp i1)
       --                  ((cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c1)))
       --                  ((sym (cong fst (Iso.rightInv cuIso (Iso.fun cuIso c1)))))
       --                  (λ _ → bp i1)
       --     ww1 k j =
       --        hcomp
       --          (λ l → λ { (j = i0) → fst ((isHAEquiv.com (snd (iso→HAEquiv (Cubeⁿ'-ΣInsideⁿ'-iso {A = A} n))) c1) l (~ k))
       --                   ; (j = i1) → bp i1
       --                   ; (k = i0) → bp i1
       --                   ; (k = i1) → (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c1)) j
       --              })
       --          ( (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c1)) (j ∨  (~ k)))


       --     ww : PathP (λ v → PathP (λ v₁ → NestedΣᵣ (dropLast (NCubeSig' n A)))
       --                         (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c0) v)
       --                         ((cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c1) v)))
       --                   ( cong fst (Iso.rightInv cuIso (Iso.fun cuIso c0))
       --                       ∙∙ bp ∙∙
       --                     sym (cong fst (Iso.rightInv cuIso (Iso.fun cuIso c1)))) bp
       --     ww j l =
       --        hcomp
       --          (λ k → λ { (j = i0) → ww' k l --
       --                   ; (j = i1) → bp l
       --                   ; (l = i0) → ww0 k j
       --                   ; (l = i1) → ww1 k j
       --              })
       --          ( bp l)

       -- in  ((c0' , c1') , λ i₁ → ww i i₁)

postulate InsideOfPⁿ'-elim-iso :  ∀ {ℓ} → ∀ n → {A : Cubeⁿ' (suc n) (Type ℓ)} →
                         (bd : (BoundaryPⁿ' (suc n) A))
                       → Iso (InsideOfPⁿ' {n = suc n} bd)
                             (PathP (λ i → InsideOfPⁿ' {n = n} (snd (fst (Iso.fun (BoundaryPⁿ'-elim-iso2 n A) bd)) i))
                                (fst (snd (Iso.fun (BoundaryPⁿ'-elim-iso2 n A) bd)))
                                (snd (snd (Iso.fun (BoundaryPⁿ'-elim-iso2 n A) bd))))
                       
-- Iso.fun (InsideOfPⁿ'-elim-iso n bd) x =
--    let z = snd (Iso.fun (CubePⁿ'-elim-iso n _) (Iso.inv (CubePⁿ'-ΣInsidePⁿ'-iso (suc n) _) (bd , x)))
--        zz : PathP {!!} {!!} {!!}
--        zz i = snd (Iso.fun (CubePⁿ'-ΣInsidePⁿ'-iso (n) _) (z i))
--    in {!zz!}
   
-- Iso.inv (InsideOfPⁿ'-elim-iso n bd) = {!!}

-- Iso.rightInv (InsideOfPⁿ'-elim-iso n bd) = {!!}

-- Iso.leftInv (InsideOfPⁿ'-elim-iso n bd) = {!!}





-- -- map2-elim-I : ∀ {ℓ ℓb} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ))
-- --               → ∀ (f : Type ℓ → Type ℓb) → (i : I) →
-- --               Iso (CubePⁿ' n (Cubeⁿ'-elim n (Cubeⁿ'-map (suc n) f A) i))
-- --                   (CubePⁿ' n (Cubeⁿ'-map n f (Cubeⁿ'-elim n A i)))
-- -- map2-elim-I = {!!}






-- -- map2-elim-I : ∀ {ℓ ℓb} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) → (B : Cubeⁿ' (suc n) (Type ℓ))
-- --               → ∀ (f : Type ℓ → Type ℓ → Type ℓb) → (i : I)
-- --               → (CubePⁿ' n (Cubeⁿ'-elim n (Cubeⁿ'-map2 (suc n) f A B) i))
-- --               → CubePⁿ' n (Cubeⁿ'-map2 n f (Cubeⁿ'-elim n A i) (Cubeⁿ'-elim n B i))
-- -- map2-elim-I zero A B f i x = x
-- -- map2-elim-I (suc n) A B f i x = {!!}

postulate slice-fun : ∀ {ℓ} → ∀ n → {A : Cubeⁿ' (suc n) (Type ℓ)} → {B : Cubeⁿ' (suc n) (Type ℓ)}
                 → (f : CubePⁿ' (suc n) (Cubeⁿ'-map2 (suc n) (λ x x₁ → x → x₁) A B))
                 → (∀ i → CubePⁿ' n
                              (Cubeⁿ'-map2 n (λ x x₁ → x → x₁) (Cubeⁿ'-elim n A i)
                              (Cubeⁿ'-elim n B i)))
                              

-- -- slice-fun zero f i = snd (snd f) i
-- slice-fun n f i = 
--   let z : (i : I) → {!!}
--       z = {! !}
--   in {!!}






--TODO fix to hanel diferent levels
BoundaryPⁿ'-map : ∀ {ℓ} → ∀ n → {A : Cubeⁿ' n (Type ℓ)} → {B : Cubeⁿ' n (Type ℓ)}
                 → (CubePⁿ' n (Cubeⁿ'-map2 n (λ x x₁ → x → x₁) A B))
                 → BoundaryPⁿ' n A
                 → BoundaryPⁿ' n B

InsideOfPⁿ'-map : ∀ {ℓ} → ∀ n → {A : Cubeⁿ' n (Type ℓ)} → {B : Cubeⁿ' n (Type ℓ)}
                 → (f : CubePⁿ' n (Cubeⁿ'-map2 n (λ x x₁ → x → x₁) A B))
                 → (bd : BoundaryPⁿ' n A)
                 → InsideOfPⁿ' {n = n} bd 
                 → InsideOfPⁿ' {n = n} (BoundaryPⁿ'-map n f bd)

BoundaryPⁿ'-map zero _ _ = _
BoundaryPⁿ'-map (suc n) {A = A} {B = B} f bd = 
  let ( (_ , bdP) , (lid0 , lid1 ) ) = Iso.fun (BoundaryPⁿ'-elim-iso2 n A) bd

      f' = slice-fun n f
  in Iso.inv (BoundaryPⁿ'-elim-iso2 n B)
              (( (_ , λ i → BoundaryPⁿ'-map n (f' i) (bdP i))
                                 , (InsideOfPⁿ'-map n (f' i0) _ lid0 , InsideOfPⁿ'-map n (f' i1) _ lid1) ))

InsideOfPⁿ'-map zero f bd x = f x
InsideOfPⁿ'-map (suc n) {A = A} {B = B} f bd x =
   let ( (_ , bdP) , (lid0 , lid1 ) ) = Iso.fun (BoundaryPⁿ'-elim-iso2 n A) bd

       z = Iso.fun (InsideOfPⁿ'-elim-iso n bd) x

       z' : PathP (λ i →
                      InsideOfPⁿ' {n = n}
                      (BoundaryPⁿ'-map n (slice-fun n f i)
                       (snd (fst (Iso.fun (BoundaryPⁿ'-elim-iso2 n A) bd)) i)))

                         (InsideOfPⁿ'-map n (slice-fun n f i0)
                           (snd (fst (Iso.fun (BoundaryPⁿ'-elim-iso2 n A) bd)) i0)
                           (Iso.fun (InsideOfPⁿ'-elim-iso n bd) x i0))

                         (InsideOfPⁿ'-map n (slice-fun n f i1)
                            (snd (fst (Iso.fun (BoundaryPⁿ'-elim-iso2 n A) bd)) i1)
                            (Iso.fun (InsideOfPⁿ'-elim-iso n bd) x i1))
       z' i = InsideOfPⁿ'-map n
                (slice-fun n f i)
                (snd (fst (Iso.fun (BoundaryPⁿ'-elim-iso2 n A) bd)) i)
                (z i)

       zz : PathP
              (λ i →
                 InsideOfPⁿ' {n = n}
                 (snd
                  (fst
                   (Iso.fun (BoundaryPⁿ'-elim-iso2 n B)
                    (BoundaryPⁿ'-map (suc n) f bd)))
                  i))
              (fst
               (snd
                (Iso.fun (BoundaryPⁿ'-elim-iso2 n B)
                 (BoundaryPⁿ'-map (suc n) f bd))))
              (snd
               (snd
                (Iso.fun (BoundaryPⁿ'-elim-iso2 n B)
                 (BoundaryPⁿ'-map (suc n) f bd))))
       zz = {!!}
   in Iso.inv ((InsideOfPⁿ'-elim-iso n (BoundaryPⁿ'-map (suc n) f bd))) zz

-- InsideOfⁿ'-map zero f bd x = f x

-- InsideOfⁿ'-map (suc zero) f bd x = cong f x
-- InsideOfⁿ'-map (suc (suc zero)) f bd x i j =
--    {! (x i)!}
-- InsideOfⁿ'-map (suc (suc (suc n))) f bd x = {!!}












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


