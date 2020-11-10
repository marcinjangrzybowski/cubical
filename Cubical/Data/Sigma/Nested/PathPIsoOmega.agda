

{-# OPTIONS --cubical #-}

module Cubical.Data.Sigma.Nested.PathPIsoOmega where

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

open import Cubical.Data.Sigma.Nested.PathP



CubePⁿ'-Isomω : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' n (Type ℓ)) →
                                Isoω (CubePⁿ' n A)
                                     (cu n (toCType n A))
Isoω.to (CubePⁿ'-Isomω zero A) x x₁ = x
Isoω.toω (CubePⁿ'-Isomω zero A) t₀ t₁ x x₁ = x
Isoω.from (CubePⁿ'-Isomω zero A) x = x 1=1
Isoω.sec (CubePⁿ'-Isomω zero A) b = refl
Isoω.ret (CubePⁿ'-Isomω zero A) a _ = refl

CubePⁿ'-Isomω (suc n) A = h
  where

    module ciso = Iso (CubePⁿ'-elim-iso n A)

    h : Isoω (CubePⁿ' (suc n) A)
          (cu (suc n) (toCType (suc n) A))

    Isoω.to h x =
      let ((e0 , e1) , p) = ciso.fun x
      in λ i → Isoω.to (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i)) (p i)
    Isoω.toω h t₀ t₁ x j =
      let ((e0 , e1) , p) = ciso.fun (x j)
      in {!!}
    Isoω.from h x = ciso.inv (_ , λ i →  Isoω.from (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i)) (x i))
    Isoω.sec h b = {!!}
    Isoω.ret h = {!!}








BoundaryPⁿ'-Boundaryω-Isoω : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' n (Type ℓ)) →
                                Isoω (BoundaryPⁿ' n A) (Boundaryω n (toCType n A))




-- toFromCType-cu : ∀ {ℓ} → ∀ n → (A : T[ CType ℓ n ]) → T[ cu n A ] →  T[ cu n (toCType n (fromCType n A)) ]
-- toFromCType-cu zero A x = x
-- toFromCType-cu (suc n) A x = {!!}






CylΣ-squashedTy : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
                     (c0 : CubePⁿ' n ((Cubeⁿ'-elim n) A i0)) →
                     (c1 : CubePⁿ' n ((Cubeⁿ'-elim n) A i1)) → 
                     Type ℓ
CylΣ-squashedTy n A c0 c1 = BoundaryPⁿ' n (PathCu n A c0 c1)

Cylω-squashedTy : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
                     (c0 : CubePⁿ' n ((Cubeⁿ'-elim n) A i0)) →
                     (c1 : CubePⁿ' n ((Cubeⁿ'-elim n) A i1)) → 
                     ωType
Cylω-squashedTy n A c0 c1 = Boundaryω n (toCType n (PathCu n A c0 c1))


CylΣ-squash : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
                     (c0 : CubePⁿ' n ((Cubeⁿ'-elim n) A i0)) →
                     (c1 : CubePⁿ' n ((Cubeⁿ'-elim n) A i1)) →
                     (PathP (λ i → BoundaryPⁿ' n (Cubeⁿ'-elim n A i))
                                    (cubeBdP' n _ c0) 
                                    (cubeBdP' n _ c1))
                     → CylΣ-squashedTy n A c0 c1
CylΣ-squash = {!!}

CylΣ-unsquash : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
                     (c0 : CubePⁿ' n ((Cubeⁿ'-elim n) A i0)) →
                     (c1 : CubePⁿ' n ((Cubeⁿ'-elim n) A i1)) →
                     CylΣ-squashedTy n A c0 c1 → 
                     (PathP (λ i → BoundaryPⁿ' n (Cubeⁿ'-elim n A i))
                                    (cubeBdP' n _ c0) 
                                    (cubeBdP' n _ c1))
                     
CylΣ-unsquash = {!!}



mkCylEndsΣ : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
                     (c0 : CubePⁿ' n ((Cubeⁿ'-elim n) A i0)) →
                     (c1 : CubePⁿ' n ((Cubeⁿ'-elim n) A i1)) →
                T[ Partialⁿ (suc n) (↑Expr 1 (boundaryExpr n) ∧ⁿ (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) (toCType (suc n) A) ]
mkCylEndsΣ = {!!}

CylωΣ : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
                     (c0 : CubePⁿ' n ((Cubeⁿ'-elim n) A i0)) →
                     (c1 : CubePⁿ' n ((Cubeⁿ'-elim n) A i1)) →
                     ωType 
CylωΣ n A c0 c1 = Partialⁿ-Sub (suc n) {A = toCType (suc n) A}
                        {i = ↑Expr 1 (boundaryExpr n)}
                        {j = (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)}
                        (mkCylEndsΣ n A c0 c1) 

Cylω-squash : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
                     (c0 : CubePⁿ' n ((Cubeⁿ'-elim n) A i0)) →
                     (c1 : CubePⁿ' n ((Cubeⁿ'-elim n) A i1)) →
                     T[ CylωΣ n A c0 c1 ]
                     → T[ Cylω-squashedTy n A c0 c1 ] 
Cylω-squash = {!!}


Cylω-unsquash : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
                     (c0 : CubePⁿ' n ((Cubeⁿ'-elim n) A i0)) →
                     (c1 : CubePⁿ' n ((Cubeⁿ'-elim n) A i1)) →
                     T[ Cylω-squashedTy n A c0 c1 ]
                     → T[ CylωΣ n A c0 c1 ] 
Cylω-unsquash = {!!}

fromωCyl : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
                     (c0 : CubePⁿ' n ((Cubeⁿ'-elim n) A i0)) →
                     (c1 : CubePⁿ' n ((Cubeⁿ'-elim n) A i1)) →
                     T[ CylωΣ n A c0 c1 ]
                     → T[ Boundaryω (suc n) (toCType (suc n) A) ]
fromωCyl = {!!}

toωCyl : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
                     (bdω : T[ Boundaryω (suc n) (toCType (suc n) A) ]) →
                     T[ CylωΣ n A
                          (Isoω.from (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i0)) (Boundaryω-getLid n false (toCType (suc n) A) bdω))
                          (Isoω.from (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i1)) (Boundaryω-getLid n true (toCType (suc n) A) bdω)) ]

toωCyl = {!!}


BoundaryPⁿ'-Boundaryω-Isoω zero A =
  record { to = λ x ()
         ; toω = λ t₀ t₁ x ()
         ; from = λ x → _
         ; sec = λ b → refl
         ; ret = λ a () }


BoundaryPⁿ'-Boundaryω-Isoω (suc n) A = h

  where


   
    module bIso = Iso (BoundaryPⁿ'-elim-iso n A) 

    h : Isoω (BoundaryPⁿ' (suc n) A)
          (Boundaryω (suc n) (toCType (suc n) A))
    Isoω.to h bd =
      let ((e0 , e1) , cy) = bIso.fun bd
          w = Isoω.to (BoundaryPⁿ'-Boundaryω-Isoω n _) (CylΣ-squash n A e0 e1 cy)

      in fromωCyl n A e0 e1 (Cylω-unsquash n A e0 e1 w)       
    
    Isoω.toω h bd = {!!}
      
    Isoω.from h bdω =
      let c0 = (Isoω.from (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i0)) (Boundaryω-getLid n false (toCType (suc n) A) bdω))
          c1 = (Isoω.from (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i1)) (Boundaryω-getLid n true (toCType (suc n) A) bdω))

          z = Cylω-squash n A
                    c0 c1
                 ((toωCyl n A bdω))
          w = Isoω.from (BoundaryPⁿ'-Boundaryω-Isoω n _) z
      in bIso.inv ((c0 , c1) ,
           CylΣ-unsquash n A
             c0
             c1
             w)

    
    Isoω.sec h = {!!}
    Isoω.ret h = {!!}


