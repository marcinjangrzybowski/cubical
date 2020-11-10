{-# OPTIONS --cubical --safe  #-}
module Cubical.HITs.NCube.SigmaHelp where


import Agda.Primitive.Cubical

open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat renaming (elim to ℕ-elim)
open import Cubical.Data.Nat.Order

open import Cubical.Data.Vec
open import Cubical.Data.Fin renaming (elim to Fin-elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum

open import Cubical.HITs.Interval
open import Cubical.HITs.PropositionalTruncation renaming (map to mapₚ)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 hiding (_*_)
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
import Cubical.Functions.Logic as Lo

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.IntervalPrim

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying
open import Cubical.Data.Sigma.Nested.Path

variable
  ℓ : Level



-- record BdHlp {i : I} {n : ℕ} {A : Type ℓ} : Typeω where
--   field
--     s0 s1 : T[ Boundaryω n (Cu[ n , A ]) ]
--     bb : T[ Partialⁿ-Sub (suc n) {A = Cu[ suc n , A ]}
--                  (⊆'2-∧ (↑Expr 1 (boundaryExpr n)) (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)
--                    ({!!}))  ]


hlp-cu-Cu : ∀ {ℓ} → ∀ n → {A : Type ℓ} → T[ cu n Cu[ n , A ] ] →  T[ Cu A n ]
hlp-cu-Cu zero x = x
hlp-cu-Cu (suc n) x i = hlp-cu-Cu n (x i)

hlp-Cu-cu : ∀ {ℓ} → ∀ n → {A : Type ℓ} →  T[ Cu A n ] → T[ cu n Cu[ n , A ] ]
hlp-Cu-cu zero x = x
hlp-Cu-cu (suc n) x i = hlp-Cu-cu n (x i)



-- Partialⁿ-~i-∨-i  :  ∀ {ℓ}  → ∀ n → {A : T[ CType ℓ n ]}
--               → (i j : Ie n)
--               → (∩a : T[ Partialⁿ n (i ∧ⁿ j) A ])
--               → T[ Partialⁿ-Sub n ∩a ]
--               → T[ Partialⁿ-Sub n (⊆I→⊆'I n (∧-comm j i) ∩a) ]
--               → T[ Partialⁿ n (i ∨ⁿ j) A ]
-- Partialⁿ-~i-∨-i = ?

Partialⁿ-Cyl-Sub : ∀ {ℓ} → ∀ n → {e :  Ie n} → {A : T[ CType ℓ (suc n) ]}
                   → (a : T[ Partialⁿ (suc n) ((λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) ∨ⁿ ↑Expr 1 e) A ])
                   → T[ Partialⁿ-Sub {ℓ} (suc n) {A} {i = ((λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) ∨ⁿ ↑Expr 1 e)}
                                                 {j = ((λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) ∧ⁿ ↑Expr 1 e)}
                           ({!!})   ]
--                           Ct[ n ,
--                              (λ c → PathP (λ i → ((CType-ev (suc n) A) i∷ i) c)
--                                      (from-cu (Partialⁿ-getLid n _ false A a) c)
--                                      (from-cu (Partialⁿ-getLid n _ true A a) c))
--                              ] ]
Partialⁿ-Cyl-Sub = {!!}






Partialⁿ-pathApp-out : ∀ {ℓ ℓb} → ∀ n → {e : Ie n}
               → {A : T[ CType ℓ (suc n) ]} → {B : Type ℓb} 
               → ∀ {x0 : T[ cu n (A i0) ]} → ∀ {x1 : T[ cu n (A i1) ]}
               → T[ Partialⁿ n e (cu-PathP n A x0 x1) ]
               → (fOut : ∀ i → T[ Partialⁿ n e (A i) ] → B)                              
               → (fOut i0 (paⁿ n x0)) ≡ (fOut i1 (paⁿ n x1))

Partialⁿ-pathApp-out zero x fOut i =  fOut i λ j → x j i
Partialⁿ-pathApp-out (suc n) x fOut = {!!}


-- sidesPath-Cu : ∀ {ℓ} → ∀ n → {e :  Ie n} → {A : Type ℓ}
--                    → (a : T[ Partialⁿ (suc n) ((λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) ∨ⁿ ↑Expr 1 e) ( Cu[ suc n , A ]) ])
--                    → T[ Partialⁿ {ℓ} n e
--                           (Cu-≡ n
--                             (Partialⁿ-getLid-Cu n e false A a)
--                             (Partialⁿ-getLid-Cu n e true A a)) ]
-- sidesPath-Cu zero {e = e} a e=1 i = a i (IsOne2 (i ∨ ~ i) e e=1)
-- sidesPath-Cu (suc zero) a i = sidesPath-Cu zero λ i₁ → a i₁ i
-- sidesPath-Cu (suc (suc n)) a i = {! sidesPath! (suc n) λ i₁ → a i₁ i!}


-- Boundaryω-getCyl-Cu : ∀ {ℓ} → ∀ n
--           → {A : Type ℓ}
--           → (x : T[ Boundaryω (suc n) (Cu A n) ])
--           → T[ Boundaryω n
--                  Ct[ n , (λ c →   Cu-app (Boundaryω-getLid' n false A x) c
--                                 ≡ Cu-app (Boundaryω-getLid' n true A x) c ) ]
--                  ]
-- Boundaryω-getCyl-Cu zero x ()
-- Boundaryω-getCyl-Cu (suc n) x = sidesPath' (suc n) x



Boundaryω-getCyl : ∀ {ℓ} → ∀ n
          → {A : T[ CType ℓ (suc n) ]}
          → (x : T[ Boundaryω (suc n) A ])
          → T[ Boundaryω n
               (cu-PathP n A
                 (Boundaryω-getLid n false A x)
                 (Boundaryω-getLid n true A x)) ]
Boundaryω-getCyl zero x ()
Boundaryω-getCyl (suc n) x = sidesPath (suc n) x



Partialⁿ-attach-Ends-Cu :  ∀ {ℓ} → ∀ n → {A : Type ℓ } → {e : Ie n}
                      → (y : (j : I) → T[ Partialⁿ n e (Cu[ n , A ]) ])
                      → (end0 : T[ Subⁿ n _ (y i0) ])
                      → (end1 : T[ Subⁿ n _ (y i1) ])
                      → T[ Partialⁿ (suc n)
                                 ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ ↑Expr 1 e)
                                 Cu[ suc n , A ] ]
Partialⁿ-attach-Ends-Cu = {!!}



Boundaryω-attach-Ends-Cu :  ∀ {ℓ} → ∀ n → {A : Type ℓ } 
                      → (y : (j : I) → T[ Boundaryω n (Cu[ n , A ]) ])
                      → (end0 : T[ Subⁿ n _ (y i0) ])
                      → (end1 : T[ Subⁿ n _ (y i1) ])
                      → T[ Boundaryω (suc n) Cu[ suc n , A ] ]
Boundaryω-attach-Ends-Cu = {!!}

-- Partialⁿ-pathApp-Cu : ∀ {ℓ} → ∀ n → {e : Ie n}
--                → {A : Type ℓ}
--                → ∀ {x0 x1 : T[ Cu A n ]}
--                → T[ Partialⁿ n e (Cu-≡ n x0 x1)  ]
--                → ∀ (i : I) → T[ Partialⁿ n e Cu[ n , A ] ]
-- Partialⁿ-pathApp-Cu = {!!}


-- Partialⁿ-pathApp-Cu-out : ∀ {ℓ} → ∀ n → {e : Ie n}
--                → {A B : Type ℓ}
--                → ∀ {x0 x1 : T[ Cu A n ]}
--                → T[ Partialⁿ n e (Cu-≡ n x0 x1)  ]
--                → (fOut : T[ Partialⁿ n e Cu[ n , A ] ] → B)
--                → fOut (paⁿ-Cu n x0) ≡ fOut (paⁿ-Cu n x1) 
-- Partialⁿ-pathApp-Cu-out = {!!}


-- Partialⁿ-attach-Ends zero {e = e} y end0 end1 i = zzz
--  where
--    zzz : _
--    zzz (i = i0) = outS end0
--    zzz (i = i1) = outS end1
--    zzz (e = i1) = y i 1=1

-- Partialⁿ-attach-Ends (suc zero) {A = A} {e = e} y end0 end1 i i₁ =
--   Partialⁿ-attach-Ends (zero) {A = λ x → A x i₁} {e = e i₁}
--                      (λ j x → y j i₁ x) (end0 i₁) ((end1 i₁)) i
-- Partialⁿ-attach-Ends (suc (suc n)) {A = A} {e = e} y end0 end1 i i₁ =
--   Partialⁿ-attach-Ends (suc n) {A = λ x → A x i₁} {e = λ x → e i₁ x}
--                      (λ x → y x i₁) (λ x → end0 i₁ x) (λ x → end1 i₁ x) i



iso-NCube : ∀ {n} → ∀ {A : Type ℓ}
              → Iso
                (NCube (suc n) → A)
                ((Σ[ (x₀ , x₁) ∈ (NCube n → A) × (NCube n → A) ] x₀ ≡ x₁))

(Iso.fun (iso-NCube {n = n}) x) = (_ , _) , (λ i → x i∷ i)
Iso.inv (iso-NCube {n = n}) ((_ , _) , snd₁) (x ∷ x₁) = Iapp= snd₁ x x₁
Iso.rightInv (iso-NCube {n = n}) b = refl

Iso.leftInv (iso-NCube {n = n}) a i (end false ∷ x₁) =  a (end false ∷ x₁)
Iso.leftInv (iso-NCube {n = n}) a i (end true ∷ x₁) = a (end true ∷ x₁)
Iso.leftInv (iso-NCube {n = n}) a i (inside i₁ ∷ x₁) = a (inside i₁ ∷ x₁)



IsoCub' : {A : Type ℓ} → ∀ n → Iso (NCube n → A ) (Cubeⁿ' n A)

Iso.fun (IsoCub' 0) x = x []
Iso.inv (IsoCub' 0) x _ = x
Iso.rightInv (IsoCub' 0) b = refl
Iso.leftInv (IsoCub' 0) a i [] = a []

IsoCub' {A = A} (suc n) = 
      _ Iso⟨ iso-NCube  ⟩
      _ Iso⟨ equivToIso
              (cong≃ (λ T → (Σ[ (x₀ , x₁) ∈ T × T ] x₀ ≡ x₁)) (isoToEquiv (IsoCub' {A = A} n)))  ⟩
      _ Iso⟨ invIso (Cube'-elim-iso n) ⟩ _ ∎Iso



-- IsoCub* : {A : Type ℓ} → ∀ n → Iso (NCube n → A ) (Cubeⁿ* n A)

-- Iso.fun (IsoCub* 0) x = x []
-- Iso.inv (IsoCub* 0) x _ = x
-- Iso.rightInv (IsoCub* 0) b = refl
-- Iso.leftInv (IsoCub* 0) a i [] = a []

-- IsoCub* {A = A} (suc n) =
--       _ Iso⟨ iso-NCube  ⟩
--       _ Iso⟨ equivToIso
--               (cong≃ (λ T → (Σ[ (x₀ , x₁) ∈ T × T ] x₀ ≡ x₁)) (isoToEquiv (IsoCub* {A = A} n)))  ⟩
--       _ Iso⟨ invIso (Cube*-elim-iso n)  ⟩ _ ∎Iso




Isoω-CubeΣ-Cubeω : ∀ {ℓ} → {A : Type ℓ}
                      → ∀ n → Isoω (Cubeⁿ' n A) (Cu A n)

Isoω.to (Isoω-CubeΣ-Cubeω zero) x _ = x
Isoω.toω (Isoω-CubeΣ-Cubeω zero) t₀ t₁ x _ i = lowerω (λ _ → x i) 
Isoω.from (Isoω-CubeΣ-Cubeω zero) x = x 1=1
-- Isoω.fromω (Isoω-CubeΣ-Cubeω zero) t₀ t₁ p = p 1=1
Isoω.sec (Isoω-CubeΣ-Cubeω zero) b = refl
Isoω.ret (Isoω-CubeΣ-Cubeω zero) a _ = refl

Isoω-CubeΣ-Cubeω {A = A} (suc n) = Isoω.precomp ww (Cube'-elim-iso n)

   where

     module prev = Isoω (Isoω-CubeΣ-Cubeω {A = A} n)

     ww : Isoω (Σ (Cubeⁿ' n _ × Cubeⁿ' n _) (λ a → fst a ≡ snd a))
               (Cu _ (suc n))

     Isoω.to ww x i = prev.to (snd x i) 
     Isoω.toω ww t₀ t₁ x i = prev.toω (snd t₀ i) (snd t₁ i) λ j → snd (x j) i 
     Isoω.from ww x = _ , (λ i → prev.from (x i))
     -- Isoω.fromω ww t₀ t₁ p i = ({!prev.fromω _ _ (p i)!} , {!!}) , λ j → prev.from ({!p i!})
     Isoω.sec ww ((e0 , e1) , p) i = ((prev.sec e0 i) , prev.sec e1 i) , λ j → prev.sec (p j) i
     Isoω.ret ww a i = prev.ret (a i)



-- module Isoω-CubeΣ-Cubeω-test (A : Type₀) where

--    n : ℕ
--    n = 5   

--    open Isoω (Isoω-CubeΣ-Cubeω {A = A} n)


--    Test-to : (Cubeⁿ' n A) → Unit
--    Test-to x = {!to x!}
   
--    Test-from : (T[ Cu A n ]) → Unit
--    Test-from x = {!from x!} 



-- Boundaryω-getCylω : ∀ {ℓ} → ∀ n 
--           → {A : Type ℓ}
--           → (x : T[ Boundaryω (suc n) Cu[ suc n , A ] ])
--           → ωType._≡ω_ ( Boundaryω n Cu[ n , A ] )
--                          (paⁿ n (Boundaryω-getLid n false Cu[ suc n , A ] x) )
--                          (paⁿ n (Boundaryω-getLid n true Cu[ suc n , A ] x) )

-- Boundaryω-getCylω n x = {!!}


Isoω-BoundaryΣ-Boundaryω : ∀ {ℓ} → {A : Type ℓ}
                      → ∀ n → Isoω (Boundaryⁿ' n A) (Boundaryω n Cu[ n , A ])
                                                              

Boundaryω-getCyl-lem : ∀ {ℓ} → ∀ n
          → {A : Type ℓ}
          → (x : T[ Boundaryω (suc n) (Cu[ suc n , A ]) ])
          → cubeBd' n A (Isoω.from (Isoω-CubeΣ-Cubeω n) (Boundaryω-getLid' n false A x)) ≡
            cubeBd' n A (Isoω.from (Isoω-CubeΣ-Cubeω n) (Boundaryω-getLid' n true A x))



Isoω.to (Isoω-BoundaryΣ-Boundaryω zero) x ()
Isoω.toω (Isoω-BoundaryΣ-Boundaryω zero) t₀ t₁ x () i
Isoω.from (Isoω-BoundaryΣ-Boundaryω zero) x = lift tt
Isoω.sec (Isoω-BoundaryΣ-Boundaryω zero) b = refl
Isoω.ret (Isoω-BoundaryΣ-Boundaryω zero) a () i

Isoω-BoundaryΣ-Boundaryω {A = A} (suc n) = Isoω.precomp ww (Boundary'-elim-iso n)

  where

    module CuIso = Isoω (Isoω-CubeΣ-Cubeω {A = A} n)
    module prev = Isoω (Isoω-BoundaryΣ-Boundaryω {A = A} n)

    ww : Isoω
           (Σ (Cubeⁿ' n _ × Cubeⁿ' n _)
            (λ a → cubeBd' n _ (fst a) ≡ cubeBd' n _ (snd a)))
           (Boundaryω (suc n) Cu[ suc n , A ])
    Isoω.to ww ((e0 , e1) , cyl) =
       Boundaryω-attach-Ends-Cu n
          (λ j → prev.to (cyl j))
           {!!}
           {!!}
    Isoω.toω ww = {!!}
    Isoω.from ww x =
        (CuIso.from (hlp-cu-Cu n (Boundaryω-getLid n false _ x)) , --Boundaryω-getLid' n false {!!} x
          CuIso.from (hlp-cu-Cu n (Boundaryω-getLid n true _ x))) , {!!}
          
           -- ({!!} ∙∙ (Partialⁿ-pathApp-out n (Boundaryω-getCyl n x) λ _ → prev.from) ∙∙ {!!} )
    -- Isoω.fromω ww x = {!!}
    Isoω.sec ww = {!!}
    Isoω.ret ww = {!!}

-- Boundaryω-getCyl-lem = {!!}

Boundaryω-getCyl-lem zero x = refl
Boundaryω-getCyl-lem (suc n) {A} x i = outS zz

  where

    zz : Sub (Boundaryⁿ' (suc n) A) (~ i ∨ i) (primPOr (~ i) i
               (λ p → cubeBd' (suc n) A
                         (Isoω.from (Isoω-CubeΣ-Cubeω (suc n))
                           (Boundaryω-getLid' (suc n) false A x)))
                λ p → cubeBd' (suc n) A
                         (Isoω.from (Isoω-CubeΣ-Cubeω (suc n))
                           (Boundaryω-getLid' (suc n) true A x))
               )
    zz = {!!}


    zzz : T[ Partialⁿ-Sub (suc n) {A = Cu[ suc n , A ]} {boundaryExpr (suc n)} { (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) }
                                  (λ i → {!!}) ]
    zzz = {!!}


-- dropLastΣᵣ (NCubeSig' (suc n) A)
-- (Isoω.from (Isoω-CubeΣ-Cubeω (suc n))
--  (Boundaryω-getLid' (suc n) true A x))
--   = ?11 (i = i1)
--   : NestedΣᵣ (dropLast (NCubeSig' (suc n) A))
-- dropLastΣᵣ (NCubeSig' (suc n) A)
-- (Isoω.from (Isoω-CubeΣ-Cubeω (suc n))
--  (Boundaryω-getLid' (suc n) false A x))
--   = ?11 (i = i0)
--   : NestedΣᵣ (dropLast (NCubeSig' (suc n) A))

-- Boundaryω-getCyl-lem (suc n) x =
--       sym p0 ∙∙
--         (λ i →  Isoω.from (Isoω-BoundaryΣ-Boundaryω (suc n))
--                  {!(Partialⁿ-pathApp (suc n) ? i)!})
--       ∙∙ p1
--   where

--     p0 : {!!}
--     p0 = {!!}

--     p1 : {!!}
--     p1 = {!!}
