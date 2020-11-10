{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.IntervalPrimMore where


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

open import Cubical.HITs.Interval hiding (end)
open import Cubical.HITs.PropositionalTruncation renaming (map to mapₚ)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 hiding (_*_)
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
import Cubical.Foundations.Logic as Lo

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.IntervalPrim


-- test : T[ Boundaryω 4 Ct[ 4 , const Type₀ ] ]
-- test = {!paⁿ 4 {Ct[ 4 , const Type₀ ]} {boundaryExpr 4}!}

-- Partialⁿ-pathApp : ∀ {ℓ} → ∀ n → {e : Ie n}
--                → {A : NCube n → Type ℓ}
--                → {x0 : ∀ c → (CType-ev n (A i0) c)}
--                → {x1 : ∀ c → (CType-ev n (A i1) c)}
--                → T[ Partialⁿ n e
--                     (Ct[ n , (λ c → PathP (λ i → CType-ev (suc n) A (inside i ∷ c) ) (x0 c) (x1 c)) ]) ]
--                -- → ∀ i → T[ Partialⁿ n e Ct[ n , (λ c → CType-ev (suc n) A (inside i ∷ c)) ] ]
--                → ∀ i → T[ Partialⁿ n e {!A i∷!} ]
-- Partialⁿ-pathApp = {!!}

Partialⁿ-pathApp : ∀ {ℓ} → ∀ n → {e : Ie n}
               → {A : NCube (suc n) → Type ℓ}
               → {x0 : Π (A i∷ i0)}
               → {x1 : Π (A i∷ i1)}
               → T[ Partialⁿ n e
                    (Ct[ n , (λ c → PathP (λ i → (A i∷ i) c ) (x0 c) (x1 c)) ]) ]
               → ∀ i → T[ Partialⁿ n e Ct[ n , A i∷ i ] ]
Partialⁿ-pathApp zero x i 1=1 = x 1=1 i
Partialⁿ-pathApp (suc n) {A = A} x i i₁ = Partialⁿ-pathApp n {A = λ x₁ → A (head x₁ ∷ inside i₁ ∷ tail x₁)} (x i₁) i

Partialⁿ-mapInsPathP : ∀ {ℓ} → ∀ n → {e : Ie n}
               → {A : NCube (suc n) → Type ℓ}
               → {B : NCube (suc n) → Type ℓ}
               → {x0 : Π (A i∷ i0)}
               → {x1 : Π (A i∷ i1)}
               → (f : ∀ c → A c → B c)
               → T[ Partialⁿ n e
                    (Ct[ n , (λ c → PathP (λ i → (A i∷ i) c ) (x0 c) (x1 c)) ]) ]
               → T[ Partialⁿ n e
                    (Ct[ n , (λ c → PathP (λ i → (B i∷ i) c ) (f (end false ∷ c) (x0 c)) (f (end true ∷ c) (x1 c))) ]) ]
Partialⁿ-mapInsPathP n f = Partialⁿ-map→ n (paⁿ n cu→[ n , (λ c x i → f (inside i ∷ c) (x i)) ])


CIso : ∀ {ℓ} → ∀ {n} → (A : NCube n → Type ℓ) → Isoω (NCube' A)  (cu n Ct[ n , A ])
BIso : ∀ {ℓ} → ∀ {n} → (A : NCube n → Type ℓ) → Isoω (Boundary A)  (Boundaryω n Ct[ n , A ])


cubSub : ∀ {ℓ} → ∀ {n} → (A : NCube n → Type ℓ) → (cu : NCube' A)
               → T[ Subⁿ n (boundaryExpr n) (Isoω.to (BIso A) (fst cu)) ]


-- BIso-hlp : ∀ {ℓ} → ∀ {n} → (A : NCube (suc n) → Type ℓ) →
--           ∀ si →
--            T[ Subⁿ (suc n) (boundaryExpr (suc n))
--               (paⁿ (suc n) {e = boundaryExpr (suc n)}
--                      (Isoω.to (CIso {n = suc n} A) si)) ]
--           →
--            T[ Subⁿ (suc n) (boundaryExpr (suc n))
--                      (Isoω.to (BIso {n = suc n} A) (fst si)) ]

Isoω.to (CIso {n = zero} A) x x₁ = snd x
Isoω.to (CIso {n = suc zero} A) x i 1=1 = snd x i
Isoω.to (CIso {n = suc (suc n)} A) x i = Isoω.to (CIso {n = suc n} _)  (snd x i)

Isoω.from (CIso {n = zero} A) x = _ , x 1=1
fst (Isoω.from (CIso {n = suc n} A) x) = Isoω.from (BIso {n = suc n} A) (paⁿ (suc n) x)
snd (Isoω.from (CIso {n = suc zero} A) x) i = x i 1=1
snd (Isoω.from (CIso {n = suc (suc n)} A) x) i =
  hcomp
    (λ j → primPOr i (~ i)
         (λ p → Isoω.from (CIso {n = suc n} (A i∷ i)) {!x!})
         (λ p → Isoω.from (CIso {n = suc n} (A i∷ i)) {!!}))
    (Isoω.from (CIso {n = suc n} (A i∷ i)) (x i))
  -- λ i → {! Isoω.from (CIso {n = suc n} (A i∷ i1)) (x i1) !}

-- Partialⁿ-i1-elim n (⊆I→⊆'I (suc n) _ (paⁿ (suc (suc n)) x i1) i₁)

-- x i1 i₁ 



-- Isoω.from (CIso {n = suc n} (A i∷ i1)) (x i1)

-- ?3 (i = i1)
--   = Isoω.from (CIso (λ x₁ → A (end true ∷ x₁)))
--     (λ i₁ → Partialⁿ-i1-elim n (⊆I→⊆'I n _ (paⁿ n (x i1 i₁))))
--   : Σ (Boundary (λ x₁ → A (end true ∷ x₁))) InsideOf
-- ?3 (i = i0)
--   = Isoω.from (CIso (λ x₁ → A (end false ∷ x₁)))
--     (λ i₁ → Partialⁿ-i1-elim n (⊆I→⊆'I n _ (paⁿ n (x i0 i₁))))
--   : Σ (Boundary (λ x₁ → A (end false ∷ x₁))) InsideOf

Isoω.sec (CIso {n = n} A) = {! !}

Isoω.ret (CIso {n = n} A) = {!!}

Isoω.to (BIso {n = zero} A) x ()
Isoω.to (BIso {n = suc zero} A) x i = z
  where
    z : _
    z (i = i1) = side true x
    z (i = i0) = side false x
    
Isoω.to (BIso {n = suc (suc n)} A) ((side0@(bd0 , ins0)  ,p side1@(bd1 , ins1)) , snd₁) =
   (Partialⁿ-attach-Ends (suc n) {e = boundaryExpr (suc n)}
     (λ j i → Isoω.to (BIso {n = suc n} (A i∷ j)) (snd₁ j) i)
     (cubSub _ side0) (cubSub _ side1)
     -- (BIso-hlp {n = n} (A i∷ i0) side0 (inSⁿ (suc n) (boundaryExpr (suc n)) (Isoω.to (CIso {n = suc n} (A i∷ i0)) side0 )))
     -- (BIso-hlp {n = n} (A i∷ i1) side1 (inSⁿ (suc n) (boundaryExpr (suc n)) (Isoω.to (CIso {n = suc n} (A i∷ i1)) side1 )))
     )
  -- where
  --   si0 : T[ Subⁿ (suc n) (boundaryExpr (suc n))
  --             (paⁿ (suc n) {e = boundaryExpr (suc n)}
  --                    (Isoω.to (CIso (A i∷ i0)) side0)) ] 
  --   si0 = inSⁿ (suc n) (boundaryExpr (suc n)) (Isoω.to (CIso {n = suc n} (A i∷ i0)) side0 )

  --   -- sii0' : T[ Subⁿ (suc n) (boundaryExpr (suc n))
  --   --                  {!!} ]
  --   -- sii0' = {!(Isoω.to (BIso {n = suc n} (A i∷ i0)) bd0 )!}


  --   sii0 : T[ Subⁿ (suc n) (boundaryExpr (suc n))
  --                    (Isoω.to (BIso (A i∷ i0)) bd0) ]
  --   sii0 = cubSub {!!} side0


Isoω.from (BIso {n = zero} A) x = _
Isoω.from (BIso {n = suc zero} A) x = x i0 1=1 ,p x i1 1=1
Isoω.from (BIso {n = suc (suc n)} A) x =
      (Isoω.from (CIso (A b∷ false)) (Boundaryω-getLid (suc n) false _ x)
      ,p
      Isoω.from (CIso (A b∷ true)) (Boundaryω-getLid (suc n) true _ x)) ,
      qq

  where

     bcyl : T[ Boundaryω (suc n)
                (λ z →
                    Ct[ suc n , (λ c → PathP (λ i → (CType-ev (suc (suc n)) Ct[ suc (suc n) , A ] i∷ i) c)
                       (from-cu
                        (Boundaryω-getLid (suc n) false
                         (λ z₁ i₁ → Ct[ suc (suc n) , A ] z₁ i₁) x)
                        c)
                       (from-cu
                        (Boundaryω-getLid (suc n) true
                         (λ z₁ i₁ → Ct[ suc (suc n) , A ] z₁ i₁) x)
                        c))
                    ]
                    z) ]
     bcyl = (Boundaryω-getCyl (suc n) x)

     zzz : (i : I) → T[ Boundaryω (suc n) Ct[ suc n , A i∷ i ] ]
     zzz = ((Partialⁿ-pathApp (suc n)
                 {A = A}
                 {x0 = λ c → 
                     CType-ev-elim (suc n) {A i∷ i0} c
                     ((from-cu (Boundaryω-getLid (suc n) false (λ z i₁ → Ct[ suc (suc n) , A ] z i₁) x)) c)
                     }
                 {x1 = λ c → 
                     CType-ev-elim (suc n) {A i∷ i1} c
                     ((from-cu (Boundaryω-getLid (suc n) true (λ z i₁ → Ct[ suc (suc n) , A ] z i₁) x)) c)}
                               (Partialⁿ-mapInsPathP
                                 (suc n)
                                   {x0 =
                               λ c → ((from-cu (Boundaryω-getLid (suc n) false (λ z i₁ → Ct[ suc (suc n) , A ] z i₁) x)) c)}
                                   {x1 =
                               λ c → ((from-cu (Boundaryω-getLid (suc n) true (λ z i₁ → Ct[ suc (suc n) , A ] z i₁) x)) c)}
                                 (CType-ev-elim (suc (suc n)) {A = A}) bcyl )

--                 ((Boundaryω-getCyl (suc n) x))
                                        ))

     zzzz : PathP (λ i → Boundary (A i∷ i))
              (Isoω.from (BIso (A i∷ i0)) (zzz i0))
              (Isoω.from (BIso (A i∷ i1)) (zzz i1))
     zzzz = λ i → (Isoω.from (BIso (A i∷ i)) (zzz i))


     qq : PathP (λ i → Boundary (λ x₁ → A (inside i ∷ x₁)))
             (Isoω.from (BIso (A i∷ i0))
              (λ i → paⁿ n (Partialⁿ-i1-elim n (⊆I→⊆'I n _ (x i0 i)))))
             (Isoω.from (BIso (A i∷ i1))
              (λ i → paⁿ n (Partialⁿ-i1-elim n (⊆I→⊆'I n _ (x i1 i)))))
     qq i = hcomp
          (λ j → λ {
           (i = i0) → {!!}
        ;  (i = i1) → {!!}
          })
        (zzzz i)

         

    
Isoω.sec (BIso A) = {!!}

Isoω.ret (BIso A) = {!!}


-- BIso-hlp {n = zero} A si x = x
-- BIso-hlp {n = suc n} A si x i = ?

Subⁿ-attach-Ends :  ∀ {ℓ} → ∀ n → {A : T[ CType ℓ (suc n) ]} → {e : Ie n}
                      → (y : (j : I) → T[ Partialⁿ n e (A j) ])
                      → (x0 : T[ Subⁿ n e (y i0) ])
                      → (x1 : T[ Subⁿ n e (y i1) ])
                      → T[ Subⁿ (suc n)
                             ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ ↑Expr 1 e)
                              (Partialⁿ-attach-Ends n y x0 x1) ]
Subⁿ-attach-Ends = {!!}

cubSub {n = zero} A x = inS (snd x)
cubSub {n = suc zero} A x i = inS (snd x i)
cubSub {n = suc (suc zero)} A x i j = {!!}
cubSub {n = suc (suc n@(suc m) )} A ((sd0 , sd1) , snd₁) = 
 let sb : ∀ i → T[
             Subⁿ (suc n) (boundaryExpr (suc n))
                (Isoω.to (BIso (A i∷ i)) (fst (snd₁ i)))
             ]
     sb i = cubSub {n = suc n} (A i∷ i) (snd₁ i)

     sbb : T[
             Subⁿ (suc (suc n)) (↑Expr 1 (boundaryExpr (suc n)))
                (λ i → (Isoω.to (BIso (A i∷ i)) (fst (snd₁ i))))
             ]
     sbb i = cubSub {n = suc n} (A i∷ i) (snd₁ i)

     sbb' : T[
             Subⁿ (suc (suc n)) (↑Expr 1 (boundaryExpr (suc n)))
                (λ i → (Isoω.to (BIso (A i∷ i)) (sd1 i)))
             ]
     sbb' i = cubSub {n = suc n} (A i∷ i) ((sd1 i) , {! (snd₁ i)!})


     scc : {!!}
     scc = {!!}

     gl : 
      T[
      Subⁿ (suc (suc n))
        (((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ ↑Expr 1 (boundaryExpr (suc n))))
      (Partialⁿ-attach-Ends (suc n)
       (λ i → Isoω.to (BIso (A i∷ i)) (sd1 i))
       (cubSub (A i∷ i0 )
        (Pair.side0 sd0))
       (cubSub (A i∷ i1 )
        (Pair.side1 sd0))
       )
      ]
     gl = {!!}

 in gl




-- cubSub {n = suc (suc n)} A x =
--       Subⁿ-attach-Ends (suc n) {A = Ct[ suc (suc n) , A ]} {e = boundaryExpr (suc n)}
--         -- (λ j → Isoω.to (BIso (A i∷ j)) (snd (fst x) j))
--         -- (cubSub (A b∷ false)
--         --   (fst (Pair.side0 (fst (fst x))) , snd (Pair.side0 (fst (fst x)))))
--         -- (cubSub (A b∷ true)
--         --   (fst (Pair.side1 (fst (fst x))) , snd (Pair.side1 (fst (fst x))))) 
