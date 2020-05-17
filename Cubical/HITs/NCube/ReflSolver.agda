{-# OPTIONS --cubical  #-}
module Cubical.HITs.NCube.ReflSolver where


open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≟_ to _≟Nat_)
open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum as Sum

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
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint


open import Cubical.HITs.NCube.IntervalPrim
-- open import Cubical.HITs.NCube.Cub

open import Cubical.HITs.NCube.BaseVec
open import Cubical.HITs.NCube.CompN

open import Cubical.HITs.NCube.Refl
open import Cubical.HITs.NCube.ReflN
open import Cubical.HITs.NCube.Cub


run : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n m} → (a : A) → Refl n m → InsConst a n
run a (rfl _) = insRefl a _
run a (cmp x x₁) = hcompReflCut a (run a ∘ x) (run a x₁)

makeGridR : ∀ n m → Refl n m
makeGridR n zero = rfl _
makeGridR n (suc m) = cmp (const (makeGridR n m)) ((makeGridR n m))


makeGrid : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ n → ℕ → (a : A) → InsConst a n
makeGrid n m a = run a ((makeGridR n m))


makeGridTest0 : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
               → makeGrid 1 0 a ≡ refl
makeGridTest0 a = refl

makeGridTest1 : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
               → makeGrid 1 1 a ≡ ((refl {x = a} ∙∙ refl {x = a} ∙∙ refl {x = a}))
makeGridTest1 a = refl


makeGridTest2 : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
               → makeGrid 1 2 a ≡  
                    (refl {x = a} ∙∙ refl {x = a} ∙∙ refl {x = a})
                 ∙∙ (refl {x = a} ∙∙ refl {x = a} ∙∙ refl {x = a})
                 ∙∙ (refl {x = a} ∙∙ refl {x = a} ∙∙ refl {x = a})
makeGridTest2 a = refl

solve-refl :  ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
         → ∀ {n m}
         → (x : Refl n m)
         → insRefl a n ≡ run a x 
solve-refl a (rfl _) = refl
solve-refl a (cmp x x₁) =
  reflFill a ∙ λ i → hcompReflCut a ( (λ y → (solve-refl a y i)) ∘ x) (solve-refl a x₁ i)


solve-Ins :  ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
         → ∀ {n m}
         → (x : Refl n m)
         → Ins a n 
solve-Ins a x = (run a x) , (solve-refl a x)

Grid-solve :   ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
         → ∀ n m
         → insRefl a n ≡ makeGrid n m a 
Grid-solve a n m = solve-refl a (makeGridR n m)

-- Grid-solve-Test0 : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
--                → Grid-solve a 1 1 ≡  
--                     (compPath-filler refl refl)
                 
-- Grid-solve-Test0 a i i₁ i₂ = {!!}


Grid-solve-Test : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
               → refl ≡  
                    (refl {x = a} ∙∙ refl {x = a} ∙∙ refl {x = a})
                 ∙∙ (refl {x = a} ∙∙ refl {x = a} ∙∙ refl {x = a})
                 ∙∙ (refl {x = a} ∙∙ refl {x = a} ∙∙ refl {x = a})
Grid-solve-Test a = Grid-solve a 1 2


partial-test : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
               → Square (makeGrid 1 1 a) ((makeGrid 1 1 a)) ((makeGrid 1 1 a)) ((makeGrid 1 1 a))
partial-test a i i₁ = fillReflBdCut 2 a sides (insRefl a 2) i1 i i₁  

  where
   sides : Bool × Fin 2 → Ins a (predℕ 2)
   sides (fst₁ , snd₁) = solve-Ins a (makeGridR 1 1)


partial-test2-man : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
                → Cube (insRefl a 2)
                       (λ i₁ i₂ →
                              hcomp
                              (λ k → λ {                                
                                 (i₁ = i0) → a 
                               ; (i₂ = i0) → a
                               ; (i₁ = i1)(i₂ = i1) → a 
                              })
                              a
                       )
                       (insRefl a 2)
                       (reflFill a)
                       (insRefl a 2)
                       ((reflFill a))
partial-test2-man a i₀ i₁ i₂ = 
   hcomp {φ = (~ (i₀ ∧ i₁ ∧ i₂)) ∨ (i₁ ∧ i₂) } (λ _ _ → a) a

hc : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A) → I → A
hc a φ = hcomp {φ = φ} (λ _ _ → a) a 

ptest3 : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A) →
            Iⁿ→ A 2
ptest3 a i i₁ i₀ =
   hcomp {φ = i₁ ∨ i₀}
     (λ l → λ {
       (i₀ = i1) → hc a (~ i₁ ∨ ~ l ∨ (i₁ ∧ i))
     ; (i₁ = i1) → hc a (~ i₀ ∨ ~ l ∨ (i₀ ∧ i))
     ; (i₁ = i1)(i₀ = i1) → hc a (~ l ∨ i)
     })
     a


ptest3ai0 : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A) →
           Square (λ i → hc a (i)) (λ i → hc a (~ i)) (λ i → hc a (i)) (λ i → hc a (~ i))
ptest3ai0 a i₀ i₁ = ptest3 a i0 i₀ i₁

ptest3ai1 : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A) →
           Square (λ i → hc a (i)) (λ i → hc a (~ i ∨ i)) (λ i → hc a (i)) (λ i → hc a (~ i ∨ i))
ptest3ai1 a i₀ i₁ = ptest3 a i1 i₀ i₁

ptest4 : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A) →
            Iⁿ→ A 2
ptest4 a i i₁ i₀ =
   hcomp {φ = i₁ ∨ i₀}
     (λ l → λ {
       (i₀ = i1) → hc a (~ i₁ ∨ ~ l ∨ i₁ ∨ l)
     ; (i₁ = i1) → hc a (~ i₀ ∨ ~ l ∨ i₀ ∨ l)
     
     })
     a


-- partial-test2 : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
--                 → Cube (insRefl a 2)
--                        (λ i₁ i₂ →
--                               hcomp
--                               (λ k → λ {                                
--                                  (i₁ = i0) → a 
--                                ; (i₂ = i0) → a
--                                ; (i₁ = i1)(i₂ = i1) → a 
--                               })
--                               a
--                        )
--                        (insRefl a 2)
--                        (reflFill a) --(Grid-solve a 1 1)
--                        (insRefl a 2)
--                        ((reflFill a)) --(Grid-solve a 1 1)
-- partial-test2 a i₀ i₁ i₂ = (fillReflBdCut 3 a sides (insRefl a 3) i1) i₀ i₁ i₂
-- -- insideOf (Cu←I 2 (fillReflBdCut 3 a sides (insRefl a 3) i1))  

--   where

--    si12-sides : Bool × Fin 2 → Ins a 1
--    si12-sides (true , zero , _) = _ , λ i  → (reflFill a {n = 1}) i
--    si12-sides (fst₁ , _ , _) = insRefl a 1 , refl

--    si12 : Ins a 2
--    si12 = _ , λ i i₃ i₄ → {!fillReflBdCut 2 a si12-sides (insRefl a 2) i i₃ i₄!}


--    si0 : Ins a 2
--    si0 = {!!}

--    sides : Bool × Fin 3 → Ins a (predℕ 3)
--    sides (false , k , _) = (insRefl a 2) , refl
--    sides (true , zero , _) = si0
--    sides (true , suc k , _) = {!!} --si12




-- parBouCylΣ : ∀ {ℓ} → ∀ {A  : Type ℓ} → (a : A)
--             → ∀ n → PartialBoundary n
--             → Σ (NBoundary n → A)
--              (λ bd → Σ ((const a) ≡ bd)
--                 λ x → Σ _ (PathP (λ i → InsideOf (x i)) (reflⁿ n a)))
-- fst (parBouCylΣ a zero x) ()
-- fst (snd (parBouCylΣ a zero x)) i ()
-- fst (snd (snd (parBouCylΣ a zero x))) = a
-- snd (snd (snd (parBouCylΣ a zero x))) = refl

-- parBouCylΣ a (1) x = {!!}
-- parBouCylΣ a (2) x = {!!}
-- parBouCylΣ a (3) x = {!!}
-- parBouCylΣ a (4) x = {!!}

-- fst (parBouCylΣ a 5 x) = {!!}

-- fst (snd (parBouCylΣ a 5 x)) i = {!!}

-- fst (snd (snd (parBouCylΣ a 5 x))) = {!!}
-- snd (snd (snd (parBouCylΣ a 5 x))) = {!!}

-- parBouCylΣ a (suc (suc (suc (suc (suc (suc n)))))) x = {!!}
