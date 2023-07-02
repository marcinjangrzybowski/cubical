{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.BaseAssoc5More where

import Cubical.Data.Nat.Base as ℕ
import Cubical.Data.Nat.Properties as ℕprops


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution

open import Cubical.Foundations.Everything
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive
-- open import Cubical.Data.Nat.Order.RecursiveMoreEquiv

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group

open import Cubical.Algebra.SymmetricGroup

import Cubical.Functions.Logic as L

open import Cubical.Functions.Embedding

open import Cubical.Data.List as Li

import Cubical.Data.Nat.FinGenAut2 as A

import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Implicit

open import Cubical.HITs.SequentialColimit as SC

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)


open import Cubical.Relation.Binary

-- import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint

import Cubical.HITs.Permutation.Base as B

open import Cubical.HITs.Permutation.BaseAssoc5

private
  variable
    ℓ : Level
    A : Type ℓ


𝕡·invol : ∀ {n m} → (x : ℙrmₐ {true} n)
         (y : ℙrmₐ {true} m)
         (s : +-sym n m ≡ sym (+-sym m n)) → 
     SquareP (λ j i → ℙrmₐ {true}
            (s j i))
       (𝕡·-comm x y)
       (symP (𝕡·-comm y x))
       (λ _ → 𝕡· x y)
       λ _ → 𝕡· y x
𝕡·invol = ℙrmElimProp₂.f₂ w
 where
 open AB
 open ℙrmElimProp₂
 w : ℙrmElimProp₂ λ {n m} (x : ℙrmₐ {true} n)
         (y : ℙrmₐ {true} m) →
         (s : +-sym n m ≡ sym (+-sym m n)) →
     SquareP (λ j i → ℙrmₐ {true}
            (s j i))
       (𝕡·-comm x y)
       (symP (𝕡·-comm y x))
       (λ _ → 𝕡· x y)
       λ _ → 𝕡· y x
 asquash₂ w _ _ = isPropΠ λ _ →
   isOfHLevelPathP' 1
    (isOfHLevelPathP' 2 (𝕡squash _) _ _) _ _
 abase₂ w {n} {m} s i j = 
  𝕡invol
    (𝕒𝕓 nothing n m nothing 
       (isSet→isSet' isSetℕₐ⁺¹
         (λ j' → +-sym n m (j' ∧ j))
         (λ j' → +-sym m n (~ j ∨ ~ j'))
         (λ _ → n + m)
         (λ i → s i j) i))

    (𝕒𝕓 nothing m n nothing
      (isSet→isSet' isSetℕₐ⁺¹
         (λ j' → +-sym n m (j ∨ ~ j'))
         (λ j' → +-sym m n (~ j ∧ j'))
         (λ _ → m + n)
         (λ i → s i j) i))

    (refl , (refl , refl , refl)) i j


lenFCSG⊥ : FCSG⊤ → ℕₐ⁺¹
lenFCSG⊥ = RecSetFCSG.f w
 where
 w : RecSetFCSG ℕₐ⁺¹
 RecSetFCSG.asquash w = isSetℕₐ⁺¹
 RecSetFCSG.●a w = one
 RecSetFCSG.·a w = _+_
 RecSetFCSG.·a-assoc w = +-assoc
 RecSetFCSG.·a-comm w = +-sym
 RecSetFCSG.·a-hexDiag w a b c =
    (sym (+-assoc _ _ _)) ∙∙ +-sym _ _ ∙∙ sym (+-assoc _ _ _)
 RecSetFCSG.·a-pentagon-diag w a b c d =
    cong (_+ d) (sym (+-assoc _ _ _))
      ∙∙ sym (+-assoc _ _ _) ∙∙ cong (a +_) (sym (+-assoc _ _ _))
   -- sym (+-assoc _ _ _) ∙ sym (+-assoc _ _ _)
  
-- -- j = i0 ⊢ (+-assoc n m o i)
-- -- j = i1 ⊢ (+-assoc m o n (~ i))
-- -- i = i0 ⊢ (+-sym n (m + o) j)
-- -- i = i1 ⊢ (hcomp
-- --           (doubleComp-faces (+-sym (n + m) o) (+-sym (o + n) m) j)
-- --           (+-assoc o n m j))
-- -- —————————————————————————————

-- fromFCSG-hexup : ∀ {n} {m} {o} → 
--  (a : ℙrmₐ n)
--  (b : ℙrmₐ m)
--  (c : ℙrmₐ o)
--  → (s : Square (+-sym n (m + o))
--              ((+-sym (n + m) o)  ∙∙ +-assoc _ _ _ ∙∙ (+-sym (o + n) m))
--               (+-assoc n m o) (sym (+-assoc m o n)))
--  →
--   SquareP (λ i j → ℙrmₐ {true} (s i j))
--       (𝕡·-comm a (𝕡· b c))
--       (λ i →
--          comp
--          (λ k →
--             ℙrmₐ {true}
--             (doubleCompPath-filler
--              (+-sym (n + m) (o))
--              (+-assoc (o) (n) (m))
--              (+-sym (o + n) (m)) k i))
--          (λ { k (i = i0) → 𝕡·-comm (𝕡· a b) c (~ k)
--             ; k (i = i1) → 𝕡·-comm (𝕡· c a) b k
--             })
--          (𝕡·-assoc c a b i))
--       (𝕡·-assoc a b c) (symP (𝕡·-assoc b c a))
-- fromFCSG-hexup {n} {m} {o} = ℙrmElimProp₃.f₃ w
--  where

--  zz : (a : ℙrmₐ n)
--       (b : ℙrmₐ m)
--       (c : ℙrmₐ o)
--        → (s : Square (+-sym n (m + o))
--              ((+-sym (n + m) o)  ∙∙ +-assoc _ _ _ ∙∙ (+-sym (o + n) m))
--               (+-assoc n m o) (sym (+-assoc m o n)))
--        → SquareP (λ j i → ℙrmₐ {true}
--             (doubleCompPath-filler
--              (+-sym (n + m) (o))
--              (+-assoc (o) (n) (m))
--              (+-sym (o + n) (m)) j i))
         
--          (λ i → 𝕡·-assoc c a b i)
--          (λ i →
--          comp
--          (λ k →
--             ℙrmₐ {true}
--             (doubleCompPath-filler
--              (+-sym (n + m) (o))
--              (+-assoc (o) (n) (m))
--              (+-sym (o + n) (m)) k i))
--          (λ { k (i = i0) → 𝕡·-comm (𝕡· a b) c (~ k)
--             ; k (i = i1) → 𝕡·-comm (𝕡· c a) b k
--             })
--          (𝕡·-assoc c a b i))
--          (λ j → 𝕡·-comm (𝕡· a b) c (~ j))
--          (λ j → 𝕡·-comm (𝕡· c a) b j)
--  zz a b c s j i = 
--          fill
--          (λ k →
--             ℙrmₐ {true}
--             (doubleCompPath-filler
--              (+-sym (n + m) (o))
--              (+-assoc (o) (n) (m))
--              (+-sym (o + n) (m)) k i))
--          (λ { k (i = i0) → 𝕡·-comm (𝕡· a b) c (~ k)
--             ; k (i = i1) → 𝕡·-comm (𝕡· c a) b k
--             })
--          (inS (𝕡·-assoc c a b i)) j

--  w : ℙrmElimProp₃ λ {n} {m} {o} (a : ℙrmₐ n) (b : ℙrmₐ m) (c : ℙrmₐ o)
--              → (s : Square (+-sym n (m + o))
--                         ((+-sym (n + m) o)  ∙∙ +-assoc _ _ _ ∙∙ (+-sym (o + n) m))
--                          (+-assoc n m o) (sym (+-assoc m o n)))
--             →
--              SquareP (λ i j → ℙrmₐ {true} (s i j))
--                  (𝕡·-comm a (𝕡· b c))
--                  (λ i →
--                     comp
--                     (λ k →
--                        ℙrmₐ {true}
--                        (doubleCompPath-filler
--                         (+-sym (n + m) (o))
--                         (+-assoc (o) (n) (m))
--                         (+-sym (o + n) (m)) k i))
--                     (λ { k (i = i0) → 𝕡·-comm (𝕡· a b) c (~ k)
--                        ; k (i = i1) → 𝕡·-comm (𝕡· c a) b k
--                        })
--                     (𝕡·-assoc c a b i))
--                  (𝕡·-assoc a b c) (symP (𝕡·-assoc b c a))
--  ℙrmElimProp₃.asquash₃ w _ _ _ = isPropΠ λ _ →
--   {!!}
--  ℙrmElimProp₃.abase₃ w _ =
--    {!!} ◁ {!!} ▷ {!!}


-- ∀ l c r →
--       ((l · c) · r) ≡ (c · (r · l))

-- 𝕡·-hexDiag : ∀ {n m o} → (l : ℙrmₐ {true} n)
--          (c : ℙrmₐ {true} m)
--          (r : ℙrmₐ {true} o) →
--          (p : n + m + o ≡ m + (o + n)) → 
--      PathP (λ i → ℙrmₐ {true} (p i))
--        (𝕡· (𝕡· l c) r)
--        (𝕡· c (𝕡· r l))
-- 𝕡·-hexDiag =  ℙrmElimSet₃.f₃ w
--  where
--  open ℙrmElimSet₃
--  open AB
--  w : ℙrmElimSet₃ λ {n m o} (l : ℙrmₐ {true} n)
--          (c : ℙrmₐ {true} m)
--          (r : ℙrmₐ {true} o) →
--          (p : n + m + o ≡ m + (o + n)) → 
--      PathP (λ i → ℙrmₐ {true} (p i))
--        (𝕡· (𝕡· l c) r)
--        (𝕡· c (𝕡· r l))
--  asquash₃ w _ _ _ =
--    isSetΠ λ _ → isOfHLevelPathP' 2 (𝕡squash _) _ _ 
--  abase₃ w _ _ = 𝕡base
--  aloopₙ w = {!!}
--  aloopₘ w = {!!}
--  aloopₒ w = {!!}
 
--  asquash₃ w _ _ _ =
--   isOfHLevelPathP' 2 (𝕡squash _) _ _ 
--  abase₃ w _ = 𝕡base
--  aloopₙ w ab = flipSquareP (congP (λ _ → 𝕡loop)
--    (congP₂ (λ _ → 𝕒𝕓 (lPad ab) (l ab) (r ab))
--          (cong just +-+ₐ≡ₐ+-+')
--            (isSet→SquareP (λ _ _ → isSetℕₐ⁺¹)
--             _ _ _ _)))
   

--  aloopₘ  w {n} {m} {o} ab =
--    flipSquareP (congP (λ _ → 𝕡loop)
--      (congP (λ _ → 𝕒𝕓 (just (n ₐ+ lPad ab)) (l ab) (r ab)
--              (just (rPad ab +ₐ o)))
--        (isSet→SquareP (λ _ _ → isSetℕₐ⁺¹)
--             _ _ _ _)))
--  aloopₒ w {n} {m} {o} ab = flipSquareP (congP (λ _ → 𝕡loop)
--     (congP₂ (λ i x → 𝕒𝕓 {n = +-assoc n m o i} x (l ab) (r ab)
--              (rPad ab))
--              (cong just +-ₐ+≡ₐ+-+')
--        (isSet→SquareP (λ _ _ → isSetℕₐ⁺¹)
--             _ _ _ _)))


fromFCSG : ∀ x → ℙrmₐ {true} (lenFCSG⊥ x)
fromFCSG = ElimFCSG.f w
 where
 w : ElimFCSG (λ z → ℙrmₐ (lenFCSG⊥ z))
 ElimFCSG.asquash w _ = 𝕡squash _
 ElimFCSG.●a w = 𝕡base
 ElimFCSG.·a w x y = 𝕡· x y
 ElimFCSG.·a-assoc w x y z = 𝕡·-assoc x y z
 ElimFCSG.·a-comm w x y = 𝕡·-comm x y
 ElimFCSG.·a-comminvol w x y = 𝕡·invol x y _
 ElimFCSG.·a-hexDiag w {n} {m} {o} a b c i =
   comp (λ k → ℙrmₐ {true} (
              (doubleCompPath-filler
                 (sym (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m) (lenFCSG⊥ o)))
                 (+-sym (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o))
                 (sym (+-assoc _ _ _))
                 k i)))
        (λ k → λ { (i = i0) → 𝕡·-assoc a b c k
                 ; (i = i1) → 𝕡·-assoc b c a (~ k)
               })
        (𝕡·-comm a (𝕡· b c) i)

 ElimFCSG.·a-hex-up w {n} {m} {o} a b c j i =
   comp (λ k →  ℙrmₐ {true}
                (isGroupoid→isGroupoid' (isSet→isGroupoid isSetℕₐ⁺¹)
                 (λ _ i → +-sym (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o) i)
                 (λ j i → (lenFCSG⊥ (·-hex-up n m o j i)))
                 (λ k i → (+-sym (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o) i))
                 (λ k i → (doubleCompPath-filler
                             (sym (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m) (lenFCSG⊥ o)))
                             (+-sym (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o))
                             (sym (+-assoc _ _ _))
                             k i))
                 (λ k j → +-assoc (lenFCSG⊥ n) (lenFCSG⊥ m) (lenFCSG⊥ o) (k ∧ j))
                 (λ k j → +-assoc (lenFCSG⊥ m) (lenFCSG⊥ o) (lenFCSG⊥ n) (~ k ∨ ~ j)) k j i)
                 )
      (λ k → λ { (i = i0) → 𝕡·-assoc a b c (k ∧ j)
                 ; (i = i1) → 𝕡·-assoc b c a (~ k ∨ ~ j)
                 ; (j = i0) → (𝕡·-comm a (𝕡· b c) i)
                 })
     (𝕡·-comm a (𝕡· b c) i)
             
 ElimFCSG.·a-hex-down w {n} {m} {o} a b c = {!!}


 ElimFCSG.·a-pentagon-diag w {n} {m} {o} {p}  xs ys zs ws i = 
      comp (λ k → ℙrmₐ {true} (
              (doubleCompPath-filler
                 (cong (_+ (lenFCSG⊥ p)) (sym (+-assoc _ (lenFCSG⊥ m) (lenFCSG⊥ o))))
                 (sym (+-assoc _ _ _))
                 (cong ((lenFCSG⊥ n) +_) (sym (+-assoc _ _ _))) k i)))
        (λ k → λ { (i = i0) → 𝕡· (𝕡·-assoc xs ys zs k) ws 
                 ; (i = i1) → 𝕡· xs (𝕡·-assoc ys zs ws (~ k))
               })
        (𝕡·-assoc xs (𝕡· ys zs) ws (~ i))

 ElimFCSG.·a-pentagon-△ w = {!!}


 ElimFCSG.·a-pentagon-□ w {n} {m} {o} {p} xs ys zs ws j i =
     comp (λ k → ℙrmₐ {true}
        (isGroupoid→isGroupoid' (isSet→isGroupoid isSetℕₐ⁺¹)
            (λ j i → (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o)
                    (lenFCSG⊥ p) (~ i)))
            (λ j i → (lenFCSG⊥ (·-pentagon-□ n m o p j i)))
            (doubleCompPath-filler _ _ _)
            (λ k i → (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o)
                 (lenFCSG⊥ p) (~ i)))
            (λ k j → (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m) (lenFCSG⊥ o) (k ∧ ~ j)
                     + lenFCSG⊥ p))
            (λ k j → (lenFCSG⊥ n +
                      +-assoc (lenFCSG⊥ m) (lenFCSG⊥ o) (lenFCSG⊥ p) (~ k ∨ j)))
            k j i))
        (λ k → λ { (i = i0) → 𝕡· (𝕡·-assoc xs ys zs (k ∧ ~ j)) ws 
                 ; (i = i1) → 𝕡· xs (𝕡·-assoc ys zs ws (~ k ∨ j))
                 ; (j = i1) → 𝕡·-assoc xs (𝕡· ys zs) ws (~ i)
               })
        (𝕡·-assoc xs (𝕡· ys zs) ws (~ i))


repℕ : ℕ.ℕ → FCSG⊤
repℕ ℕ.zero = ●
repℕ (ℕ.suc x) = ● · repℕ x

repFCSG : (x : ℕₐ⁺¹) → singl (repℕ (ℕ.predℕ (ℕₐ⁺¹→ℕ x)))
repFCSG = ℕₐ⁺¹elim.f w
 where
 w : ℕₐ⁺¹elim (λ z → singl (repℕ (ℕ.predℕ (ℕₐ⁺¹→ℕ z))))
 ℕₐ⁺¹elim.aOne w = _ , refl
 (w ℕₐ⁺¹elim.a+ x) x₁ =
  (fst x · fst x₁) ,
    {!!} ∙ cong₂ _·_ (snd x) (snd x₁)
 ℕₐ⁺¹elim.a-assoc w = {!!}
 ℕₐ⁺¹elim.a-sym w = {!!}
 ℕₐ⁺¹elim.asquash w = {!!}
