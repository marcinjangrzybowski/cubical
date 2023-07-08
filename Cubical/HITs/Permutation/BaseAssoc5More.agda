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


open import Cubical.Data.Nat.Order.Recursive as CDNOR
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


fromFCSG : FCSG⊤ → Σ _ (ℙrmₐ {true})
fromFCSG = RecFCSG.f w
 where
 open RecFCSG
 w : RecFCSG (Σ ℕₐ⁺¹ ℙrmₐ)
 asquash w = isGroupoidΣ (isSet→isGroupoid isSetℕₐ⁺¹)
                       λ _ → 𝕡squash _
 ●a w = one , 𝕡base
 fst (·a w (p , P) (q , Q)) = p + q
 snd (·a w (p , P) (q , Q)) = 𝕡· P Q
 fst (·a-assoc w (a , _) (b , _) (c , _) i) =
    +-assoc a b c i
 snd (·a-assoc w (a , A) (b , B) (c , C) i) =
    𝕡·-assoc A B C i
 fst (·a-comm w (a , _) (b , _) i) = +-sym a b i
 snd (·a-comm w (a , A) (b , B) i) = 𝕡·-comm A B i
 fst (·a-comminvol w a b i i₁) = _
 snd (·a-comminvol w (_ , A) (_ , B) j i) =
    𝕡·invol A B (isSetℕₐ⁺¹ _ _ _ _) j i
 ·a-hexDiag w (a , A) (b , B) (c , C) =
   ΣPathP (_ , symP (𝕡·-assoc A B C))
    ∙∙ ΣPathP (_ , (𝕡·-comm A (𝕡· B C))) ∙∙
   ΣPathP (_ , symP (𝕡·-assoc B C A))
 ·a-pentagon-diag w (a , A) (b , B) (c , C) (d , D) =
    ΣPathP (_ , symP (congP (λ i x → 𝕡· x D) (𝕡·-assoc A B C)))
    ∙∙ ΣPathP (_ , symP (𝕡·-assoc A (𝕡· B C) D)) ∙∙
   ΣPathP (_ , symP (congP (λ i → 𝕡· A) (𝕡·-assoc B C D)))
 ·a-hex-up w _ _ _ = doubleCompPath-filler _ _ _
 ·a-hex-down w = {!!}

 ·a-pentagon-△ w = {!!}
 ·a-pentagon-□ w _ _ _ _ = symP (doubleCompPath-filler _ _ _)





repℕ : ℕ.ℕ → FCSG⊤
repℕ ℕ.zero = ●
repℕ (ℕ.suc x) = ● · repℕ x

repℕ+ : ∀ n m → 0 < n → 0 < m → repℕ (ℕ.predℕ (n ℕ.+ m)) ≡
      repℕ (ℕ.predℕ n) · repℕ (ℕ.predℕ m)
repℕ+ (ℕ.suc ℕ.zero) (ℕ.suc m) x x₁ = refl
repℕ+ (ℕ.suc (ℕ.suc n)) (ℕ.suc m) x x₁ =
  cong (● ·_) (repℕ+ (ℕ.suc n) (ℕ.suc m) _ _) ∙  (·-assoc _ _ _)

-- repFCSG : (x : ℕₐ⁺¹) → singl (repℕ (ℕ.predℕ (ℕₐ⁺¹→ℕ x)))
-- repFCSG = ℕₐ⁺¹elim.f w
--  where
--  w : ℕₐ⁺¹elim (λ z → singl (repℕ (ℕ.predℕ (ℕₐ⁺¹→ℕ z))))
--  ℕₐ⁺¹elim.aOne w = _ , refl
--  (w ℕₐ⁺¹elim.a+ x) x₁ =
--   (fst x · fst x₁) ,
--     {!!} ∙ cong₂ _·_ (snd x) (snd x₁)
--  ℕₐ⁺¹elim.a-assoc w = {!!}
--  ℕₐ⁺¹elim.a-sym w = {!!}
--  ℕₐ⁺¹elim.asquash w = {!!}

<+ : ∀ n m → 0 < n → 0 < m → 0 < (n ℕ.+ m)
<+ (ℕ.suc n) (ℕ.suc m) x x₁ = tt

0<ℕₐ⁺¹→ℕ : ∀ x → 0 < ℕₐ⁺¹→ℕ x
0<ℕₐ⁺¹→ℕ = ℕₐ⁺¹elimProp.f w
 where
 w : ℕₐ⁺¹elimProp (λ z → 0 < ℕₐ⁺¹→ℕ z)
 ℕₐ⁺¹elimProp.aOne w = tt
 ℕₐ⁺¹elimProp._a+_ w {n} {m} = <+ (ℕₐ⁺¹→ℕ n) (ℕₐ⁺¹→ℕ m)
 ℕₐ⁺¹elimProp.asquash w x = CDNOR.isProp≤ {1} {ℕₐ⁺¹→ℕ x}

repFCSGSingl : (x : ℕₐ⁺¹) → singl (repℕ (ℕ.predℕ (ℕₐ⁺¹→ℕ x)))
repFCSGSingl = ℕₐ⁺¹elimProp.f w
 where
 w : ℕₐ⁺¹elimProp (λ z → singl (repℕ (ℕ.predℕ (ℕₐ⁺¹→ℕ z))))
 ℕₐ⁺¹elimProp.aOne w = _ , refl
 fst ((w ℕₐ⁺¹elimProp.a+ x) x₁) = fst x · fst x₁
 snd (ℕₐ⁺¹elimProp._a+_ w {n} {m} x x₁) = 
  repℕ+ ((ℕₐ⁺¹→ℕ n)) (ℕₐ⁺¹→ℕ m)
   (0<ℕₐ⁺¹→ℕ n) (0<ℕₐ⁺¹→ℕ m) ∙ cong₂ _·_ (snd x) (snd x₁)
 ℕₐ⁺¹elimProp.asquash w _ = isPropSingl 

repFCSG : ℕₐ⁺¹ → FCSG⊤
repFCSG = fst ∘ repFCSGSingl

¬ABone : ¬ AB one
¬ABone (𝕒𝕓 nothing l r nothing <n) = +≢one _ _ <n
¬ABone (𝕒𝕓 nothing l r (just x) <n) = +≢one _ _ <n
¬ABone (𝕒𝕓 (just x) l r nothing <n) = +≢one _ _ <n
¬ABone (𝕒𝕓 (just x) l r (just x₁) <n) = +≢one _ _ <n


addPadds : ℕₐ → FCSG⊤ → ℕₐ → FCSG⊤
addPadds nothing x₁ nothing = x₁
addPadds nothing x₁ (just x) = x₁ · repFCSG x
addPadds (just x) x₁ nothing = repFCSG x · x₁
addPadds (just x) x₁ (just x₂) = (repFCSG x · x₁) · repFCSG x₂

repFCSG' : ∀ n → (ab : AB n) → FCSG⊤
repFCSG' n (𝕒𝕓 lPad l r rPad <n) =
  addPadds lPad (repFCSG l · repFCSG r) rPad

repFCSG'≡ : ∀ n → (ab : AB n) → repFCSG n ≡ repFCSG' n ab
repFCSG'≡ n (𝕒𝕓 nothing l r nothing <n) = sym (cong repFCSG <n)
repFCSG'≡ n (𝕒𝕓 nothing l r (just x) <n) = sym (cong repFCSG <n)
repFCSG'≡ n (𝕒𝕓 (just x) l r nothing <n) = sym (cong repFCSG <n)
repFCSG'≡ n (𝕒𝕓 (just x) l r (just x₁) <n) = sym (cong repFCSG <n)

-- -- -- ℕₐ⁺¹elim.f w
-- -- --  where
-- -- --  w : ℕₐ⁺¹elim
-- -- --        (λ z →
-- -- --           (ab : AB z) →
-- -- --           repFCSG z ≡
-- -- --           addPadds (AB.lPad ab) (repFCSG (AB.l ab) · repFCSG (AB.r ab))
-- -- --           (AB.rPad ab))
-- -- --  ℕₐ⁺¹elim.asquash w _ = isSetΠ λ _ → trunc _ _
-- -- --  ℕₐ⁺¹elim.aOne w = ⊥.rec ∘ ¬ABone
-- -- --  (w ℕₐ⁺¹elim.a+ x) x₁ ab = {!!}
-- -- --  ℕₐ⁺¹elim.a-assoc w = {!!}
-- -- --  ℕₐ⁺¹elim.a-sym w = {!!}

repFCSG'loop : ∀ n → (ab : AB n) → repFCSG' n ab ≡ repFCSG' n (swapAB ab)
repFCSG'loop n (𝕒𝕓 lPad l r rPad <n) i =
  addPadds lPad (·-comm (repFCSG l) (repFCSG r) i) rPad



repFCSGloop : ∀ n → (ab : AB n) → repFCSG n ≡ repFCSG n
repFCSGloop n ab =
  repFCSG'≡ n ab
   ∙∙ repFCSG'loop n ab ∙∙
   sym (repFCSG'≡ n (swapAB ab))


-- repFCSGloopInvol' : ∀ n (p₀₋ p₁₋ : AB n) (g : involGuard p₀₋ p₁₋) →
--       MaybePath.Cover (AB.lPad p₀₋) (AB.lPad p₁₋) →
--       MaybePath.Cover (AB.rPad p₀₋) (AB.rPad p₁₋) → 
--       SquareP (λ i j → FCSG⊤) (repFCSGloop n p₀₋)
--       (symP (repFCSGloop n p₁₋)) refl refl 
-- repFCSGloopInvol' n ab@(𝕒𝕓 nothing l r nothing <n) ab'@(𝕒𝕓 nothing l₁ r₁ nothing <n₁) g _ _ i =
--   (λ j → repFCSG ((isSet→SquareP (λ _ _ → isSetℕₐ⁺¹)
--                    (sym <n)
--                    (sym (AB.<n (swapAB ab')))
--                    (λ _ → n)
--                    (cong₂ _+_ (fst (snd (snd g))) (fst (snd g)))) i j))
--    ∙∙ (λ i₁ → ·-comminvol (repFCSG ((fst (snd (snd g))) i))
--                           (repFCSG ((fst (snd g)) i)) i i₁) ∙∙
--    (λ j → repFCSG ((isSet→SquareP (λ _ _ → isSetℕₐ⁺¹)
                   
--                    ((AB.<n (swapAB ab)))
--                    (<n₁)
                   
--                    (cong₂ _+_ ((fst (snd g))) (fst (snd (snd g))))
--                    (λ _ → n)) i j))

-- repFCSGloopInvol' n (𝕒𝕓 nothing l r (just x) <n) (𝕒𝕓 nothing l₁ r₁ (just x₁) <n₁) g _ _ = {!!}
-- repFCSGloopInvol' n (𝕒𝕓 (just x) l r nothing <n) (𝕒𝕓 (just x₁) l₁ r₁ nothing <n₁) g _ _ = {!!}
-- repFCSGloopInvol' n (𝕒𝕓 (just x) l r (just x₁) <n) (𝕒𝕓 (just x₂) l₁ r₁ (just x₃) <n₁) g _ _ = {!!}


-- repFCSGloopInvol : ∀ n (p₀₋ p₁₋ : AB n) (g : involGuard p₀₋ p₁₋) →
--       SquareP (λ i j → FCSG⊤) (repFCSGloop n p₀₋)
--       (symP (repFCSGloop n p₁₋)) refl refl 
-- repFCSGloopInvol n p₀₋ p₁₋ g =
--   repFCSGloopInvol' n p₀₋ p₁₋ g
--     (MaybePath.encode _ _ (fst g))
--     (MaybePath.encode _ _  (snd (snd (snd g))))

toFCSG : ∀ n →  (ℙrmₐ {true} n) → FCSG⊤
toFCSG n = ℙrmElim.f (w n)
 where
 w : ∀ n → ℙrmElim n (λ _ → FCSG⊤)
 ℙrmElim.asquash (w n) _ = trunc
 ℙrmElim.abase (w n) = repFCSG n
 ℙrmElim.aloop (w n) = repFCSGloop n
 ℙrmElim.ainvol (w n) = {!!} --repFCSGloopInvol n
 ℙrmElim.ahex (w n) = {!!}
 ℙrmElim.acomm (w n) = {!!}
 ℙrmElim.aover (w n) = {!!}

toFromFCSG : section fromFCSG (uncurry toFCSG)
toFromFCSG b = {!b!}


ret· : ∀ n m N M → uncurry toFCSG ((n + m) , (𝕡· N M)) ≡
      uncurry toFCSG (n , N) · uncurry toFCSG (m , M)
ret· n m = ℙrmElimSet₂.f₂ w
 where
 w : ℙrmElimSet₂ λ {n} {m} N M → toFCSG (n + m) (𝕡· N M) ≡
      toFCSG n N · toFCSG m M
 ℙrmElimSet₂.asquash₂ w _ _ = trunc _ _
 ℙrmElimSet₂.abase₂ w = refl
 ℙrmElimSet₂.aloopₙ w {n = n} {m = m} ab j i =
   hcomp (λ k →
            λ { (i = i1) → toFCSG n (𝕡loop ab (j ∨ (~ k))) · toFCSG m 𝕡base
               ; (j = i0) → {!!}
               ; (j = i1) → repFCSG {!!}
               })
         ( toFCSG (n + m) (𝕡loop (AB+m m ab) (j ∨ i)))
 ℙrmElimSet₂.aloopₘ w = {!!}

-- i = i0 ⊢ toFCSG (n + m) (𝕡· (𝕡loop ab j) 𝕡base)
-- i = i1 ⊢ toFCSG n (𝕡loop ab j) · toFCSG m 𝕡base
-- j = i0 ⊢ toFCSG (n + m) (𝕡· 𝕡base 𝕡base)
-- j = i1 ⊢ toFCSG (n + m) (𝕡· 𝕡base 𝕡base)

fromToFCSG : retract fromFCSG (uncurry toFCSG)
fromToFCSG = ElimSetFCSG.f w
 where
 open ElimSetFCSG
 w : ElimSetFCSG (λ z → uncurry toFCSG (fromFCSG z) ≡ z)
 asquash w x = trunc _ _
 ●a w = refl
 ·a w {n} {m} p q =
   ret· _ _ (snd (fromFCSG n)) (snd (fromFCSG m))
    ∙ cong₂ _·_ p q
 ·a-assoc w = {!!}
 ·a-comm w a b = {!!}
 ·a-hexDiag w = {!!}
 ·a-pentagon-diag w = {!!}


-- fromFCSG = ElimFCSG.f w
--  where
--  w : ElimFCSG (λ z → ℙrmₐ (lenFCSG⊥ z))
--  ElimFCSG.asquash w _ = 𝕡squash _
--  ElimFCSG.●a w = 𝕡base
--  ElimFCSG.·a w x y = 𝕡· x y
--  ElimFCSG.·a-assoc w x y z = 𝕡·-assoc x y z
--  ElimFCSG.·a-comm w x y = 𝕡·-comm x y
--  ElimFCSG.·a-comminvol w x y = 𝕡·invol x y _
--  ElimFCSG.·a-hexDiag w a b c = {!𝕡·-comm!}
--    -- comp (λ k → ℙrmₐ {true} (
--    --            (doubleCompPath-filler
--    --               (sym (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m) (lenFCSG⊥ o)))
--    --               (+-sym (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o))
--    --               (sym (+-assoc _ _ _))
--    --               k i)))
--    --      (λ k → λ { (i = i0) → 𝕡·-assoc a b c k
--    --               ; (i = i1) → 𝕡·-assoc b c a (~ k)
--    --             })
--    --      (𝕡·-comm a (𝕡· b c) i)


-- -- 𝕡·-hexDiag : ∀ {n m o} → (a : ℙrmₐ {true} n)
-- --          (b : ℙrmₐ {true} m)
-- --          (c : ℙrmₐ {true} o) →
-- --       PathP (λ i → ℙrmₐ ({!!})) (𝕡· (𝕡· a b) c)
-- --       (𝕡· b (𝕡· c a))
-- -- 𝕡·-hexDiag = {!!}

-- -- lenFCSG⊥ : FCSG⊤ → ℕₐ⁺¹
-- -- lenFCSG⊥ = RecSetFCSG.f w
-- --  where
-- --  w : RecSetFCSG ℕₐ⁺¹
-- --  RecSetFCSG.asquash w = isSetℕₐ⁺¹
-- --  RecSetFCSG.●a w = one
-- --  RecSetFCSG.·a w = _+_
-- --  RecSetFCSG.·a-assoc w = +-assoc
-- --  RecSetFCSG.·a-comm w = +-sym
-- --  RecSetFCSG.·a-hexDiag w a b c =
-- --     (sym (+-assoc _ _ _)) ∙∙ +-sym _ _ ∙∙ sym (+-assoc _ _ _)
-- --  RecSetFCSG.·a-pentagon-diag w a b c d =
-- --     cong (_+ d) (sym (+-assoc _ _ _))
-- --       ∙∙ sym (+-assoc _ _ _) ∙∙ cong (a +_) (sym (+-assoc _ _ _))
-- --    -- sym (+-assoc _ _ _) ∙ sym (+-assoc _ _ _)
  
-- -- -- j = i0 ⊢ (+-assoc n m o i)
-- -- -- j = i1 ⊢ (+-assoc m o n (~ i))
-- -- -- i = i0 ⊢ (+-sym n (m + o) j)
-- -- -- i = i1 ⊢ (hcomp
-- -- --           (doubleComp-faces (+-sym (n + m) o) (+-sym (o + n) m) j)
-- -- --           (+-assoc o n m j))
-- -- -- —————————————————————————————

-- -- fromFCSG-hexup : ∀ {n} {m} {o} → 
-- --  (a : ℙrmₐ n)
-- --  (b : ℙrmₐ m)
-- --  (c : ℙrmₐ o)
-- --  → (s : Square (+-sym n (m + o))
-- --              ((+-sym (n + m) o)  ∙∙ +-assoc _ _ _ ∙∙ (+-sym (o + n) m))
-- --               (+-assoc n m o) (sym (+-assoc m o n)))
-- --  →
-- --   SquareP (λ i j → ℙrmₐ {true} (s i j))
-- --       (𝕡·-comm a (𝕡· b c))
-- --       (λ i →
-- --          comp
-- --          (λ k →
-- --             ℙrmₐ {true}
-- --             (doubleCompPath-filler
-- --              (+-sym (n + m) (o))
-- --              (+-assoc (o) (n) (m))
-- --              (+-sym (o + n) (m)) k i))
-- --          (λ { k (i = i0) → 𝕡·-comm (𝕡· a b) c (~ k)
-- --             ; k (i = i1) → 𝕡·-comm (𝕡· c a) b k
-- --             })
-- --          (𝕡·-assoc c a b i))
-- --       (𝕡·-assoc a b c) (symP (𝕡·-assoc b c a))
-- -- fromFCSG-hexup {n} {m} {o} = ℙrmElimProp₃.f₃ w
-- --  where

-- --  zz : (a : ℙrmₐ n)
-- --       (b : ℙrmₐ m)
-- --       (c : ℙrmₐ o)
-- --        → (s : Square (+-sym n (m + o))
-- --              ((+-sym (n + m) o)  ∙∙ +-assoc _ _ _ ∙∙ (+-sym (o + n) m))
-- --               (+-assoc n m o) (sym (+-assoc m o n)))
-- --        → SquareP (λ j i → ℙrmₐ {true}
-- --             (doubleCompPath-filler
-- --              (+-sym (n + m) (o))
-- --              (+-assoc (o) (n) (m))
-- --              (+-sym (o + n) (m)) j i))
         
-- --          (λ i → 𝕡·-assoc c a b i)
-- --          (λ i →
-- --          comp
-- --          (λ k →
-- --             ℙrmₐ {true}
-- --             (doubleCompPath-filler
-- --              (+-sym (n + m) (o))
-- --              (+-assoc (o) (n) (m))
-- --              (+-sym (o + n) (m)) k i))
-- --          (λ { k (i = i0) → 𝕡·-comm (𝕡· a b) c (~ k)
-- --             ; k (i = i1) → 𝕡·-comm (𝕡· c a) b k
-- --             })
-- --          (𝕡·-assoc c a b i))
-- --          (λ j → 𝕡·-comm (𝕡· a b) c (~ j))
-- --          (λ j → 𝕡·-comm (𝕡· c a) b j)
-- --  zz a b c s j i = 
-- --          fill
-- --          (λ k →
-- --             ℙrmₐ {true}
-- --             (doubleCompPath-filler
-- --              (+-sym (n + m) (o))
-- --              (+-assoc (o) (n) (m))
-- --              (+-sym (o + n) (m)) k i))
-- --          (λ { k (i = i0) → 𝕡·-comm (𝕡· a b) c (~ k)
-- --             ; k (i = i1) → 𝕡·-comm (𝕡· c a) b k
-- --             })
-- --          (inS (𝕡·-assoc c a b i)) j

-- --  w : ℙrmElimProp₃ λ {n} {m} {o} (a : ℙrmₐ n) (b : ℙrmₐ m) (c : ℙrmₐ o)
-- --              → (s : Square (+-sym n (m + o))
-- --                         ((+-sym (n + m) o)  ∙∙ +-assoc _ _ _ ∙∙ (+-sym (o + n) m))
-- --                          (+-assoc n m o) (sym (+-assoc m o n)))
-- --             →
-- --              SquareP (λ i j → ℙrmₐ {true} (s i j))
-- --                  (𝕡·-comm a (𝕡· b c))
-- --                  (λ i →
-- --                     comp
-- --                     (λ k →
-- --                        ℙrmₐ {true}
-- --                        (doubleCompPath-filler
-- --                         (+-sym (n + m) (o))
-- --                         (+-assoc (o) (n) (m))
-- --                         (+-sym (o + n) (m)) k i))
-- --                     (λ { k (i = i0) → 𝕡·-comm (𝕡· a b) c (~ k)
-- --                        ; k (i = i1) → 𝕡·-comm (𝕡· c a) b k
-- --                        })
-- --                     (𝕡·-assoc c a b i))
-- --                  (𝕡·-assoc a b c) (symP (𝕡·-assoc b c a))
-- --  ℙrmElimProp₃.asquash₃ w _ _ _ = isPropΠ λ _ →
-- --   {!!}
-- --  ℙrmElimProp₃.abase₃ w _ =
-- --    {!!} ◁ {!!} ▷ {!!}


-- -- ∀ l c r →
-- --       ((l · c) · r) ≡ (c · (r · l))

-- -- 𝕡·-hexDiag : ∀ {n m o} → (l : ℙrmₐ {true} n)
-- --          (c : ℙrmₐ {true} m)
-- --          (r : ℙrmₐ {true} o) →
-- --          (p : n + m + o ≡ m + (o + n)) → 
-- --      PathP (λ i → ℙrmₐ {true} (p i))
-- --        (𝕡· (𝕡· l c) r)
-- --        (𝕡· c (𝕡· r l))
-- -- 𝕡·-hexDiag =  ℙrmElimSet₃.f₃ w
-- --  where
-- --  open ℙrmElimSet₃
-- --  open AB
-- --  w : ℙrmElimSet₃ λ {n m o} (l : ℙrmₐ {true} n)
-- --          (c : ℙrmₐ {true} m)
-- --          (r : ℙrmₐ {true} o) →
-- --          (p : n + m + o ≡ m + (o + n)) → 
-- --      PathP (λ i → ℙrmₐ {true} (p i))
-- --        (𝕡· (𝕡· l c) r)
-- --        (𝕡· c (𝕡· r l))
-- --  asquash₃ w _ _ _ =
-- --    isSetΠ λ _ → isOfHLevelPathP' 2 (𝕡squash _) _ _ 
-- --  abase₃ w {n} {m} {o} p i = 𝕡loop {n = p i}
-- --      (𝕒𝕓 nothing n (m + o)
-- --           nothing (+-assoc  _ _ _ ∙ λ i' → p (i' ∧ i))) i
-- --  aloopₙ w ab i p i₁ = {!!}
-- --  aloopₘ w = {!!}
-- --  aloopₒ w = {!!}
 
--  -- asquash₃ w _ _ _ = ?
--  --  -- isOfHLevelPathP' 2 (𝕡squash _) _ _ 
--  -- abase₃ w _ = 𝕡base
--  -- aloopₙ w ab = flipSquareP (congP (λ _ → 𝕡loop)
--  --   (congP₂ (λ _ → 𝕒𝕓 (lPad ab) (l ab) (r ab))
--  --         (cong just +-+ₐ≡ₐ+-+')
--  --           (isSet→SquareP (λ _ _ → isSetℕₐ⁺¹)
--  --            _ _ _ _)))
   

--  -- aloopₘ  w {n} {m} {o} ab =
--  --   flipSquareP (congP (λ _ → 𝕡loop)
--  --     (congP (λ _ → 𝕒𝕓 (just (n ₐ+ lPad ab)) (l ab) (r ab)
--  --             (just (rPad ab +ₐ o)))
--  --       (isSet→SquareP (λ _ _ → isSetℕₐ⁺¹)
--  --            _ _ _ _)))
--  -- aloopₒ w {n} {m} {o} ab = flipSquareP (congP (λ _ → 𝕡loop)
--  --    (congP₂ (λ i x → 𝕒𝕓 {n = +-assoc n m o i} x (l ab) (r ab)
--  --             (rPad ab))
--  --             (cong just +-ₐ+≡ₐ+-+')
--  --       (isSet→SquareP (λ _ _ → isSetℕₐ⁺¹)
--  --            _ _ _ _)))



-- aHexBot : ∀ n m o → SquareP (λ i j → ℙrmₐ {true} (+-sym n (m + o) (j)))
--             (λ i → 𝕡loop
--               (𝕒𝕓 nothing n (m + o) nothing (λ i' → +-sym n (m + o) (i' ∧ i))) i)
--             (λ i →
--                 𝕡loop
--                 (𝕒𝕓 nothing n m (just o)
--                  (λ i₁ →
--                     hcomp
--                     (doubleComp-faces (λ _ → n + m + o)
--                      (λ i' → +-sym n (m + o) (i' ∧ i)) i₁)
--                     (+-assoc n m o (~ i₁))))
--                 i)
--             (λ i → 𝕡base)
--             λ i →
--                 𝕡loop
--                 (𝕒𝕓 (just m) n o nothing
--                  (λ i₁ →
--                     hcomp
--                     (doubleComp-faces
--                      (λ i₂ →
--                         hcomp
--                         (doubleComp-faces (λ _ → m + (n + o)) (λ i₃ → +-sym m n i₃ + o) i₂)
--                         (+-assoc m n o i₂))
--                      (λ i' → +-sym n (m + o) i') i₁)
--                     (+-assoc n m o (~ i₁))))
--                 (~ i)
-- aHexBot n m o = (λ j i → 𝕡hex
--        (𝕒𝕓 nothing n m (just o) (sym (+-assoc _ _ _) ∙ λ i' → +-sym n (m + o) (i' ∧ i)))
--        (𝕒𝕓 nothing n (m + o) nothing λ i' → +-sym n (m + o) (i' ∧ i))
--        (𝕒𝕓 (just m) n o nothing ((+-assoc _ _ _ ∙ cong (_+ o) (+-sym _ _) )
--          ∙∙ sym (+-assoc _ _ _)
--           ∙∙ λ i' → +-sym n (m + o) (i' ∧ i)))
--        (refl , refl , refl , refl , refl ) (~ j) i
--        )


-- -- k = i0 ⊢ λ i₁ →
-- --            hcomp
-- --            (doubleComp-faces
-- --             (λ i₂ →
-- --                hcomp
-- --                (doubleComp-faces (λ _ → m + (n + o)) (λ i₃ → +-sym m n i₃ + o) i₂)
-- --                (+-assoc m n o i₂))
-- --             (λ i' → +-sym n (m + o) i') i₁)
-- --            (+-assoc n m o (~ i₁))

-- aHexDown' : ∀ (n m o : ℕₐ⁺¹') → 
--        Square {A = Σ _  (ℙrmₐ {true})}
--           (ΣPathP ((λ i →
--                        hcomp (doubleComp-faces (λ _ → n + (m + o)) (λ _ → m + o + n) i)
--                        (+-sym n (m + o) i)) , (λ i →
--                                                   fill
--                                                   (λ k →
--                                                      ℙrmₐ {true}
--                                                      (doubleCompPath-filler (λ _ → n + (m + o)) (+-sym n (m + o))
--                                                       (λ _ → m + o + n) k i))
--                                                   (λ { i₁ (i = i0) → 𝕡base ; i₁ (i = i1) → 𝕡base })
--                                                   (inS
--                                                    (𝕡loop
--                                                     (𝕒𝕓 nothing n (m + o) nothing (λ i' → +-sym n (m + o) (i' ∧ i)))
--                                                     i))
--                                                   i1)))
--           -- (ΣPathP ((+-sym n (m + o)) ,
--           --      λ i → 𝕡loop
--           --              (𝕒𝕓 nothing n (m + o) nothing
--           --                (λ i' → +-sym n (m + o) (i' ∧ i))) i) ∙ refl)
--           refl
--           (ΣPathP (+-sym n (m + o) ,
--                    λ i → 𝕡loop (𝕒𝕓 nothing n m (just o)
--                                  (λ i₁ →
--                                     hcomp
--                                     (doubleComp-faces (λ _ → n + m + o)
--                                      (λ i' → +-sym n (m + o) (i' ∧ i)) i₁)
--                                     (+-assoc n m o (~ i₁)))) i))
--           (ΣPathP (refl ,
--              (𝕡loop (𝕒𝕓 (just m) o n nothing (+-assoc m o n)))))
      
-- aHexDown' n m o j i =
--   hcomp
--     (λ k →
--         λ {  (i = i0) →
--                +-sym n (m + o) (j ∧ k) , aHexBot n m o i1 (j ∧ k)
--            ; (i = i1) →
--              m + o + n , (𝕡invol
--                   (𝕒𝕓 (just m) o n nothing (+-assoc _ _ _))
--                   (𝕒𝕓 (just m) n o nothing
--                     ((+-assoc m n o ∙
--                       (λ i₃ → +-sym m n i₃ + o))
--                        ∙∙ sym (+-assoc n m o) ∙∙ +-sym n (m + o)))
--                   (refl , refl , refl , refl) (~ k) j)
--            ; (j = i0) → _ ,
               
--                             fill
--                             (λ k →
--                                ℙrmₐ {true}
--                                (doubleCompPath-filler
--                                 (refl)
--                                 (+-sym n (m + o))
--                                 refl k
--                                 i))
--                             (λ { k (i = i0) → 𝕡base
--                                ; k (i = i1) → 𝕡base
--                                })
--                             (inS (𝕡loop
--               (𝕒𝕓 nothing n (m + o) nothing (λ i' → +-sym n (m + o) (i' ∧ i))) i                  )) k
--            ; (j = i1) → +-sym n (m + o) (i ∨ k) , aHexBot n m o i1 (i ∨ k)
--            })
--     (_ , aHexBot n m o j i)


-- aHexDown : ∀ {n} {m} {o} (l : ℙrmₐ n) (c : ℙrmₐ m)
--       (r : ℙrmₐ o) → (s : Square _ _ _ _ ) → 
--       SquareP (λ i j → ℙrmₐ {true} (s i j))
--       (λ i →
--          comp
--          (λ k →
--             ℙrmₐ {true}
--             (doubleCompPath-filler
--              (λ i₁ → +-assoc n m o (~ i₁))
--              (+-sym n (m +  o))
--              (λ i₁ → +-assoc m o n (~ i₁)) k
--              i))
--          (λ { k (i = i0) → 𝕡·-assoc l c r k
--             ; k (i = i1) → 𝕡·-assoc c r l (~ k)
--             })
--          (𝕡·-comm l (𝕡· c r) i))
--       (symP (𝕡·-assoc c l r)) (congP (λ z x → 𝕡· x r) (𝕡·-comm l c))
--       (congP (λ z y → 𝕡· c y) (𝕡·-comm r l))
-- aHexDown = ℙrmElimProp₃.f₃ w
--  where
--  w : ℙrmElimProp₃ λ {n} {m} {o} (l : ℙrmₐ n) (c : ℙrmₐ m)
--       (r : ℙrmₐ o) → (s : Square _ _ _ _ ) → 
--       SquareP (λ i j → ℙrmₐ {true} (s i j))
--       (λ i →
--          comp
--          (λ k →
--             ℙrmₐ {true}
--             (doubleCompPath-filler
--              (λ i₁ → +-assoc n m o (~ i₁))
--              (+-sym n (m +  o))
--              (λ i₁ → +-assoc m o n (~ i₁)) k
--              i))
--          (λ { k (i = i0) → 𝕡·-assoc l c r k
--             ; k (i = i1) → 𝕡·-assoc c r l (~ k)
--             })
--          (𝕡·-comm l (𝕡· c r) i))
--       (symP (𝕡·-assoc c l r))
--       (congP (λ z x → 𝕡· x r) (𝕡·-comm l c))
--       (congP (λ z y → 𝕡· c y) (𝕡·-comm r l))
--  ℙrmElimProp₃.asquash₃ w _ _ _ = isPropΠ λ _ →
--   isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (𝕡squash _) _ _) _ _
--  ℙrmElimProp₃.abase₃ w {n} {m} {o} s =
--    whiskSq.sq' _
--       (λ j i → 𝕡hex
--        (𝕒𝕓 nothing n m (just o) {!!})
--        (𝕒𝕓 nothing n (m + o) nothing {!!})
--        (𝕒𝕓 (just m) n o nothing {!!})
--        (refl , refl , refl , refl , refl ) (~ j) i
--        )
--       {!!}
--       (λ j i → 𝕡loop (𝕒𝕓 nothing n m (just o) {!!}) (j ∨ i))
--       (λ i i₁ → 𝕡loop
--          (𝕒𝕓 nothing n m (just o) {!!})
--           (i ∧ i₁))
--       λ i i₁ → 𝕡invol
--         (𝕒𝕓 (just m) o n nothing {!!})
--         (𝕒𝕓 (just m) n o nothing {!!})
--         {!!} (~ i₁) i
--    -- CompPSq.cu (λ j i k →
--    --     ℙrmₐ {true}
--    --        (isGroupoid→isGroupoid' (isSet→isGroupoid isSetℕₐ⁺¹)
--    --          -- (λ i k → fst (aHexDown' n m o k i))
--    --          -- s
--    --          -- (λ i k → ({!!} ∙∙ {!!} ∙∙ {!!}) i)
--    --          (λ i k → ({!!} ∙∙ {!!} ∙∙ {!!}) i)
--    --          {!!}
--    --          {!!}
--    --          {!!}
--    --          (congSq fst (aHexDown' n m o))
--    --          s j i k))
--    --   {!!}
--    --   (λ i k → 𝕡base)
--    --   (λ i k → 𝕡loop (𝕒𝕓 nothing n m (just o) {!!}) i)
--    --   (λ i k → 𝕡loop (𝕒𝕓 (just m) o n nothing {!!}) i)
--    --   (congSq' {B = λ x → ℙrmₐ {true} (fst x)} (snd) (aHexDown' n m o))

-- -- j = i0 ⊢ ℙrmₐ (fst (aHexDown' n m o k i))
-- -- j = i1 ⊢ ℙrmₐ (s k i)


-- -- --    let z : Square {A = Σ ℕₐ⁺¹ (ℙrmₐ {true})}
-- -- --               (ΣPathP (
-- -- --                ((λ i → +-assoc n m o (~ i))
-- -- --                 ∙∙ (λ i → +-sym n (m + o) i) ∙∙
-- -- --                 λ i → +-assoc m o n (~ i))
-- -- --                 , (λ i →
-- -- --                         comp
-- -- --                         (λ k →
-- -- --                            ℙrmₐ {true}
-- -- --                            (doubleCompPath-filler
-- -- --                             (λ i₁ → +-assoc n m o (~ i₁))
-- -- --                             (+-sym n (m +  o))
-- -- --                             (λ i₁ → +-assoc m o n (~ i₁)) k
-- -- --                             i))
-- -- --                         (λ { k (i = i0) → 𝕡·-assoc 𝕡base 𝕡base 𝕡base k
-- -- --                            ; k (i = i1) → 𝕡·-assoc 𝕡base 𝕡base 𝕡base (~ k)
-- -- --                            })
-- -- --                         (𝕡·-comm 𝕡base (𝕡· 𝕡base 𝕡base) i))))
-- -- --               (ΣPathP ((λ i → +-assoc m n o (~ i)) ,
-- -- --                   (symP (𝕡·-assoc {n = m} {n} {o} 𝕡base 𝕡base 𝕡base))))
-- -- --               (ΣPathP ((λ i → +-sym n m i + o) ,
-- -- --                  congP (λ z x → 𝕡· x (𝕡base {n = o})) (𝕡·-comm 𝕡base 𝕡base)))
-- -- --               (ΣPathP ((λ i → m + +-sym o n i) ,
-- -- --                 congP (λ z y → 𝕡· (𝕡base {n = m}) y) (𝕡·-comm  𝕡base 𝕡base)))
-- -- --        z = whiskSq.sq' (λ _ i → Σ ℕₐ⁺¹ ℙrmₐ)
-- -- --               (λ i j → (+-sym n (m + o) (j)) ,
-- -- --                   aHexBot n m o i j)
       
-- -- --               (ΣSquareP ((λ i i₁ → doubleCompPath-filler
-- -- --                  (sym (+-assoc n m o)) (+-sym n (m + o))
-- -- --                    (sym (+-assoc m o n)) i₁ i)
-- -- --                    , λ i k → fill 
-- -- --                  (λ k →
-- -- --                     ℙrmₐ {true}
-- -- --                     (doubleCompPath-filler
-- -- --                      (λ i₁ → +-assoc n m o (~ i₁))
-- -- --                      (+-sym n (m +  o))
-- -- --                      (λ i₁ → +-assoc m o n (~ i₁)) k
-- -- --                      i))
-- -- --                  (λ { k (i = i0) → 𝕡·-assoc {n} {m} {o}
-- -- --                          𝕡base 𝕡base 𝕡base k
-- -- --                     ; k (i = i1) → 𝕡·-assoc {m} {o} {n} 
-- -- --                         𝕡base 𝕡base 𝕡base (~ k)
-- -- --                     })
-- -- --                  (inS (𝕡·-comm (𝕡base {n = n})
-- -- --                    (𝕡· (𝕡base {n = m}) (𝕡base {n = o})) i)) k))
-- -- --               {!!} --(ΣSquareP ({!!} , {!!}))
-- -- --               {!!} --(ΣSquareP ({!!} , {!!}))
-- -- --               {!!} --(ΣSquareP ({!!} , {!!}))
-- -- --    in {!!}
-- -- --      -- hcomp
-- -- --      --   (λ k → {!λ {
-- -- --      --     (i = i0) → ?
-- -- --      --    ;(j = i0) → ?
-- -- --      --    ;(j = i1) → ?
-- -- --      --    }!})
-- -- --      --   {!!}
       
-- -- -- CompPSq.cu
       
-- -- --        (λ j i k → ℙrmₐ {true} (isGroupoid→isGroupoid' (isSet→isGroupoid isSetℕₐ⁺¹)
-- -- --         (λ _ → +-sym n (m + o)) s
-- -- --         (doubleCompPath-filler _ _ _)
-- -- --         (isSet→isSet' isSetℕₐ⁺¹ _ _
-- -- --           (+-assoc _ _ _ ∙ cong (_+ o) (+-sym _ _))
-- -- --           (sym (+-assoc _ _ _) ∙ cong (m +_) (+-sym _ _)))
-- -- --         ((isSet→isSet' isSetℕₐ⁺¹ _ _ _ _))
-- -- --         ((isSet→isSet' isSetℕₐ⁺¹ _ _ _ _)) k j i))
-- -- --        {a₀₀₋ = λ k → 𝕡base {n = +-assoc n m o k}}
-- -- --        {a₀₁₋ = λ k → 𝕡base {n = +-assoc m o n (~ k)}}

-- -- --         (λ i k → fill (λ k → ℙrmₐ
-- -- --       (doubleCompPath-filler (λ i₁ → +-assoc n m o (~ i₁))
-- -- --        (λ i₁ → +-sym n (m + o) i₁) (λ i₁ → +-assoc m o n (~ i₁)) k i))
-- -- --         (λ { k (i = i0) → 𝕡·-assoc 𝕡base 𝕡base 𝕡base k
-- -- --             ; k (i = i1) → 𝕡·-assoc 𝕡base 𝕡base 𝕡base (~ k)
-- -- --             }) (inS (𝕡·-comm 𝕡base (𝕡· 𝕡base 𝕡base) i)) k)
-- -- --        {a₁₀₋ = λ k → 𝕡loop {n = hcomp
-- -- --                                   (doubleComp-faces (λ _ → n + (m + o)) (λ i → +-sym n m i + o) k)
-- -- --                                   (+-assoc n m o k)} (𝕒𝕓 nothing n m (just o)
-- -- --                    {!!}) k}
-- -- --        {a₁₁₋ = λ k → 𝕡base {n = hcomp
-- -- --                                   (doubleComp-faces (λ _ → m + o + n) (λ i → m + +-sym o n i) k)
-- -- --                                   (+-assoc m o n (~ k))}}
     
-- -- --      (congSqP
-- -- --         {a₁₁ = cong (_+ o) (+-sym _ _) ∙ sym (+-assoc _ _ _)}
-- -- --         {a₁₋ = isSet→isSet' isSetℕₐ⁺¹ _ _ _ _}
-- -- --         {a₋₁ = isSet→isSet' isSetℕₐ⁺¹ _ _ _ _}
-- -- --         (λ i k x → 𝕡loop
-- -- --          (𝕒𝕓 nothing n m (just o) x)
-- -- --          (i ∨ k))
-- -- --            (flipSquareP (isSet→SquareP (λ _ _ → isProp→isSet (isSetℕₐ⁺¹ _ _))
-- -- --               _ _ _ _ )))
-- -- --      (λ i k → 𝕡loop {n = {!!}}
-- -- --                            (𝕒𝕓 nothing n m (just o)
-- -- --                            {!!}
-- -- --                            ) (i ∧ k))


-- -- -- -- Goal: n + m + o ≡
-- -- -- --       isSet→isSet' isSetℕₐ⁺¹ (λ i₁ → n + (m + o))
-- -- -- --       (λ i₁ → +-sym n m i₁ + o) (λ i₁ → +-assoc n m o i₁)
-- -- -- --       (λ i₁ → (+-assoc n m o ∙ (λ i₂ → +-sym n m i₂ + o)) i₁) k i
-- -- -- -- ———— Boundary (wanted) —————————————————————————————————————
-- -- -- -- k = i1 ⊢ λ i₁ → +-sym n m (i₁ ∧ i) + o
-- -- -- -- i = i1 ⊢ ((λ i₁ → +-assoc n m o (~ i₁)) ∙
-- -- -- --           (λ i' → (+-assoc n m o ∙ (λ i₁ → +-sym n m i₁ + o)) (k ∧ i')))

-- -- --      -- (λ i k → 𝕡loop ((𝕒𝕓 nothing n m (just o)
-- -- --      --        λ i₁ → {!!}
-- -- --      --       )) (i ∧  k))

-- -- -- -- Goal: n + m + o ≡
-- -- -- --       isSet→isSet' isSetℕₐ⁺¹ (λ i₁ → n + (m + o))
-- -- -- --       (λ i₁ → +-sym n m i₁ + o) (λ i₁ → +-assoc n m o i₁)
-- -- -- --       (λ i₁ → (+-assoc n m o ∙ (λ i₂ → +-sym n m i₂ + o)) i₁) k i
-- -- -- -- ———— Boundary (wanted) —————————————————————————————————————
-- -- -- -- k = i1 ⊢ λ i₁ → +-sym n m (i₁ ∧ i) + o
-- -- -- -- i = i1 ⊢ ((λ i₁ → +-assoc n m o (~ i₁)) ∙
-- -- -- --           (λ i' → (+-assoc n m o ∙ (λ i₁ → +-sym n m i₁ + o)) (k ∧ i')))

-- -- --      {!!}
-- -- --      -- ((λ j k → 𝕡invol
-- -- --      --     (𝕒𝕓 (just m) o n nothing {!λ i → m + +-sym o n (i ∧ j)!})
-- -- --      --     (𝕒𝕓 (just m) n o nothing {!!})
-- -- --      --       (refl , (refl , (refl , refl)))
-- -- --      --      (~ k) j))
-- -- --      (aHexBot n m o)

-- -- --    -- where
-- -- --    --  zz : SquareP
-- -- --    --         (λ i k →
-- -- --    --            ℙrmₐ {true}
-- -- --    --            (isGroupoid→isGroupoid' (isSet→isGroupoid isSetℕₐ⁺¹)
-- -- --    --             (λ _ → +-sym n (m + o)) s
-- -- --    --             (doubleCompPath-filler (λ i₁ → +-assoc n m o (~ i₁))
-- -- --    --              (+-sym n (m + o)) (λ i₁ → +-assoc m o n (~ i₁)))
-- -- --    --             (isSet→isSet' isSetℕₐ⁺¹ (+-sym n (m + o))
-- -- --    --              (λ i₁ → +-assoc m n o (~ i₁))
-- -- --    --              (+-assoc n m o ∙ (λ i₁ → +-sym n m i₁ + o))
-- -- --    --              ((λ i₁ → +-assoc m o n (~ i₁)) ∙ (λ i₁ → m + +-sym o n i₁)))
-- -- --    --             (isSet→isSet' isSetℕₐ⁺¹ (λ i₁ → n + (m + o))
-- -- --    --              (λ i₁ → +-sym n m i₁ + o) (λ i₁ → +-assoc n m o i₁)
-- -- --    --              (λ i₁ → (+-assoc n m o ∙ (λ i₂ → +-sym n m i₂ + o)) i₁))
-- -- --    --             (isSet→isSet' isSetℕₐ⁺¹ (λ i₁ → m + o + n)
-- -- --    --              (λ i₁ → m + +-sym o n i₁) (λ i₁ → +-assoc m o n (~ i₁))
-- -- --    --              (λ i₁ →
-- -- --    --                 ((λ i₂ → +-assoc m o n (~ i₂)) ∙ (λ i₂ → m + +-sym o n i₂)) i₁))
-- -- --    --             k i i0))
-- -- --    --         (λ k → 𝕡base)
-- -- --    --         (λ k →
-- -- --    --            𝕡loop
-- -- --    --            (𝕒𝕓 nothing n m (just o)
-- -- --    --             ((λ i → +-assoc n m o (~ i)) ∙
-- -- --    --              (λ i' → (+-assoc n m o ∙ (λ i → +-sym n m i + o)) (k ∧ i'))))
-- -- --    --            k)
-- -- --    --         (λ j → 𝕡base)
-- -- --    --         (λ j → congP (λ z x → 𝕡· x {m = {!!}} 𝕡base) (𝕡·-comm 𝕡base 𝕡base) j)
-- -- --    --  zz = 
-- -- --    --    congSqP
-- -- --    --      (λ i k x → 𝕡loop ((𝕒𝕓 nothing n m (just o)
-- -- --    --          x
-- -- --    --         )) (i ∧  k))
-- -- --    --    ((isSet→SquareP (λ _ _ → isProp→isSet (isSetℕₐ⁺¹ _ _))
-- -- --    --            _ _ _ _ ))
              
-- -- -- --    CompPSq.cu
-- -- -- --       (λ j i k → ℙrmₐ {true} (isGroupoid→isGroupoid' (isSet→isGroupoid isSetℕₐ⁺¹)
-- -- -- --         (λ _ → +-sym n (m + o)) s
-- -- -- --         (doubleCompPath-filler _ _ _)
-- -- -- --         (isSet→isSet' isSetℕₐ⁺¹ _ _ _ _)
-- -- -- --         ((isSet→isSet' isSetℕₐ⁺¹ _ _ _ _))
-- -- -- --         ((isSet→isSet' isSetℕₐ⁺¹ _ _ _ _)) k j i))

-- -- -- --       (λ i k → fill (λ k → ℙrmₐ
-- -- -- --       (doubleCompPath-filler (λ i₁ → +-assoc n m o (~ i₁))
-- -- -- --        (λ i₁ → +-sym n (m + o) i₁) (λ i₁ → +-assoc m o n (~ i₁)) k i))
-- -- -- --         (λ { k (i = i0) → 𝕡·-assoc 𝕡base 𝕡base 𝕡base k
-- -- -- --             ; k (i = i1) → 𝕡·-assoc 𝕡base 𝕡base 𝕡base (~ k)
-- -- -- --             }) (inS (𝕡·-comm 𝕡base (𝕡· 𝕡base 𝕡base) i)) k)

-- -- -- --        (λ i k → 𝕡loop (𝕒𝕓 nothing n m (just o)
         
-- -- -- --          (isSet→SquareP {A = λ i k →
-- -- -- --                           n + m + o ≡
-- -- -- --                   isSet→isSet' isSetℕₐ⁺¹ (+-sym n (m + o))
-- -- -- --                   (λ i₁ → +-assoc m n o (~ i₁))
-- -- -- --                   (λ i₁ → ((λ i₂ → +-assoc n m o i₂) ∙ (λ i₂ → +-sym n m i₂ + o)) i₁)
-- -- -- --                   (λ i₁ →
-- -- -- --                      ((λ i₂ → +-assoc m o n (~ i₂)) ∙ (λ i₂ → m + +-sym o n i₂)) i₁)
-- -- -- --                   k i}
               
-- -- -- --             (λ i k → isProp→isSet (isSetℕₐ⁺¹ _ _))
-- -- -- --             {a₀₀ = sym (+-assoc _ _ _)}
-- -- -- --             {a₀₁ = cong (_+ o) (+-sym _ _)}
-- -- -- --             (isSet→isSet' isSetℕₐ⁺¹ _ _ _ _)
-- -- -- --             {a₁₀ = sym (+-assoc _ _ _) ∙ +-sym _ _}
-- -- -- --             {a₁₁ = cong (_+ o) (+-sym _ _) ∙ sym (+-assoc _ _ _)}
-- -- -- --             (isSet→isSet' isSetℕₐ⁺¹ _ _ _ _)
-- -- -- --             (isSet→isSet' isSetℕₐ⁺¹ _ _ _ _)
-- -- -- --             (isSet→isSet' isSetℕₐ⁺¹ _ _ _ _) i k)
-- -- -- --             ) (k ∨ i))

-- -- -- --        (λ j k → 𝕡loop
-- -- -- --          (𝕒𝕓 nothing n m (just o)
-- -- -- --          (isSet→SquareP {A = λ j k → n + m + o ≡
-- -- -- --                 isSet→isSet' isSetℕₐ⁺¹ (λ i → n + (m + o)) (λ i → +-sym n m i + o)
-- -- -- --       (λ i → +-assoc n m o i)
-- -- -- --       (+-assoc _ _ _ ∙ cong (_+ o) (+-sym _ _)) k j}
-- -- -- --       (λ i k → isProp→isSet (isSetℕₐ⁺¹ _ _))
-- -- -- --                 {a₀₀ = sym (+-assoc _ _ _) }
-- -- -- --                 {a₀₁ = refl}
-- -- -- --                 (isSet→isSet' isSetℕₐ⁺¹ _ _ _ _)
-- -- -- --                 {sym (+-assoc _ _ _)}
-- -- -- --                 {cong (_+ o) (+-sym _ _)}
-- -- -- --                 (isSet→isSet' isSetℕₐ⁺¹ _ _ _ _)
-- -- -- --                 (isSet→isSet' isSetℕₐ⁺¹ _ _ _ _)
-- -- -- --                 (isSet→isSet' isSetℕₐ⁺¹ _ _ _ _)
-- -- -- --                 j k)
-- -- -- --                 )
-- -- -- --          (j ∧ k))
-- -- -- --        (λ j k → 𝕡invol
-- -- -- --          (𝕒𝕓 (just m) o n nothing {!!})
-- -- -- --          (𝕒𝕓 (just m) n o nothing {!!})
-- -- -- --            (refl , (refl , (refl , refl)))
-- -- -- --           (~ k) j)
-- -- -- --       (λ j i → 𝕡hex
-- -- -- --        (𝕒𝕓 nothing n m (just o) (sym (+-assoc _ _ _) ∙ λ i' → +-sym n (m + o) (i' ∧ i)))
-- -- -- --        (𝕒𝕓 nothing n (m + o) nothing λ i' → +-sym n (m + o) (i' ∧ i))
-- -- -- --        (𝕒𝕓 (just m) n o nothing ((+-assoc _ _ _ ∙ cong (_+ o) (+-sym _ _) )
-- -- -- --          ∙∙ sym (+-assoc _ _ _)
-- -- -- --           ∙∙ λ i' → +-sym n (m + o) (i' ∧ i)))
-- -- -- --        (refl , refl , refl , refl , refl ) (~ j) i
-- -- -- --        ) 
-- -- -- --    -- comp
-- -- -- --    --   (λ k → ℙrmₐ {true}
-- -- -- --    --      (isGroupoid→isGroupoid' (isSet→isGroupoid isSetℕₐ⁺¹)
-- -- -- --    --        (λ j i → +-sym n (m + o) i) s 
-- -- -- --    --        (doubleCompPath-filler _ _ _)
-- -- -- --    --         {!!}
-- -- -- --    --        {!!} {!λ k j → ?!}
-- -- -- --    --        k j i))
-- -- -- --    --   (λ k → λ {
-- -- -- --    --      (j = i0) →
-- -- -- --    --        fill (λ k → ℙrmₐ
-- -- -- --    --    (doubleCompPath-filler (λ i₁ → +-assoc n m o (~ i₁))
-- -- -- --    --     (λ i₁ → +-sym n (m + o) i₁) (λ i₁ → +-assoc m o n (~ i₁)) k i))
-- -- -- --    --      (λ { k (i = i0) → 𝕡·-assoc 𝕡base 𝕡base 𝕡base k
-- -- -- --    --          ; k (i = i1) → 𝕡·-assoc 𝕡base 𝕡base 𝕡base (~ k)
-- -- -- --    --          }) (inS (𝕡·-comm 𝕡base (𝕡· 𝕡base 𝕡base) i)) k
-- -- -- --    --     ;(j = i1) → 𝕡loop
-- -- -- --    --       (𝕒𝕓 nothing n m (just o)
-- -- -- --    --        λ i₁ →  +-sym n m i₁ + o)
-- -- -- --    --       (i ∨ k)
-- -- -- --    --     ;(i = i0) → 𝕡loop
-- -- -- --    --       (𝕒𝕓 nothing n m (just o)
-- -- -- --    --        λ i₁ → +-sym n m (i₁ ∧ j) + o)
-- -- -- --    --       (j ∧ k)
-- -- -- --    --     -- 𝕡·-assoc {n} {m} {o} 𝕡base 𝕡base 𝕡base (k ∧ ~ j)
-- -- -- --    --     ;(i = i1) → 𝕡invol ((m+AB m
-- -- -- --    --        (𝕒𝕓 nothing o n nothing (λ j₁ → +-sym o n (j₁ ∧ j)))))
-- -- -- --    --         ((𝕒𝕓 (just m) n o nothing λ i' → m + (n + o)))
-- -- -- --    --         {!!} (~ k) j
-- -- -- --    --       -- 𝕡·-assoc {m} {o} {n} 𝕡base 𝕡base 𝕡base ((~ k) ∨ j)
-- -- -- --    --     })
-- -- -- --    --   (𝕡hex
-- -- -- --    --     (𝕒𝕓 nothing n m (just o) λ i₁ → {!!})
-- -- -- --    --     (𝕒𝕓 nothing n (m + o) nothing (λ j₁ →  +-sym n (m + o) (j₁ ∧ i)))
-- -- -- --    --     (𝕒𝕓 (just m) n o nothing λ i₁ → {!!})
-- -- -- --    --     (refl , (refl , (refl , refl , refl))) (~ j) i)

-- fromFCSG : ∀ x → ℙrmₐ {true} (lenFCSG⊥ x)
-- fromFCSG = ElimFCSG.f w
--  where
--  w : ElimFCSG (λ z → ℙrmₐ (lenFCSG⊥ z))
--  ElimFCSG.asquash w _ = 𝕡squash _
--  ElimFCSG.●a w = 𝕡base
--  ElimFCSG.·a w x y = 𝕡· x y
--  ElimFCSG.·a-assoc w x y z = 𝕡·-assoc x y z
--  ElimFCSG.·a-comm w x y = 𝕡·-comm x y
--  ElimFCSG.·a-comminvol w x y = 𝕡·invol x y _
--  ElimFCSG.·a-hexDiag w a b c = {!𝕡·-comm!}
--    -- comp (λ k → ℙrmₐ {true} (
--    --            (doubleCompPath-filler
--    --               (sym (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m) (lenFCSG⊥ o)))
--    --               (+-sym (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o))
--    --               (sym (+-assoc _ _ _))
--    --               k i)))
--    --      (λ k → λ { (i = i0) → 𝕡·-assoc a b c k
--    --               ; (i = i1) → 𝕡·-assoc b c a (~ k)
--    --             })
--    --      (𝕡·-comm a (𝕡· b c) i)

--  ElimFCSG.·a-hex-up w {n} {m} {o} a b c j i =
--     {!!}
--    -- comp (λ k →  ℙrmₐ {true}
--    --              (isGroupoid→isGroupoid' (isSet→isGroupoid isSetℕₐ⁺¹)
--    --               (λ _ i → +-sym (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o) i)
--    --               (λ j i → (lenFCSG⊥ (·-hex-up n m o j i)))
--    --               (λ k i → (+-sym (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o) i))
--    --               (λ k i → (doubleCompPath-filler
--    --                           (sym (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m) (lenFCSG⊥ o)))
--    --                           (+-sym (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o))
--    --                           (sym (+-assoc _ _ _))
--    --                           k i))
--    --               (λ k j → +-assoc (lenFCSG⊥ n) (lenFCSG⊥ m) (lenFCSG⊥ o) (k ∧ j))
--    --               (λ k j → +-assoc (lenFCSG⊥ m) (lenFCSG⊥ o) (lenFCSG⊥ n) (~ k ∨ ~ j)) k j i)
--    --               )
--    --    (λ k → λ { (i = i0) → 𝕡·-assoc a b c (k ∧ j)
--    --               ; (i = i1) → 𝕡·-assoc b c a (~ k ∨ ~ j)
--    --               ; (j = i0) → (𝕡·-comm a (𝕡· b c) i)
--    --               })
--    --   (𝕡·-comm a (𝕡· b c) i)
             
--  ElimFCSG.·a-hex-down w {n} {m} {o} l c r =
--     {!!}
--    -- aHexDown l c r λ i i₁ → lenFCSG⊥ (·-hex-down n m o i i₁)


--  ElimFCSG.·a-pentagon-diag w {n} {m} {o} {p}  xs ys zs ws i = 
--       comp (λ k → ℙrmₐ {true} (
--               (doubleCompPath-filler
--                  (cong (_+ (lenFCSG⊥ p)) (sym (+-assoc _ (lenFCSG⊥ m) (lenFCSG⊥ o))))
--                  (sym (+-assoc _ _ _))
--                  (cong ((lenFCSG⊥ n) +_) (sym (+-assoc _ _ _))) k i)))
--         (λ k → λ { (i = i0) → 𝕡· (𝕡·-assoc xs ys zs k) ws 
--                  ; (i = i1) → 𝕡· xs (𝕡·-assoc ys zs ws (~ k))
--                })
--         (𝕡·-assoc xs (𝕡· ys zs) ws (~ i))

--  ElimFCSG.·a-pentagon-△ w = {!!}


--  ElimFCSG.·a-pentagon-□ w {n} {m} {o} {p} xs ys zs ws j i =
--      comp (λ k → ℙrmₐ {true}
--         (isGroupoid→isGroupoid' (isSet→isGroupoid isSetℕₐ⁺¹)
--             (λ j i → (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o)
--                     (lenFCSG⊥ p) (~ i)))
--             (λ j i → (lenFCSG⊥ (·-pentagon-□ n m o p j i)))
--             (doubleCompPath-filler _ _ _)
--             (λ k i → (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m + lenFCSG⊥ o)
--                  (lenFCSG⊥ p) (~ i)))
--             (λ k j → (+-assoc (lenFCSG⊥ n) (lenFCSG⊥ m) (lenFCSG⊥ o) (k ∧ ~ j)
--                      + lenFCSG⊥ p))
--             (λ k j → (lenFCSG⊥ n +
--                       +-assoc (lenFCSG⊥ m) (lenFCSG⊥ o) (lenFCSG⊥ p) (~ k ∨ j)))
--             k j i))
--         (λ k → λ { (i = i0) → 𝕡· (𝕡·-assoc xs ys zs (k ∧ ~ j)) ws 
--                  ; (i = i1) → 𝕡· xs (𝕡·-assoc ys zs ws (~ k ∨ j))
--                  ; (j = i1) → 𝕡·-assoc xs (𝕡· ys zs) ws (~ i)
--                })
--         (𝕡·-assoc xs (𝕡· ys zs) ws (~ i))

