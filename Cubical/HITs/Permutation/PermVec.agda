{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.PermVec where

open import Cubical.Data.Nat.Base as ℕ hiding (_·_)
open import Cubical.Data.Nat.Properties


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution

open import Cubical.Foundations.Everything
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Nat.Order.Permutation
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

open import Cubical.HITs.SequentialColimit as SC



open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)

open import Cubical.Relation.Binary

import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.Permutation.Base
open import Cubical.HITs.Permutation.Group

private
  variable
    ℓ : Level

module _ (A : Type ℓ) where

 em𝕍 : ∀ n → emℙrm n → Type ℓ
 em𝕍 n = 𝕍₃ A n ∘' Iso.inv (emℙrmIso n) 

 record 𝑽 (n : ℕ) : Type ℓ where
  constructor _𝒗_
  field
   𝕡𝑽 : ℙrm {true} n
   𝕧 : 𝕍₃ A n 𝕡𝑽
   

 ↔× : ∀ n → Rel (A ×^ n) (A ×^ n) ℓ
 ↔× n x y = Path (𝑽 n)
             (𝕡base 𝒗 x) (𝕡base 𝒗 y)

 ↔×𝕡 : ∀ n 𝕡 → Rel (𝕍₃ A n 𝕡) (𝕍₃ A n 𝕡) ℓ
 ↔×𝕡 n 𝕡 x y = Path (𝑽 n) (𝕡 𝒗 x) (𝕡 𝒗 y)



 ↔×-trans : (n : ℕ) → (a b c : A ×^ n) → ↔× n a b → ↔× n b c → ↔× n a c
 ↔×-trans n _ _ _ = _∙_

 ↔×𝕡-trans : (n : ℕ) → ∀ 𝕡 → (a b c : _)
    → ↔×𝕡 n 𝕡 a b → ↔×𝕡 n 𝕡 b c → ↔×𝕡 n 𝕡 a c
 ↔×𝕡-trans n _ _ _ _ = _∙_

 ↔// : ∀ n → Type ℓ
 ↔// n = (A ×^ n) // ↔×-trans n

 ↔//𝕡 : ∀ n → ℙrm {true} n → Type ℓ
 ↔//𝕡 n 𝕡 = 𝕍₃ A n 𝕡 // (↔×𝕡-trans n 𝕡)
 
 adjT'// : ∀ n k → (a : A ×^ n)  → Path (↔// n) [ adjT×^ (fst k) a ]// [ a ]// 
 adjT'// n k a = eq// λ i → 𝕡loop k i 𝒗 glue'AdjT× n (fst k) i a

 adjT// : ∀ n k → (a : A ×^ n)  → Path (↔// n) [ a ]// [ adjT×^ (fst k) a ]// 
 adjT// n k a = eq// λ i → 𝕡loop k i 𝒗 glueAdjT× n (fst k) i a


 module _ (isGrpA : isGroupoid A) where


  isGroupodid𝑽 : ∀ {n} → isGroupoid (𝑽 n)
  isGroupodid𝑽 {n} = w  
   where
    private
     w = isGroupoidRetract (λ (p 𝒗 x) → p , x) (λ (p , x) → p 𝒗 x )
            (λ _ → refl) (isGroupoidΣ (𝕡squash _) (isGroupoid𝕍₃ A isGrpA n))


  cons↔𝕡 : ∀ n p a x y → (↔×𝕡 n p x y)
                    → (↔×𝕡 (suc n) (sucℙrm n p)
                      (cons𝕍₃ A isGrpA n p a x)
                      (cons𝕍₃ A isGrpA n p a y))
  cons↔𝕡 n _ a x y =
    cong′ λ (𝕡 𝒗 v) → sucℙrm n 𝕡 𝒗 cons𝕍₃ A isGrpA n 𝕡 a v



  cons↔ : ∀ n a x y → (↔× n x y)
                    → (↔× (suc n) (a , x) (a , y))
  cons↔ n a x y =
    cong λ (𝕡 𝒗 v) → sucℙrm n 𝕡 𝒗 cons𝕍₃ A isGrpA n 𝕡 a v

  cong//𝕡 : ∀ n 𝕡 → A → ↔//𝕡 n 𝕡 → ↔//𝕡 (suc n) (sucℙrm n 𝕡)
  cong//𝕡 n 𝕡 a' = GQ.Rrec.f w
   where
   w : Rrec// (↔//𝕡 (suc n) (sucℙrm n 𝕡))
   Rrec//.Bgpd w = squash//
   Rrec//.fb w = [_]// ∘' (cons𝕍₃ A isGrpA n 𝕡 a')
   Rrec//.feq w = eq// ∘ cons↔𝕡 n 𝕡 a' _ _ 
   Rrec//.fsq w p r =
      comp// _ _ ▷ 
        cong′ eq// (sym (congFunct
           (λ (𝕡 𝒗 v) → sucℙrm n 𝕡
             𝒗 cons𝕍₃ A isGrpA n 𝕡 a' v) p r))

  []//𝕡 : ∀ n 𝕡 → (𝕍₃ A n) 𝕡 → ↔//𝕡 n 𝕡 
  []//𝕡 n 𝕡 = [_]//

  -- []//𝕡 : ∀ n 𝕡 → ↔//𝕡 n 𝕡 → (𝕍₃ A n) 𝕡  
  -- []//𝕡 n 𝕡 = ?


  -- consTrans↔ : ∀  n (a' : A) {a b c : A ×^ n}
  --         (p : ↔× n a b) (r₁ : ↔× n b c) →
  --       ↔×-trans (suc n) (a' , a) (a' , b) (a' , c) (cons↔ n a' a b p)
  --             (cons↔ n a' b c r₁)
  --             ≡ (λ z → cons↔ n a' a c (↔×-trans n a b c p r₁) z)
  -- consTrans↔ n a' p r =
  --   sym (congFunct
  --    (λ (𝕡 , v) → sucℙrm n 𝕡 , cons𝕍₃ A isGrpA n 𝕡 a' v)
  --     p r)
  
  cong// : ∀ n → A → ↔// n → ↔// (suc n)
  cong// n a' = GQ.Rrec.f w
   where
   w : Rrec// (↔// (suc n))
   Rrec//.Bgpd w = squash//
   Rrec//.fb w = [_]// ∘' (a' ,_)
   Rrec//.feq w = eq// ∘ cons↔ n a' _ _ 
   Rrec//.fsq w p r =
      comp// _ _ ▷
        cong′ eq// (sym (congFunct
           (λ (𝕡 𝒗 v) → sucℙrm n 𝕡
             𝒗 cons𝕍₃ A isGrpA n 𝕡 a' v) p r))
  
  -- _++//_ : ∀ {m n} → ↔// m → ↔// n → ↔// (m + n)
  -- _++//_ {m} {n} = GQ.Rrec.f (w m n)
  --  where
  --  w : ∀ m n → Rrec// (↔// n → ↔// (m + n))
  --  Rrec//.Bgpd (w m n) = isGroupoidΠ λ _ → squash//
  --  Rrec//.fb (w zero n) _ x = x
  --  Rrec//.fb (w (suc m) n) = {!!}
  --   -- ({!cong// (m + n) ?!} ∘'_) ∘' Rrec//.fb (w m)
  --  Rrec//.feq (w m n) = {!!}
  --  Rrec//.fsq (w m n) = {!!}



  eq//-refl↔ : ∀ n → (a b : A ×^ n) → (P : a ≡ b) →
        (cong [_]// P) ≡ (eq// λ i → 𝕡base 𝒗 P i) 
  eq//-refl↔ n a b P =
   let s : Square _ _ _ _
       s i j = comp// {Rt = ↔×-trans n}
          {P i} {b} {b} (λ i' → 𝕡base 𝒗 P (i ∨ i')) refl i j
       
   in λ i j →
      hcomp (λ z →
        λ {  (i = i0) → s (~ z ∨ j) i0
           ; (i = i1) → s (~ z) j
           ; (j = i0) → s (~ z) j
           ; (j = i1) → refl≡Id
              (↔×-trans n) {b} refl (sym compPathRefl) (~ i) (~ z)
           })
        (refl≡Id (↔×-trans n) {b} (↔×-trans n b b b refl refl)
          (cong (λ q → ↔×-trans n b b b q q) (sym compPathRefl))
           (~ i) j)


  eq//-invol'' : ∀ n → (v : A ×^ (suc (suc n))) → 
    Square {A = ↔// (suc (suc n))}
      (λ z →
          eq// (λ i → 𝕡loop (zero , tt) i 𝒗 glue'AdjT× (2 + n) zero i v) z)
      (λ z →
          eq// (λ i → 𝕡loop (zero , tt) i 𝒗 glueAdjT× (2 + n) zero i v) (~ z))
      refl
      refl
      
  eq//-invol'' n v =
     whiskSq.sq' (λ _ _ → ↔// (2 + n))
       (λ _ _ → [ v ]//)
       (λ i z → (comp// {Rt = ↔×-trans (2 + n)}
           (λ i → 𝕡loop (zero , _) (~ i) 𝒗 glue'AdjT× (2 + n) zero (~ i) v)
           (λ i → 𝕡loop (zero , _) i 𝒗 glue'AdjT× (2 + n) zero i v))
            i z )
          (λ i z → eq//
         (λ i → 𝕡loop (zero , _) i 𝒗 glueAdjT× (2 + n) zero i v)
             (~ i ∧ (z)))
       (cong eq// λ i j → 𝕡invol (zero , _) (~ i) j 𝒗
           Σ-swap-01-≡-invol-ua-glue (~ i) j v)
       ((cong′ eq// (rCancel _))
         ∙ sym (eq//-refl↔ (2 + n) v v refl))

  -- eq//-adjT : ∀ n → (a a' : A) → (v : ↔// n) →
  --     cong// (suc n) a (cong// n a' v) ≡
  --     cong// (suc n) a' (cong// n a v)
  -- eq//-adjT n a a' = GQ.RelimSet.f w
  --  where
  --  w : RelimSet
  --        (λ z →
  --           cong// (suc n) a (cong// n a' z) ≡
  --           cong// (suc n) a' (cong// n a z))
  --  RelimSet.truncB w _ = squash// _ _
  --  RelimSet.fb w v = adjT// (2 + n) (zero , _) (a , a' , v)   
  --  RelimSet.fbEq w = {!!}




--   eq//-invol : ∀ n → SquareP
--       (λ i j → 𝕍₃ A (suc (suc n)) (𝕡invol (zero , _) i j) → ↔// (suc (suc n)))
--       (λ j x → eq// (λ i' → 𝕡loop (zero , _) i' 𝒗 glue'AdjT× (2 + n) zero i'
--             (unglue (j ∨ ~ j) x)) j)
--       ((λ j x → eq// (λ i' → 𝕡loop (zero , _) i' 𝒗 glue'AdjT× (2 + n) zero i'
--             (unglue (j ∨ ~ j) x)) (~ j)))
--       refl
--       refl
      
--   eq//-invol n i j x = 
--    eq//-invol'' n
--      (swap-01 (unglue (i ∨ ~ i) (unglue (j ∨ ~ j) x)))
--       i j



  P-adjT : ∀ n → (a b : A ×^ n) → ∀ (xs : ⟨ 𝕡Ω₂ n ⟩) k →
               (PathP (λ i → 𝕍₃ A n ((𝕡loop k ∙ xs) i)) a b)
              → PathP (λ i → 𝕍₃ A n (xs i)) (adjT×^ (fst k) a) b 
  P-adjT n a b xs k x i =
     comp (λ z → 𝕍₃ A n (compPath-filler (𝕡loop k) xs i z ))
       (λ z → λ {(i = i0) → glueAdjT× n (fst k) z a
                ;(i = i1) → x z
                }) a


  P-adjT-fill : ∀ n → (a b : A ×^ n) → ∀ (xs : ⟨ 𝕡Ω₂ n ⟩) k →
               (P : PathP (λ i → 𝕍₃ A n ((𝕡loop k ∙ xs) i)) a b)
              → SquareP (λ i j →
                    𝕍₃ A n (compPath-filler (𝕡loop k) xs i j))
                  (λ i → glueAdjT× n (fst k) i a)
                  P
                  refl
                  (P-adjT n a b xs k P)
  P-adjT-fill n a b xs k x i z =
     fill (λ z → 𝕍₃ A n (compPath-filler (𝕡loop k) xs i z ))
       (λ z → λ {(i = i0) → glueAdjT× n (fst k) z a
                ;(i = i1) → x z
                }) (inS a) z

  P-adjT-comp : ∀ n → (a b : A ×^ n) → ∀ (xs : ⟨ 𝕡Ω₂ n ⟩) k →
               (P : PathP (λ i → 𝕍₃ A n ((𝕡loop k ∙ xs) i)) a b)
              → Path ((𝕡base 𝒗 a) ≡ (𝕡base 𝒗 b))
                (↔×-trans n _ (adjT×^ (fst k) a) _
                (λ i → 𝕡loop k i 𝒗 glueAdjT× n (fst k) i a)
                (λ i → xs i 𝒗 P-adjT n a b xs k P i))               
                (λ i → (𝕡loop k ∙ xs) i 𝒗 P i)
  P-adjT-comp n a b xs k P =
    sym (PathP∙∙→compPathR
          {p = refl}
          {sym (λ i → xs i 𝒗 P-adjT n a b xs k P i)}
        λ i j → compPath-filler (𝕡loop k) xs (~ i) j 𝒗
                (P-adjT-fill n a b  xs k P) (~ i) j)


  adjSq : ∀ n l → SquareP (λ i i' →
          adjT×^≡ {A = A} {n = n} l (~ i) → adjT×^≡ {A = A} {n = n} l (~ i'))
            {idfun _}
            {adjT×^ l}
            (symP (glue'AdjT× n l))
            {adjT×^ l}
            {idfun _}
            (symP (glueAdjT× n l))
            (symP (unglue'AdjT× n l))
            (symP (unglueAdjT× n l))
  adjSq zero l i i' = _
  adjSq (suc n) (suc l) i i' = map-snd (adjSq n l i i')
  adjSq (suc zero) zero i i' x = x
  adjSq (suc (suc n)) zero i i' =
   ua-gluePathExt (adjT×^≃ zero) (~ i') ∘ swap-01
    ∘  ua-ungluePathExt (adjT×^≃ zero) (~ i)

  eq//-commSS : ∀ n l → 
     SquareP
       (λ i j → A × A × adjT×^≡-invol {A = A} n (fst l) j (~ i)
          → ↔// (suc (suc n)))
      (λ j → [_]//) 
      (λ j → [_]// ∘' swap-01)
      (λ i x → eq// (λ i' →
         𝕡looop (zero , _) (suc (suc (fst l)) , (snd l)) i'
         𝒗
          glueBiAdjT×<SS n l (~ i')
              (map-snd (map-snd (adjSq n (fst l) i i')) (swap-01  x))) i
         )
      (λ i x → eq// (λ i' →
         𝕡looop (suc (suc (fst l)) , (snd l)) (zero , _)  i'
         𝒗
         glueBiAdjT×<SS n l i'
           ((map-snd (map-snd (adjSq n (fst l) (~ i) (~ i')))
             (x)))
         ) i)
  eq//-commSS n l i j x =
    let sf : SquareP (λ i j →
                PathP (λ i' →
                       A × A × adjT×^≡-invol {A = A} n (fst l) j (~ i)
                     → 𝑽 (2 + n))
                   ((𝕡base 𝒗_) ∘'
                     map-snd (map-snd (adjT×^≡-invol-unglue n (fst l) i j)))
                   ((𝕡base 𝒗_) ∘' swap-01 ∘' 
                     map-snd (map-snd (adjT×^≡-invol-unglue' n (fst l) i j))))
               (congSqP {A = λ j i' → A ×^ (2 + n) →
                     𝕍₃ A (2 + n)
                      (𝕡comm (zero , _) (suc (suc (fst l)) , snd l) _ i' j)}
                      (λ j i' →
                   (𝕡comm (zero , _) (suc (suc (fst l)) , snd l) _ i' j
                       𝒗_) ∘'_)
                       λ j i' →
                         glue-biAdjT×^≡-comm {n = n} (l) i' j ∘'
                           map-snd (map-snd
                            (adjT×^≡-invol-glue n (fst l) i' j)))
               (congSqP (λ j i' →
                   (𝕡comm (zero , _) (suc (suc (fst l)) , snd l) _ i' j
                       𝒗_) ∘'_)
                       λ j i' →
                         glue-biAdjT×^≡-comm {n = n} (l) i' j ∘'
                           map-snd (map-snd
                            (adjT×^≡-invol-glue' n (fst l) i' j)))

              (λ i i' x →
                𝕡looop (zero , _) (suc (suc (fst l)) , snd l) i'
                  𝒗
                  glueBiAdjT×<SS n l (~ i')
                  (map-snd (map-snd (adjSq n (fst l) i i')) (swap-01 x)))
              λ i i' x →
                𝕡looop (suc (suc (fst l)) , snd l) (zero , _) i'
                  𝒗 glueBiAdjT×<SS n l i'
                       ((map-snd (map-snd (adjSq n (fst l) (~ i) (~ i')))
                         (x)))
        sf = isSet→SquareP
              (λ i j → (isGroupoidΠ λ _ → isGroupodid𝑽 {2 + n}) _ _)
              _ _ _ _
    in eq// {a = map-snd (map-snd (adjT×^≡-invol-unglue n (fst l) i j)) x}
            {b = swap-01 (map-snd (map-snd (adjT×^≡-invol-unglue' n (fst l) i j)) x)}
            (λ i' → sf i j i' x) i
    
  Iso-//→ : ∀ n → ∀ 𝕡 → (𝕍₃ A n) 𝕡 → (↔// n)
  Iso-//→ n 𝕡base = [_]//

  Iso-//→ (suc n) (𝕡loop (suc k , k<) i) (a , x) =
    cong// n a (Iso-//→ n (𝕡loop (k , k<) i) x)
  Iso-//→ (suc (suc n)) (𝕡loop (zero , tt) i) x =
    eq// (λ i' → 𝕡loop (zero , _) i' 𝒗 glue'AdjT× (2 + n) zero i'
      (unglue (i ∨ ~ i) x)) i

  Iso-//→ n (𝕡looop (zero , k<) (zero , l<) i) = [_]//
  Iso-//→ (suc n) (𝕡looop (suc k , k<) (suc l , l<) i) (a , x) =
    cong// n a (Iso-//→ n (𝕡looop (k , k<) (l , l<) i) x)
  Iso-//→ (suc (suc n)) (𝕡looop (zero , _) (suc (suc l) , l<) i) x =
    eq// (λ i' → 𝕡looop (zero , _) (suc (suc l) , l<) i'
               𝒗 glueBiAdjT×<SS n (l , l<) (~ i')
                 (adjSq (2 + n) (2 + l) i i' (unglue (i ∨ ~ i) x))) i
  Iso-//→ (suc (suc (suc n))) (𝕡looop (zero , _) (suc zero , _) i) x =
    eq// (λ i' → 𝕡looop (zero , _) (suc zero , _) i'
               𝒗 glueBiAdjT×< n (~ i') (unglue (i ∨ ~ i) x)) i
  Iso-//→ (suc (suc n)) (𝕡looop (suc (suc k) , k<) (zero , _) i) x =
    eq// (λ i' → 𝕡looop (suc (suc k) , k<) (zero , _) i'
               𝒗 glueBiAdjT×<SS n (k , k<) i'
                 (adjSq (2 + n) (2 + k) (~ i) (~ i') (unglue (i ∨ ~ i) x))) i

  Iso-//→ (suc (suc (suc n))) (𝕡looop (suc zero , _) (zero , _) i) x =
    eq// (λ i' → 𝕡looop (suc zero , _) (zero , _) i'
               𝒗 glueBiAdjT×< n i' (unglue (i ∨ ~ i) x)) i

  Iso-//→ (suc n) (𝕡comp (suc k , k<) (suc l , l<) i i₁) (a , x) =
    cong// n a (Iso-//→ n  (𝕡comp (k , k<) (l , l<) i i₁) x)
  Iso-//→ (suc (suc n)) (𝕡comp (zero , _) (zero , _) i i₁) x =
    Iso-//→ (suc (suc n)) (𝕡loop (zero , _) i₁) x

  Iso-//→ (suc (suc n)) (𝕡comp (zero , _) (suc (suc l) , l<) i i₁) x =
    {!!}
  Iso-//→ (suc (suc (suc n))) (𝕡comp (zero , _) (suc zero , l<) i i₁) x =
    {!!}

  Iso-//→ (suc (suc n)) (𝕡comp (suc zero , k<) (zero , l<) i i₁) x =
    {!!}
  Iso-//→ (suc (suc (suc n))) (𝕡comp (suc (suc k) , k<) (zero , l<) i i₁) x =
    {!!}

  Iso-//→ (suc n) (𝕡invol (suc k , k<) i i₁) (a , x) =
    cong// n a (Iso-//→ n  (𝕡invol (k , k<) i i₁) x)
  Iso-//→ (suc (suc n)) (𝕡invol (zero , _) i j) =
     (λ x → eq//-invol'' n x i j) ∘' 
     (swap-01 ∘' unglue (i ∨ ~ i) ∘' unglue (j ∨ ~ j))
      
  Iso-//→ (suc n) (𝕡comm (suc k , k<) (suc l , l<) x₁ i j) (a , x) =
    cong// n a (Iso-//→ n (𝕡comm (k , k<) (l , l<) (pred-commT k l x₁) i j) x)
  Iso-//→ (suc (suc n)) (𝕡comm (zero , _) (suc (suc l) , l<) _ i j) =
    eq//-commSS n (l , l<) i j ∘' unglue (j ∨ ~ j) ∘' unglue (i ∨ ~ i)

  Iso-//→ (suc n) (𝕡braid (suc k) k< i i₁) (a , x) =
    cong// n a (Iso-//→ n (𝕡braid k k< i i₁) x)
  Iso-//→ (suc (suc (suc n))) (𝕡braid zero k< i i₁) x = {!!}
  
  Iso-//→ n (𝕡squash _ x y p q r s i i₁ i₂) =
    isOfHLevel→isOfHLevelDep 3 (λ _ → isGroupoidΠ (λ x → squash//))
      (Iso-//→ n x) (Iso-//→ n y)
      (λ i → Iso-//→ n (p i)) (λ i → Iso-//→ n (q i))
      (λ i j → Iso-//→ n (r i j)) (λ i j → Iso-//→ n (s i j))
      (𝕡squash _ x y p q r s)
      i i₁ i₂
  

  Iso-//← : ∀ n → (↔// n) → 𝑽 n 
  Iso-//← n [ a ]// = 𝕡base 𝒗 a 
  Iso-//← n (eq// r i) = r i
  Iso-//← n (comp// r s j i) = compPath-filler r s j i
  Iso-//← n (squash// x x₁ p q r s i i₁ i₂) =
    isGroupodid𝑽
      _ _ _ _
       (λ i j → Iso-//← n (r i j))
       (λ i j → Iso-//← n (s i j))
       i i₁ i₂
       
  adjT-sec : ∀ n k a →
    (cong (λ (x 𝒗 y) →  (Iso-//→ n) x y)
       (λ i → (𝕡loop k i) 𝒗 (glueAdjT× n (fst k) i a)))
    ≡ eq// (λ i → 𝕡loop k i 𝒗 glueAdjT× n (fst k) i a) 
  adjT-sec (suc n) (suc k , k<) (x , xs)  =
    cong′ (cong′ (cong// n x)) (adjT-sec (n) (k , k<) (xs))
  adjT-sec (suc (suc n)) (zero , _) _ = refl
  
  Iso-//-sec-eq' :  ∀ n (p : ⟨ 𝕡Ω₂ n ⟩) a b
      (P : PathP (λ i → 𝕍₃ A n (p i)) a b) →
     (cong (λ (x 𝒗 y) →  (Iso-//→ n) x y) (λ i → p i 𝒗 P i))
       ≡ eq// (λ i → p i 𝒗 P i)
  Iso-//-sec-eq' n = elimℙrm≡ _ _
      (λ _ → isPropΠ3 λ _ _ _ → squash// _ _ _ _)
    (eq//-refl↔ n)
    λ k xs x a b P →
      let x' : cong (λ (x 𝒗 y) →  (Iso-//→ n) x y)
               (λ i → xs i 𝒗 P-adjT n a b xs k P i) ≡
                 eq// (λ i → xs i 𝒗 P-adjT n a b xs k P i)
          x' = x (adjT×^ (fst k) a) b (P-adjT n a b xs k P)

          pp : cong (λ (x 𝒗 y) →  (Iso-//→ n) x y)
                 ((λ i → 𝕡loop k i 𝒗 glueAdjT× n (fst k) i a) ∙
                  (λ i → xs i 𝒗 P-adjT n a b xs k P i))
                 ≡
                 eq//
                 (↔×-trans n (glueAdjT× n (fst k) i0 a) (P-adjT n a b xs k P i0)
                  (P-adjT n a b xs k P i1)
                  (λ i → 𝕡loop k i 𝒗 glueAdjT× n (fst k) i a)
                  (λ i → xs i 𝒗 P-adjT n a b xs k P i))
          pp = (
            congFunct (λ (x 𝒗 y) →  (Iso-//→ n) x y)
               (λ i → 𝕡loop k i 𝒗 glueAdjT× n (fst k) i a)
                (λ i → xs i 𝒗 P-adjT n a b xs k P i))
           ∙∙ (λ i → adjT-sec n k a i ∙ x' i) ∙∙
            (sym (comp'// _  (↔×-trans n) _ _))
      in  cong′ (cong (λ (x 𝒗 y) →  (Iso-//→ n) x y))
            (sym (P-adjT-comp n a b xs k P))
         ∙∙ pp ∙∙
          cong′ eq// (P-adjT-comp n a b xs k P)


  Iso-//-sec : ∀ n → section {A = 𝑽 n} {↔// n} (λ (x 𝒗 y) → (Iso-//→ n) x y) (Iso-//← n)
  Iso-//-sec n = GQ.RelimSet.f (w n)
   where
   w : ∀ n → GQ.RelimSet {Rt = ↔×-trans n}
        (λ z →  (let (x 𝒗 y) = Iso-//← n z
                 in  Iso-//→ n x y) ≡ z)
   RelimSet.truncB (w _) _ = squash// _ _
   RelimSet.fb (w n) _ = refl
   RelimSet.fbEq (w n) p = 
     flipSquare
     (Iso-//-sec-eq' n (cong′ 𝑽.𝕡𝑽 p) _ _ (cong 𝑽.𝕧 p))
   


  -- Iso-//-ret-lem' : ∀ n k k< (a : A) (x// : ↔// n) → 
  --    SquareP (λ i _ → Σ (ℙrm (suc n)) (𝕍₃ A (suc n)))
  --      {!!}
  --      {!!}
  --      (λ i →
  --        let (q , v) = Iso-//← n x// 
  --        in (sucℙrm n q) ,
  --           cons𝕍₃ A isGrpA n q a (v))
  --      (λ i → Iso-//← (suc n)
  --        (cong// n a x//))
  --      -- (λ i v → Iso-//← (suc n)
  --      --   (uncurry (Iso-//→ (suc n)) (𝕡loop (suc k , k<) i , (a , v))))
  -- Iso-//-ret-lem' n k k< a i j = {!!}


--  -- -- --  Iso-//-ret-lem : ∀ n k k< (a : A) →
--  -- -- --     SquareP (λ i _ → adjT×^≡ {A = A} {n = n} k i → Σ (ℙrm (suc n)) (𝕍₃ A (suc n)))
--  -- -- --       refl
--  -- -- --       refl
--  -- -- --       (λ i v' →
--  -- -- --         let (q , v) = Iso-//← n (uncurry (Iso-//→ n)
--  -- -- --                       (𝕡loop (k , k<) i , (v'))) 
--  -- -- --         in (sucℙrm n q) ,
--  -- -- --            cons𝕍₃ A isGrpA n q a (v))
--  -- -- --       (λ i v → Iso-//← (suc n)
--  -- -- --         (cong// n a (Iso-//→ n (𝕡loop (k , k<) i) v)))
--  -- -- --       -- (λ i v → Iso-//← (suc n)
--  -- -- --       --   (uncurry (Iso-//→ (suc n)) (𝕡loop (suc k , k<) i , (a , v))))
--  -- -- --  Iso-//-ret-lem n k k< a i j = {!!}

--  -- -- --  Iso-//-ret : ∀ n → retract (uncurry (Iso-//→ n)) (Iso-//← n)
--  -- -- --  Iso-//-ret n = uncurry (R𝕡elimSet'.f (w n))
--  -- -- --   where
--  -- -- --   w : ∀ n → R𝕡elimSet'
--  -- -- --         (λ z →
--  -- -- --            (y : 𝕍₃ A n z) → Iso-//← n (uncurry (Iso-//→ n) (z , y)) ≡ (z , y))
--  -- -- --   R𝕡elimSet'.isSetA (w n) _ = isSetΠ
--  -- -- --     λ _ → isGroupoidΣ (𝕡squash _ ) (isGroupoid𝕍₃ A isGrpA n) _ _
--  -- -- --   R𝕡elimSet'.abase (w n) y = refl


--  -- -- --   R𝕡elimSet'.aloop (w (suc n)) (suc k , k<) = 
--  -- -- --     let X = R𝕡elimSet'.aloop (w n) (k , k<)
--  -- -- --     in  λ i (a , v) j →
--  -- -- --          hcomp
--  -- -- --              (λ z →
--  -- -- --                λ { (i = i0) →
--  -- -- --                 Iso-//← (suc n) (uncurry (Iso-//→ (suc n)) (𝕡base , (a , v)))
--  -- -- --                  ; (i = i1) →
--  -- -- --                 Iso-//← (suc n) (uncurry (Iso-//→ (suc n)) (𝕡base , (a , v)))
--  -- -- --                  ; (j = i0) → Iso-//-ret-lem n k k< a i z v
--  -- -- --                  ; (j = i1) → (𝕡loop (suc k , k<) i , (a , v))
--  -- -- --                  })
--  -- -- --              (sucℙrm n (fst (X i v j)) ,
--  -- -- --                cons𝕍₃ A isGrpA n (fst (X i v j)) a (snd (X i v j))) 

--  -- -- --   R𝕡elimSet'.aloop (w (suc (suc n))) (zero , tt) i (y) i₁ =
--  -- -- --     𝕡loop (zero , tt) i , y
   
--  -- -- -- -- -- --  -- Iso-//← : ∀ n → (↔// n) → {!Σ ? ?!}
--  -- -- -- -- -- --  -- Iso-//← = {!!}

--  -- -- -- -- -- -- -- -- EMelim.f w
--  -- -- -- -- -- -- -- --  where
--  -- -- -- -- -- -- -- --  w : EMelim (𝕡Ω₂ n) (λ z → em𝕍 n z → ↔// n)
--  -- -- -- -- -- -- -- --  EMelim.isGrpB w _ = isGroupoidΠ λ _ →  squash//
--  -- -- -- -- -- -- -- --  EMelim.b w = [_]//
--  -- -- -- -- -- -- -- --  EMelim.bPathP w g i xᵍ =
--  -- -- -- -- -- -- -- --    let x = {!xᵍ!}
--  -- -- -- -- -- -- -- --    in {!!}
--  -- -- -- -- -- -- -- --  -- eq// (g , {!x!}) i
--  -- -- -- -- -- -- -- --  EMelim.bSqP w = {!!}


--  -- -- -- -- -- -- -- -- Iso-//→ : ∀ n → ∀ emp →  (em𝕍 n) emp → (↔// n)
--  -- -- -- -- -- -- -- -- Iso-//→ n = EMelim.f w
--  -- -- -- -- -- -- -- --  where
--  -- -- -- -- -- -- -- --  w : EMelim (𝕡Ω₂ n) (λ z → em𝕍 n z → ↔// n)
--  -- -- -- -- -- -- -- --  EMelim.isGrpB w _ = isGroupoidΠ λ _ →  squash//
--  -- -- -- -- -- -- -- --  EMelim.b w = [_]//
--  -- -- -- -- -- -- -- --  EMelim.bPathP w g i xᵍ =
--  -- -- -- -- -- -- -- --    let x = {!xᵍ!}
--  -- -- -- -- -- -- -- --    in {!!}
--  -- -- -- -- -- -- -- --  -- eq// (g , {!x!}) i
--  -- -- -- -- -- -- -- --  EMelim.bSqP w = {!!}

--  -- -- -- -- -- -- -- -- -- Iso-// : ∀ n → Iso (Σ _ (em𝕍 n)) (↔// n)
--  -- -- -- -- -- -- -- -- -- Iso.fun (Iso-// n) = {!!}
--  -- -- -- -- -- -- -- -- -- Iso.inv (Iso-// n) = {!!}
--  -- -- -- -- -- -- -- -- -- Iso.rightInv (Iso-// n) = {!!}
--  -- -- -- -- -- -- -- -- -- Iso.leftInv (Iso-// n) = {!!}



--  module direct-FMSet₂-≃ (isGrpA : isGroupoid A) where

--   cons↔ : ∀ n a x y → (↔× n x y)
--                     → (↔× (suc n) (a , x) (a , y))
--   cons↔ n a x y =
--     cong λ (𝕡 , v) → sucℙrm n 𝕡 , cons𝕍₃ A isGrpA n 𝕡 a v


--   cong// : ∀ n → A → ↔// n → ↔// (suc n)
--   cong// n a' = GQ.Rrec.f w
--    where
--    w : Rrec// (↔// (suc n))
--    Rrec//.Bgpd w = squash//
--    Rrec//.fb w = [_]// ∘' (a' ,_)
--    Rrec//.feq w = eq// ∘ cons↔ n a' _ _ 
--    Rrec//.fsq w p r =
--       comp// _ _ ▷
--         cong′ eq// (sym (congFunct
--            (λ (𝕡 , v) → sucℙrm n 𝕡
--              , cons𝕍₃ A isGrpA n 𝕡 a' v) p r))

--   -- cong//' : ∀ n → A → ↔// n → ↔// (suc n)
--   -- cong//' n a' [ a ]// = [ a' , a ]//
--   -- cong//' n a' (eq// r₁ i) = eq// (cons↔ n a' _ _ r₁) i
--   -- cong//' n a' (comp// p r j i) =
--   --         (comp// _ _ ▷
--   --       cong′ eq// (sym (congFunct
--   --          (λ (𝕡 , v) → sucℙrm n 𝕡
--   --            , cons𝕍₃ A isGrpA n 𝕡 a' v) p r))) j i

--   -- cong//' n a' (squash// x x₁ p q r₁ s₁ i i₁ i₂) = {!!}

-- -- GQ.Rrec.f w
-- --    where
-- --    w : Rrec// (↔// (suc n))
-- --    Rrec//.Bgpd w = squash//
-- --    Rrec//.fb w = [_]// ∘' (a' ,_)
-- --    Rrec//.feq w = eq// ∘ cons↔ n a' _ _ 
-- --    Rrec//.fsq w p r =
-- --       comp// _ _ ▷
-- --         cong′ eq// (sym (congFunct
-- --            (λ (𝕡 , v) → sucℙrm n 𝕡
-- --              , cons𝕍₃ A isGrpA n 𝕡 a' v) p r))


--   cons↔-comm : ∀ (n : ℕ) → ∀ x y → (v : ↔// n) →
--       cong// (suc n) x (cong// n y v) ≡
--       cong// (suc n) y (cong// n x v) 
--   cons↔-comm n a a' [ v ]// = adjT// _ (zero , _) _
--   cons↔-comm n a a' (eq// r i) = {!!}
--   cons↔-comm n a a' (comp// r s j i) = {!!}
--   cons↔-comm n a a' (squash// v v₁ p q r₁ s₁ i i₁ i₂) = {!!}
--     -- GQ.RelimSet.f w
--     -- where
--     -- w : RelimSet
--     --       (λ z →
--     --          cong// (suc n) a (cong// n a' z) ≡
--     --          cong// (suc n) a' (cong// n a z))
--     -- RelimSet.truncB w = {!!}
--     -- RelimSet.fb w _ = adjT// _ (zero , _) _
--     -- RelimSet.fbEq w r = {!!}
--       -- adjT// (suc (suc n)) (zero , tt) () j

-- -- --   w : RRec {A = A} {B = Σ ℕ (↔//)}
-- -- --              (isGroupoidΣ
-- -- --                   (isSet→isGroupoid isSetℕ) λ _ → squash//)
-- -- --   RRec.[]* w = zero , [ _ ]//
-- -- --   RRec._∷*_ w a (k , v) = suc k , cong// k a v 
-- -- --   RRec.comm* w x y = uncurry {!!}
   
-- -- --   RRec.comm-inv* w = {!!}
-- -- --   RRec.commmL* w = {!!}
-- -- --   RRec.commmR* w = {!!}
-- -- --   RRec.commpL* w = {!!}
-- -- --   RRec.commpR* w = {!!}
-- -- --   RRec.hex* w = {!!}

-- -- --   f : FMSet2 A → Σ _ (↔//)
-- -- --   f = RRec.f {B = Σ ℕ (↔//)} w


-- module FMSet₂-≃ (A : Type ℓ) (isGrpA : isGroupoid A) where
--  w : RRec {B = Σ (Σ _ (ℙrm {true})) (λ (n , 𝕡) → (𝕍₃ A n 𝕡))}
--              (isGroupoidΣ
--                (isGroupoidΣ
--                  (isSet→isGroupoid isSetℕ) {!!})
--                 {!!}
--                 )
--  w = {!!}

--  f : FMSet2 A → Σ (Σ _ (ℙrm {true})) (uncurry (𝕍₃ A))
--  f = RRec.f w
  
